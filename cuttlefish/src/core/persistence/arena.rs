//! WALArena: 4K-aligned memory arena for zero-copy WAL staging.
//!
//! Provides fixed-size slots for payload storage. The kernel copies payloads
//! into arena slots before invariant application, ensuring safe ownership
//! for async io_uring writes.
//!
//! ## Lifecycle Management
//!
//! Each slot has an atomic reference count that tracks consumers:
//! - `admit()` sets RefCount to N (typically 2: Persistence + Network)
//! - io_uring completion decrements RefCount
//! - Network broadcast completion decrements RefCount
//! - When RefCount reaches 0, the slot is automatically released to the free pool
//!
//! This ensures zero-copy safety: the slot memory remains valid until all
//! consumers have finished reading.

use core::cell::UnsafeCell;
use core::sync::atomic::{AtomicU32, AtomicU64, Ordering};

/// Reference count value indicating slot is not in use.
pub const REFCOUNT_FREE: u32 = 0;

/// Default reference count for dual-consumer mode (Persistence + Network).
pub const REFCOUNT_DUAL: u32 = 2;

/// Reference count for persistence-only mode.
pub const REFCOUNT_PERSIST_ONLY: u32 = 1;

/// Reference count for network-only mode (volatile facts).
pub const REFCOUNT_NETWORK_ONLY: u32 = 1;

/// Slot size: 256 bytes (fits most fact payloads, cache-line friendly).
pub const SLOT_SIZE: usize = 256;

/// Number of slots per arena page (4K / 256 = 16 slots per page, but we use more pages).
pub const SLOTS_PER_ARENA: usize = 4096;

/// Total arena size: 1MB (4096 slots × 256 bytes).
pub const ARENA_SIZE: usize = SLOTS_PER_ARENA * SLOT_SIZE;

/// Slot index type.
pub type SlotIndex = u32;

/// Invalid slot index sentinel.
pub const INVALID_SLOT: SlotIndex = u32::MAX;

/// Slot header stored at the beginning of each slot.
#[derive(Debug, Clone, Copy)]
#[repr(C)]
pub struct SlotHeader {
    /// Fact ID for this slot.
    pub fact_id: [u8; 32],
    /// Actual payload length (may be less than SLOT_SIZE - header).
    pub payload_len: u32,
    /// Sequence number for ordering.
    pub sequence: u64,
    /// Reference count (for zero-copy reads).
    pub refcount: u32,
    /// Slot state: 0 = free, 1 = writing, 2 = committed, 3 = persisted.
    pub state: u32,
}

const _: () = {
    assert!(core::mem::size_of::<SlotHeader>() == 56);
};

impl SlotHeader {
    #[inline(always)]
    pub const fn empty() -> Self {
        Self {
            fact_id: [0u8; 32],
            payload_len: 0,
            sequence: 0,
            refcount: 0,
            state: 0,
        }
    }
}

/// Payload capacity per slot (slot size minus header).
pub const PAYLOAD_CAPACITY: usize = SLOT_SIZE - core::mem::size_of::<SlotHeader>();

const _: () = {
    assert!(PAYLOAD_CAPACITY == 200);
};

/// Slot states.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u32)]
pub enum SlotState {
    Free = 0,
    Writing = 1,
    Committed = 2,
    Persisted = 3,
}

/// A single slot in the arena.
#[derive(Debug, Clone, Copy)]
#[repr(C, align(64))]
pub struct ArenaSlot {
    pub header: SlotHeader,
    pub payload: [u8; PAYLOAD_CAPACITY],
}

const _: () = {
    assert!(core::mem::size_of::<ArenaSlot>() == 256);
    assert!(core::mem::align_of::<ArenaSlot>() == 64);
};

impl ArenaSlot {
    #[inline(always)]
    pub const fn empty() -> Self {
        Self {
            header: SlotHeader::empty(),
            payload: [0u8; PAYLOAD_CAPACITY],
        }
    }
}

/// Error returned when arena operations fail.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ArenaError {
    /// No free slots available.
    Full,
    /// Payload too large for slot.
    PayloadTooLarge,
    /// Invalid slot index.
    InvalidSlot,
    /// Slot not in expected state.
    InvalidState,
}

/// WALArena: Fixed-size, 4K-aligned memory arena for WAL staging.
///
/// Design:
/// - Slots are acquired by the kernel before invariant application.
/// - Payload is copied into the slot (single memcpy).
/// - SlotIndex is passed to SPSC for io_uring worker.
/// - Worker reads directly from arena (zero-copy to disk).
/// - Network layer can also read from arena (zero-copy broadcast).
///
/// Lifecycle:
/// - `acquire_slot_with_refcount(N)` claims a slot with N consumers
/// - Each consumer calls `decrement_refcount()` when done
/// - When refcount hits 0, slot is automatically released to free pool
#[repr(C, align(4096))]
pub struct WALArena {
    slots: UnsafeCell<[ArenaSlot; SLOTS_PER_ARENA]>,
    /// Atomic reference counts for each slot.
    /// Stored separately from slots for cache-line efficiency during refcount ops.
    refcounts: [AtomicU32; SLOTS_PER_ARENA],
    /// Bitmap tracking free slots (1 = free, 0 = in use).
    /// 4096 slots = 64 u64 words.
    free_bitmap: [AtomicU64; 64],
    /// Next slot hint for allocation (reduces contention).
    alloc_hint: AtomicU32,
    /// Global sequence counter.
    sequence: AtomicU64,
    /// Count of free slots.
    free_count: AtomicU32,
    _pad: [u8; 44],
}

const _: () = {
    // Verify 4K alignment
    assert!(core::mem::align_of::<WALArena>() == 4096);
};

// Safety: WALArena uses atomic operations for synchronization.
unsafe impl Send for WALArena {}
unsafe impl Sync for WALArena {}

impl WALArena {
    /// Create a new arena with all slots free.
    pub fn new() -> Self {
        // Initialize all bitmap words to all-ones (all free).
        let mut free_bitmap: [AtomicU64; 64] = unsafe { core::mem::zeroed() };
        for word in &mut free_bitmap {
            *word = AtomicU64::new(u64::MAX);
        }

        // Initialize all refcounts to 0.
        let refcounts: [AtomicU32; SLOTS_PER_ARENA] = {
            // Safety: AtomicU32 with value 0 has same repr as zeroed memory
            unsafe { core::mem::zeroed() }
        };

        Self {
            slots: UnsafeCell::new([ArenaSlot::empty(); SLOTS_PER_ARENA]),
            refcounts,
            free_bitmap,
            alloc_hint: AtomicU32::new(0),
            sequence: AtomicU64::new(0),
            free_count: AtomicU32::new(SLOTS_PER_ARENA as u32),
            _pad: [0u8; 44],
        }
    }

    /// Acquire a free slot for writing with a specific initial refcount.
    ///
    /// The refcount determines how many consumers must call `decrement_refcount`
    /// before the slot is automatically released:
    /// - `REFCOUNT_DUAL` (2): Persistence + Network
    /// - `REFCOUNT_PERSIST_ONLY` (1): Persistence only
    /// - `REFCOUNT_NETWORK_ONLY` (1): Network only (volatile)
    ///
    /// Returns the slot index or ArenaError::Full if no slots available.
    #[inline]
    pub fn acquire_slot_with_refcount(&self, initial_refcount: u32) -> Result<SlotIndex, ArenaError> {
        let hint = self.alloc_hint.load(Ordering::Relaxed) as usize;

        // Search from hint, wrapping around.
        for offset in 0..64 {
            let word_idx = (hint / 64 + offset) % 64;
            let word = &self.free_bitmap[word_idx];

            loop {
                let current = word.load(Ordering::Acquire);
                if current == 0 {
                    break; // No free bits in this word.
                }

                // Find first set bit.
                let bit_idx = current.trailing_zeros() as usize;
                let mask = 1u64 << bit_idx;

                // Try to claim it.
                match word.compare_exchange_weak(
                    current,
                    current & !mask,
                    Ordering::AcqRel,
                    Ordering::Relaxed,
                ) {
                    Ok(_) => {
                        let slot_idx = (word_idx * 64 + bit_idx) as SlotIndex;

                        // Update hint for next allocation.
                        self.alloc_hint.store(slot_idx.wrapping_add(1), Ordering::Relaxed);
                        self.free_count.fetch_sub(1, Ordering::Relaxed);

                        // Set initial refcount atomically.
                        self.refcounts[slot_idx as usize].store(initial_refcount, Ordering::Release);

                        // Mark slot as writing.
                        unsafe {
                            let slot = &mut (*self.slots.get())[slot_idx as usize];
                            slot.header.state = SlotState::Writing as u32;
                            slot.header.sequence = self.sequence.fetch_add(1, Ordering::Relaxed);
                            slot.header.refcount = initial_refcount; // Mirror for debugging
                        }

                        return Ok(slot_idx);
                    }
                    Err(_) => continue, // Retry.
                }
            }
        }

        Err(ArenaError::Full)
    }

    /// Acquire a free slot for writing with default refcount of 1.
    /// Returns the slot index or ArenaError::Full if no slots available.
    #[inline]
    pub fn acquire_slot(&self) -> Result<SlotIndex, ArenaError> {
        self.acquire_slot_with_refcount(REFCOUNT_PERSIST_ONLY)
    }

    /// Decrement the refcount for a slot. If refcount reaches 0, the slot
    /// is automatically released back to the free pool.
    ///
    /// Returns:
    /// - `Ok(new_refcount)` on success
    /// - `Err(ArenaError::InvalidSlot)` if slot index is out of bounds
    /// - `Err(ArenaError::InvalidState)` if refcount is already 0 (underflow guard)
    ///
    /// This is the primary mechanism for lifecycle management. Both the
    /// persistence worker and network worker should call this when they
    /// finish processing a slot.
    #[inline]
    pub fn decrement_refcount(&self, slot_idx: SlotIndex) -> Result<u32, ArenaError> {
        if slot_idx as usize >= SLOTS_PER_ARENA {
            return Err(ArenaError::InvalidSlot);
        }

        // CAS loop to guard against underflow (decrementing 0 -> u32::MAX)
        loop {
            let current = self.refcounts[slot_idx as usize].load(Ordering::Acquire);
            if current == 0 {
                // Already free or double-decrement — reject to prevent corruption
                return Err(ArenaError::InvalidState);
            }

            let new_refcount = current - 1;
            match self.refcounts[slot_idx as usize].compare_exchange_weak(
                current,
                new_refcount,
                Ordering::AcqRel,
                Ordering::Relaxed,
            ) {
                Ok(_) => {
                    // If refcount hit 0, release the slot.
                    if new_refcount == 0 {
                        self.release_slot_internal(slot_idx);
                    }
                    return Ok(new_refcount);
                }
                Err(_) => continue, // Retry on contention
            }
        }
    }

    /// Increment the refcount for a slot (e.g., for additional consumers).
    #[inline]
    pub fn increment_refcount(&self, slot_idx: SlotIndex) -> Result<u32, ArenaError> {
        if slot_idx as usize >= SLOTS_PER_ARENA {
            return Err(ArenaError::InvalidSlot);
        }

        let new = self.refcounts[slot_idx as usize].fetch_add(1, Ordering::AcqRel) + 1;
        Ok(new)
    }

    /// Get current refcount for a slot.
    #[inline]
    pub fn get_refcount(&self, slot_idx: SlotIndex) -> Result<u32, ArenaError> {
        if slot_idx as usize >= SLOTS_PER_ARENA {
            return Err(ArenaError::InvalidSlot);
        }

        Ok(self.refcounts[slot_idx as usize].load(Ordering::Acquire))
    }

    /// Internal method to release a slot back to the free pool.
    /// Called automatically when refcount reaches 0.
    #[inline]
    fn release_slot_internal(&self, slot_idx: SlotIndex) {
        unsafe {
            let slot = &mut (*self.slots.get())[slot_idx as usize];
            // Reset slot header.
            slot.header = SlotHeader::empty();
        }

        // Mark as free in bitmap.
        let word_idx = slot_idx as usize / 64;
        let bit_idx = slot_idx as usize % 64;
        let mask = 1u64 << bit_idx;

        self.free_bitmap[word_idx].fetch_or(mask, Ordering::Release);
        self.free_count.fetch_add(1, Ordering::Relaxed);
    }

    /// Write payload into an acquired slot.
    /// The slot must be in Writing state.
    #[inline]
    pub fn write_slot(
        &self,
        slot_idx: SlotIndex,
        fact_id: &[u8; 32],
        payload: &[u8],
    ) -> Result<(), ArenaError> {
        if slot_idx as usize >= SLOTS_PER_ARENA {
            return Err(ArenaError::InvalidSlot);
        }

        if payload.len() > PAYLOAD_CAPACITY {
            return Err(ArenaError::PayloadTooLarge);
        }

        unsafe {
            let slot = &mut (*self.slots.get())[slot_idx as usize];

            if slot.header.state != SlotState::Writing as u32 {
                return Err(ArenaError::InvalidState);
            }

            slot.header.fact_id = *fact_id;
            slot.header.payload_len = payload.len() as u32;
            slot.payload[..payload.len()].copy_from_slice(payload);

            // Commit the slot.
            slot.header.state = SlotState::Committed as u32;
        }

        Ok(())
    }

    /// Read payload from a slot (zero-copy reference).
    ///
    /// **Important:** This increments the atomic refcount. Caller MUST call
    /// `decrement_refcount()` when done to avoid slot leaks.
    #[inline]
    pub fn read_slot(&self, slot_idx: SlotIndex) -> Result<(&[u8; 32], &[u8]), ArenaError> {
        if slot_idx as usize >= SLOTS_PER_ARENA {
            return Err(ArenaError::InvalidSlot);
        }

        // Increment atomic refcount FIRST to ensure slot isn't released mid-read
        let prev_refcount = self.refcounts[slot_idx as usize].fetch_add(1, Ordering::AcqRel);
        if prev_refcount == 0 {
            // Slot was already free — undo increment and reject
            self.refcounts[slot_idx as usize].fetch_sub(1, Ordering::Release);
            return Err(ArenaError::InvalidState);
        }

        unsafe {
            let slot = &(*self.slots.get())[slot_idx as usize];

            if slot.header.state < SlotState::Committed as u32 {
                // Slot not ready — undo refcount increment
                self.refcounts[slot_idx as usize].fetch_sub(1, Ordering::Release);
                return Err(ArenaError::InvalidState);
            }

            let payload_len = slot.header.payload_len as usize;
            Ok((&slot.header.fact_id, &slot.payload[..payload_len]))
        }
    }

    /// Get slot header (for SPSC entry construction).
    #[inline]
    pub fn get_header(&self, slot_idx: SlotIndex) -> Result<SlotHeader, ArenaError> {
        if slot_idx as usize >= SLOTS_PER_ARENA {
            return Err(ArenaError::InvalidSlot);
        }

        unsafe {
            let slot = &(*self.slots.get())[slot_idx as usize];
            Ok(slot.header)
        }
    }

    /// Get raw pointer to slot data (for io_uring).
    #[inline]
    pub fn slot_ptr(&self, slot_idx: SlotIndex) -> *const u8 {
        unsafe {
            let slot = &(*self.slots.get())[slot_idx as usize];
            slot as *const ArenaSlot as *const u8
        }
    }

    /// Mark slot as persisted (after io_uring completion).
    #[inline]
    pub fn mark_persisted(&self, slot_idx: SlotIndex) -> Result<(), ArenaError> {
        if slot_idx as usize >= SLOTS_PER_ARENA {
            return Err(ArenaError::InvalidSlot);
        }

        unsafe {
            let slot = &mut (*self.slots.get())[slot_idx as usize];
            slot.header.state = SlotState::Persisted as u32;
        }

        Ok(())
    }

    /// Release a slot back to the free pool.
    ///
    /// **Deprecated**: Prefer using `decrement_refcount()` which automatically
    /// releases the slot when refcount reaches 0. This method is kept for
    /// backward compatibility and forces immediate release regardless of refcount.
    #[inline]
    pub fn release_slot(&self, slot_idx: SlotIndex) -> Result<(), ArenaError> {
        if slot_idx as usize >= SLOTS_PER_ARENA {
            return Err(ArenaError::InvalidSlot);
        }

        // Reset refcount to 0.
        self.refcounts[slot_idx as usize].store(0, Ordering::Release);

        // Use internal release.
        self.release_slot_internal(slot_idx);

        Ok(())
    }

    /// Mark slot as persisted and decrement refcount.
    /// This is the preferred method for io_uring completion handlers.
    ///
    /// Flow:
    /// 1. Marks slot state as Persisted
    /// 2. Decrements refcount
    /// 3. If refcount hits 0, slot is auto-released
    #[inline]
    pub fn complete_persistence(&self, slot_idx: SlotIndex) -> Result<u32, ArenaError> {
        if slot_idx as usize >= SLOTS_PER_ARENA {
            return Err(ArenaError::InvalidSlot);
        }

        unsafe {
            let slot = &mut (*self.slots.get())[slot_idx as usize];
            slot.header.state = SlotState::Persisted as u32;
        }

        self.decrement_refcount(slot_idx)
    }

    /// Mark network broadcast complete and decrement refcount.
    /// This is the preferred method for network worker completion.
    ///
    /// Flow:
    /// 1. Decrements refcount
    /// 2. If refcount hits 0, slot is auto-released
    #[inline]
    pub fn complete_broadcast(&self, slot_idx: SlotIndex) -> Result<u32, ArenaError> {
        self.decrement_refcount(slot_idx)
    }

    /// Number of free slots.
    #[inline(always)]
    pub fn free_slots(&self) -> u32 {
        self.free_count.load(Ordering::Relaxed)
    }

    /// Check if arena is full.
    #[inline(always)]
    pub fn is_full(&self) -> bool {
        self.free_count.load(Ordering::Relaxed) == 0
    }

    /// Current sequence number.
    #[inline(always)]
    pub fn current_sequence(&self) -> u64 {
        self.sequence.load(Ordering::Relaxed)
    }
}

impl Default for WALArena {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_slot_sizes() {
        assert_eq!(core::mem::size_of::<ArenaSlot>(), 256);
        assert_eq!(core::mem::align_of::<ArenaSlot>(), 64);
        assert_eq!(PAYLOAD_CAPACITY, 200);
    }

    #[test]
    fn test_slot_header() {
        let header = SlotHeader::empty();
        assert_eq!(header.payload_len, 0);
        assert_eq!(header.sequence, 0);
        assert_eq!(header.refcount, 0);
        assert_eq!(header.state, 0);
    }

    #[test]
    fn test_arena_slot_empty() {
        let slot = ArenaSlot::empty();
        assert!(slot.header.state == SlotState::Free as u32);
        assert_eq!(slot.payload, [0u8; PAYLOAD_CAPACITY]);
    }

    #[test]
    fn test_arena_error_variants() {
        assert_ne!(ArenaError::Full, ArenaError::PayloadTooLarge);
        assert_ne!(ArenaError::InvalidSlot, ArenaError::InvalidState);
    }

    // NOTE: Full WALArena tests require heap allocation and are tested
    // in integration tests or benchmarks where stack size is not a concern.
    // The WALArena is ~1MB which exceeds default test thread stack size.
}
