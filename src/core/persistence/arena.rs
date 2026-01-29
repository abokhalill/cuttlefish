//! WALArena: 4K-aligned memory arena for zero-copy WAL staging.

use core::cell::UnsafeCell;
use core::sync::atomic::{AtomicU32, AtomicU64, Ordering};

pub const REFCOUNT_FREE: u32 = 0;

pub const REFCOUNT_DUAL: u32 = 2;

pub const REFCOUNT_PERSIST_ONLY: u32 = 1;

pub const REFCOUNT_NETWORK_ONLY: u32 = 1;

pub const SLOT_SIZE: usize = 256;

pub const SLOTS_PER_ARENA: usize = 4096;

pub const ARENA_SIZE: usize = SLOTS_PER_ARENA * SLOT_SIZE;

pub type SlotIndex = u32;

pub const INVALID_SLOT: SlotIndex = u32::MAX;

#[repr(C)]
pub struct SlotHeader {
    pub fact_id: [u8; 32],
    pub payload_len: u32,
    pub sequence: u64,
    pub refcount: u32,
    pub state: AtomicU32,
}

const _: () = {
    assert!(core::mem::size_of::<SlotHeader>() == 56);
};

impl SlotHeader {
    #[inline(always)]
    pub fn empty() -> Self {
        Self {
            fact_id: [0u8; 32],
            payload_len: 0,
            sequence: 0,
            refcount: 0,
            state: AtomicU32::new(SlotState::Free as u32),
        }
    }
}

pub const PAYLOAD_CAPACITY: usize = SLOT_SIZE - core::mem::size_of::<SlotHeader>();

const _: () = {
    assert!(PAYLOAD_CAPACITY == 200);
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u32)]
pub enum SlotState {
    Free = 0,
    Writing = 1,
    Committed = 2,
    Persisted = 3,
}

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
    pub fn empty() -> Self {
        Self {
            header: SlotHeader::empty(),
            payload: [0u8; PAYLOAD_CAPACITY],
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ArenaError {
    Full,
    PayloadTooLarge,
    InvalidSlot,
    InvalidState,
}

#[repr(C, align(4096))]
pub struct WALArena {
    slots: UnsafeCell<[ArenaSlot; SLOTS_PER_ARENA]>,
    refcounts: [AtomicU32; SLOTS_PER_ARENA],
    free_bitmap: [AtomicU64; 64],
    alloc_hint: AtomicU32,
    sequence: AtomicU64,
    free_count: AtomicU32,
    _pad: [u8; 44],
}

const _: () = {
    assert!(core::mem::align_of::<WALArena>() == 4096);
};

unsafe impl Send for WALArena {}
unsafe impl Sync for WALArena {}

impl WALArena {
    pub fn new() -> Self {
        let mut free_bitmap: [AtomicU64; 64] = unsafe { core::mem::zeroed() };
        for word in &mut free_bitmap {
            *word = AtomicU64::new(u64::MAX);
        }

        let refcounts: [AtomicU32; SLOTS_PER_ARENA] = unsafe { core::mem::zeroed() };

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

                        unsafe {
                            let slot = &mut (*self.slots.get())[slot_idx as usize];
                            slot.header.sequence = self.sequence.fetch_add(1, Ordering::Relaxed);
                            slot.header.refcount = initial_refcount;
                            slot.header.state.store(SlotState::Writing as u32, Ordering::Release);
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
            slot.header.fact_id = [0u8; 32];
            slot.header.payload_len = 0;
            slot.header.sequence = 0;
            slot.header.refcount = 0;
            slot.header.state.store(SlotState::Free as u32, Ordering::Release);
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

            if slot.header.state.load(Ordering::Acquire) != SlotState::Writing as u32 {
                return Err(ArenaError::InvalidState);
            }

            slot.header.fact_id = *fact_id;
            slot.header.payload_len = payload.len() as u32;
            slot.payload[..payload.len()].copy_from_slice(payload);

            slot.header.state.store(SlotState::Committed as u32, Ordering::Release);
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

            if slot.header.state.load(Ordering::Acquire) < SlotState::Committed as u32 {
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
            slot.header.state.store(SlotState::Persisted as u32, Ordering::Release);
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
            slot.header.state.store(SlotState::Persisted as u32, Ordering::Release);
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
        assert_eq!(header.state.load(Ordering::Relaxed), SlotState::Free as u32);
    }

    #[test]
    fn test_arena_slot_empty() {
        let slot = ArenaSlot::empty();
        assert_eq!(slot.header.state.load(Ordering::Relaxed), SlotState::Free as u32);
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
