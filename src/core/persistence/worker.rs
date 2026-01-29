//! io_uring-based persistence worker for async fact durability.
//!
//! ## Zero-Copy Arena Integration
//!
//! The worker reads directly from `WALArena` using `SlotIndex`:
//! 1. Kernel acquires slot, writes payload, pushes `SlotIndex` to SPSC
//! 2. Worker reads slot data via `arena.read_slot()`
//! 3. Worker writes `WalEntryHeader` + payload to WAL file
//! 4. On io_uring CQE, worker calls `arena.complete_persistence()`
//! 5. When refcount hits 0, slot is auto-released

use std::fs::{File, OpenOptions};
use std::os::unix::io::AsRawFd;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;

use io_uring::{opcode, types, IoUring};

use super::arena::{SlotIndex, WALArena};
use super::recovery::WalEntryHeader as RecoveryWalEntryHeader;
use super::ring::{PersistenceEntry, SPSCConsumer};
use crate::core::topology::CausalClock;

/// 4K block size for O_DIRECT alignment.
pub const BLOCK_SIZE: usize = 4096;

/// Number of pre-allocated submission buffers.
pub const BUFFER_POOL_SIZE: usize = 64;

/// Maximum entries to batch per write.
pub const MAX_BATCH_SIZE: usize = 32;

/// 4K-aligned buffer for io_uring submissions.
#[repr(C, align(4096))]
pub struct SubmissionBuffer {
    pub data: [u8; BLOCK_SIZE],
}

impl SubmissionBuffer {
    pub fn new() -> Self {
        Self {
            data: [0u8; BLOCK_SIZE],
        }
    }
}

impl Default for SubmissionBuffer {
    fn default() -> Self {
        Self::new()
    }
}

/// Persistence frontier tracking durable facts.
pub struct PersistenceFrontier {
    clock: CausalClock,
    sequence: AtomicU64,
}

impl PersistenceFrontier {
    pub fn new() -> Self {
        Self {
            clock: CausalClock::new(),
            sequence: AtomicU64::new(0),
        }
    }

    #[inline(always)]
    pub fn clock(&self) -> &CausalClock {
        &self.clock
    }

    #[inline(always)]
    pub fn sequence(&self) -> u64 {
        self.sequence.load(Ordering::Acquire)
    }

    /// Update frontier after successful write. Called by worker only.
    pub fn advance(&mut self, entries: &[PersistenceEntry]) {
        for entry in entries {
            self.clock.observe(&entry.fact_id);
        }
        if let Some(last) = entries.last() {
            self.sequence.store(last.sequence, Ordering::Release);
        }
    }

    pub fn dominates(&self, requirement: &CausalClock) -> bool {
        self.clock.dominates(requirement)
    }
}

impl Default for PersistenceFrontier {
    fn default() -> Self {
        Self::new()
    }
}

// WAL format unified: use RecoveryWalEntryHeader (BLAKE3, 80 bytes) for all persistence.
// This ensures write path and recovery path use identical format.

/// Aligned buffer pool for io_uring submissions.
pub struct BufferPool {
    buffers: Vec<Box<SubmissionBuffer>>,
    free_list: Vec<usize>,
}

impl BufferPool {
    pub fn new(count: usize) -> Self {
        let mut buffers = Vec::with_capacity(count);
        let mut free_list = Vec::with_capacity(count);
        for i in 0..count {
            buffers.push(Box::new(SubmissionBuffer::new()));
            free_list.push(i);
        }
        Self { buffers, free_list }
    }

    pub fn acquire(&mut self) -> Option<usize> {
        self.free_list.pop()
    }

    pub fn release(&mut self, idx: usize) {
        self.free_list.push(idx);
    }

    pub fn get_mut(&mut self, idx: usize) -> &mut SubmissionBuffer {
        &mut self.buffers[idx]
    }

    pub fn get_ptr(&self, idx: usize) -> *const u8 {
        self.buffers[idx].data.as_ptr()
    }
}

/// io_uring persistence worker.
pub struct PersistenceWorker {
    ring: IoUring,
    file: File,
    buffer_pool: BufferPool,
    write_offset: u64,
    pending_writes: Vec<(usize, Vec<PersistenceEntry>)>,
}

impl PersistenceWorker {
    /// Create a new persistence worker with the given WAL file path.
    pub fn new(wal_path: &str, ring_size: u32) -> std::io::Result<Self> {
        let file = OpenOptions::new()
            .create(true)
            .write(true)
            .append(false)
            .open(wal_path)?;

        let ring = IoUring::builder()
            .setup_single_issuer()
            .build(ring_size)?;

        Ok(Self {
            ring,
            file,
            buffer_pool: BufferPool::new(BUFFER_POOL_SIZE),
            write_offset: 0,
            pending_writes: Vec::with_capacity(BUFFER_POOL_SIZE),
        })
    }

    /// Process entries from consumer, write to disk, update frontier.
    pub fn process_batch<const N: usize>(
        &mut self,
        consumer: &SPSCConsumer<'_, N>,
        frontier: &mut PersistenceFrontier,
    ) -> std::io::Result<usize> {
        let mut batch = [PersistenceEntry::empty(); MAX_BATCH_SIZE];
        let count = consumer.drain_into(&mut batch, MAX_BATCH_SIZE);

        if count == 0 {
            return Ok(0);
        }

        let entries = &batch[..count];
        self.submit_write(entries)?;
        self.wait_completions(frontier)?;

        Ok(count)
    }

    fn submit_write(&mut self, entries: &[PersistenceEntry]) -> std::io::Result<()> {
        let buf_idx = match self.buffer_pool.acquire() {
            Some(idx) => idx,
            None => return Err(std::io::Error::new(
                std::io::ErrorKind::WouldBlock,
                "buffer pool exhausted",
            )),
        };

        let buffer = self.buffer_pool.get_mut(buf_idx);
        let mut offset = 0usize;

        let mut written_entries = Vec::with_capacity(entries.len());

        for entry in entries {
            let header_size = RecoveryWalEntryHeader::SIZE;
            let total_size = header_size + entry.data_len as usize;

            if offset + total_size > BLOCK_SIZE {
                break;
            }

            let data_slice = if entry.data_ptr != 0 && entry.data_len > 0 {
                unsafe {
                    core::slice::from_raw_parts(
                        entry.data_ptr as *const u8,
                        entry.data_len as usize,
                    )
                }
            } else {
                &[]
            };

            // Use unified BLAKE3-based header (matches recovery format)
            let header = RecoveryWalEntryHeader::new(entry.fact_id, data_slice, entry.sequence);
            let header_bytes = header.to_bytes();
            buffer.data[offset..offset + header_size].copy_from_slice(&header_bytes);
            offset += header_size;

            if !data_slice.is_empty() {
                buffer.data[offset..offset + data_slice.len()].copy_from_slice(data_slice);
                offset += data_slice.len();
            }

            written_entries.push(*entry);
        }

        // Pad to block boundary
        while offset < BLOCK_SIZE {
            buffer.data[offset] = 0;
            offset += 1;
        }

        let write_op = opcode::Write::new(
            types::Fd(self.file.as_raw_fd()),
            self.buffer_pool.get_ptr(buf_idx),
            BLOCK_SIZE as u32,
        )
        .offset(self.write_offset)
        .build()
        .user_data(buf_idx as u64);

        unsafe {
            self.ring.submission().push(&write_op).map_err(|_| {
                std::io::Error::new(std::io::ErrorKind::Other, "SQ full")
            })?;
        }

        self.ring.submit()?;
        self.write_offset += BLOCK_SIZE as u64;
        self.pending_writes.push((buf_idx, written_entries));

        Ok(())
    }

    fn wait_completions(&mut self, frontier: &mut PersistenceFrontier) -> std::io::Result<()> {
        self.ring.submit_and_wait(1)?;

        let mut completed_entries: Vec<PersistenceEntry> = Vec::new();

        {
            let cq = self.ring.completion();
            for cqe in cq {
                let buf_idx = cqe.user_data() as usize;
                let result = cqe.result();

                if result < 0 {
                    self.buffer_pool.release(buf_idx);
                    return Err(std::io::Error::from_raw_os_error(-result));
                }

                if let Some(pos) = self.pending_writes.iter().position(|(idx, _)| *idx == buf_idx) {
                    let (_, entries) = self.pending_writes.remove(pos);
                    completed_entries.extend(entries);
                }

                self.buffer_pool.release(buf_idx);
            }
        }

        if !completed_entries.is_empty() {
            let fsync_op = opcode::Fsync::new(types::Fd(self.file.as_raw_fd()))
                .build()
                .user_data(u64::MAX);

            unsafe {
                self.ring.submission().push(&fsync_op).map_err(|_| {
                    std::io::Error::new(std::io::ErrorKind::Other, "SQ full")
                })?;
            }
            self.ring.submit_and_wait(1)?;

            let cq = self.ring.completion();
            for cqe in cq {
                if cqe.result() < 0 {
                    return Err(std::io::Error::from_raw_os_error(-cqe.result()));
                }
            }

            frontier.advance(&completed_entries);
        }

        Ok(())
    }

    /// Sync all pending writes to disk.
    pub fn sync(&mut self) -> std::io::Result<()> {
        self.file.sync_all()
    }
}

/// Slot-based persistence entry for arena integration.
/// Contains only the SlotIndex - payload is read directly from arena.
#[derive(Clone, Copy, Debug)]
#[repr(C)]
pub struct ArenaSlotEntry {
    pub slot_index: SlotIndex,
    pub sequence: u64,
}

impl ArenaSlotEntry {
    pub const fn empty() -> Self {
        Self {
            slot_index: 0,
            sequence: 0,
        }
    }
}

/// Pending write tracking for arena-based worker.
#[derive(Clone, Copy)]
struct PendingArenaWrite {
    buffer_idx: usize,
    slot_indices: [SlotIndex; MAX_BATCH_SIZE],
    slot_count: usize,
}

/// Zero-copy arena-integrated persistence worker.
///
/// Reads directly from WALArena, writes WalEntryHeader + payload,
/// and calls complete_persistence() on io_uring completion.
pub struct ArenaPersistenceWorker {
    ring: IoUring,
    file: File,
    arena: Arc<WALArena>,
    buffer_pool: BufferPool,
    write_offset: u64,
    pending_writes: [Option<PendingArenaWrite>; BUFFER_POOL_SIZE],
    frontier: PersistenceFrontier,
    sequence: u64,
}

impl ArenaPersistenceWorker {
    /// Create a new arena-integrated persistence worker.
    pub fn new(wal_path: &str, arena: Arc<WALArena>, ring_size: u32) -> std::io::Result<Self> {
        let file = OpenOptions::new()
            .create(true)
            .write(true)
            .read(true)
            .open(wal_path)?;

        let ring = IoUring::builder()
            .setup_single_issuer()
            .build(ring_size)?;

        Ok(Self {
            ring,
            file,
            arena,
            buffer_pool: BufferPool::new(BUFFER_POOL_SIZE),
            write_offset: 0,
            pending_writes: [None; BUFFER_POOL_SIZE],
            frontier: PersistenceFrontier::new(),
            sequence: 0,
        })
    }

    /// Get current write offset (for checkpoint tracking).
    #[inline]
    pub fn write_offset(&self) -> u64 {
        self.write_offset
    }

    /// Get persistence frontier.
    #[inline]
    pub fn frontier(&self) -> &PersistenceFrontier {
        &self.frontier
    }

    /// Process slot entries from a fixed-size array (zero-heap).
    /// Returns number of entries processed.
    pub fn process_slots(&mut self, slots: &[SlotIndex]) -> std::io::Result<usize> {
        if slots.is_empty() {
            return Ok(0);
        }

        self.submit_arena_write(slots)?;
        self.wait_arena_completions()?;

        Ok(slots.len())
    }

    /// Submit a write for arena slots.
    fn submit_arena_write(&mut self, slots: &[SlotIndex]) -> std::io::Result<()> {
        let buf_idx = match self.buffer_pool.acquire() {
            Some(idx) => idx,
            None => return Err(std::io::Error::new(
                std::io::ErrorKind::WouldBlock,
                "buffer pool exhausted",
            )),
        };

        let buffer = self.buffer_pool.get_mut(buf_idx);
        let mut offset = 0usize;
        let mut pending = PendingArenaWrite {
            buffer_idx: buf_idx,
            slot_indices: [0; MAX_BATCH_SIZE],
            slot_count: 0,
        };

        for &slot_idx in slots {
            if pending.slot_count >= MAX_BATCH_SIZE {
                break;
            }

            // Read directly from arena (zero-copy reference)
            let (fact_id, payload) = match self.arena.read_slot(slot_idx) {
                Ok(data) => data,
                Err(_) => continue,
            };

            let header = RecoveryWalEntryHeader::new(*fact_id, payload, self.sequence);
            let total_size = RecoveryWalEntryHeader::SIZE + payload.len();

            if offset + total_size > BLOCK_SIZE {
                break;
            }

            // Write header
            let header_bytes = header.to_bytes();
            buffer.data[offset..offset + RecoveryWalEntryHeader::SIZE].copy_from_slice(&header_bytes);
            offset += RecoveryWalEntryHeader::SIZE;

            // Write payload
            if !payload.is_empty() {
                buffer.data[offset..offset + payload.len()].copy_from_slice(payload);
                offset += payload.len();
            }

            pending.slot_indices[pending.slot_count] = slot_idx;
            pending.slot_count += 1;
            self.sequence += 1;
        }

        if pending.slot_count == 0 {
            self.buffer_pool.release(buf_idx);
            return Ok(());
        }

        // Pad to block boundary
        while offset < BLOCK_SIZE {
            buffer.data[offset] = 0;
            offset += 1;
        }

        let write_op = opcode::Write::new(
            types::Fd(self.file.as_raw_fd()),
            self.buffer_pool.get_ptr(buf_idx),
            BLOCK_SIZE as u32,
        )
        .offset(self.write_offset)
        .build()
        .user_data(buf_idx as u64);

        unsafe {
            self.ring.submission().push(&write_op).map_err(|_| {
                std::io::Error::new(std::io::ErrorKind::Other, "SQ full")
            })?;
        }

        self.ring.submit()?;
        self.write_offset += BLOCK_SIZE as u64;
        self.pending_writes[buf_idx] = Some(pending);

        Ok(())
    }

    /// Wait for io_uring completions and release arena slots.
    fn wait_arena_completions(&mut self) -> std::io::Result<()> {
        self.ring.submit_and_wait(1)?;

        let mut completed_slots: Vec<(SlotIndex, [u8; 32])> = Vec::new();

        {
            let cq = self.ring.completion();
            for cqe in cq {
                let buf_idx = cqe.user_data() as usize;
                let result = cqe.result();

                if result < 0 {
                    if let Some(pending) = self.pending_writes[buf_idx].take() {
                        for i in 0..pending.slot_count {
                            let _ = self.arena.complete_persistence(pending.slot_indices[i]);
                        }
                    }
                    self.buffer_pool.release(buf_idx);
                    return Err(std::io::Error::from_raw_os_error(-result));
                }

                if let Some(pending) = self.pending_writes[buf_idx].take() {
                    for i in 0..pending.slot_count {
                        let slot_idx = pending.slot_indices[i];
                        if let Ok(header) = self.arena.get_header(slot_idx) {
                            completed_slots.push((slot_idx, header.fact_id));
                        } else {
                            completed_slots.push((slot_idx, [0u8; 32]));
                        }
                    }
                }

                self.buffer_pool.release(buf_idx);
            }
        }

        if !completed_slots.is_empty() {
            let fsync_op = opcode::Fsync::new(types::Fd(self.file.as_raw_fd()))
                .build()
                .user_data(u64::MAX);

            unsafe {
                self.ring.submission().push(&fsync_op).map_err(|_| {
                    std::io::Error::new(std::io::ErrorKind::Other, "SQ full")
                })?;
            }
            self.ring.submit_and_wait(1)?;

            let cq = self.ring.completion();
            for cqe in cq {
                if cqe.result() < 0 {
                    for (slot_idx, _) in &completed_slots {
                        let _ = self.arena.complete_persistence(*slot_idx);
                    }
                    return Err(std::io::Error::from_raw_os_error(-cqe.result()));
                }
            }

            for (slot_idx, fact_id) in completed_slots {
                self.frontier.clock.observe(&fact_id);
                let _ = self.arena.complete_persistence(slot_idx);
            }
        }

        Ok(())
    }

    /// Sync all pending writes to disk.
    pub fn sync(&mut self) -> std::io::Result<()> {
        self.file.sync_all()
    }

    /// Drain all pending completions without blocking.
    pub fn drain_completions(&mut self) -> std::io::Result<()> {
        self.ring.submit()?;
        
        let cq = self.ring.completion();
        for cqe in cq {
            let buf_idx = cqe.user_data() as usize;
            
            if let Some(pending) = self.pending_writes[buf_idx].take() {
                for i in 0..pending.slot_count {
                    let slot_idx = pending.slot_indices[i];
                    if let Ok(header) = self.arena.get_header(slot_idx) {
                        self.frontier.clock.observe(&header.fact_id);
                    }
                    let _ = self.arena.complete_persistence(slot_idx);
                }
            }
            
            self.buffer_pool.release(buf_idx);
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_submission_buffer_alignment() {
        let buf = SubmissionBuffer::new();
        let ptr = buf.data.as_ptr() as usize;
        assert_eq!(ptr % 4096, 0, "buffer must be 4K aligned");
    }

    #[test]
    fn test_persistence_frontier() {
        let mut frontier = PersistenceFrontier::new();
        let entries = [
            PersistenceEntry {
                fact_id: [1u8; 32],
                data_ptr: 0,
                data_len: 0,
                sequence: 1,
            },
            PersistenceEntry {
                fact_id: [2u8; 32],
                data_ptr: 0,
                data_len: 0,
                sequence: 2,
            },
        ];

        frontier.advance(&entries);
        assert_eq!(frontier.sequence(), 2);
        assert!(frontier.clock().might_contain(&[1u8; 32]));
        assert!(frontier.clock().might_contain(&[2u8; 32]));
    }

    #[test]
    fn test_buffer_pool() {
        let mut pool = BufferPool::new(4);

        let idx1 = pool.acquire().unwrap();
        let idx2 = pool.acquire().unwrap();
        assert_ne!(idx1, idx2);

        pool.release(idx1);
        let idx3 = pool.acquire().unwrap();
        assert_eq!(idx1, idx3);
    }
}
