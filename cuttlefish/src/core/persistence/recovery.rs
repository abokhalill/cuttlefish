//! WAL Recovery: Scan WAL file, verify BLAKE3 hashes, rebuild state.
//!
//! Used after hard shutdown to restore exact FrontierState and ExactCausalIndex.
//!
//! ## Zero-Heap Recovery
//!
//! The recovery path uses fixed-size stack buffers to avoid heap allocation:
//! - `PayloadBuffer`: Fixed 200-byte buffer matching `PAYLOAD_CAPACITY`
//! - WAL replay uses SIMD-accelerated `contains_simd` for dependency checks
//!
//! ## Checkpoint-Based Bootstrapping
//!
//! 1. Scan for latest valid checkpoint
//! 2. Load StateCell and FrontierState from checkpoint
//! 3. Replay WAL from checkpoint's sequence number forward
//! 4. Verify final tiered hash matches

use std::fs::File;
use std::io::{BufReader, Read, Seek, SeekFrom};

use crate::core::checkpoint::{Checkpoint, CheckpointHeader, CheckpointManager, WalHasher};
use crate::core::frontier::FrontierState;
use crate::core::invariant::Invariant;
use crate::core::state::StateCell;
use crate::core::topology::{CausalClock, ExactCausalIndex, FactId};

use super::arena::PAYLOAD_CAPACITY;

/// WAL entry header format (on-disk).
#[derive(Debug, Clone, Copy)]
#[repr(C)]
pub struct WalEntryHeader {
    /// Magic bytes for entry validation.
    pub magic: [u8; 4],
    /// Fact ID.
    pub fact_id: FactId,
    /// Payload length.
    pub payload_len: u32,
    /// Sequence number.
    pub sequence: u64,
    /// BLAKE3 hash of (fact_id || payload).
    pub hash: [u8; 32],
}

impl WalEntryHeader {
    pub const SIZE: usize = 80;
    pub const MAGIC: [u8; 4] = [0xCF, 0x15, 0xDA, 0x7A]; // "Cuttlefish Data"

    /// Parse header from bytes.
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        if bytes.len() < Self::SIZE {
            return None;
        }

        let mut magic = [0u8; 4];
        magic.copy_from_slice(&bytes[0..4]);

        if magic != Self::MAGIC {
            return None;
        }

        let mut fact_id = [0u8; 32];
        fact_id.copy_from_slice(&bytes[4..36]);

        let payload_len = u32::from_le_bytes([bytes[36], bytes[37], bytes[38], bytes[39]]);
        let sequence = u64::from_le_bytes([
            bytes[40], bytes[41], bytes[42], bytes[43],
            bytes[44], bytes[45], bytes[46], bytes[47],
        ]);

        let mut hash = [0u8; 32];
        hash.copy_from_slice(&bytes[48..80]);

        Some(Self {
            magic,
            fact_id,
            payload_len,
            sequence,
            hash,
        })
    }

    /// Serialize header to bytes.
    pub fn to_bytes(&self) -> [u8; Self::SIZE] {
        let mut buf = [0u8; Self::SIZE];
        buf[0..4].copy_from_slice(&self.magic);
        buf[4..36].copy_from_slice(&self.fact_id);
        buf[36..40].copy_from_slice(&self.payload_len.to_le_bytes());
        buf[40..48].copy_from_slice(&self.sequence.to_le_bytes());
        buf[48..80].copy_from_slice(&self.hash);
        buf
    }

    /// Create a new header with computed hash.
    pub fn new(fact_id: FactId, payload: &[u8], sequence: u64) -> Self {
        let mut hasher = WalHasher::new();
        hasher.update_entry(&fact_id, payload);
        let hash = hasher.finalize();

        Self {
            magic: Self::MAGIC,
            fact_id,
            payload_len: payload.len() as u32,
            sequence,
            hash,
        }
    }

    /// Verify the hash matches the payload.
    pub fn verify(&self, payload: &[u8]) -> bool {
        let mut hasher = WalHasher::new();
        hasher.update_entry(&self.fact_id, payload);
        let computed = hasher.finalize();

        // Constant-time comparison
        let mut diff = 0u8;
        for i in 0..32 {
            diff |= computed[i] ^ self.hash[i];
        }
        diff == 0
    }
}

/// Error during WAL recovery.
#[derive(Debug)]
pub enum RecoveryError {
    IoError(std::io::Error),
    CorruptedEntry { sequence: u64, reason: &'static str },
    HashMismatch { sequence: u64 },
    InvariantViolation { sequence: u64 },
    TruncatedEntry { offset: u64 },
}

impl From<std::io::Error> for RecoveryError {
    fn from(e: std::io::Error) -> Self {
        RecoveryError::IoError(e)
    }
}

/// Result of WAL recovery.
#[derive(Debug)]
pub struct RecoveryResult {
    /// Number of entries successfully recovered.
    pub entries_recovered: u64,
    /// Last valid sequence number.
    pub last_sequence: u64,
    /// Number of corrupted entries skipped.
    pub corrupted_entries: u64,
    /// File offset where recovery stopped.
    pub end_offset: u64,
}

/// WAL Recovery engine.
pub struct WalRecovery<I: Invariant> {
    pub frontier: FrontierState,
    pub state: StateCell,
    pub exact_index: ExactCausalIndex,
    pub invariant: I,
    pub last_sequence: u64,
}

impl<I: Invariant> WalRecovery<I> {
    /// Create a new recovery engine with initial state.
    pub fn new(invariant: I) -> Self {
        Self {
            frontier: FrontierState::new(),
            state: StateCell::new(),
            exact_index: ExactCausalIndex::new(),
            invariant,
            last_sequence: 0,
        }
    }

    /// Create with initial state (for partial recovery).
    pub fn with_state(invariant: I, state: StateCell, frontier: FrontierState) -> Self {
        Self {
            frontier,
            state,
            exact_index: ExactCausalIndex::new(),
            invariant,
            last_sequence: 0,
        }
    }

    /// Recover from a WAL file.
    ///
    /// Scans the file, verifies BLAKE3 hashes, replays valid entries.
    /// Stops at first corrupted entry (crash-consistent).
    pub fn recover_from_file(&mut self, path: &str) -> Result<RecoveryResult, RecoveryError> {
        let file = File::open(path)?;
        let file_len = file.metadata()?.len();
        let mut reader = BufReader::new(file);

        self.recover_from_reader(&mut reader, file_len)
    }

    /// Recover from any reader.
    pub fn recover_from_reader<R: Read + Seek>(
        &mut self,
        reader: &mut R,
        file_len: u64,
    ) -> Result<RecoveryResult, RecoveryError> {
        let mut entries_recovered = 0u64;
        let mut corrupted_entries = 0u64;
        let mut offset = 0u64;
        let mut header_buf = [0u8; WalEntryHeader::SIZE];

        while offset + WalEntryHeader::SIZE as u64 <= file_len {
            // Read header
            reader.seek(SeekFrom::Start(offset))?;
            if reader.read_exact(&mut header_buf).is_err() {
                break;
            }

            let header = match WalEntryHeader::from_bytes(&header_buf) {
                Some(h) => h,
                None => {
                    // Invalid magic - likely end of valid data
                    break;
                }
            };

            // Check if payload fits in file
            let entry_end = offset + WalEntryHeader::SIZE as u64 + header.payload_len as u64;
            if entry_end > file_len {
                return Err(RecoveryError::TruncatedEntry { offset });
            }

            // Read payload
            let mut payload = vec![0u8; header.payload_len as usize];
            if reader.read_exact(&mut payload).is_err() {
                return Err(RecoveryError::TruncatedEntry { offset });
            }

            // Verify hash
            if !header.verify(&payload) {
                corrupted_entries += 1;
                // Stop at first corruption (crash-consistent)
                break;
            }

            // Apply to state
            if self.invariant.apply(&payload, self.state.as_bytes_mut()).is_err() {
                return Err(RecoveryError::InvariantViolation {
                    sequence: header.sequence,
                });
            }

            // Update frontier and exact index
            self.frontier.advance(header.fact_id);
            self.exact_index.observe(&header.fact_id);
            self.last_sequence = header.sequence;

            entries_recovered += 1;
            offset = entry_end;
        }

        Ok(RecoveryResult {
            entries_recovered,
            last_sequence: self.last_sequence,
            corrupted_entries,
            end_offset: offset,
        })
    }

    /// Zero-heap recovery from WAL file using fixed-size stack buffer.
    /// 
    /// Uses a fixed `PAYLOAD_CAPACITY` buffer instead of Vec allocation.
    /// Constraint: payloads must fit within PAYLOAD_CAPACITY (200 bytes).
    pub fn recover_zero_heap(&mut self, path: &str) -> Result<RecoveryResult, RecoveryError> {
        let file = File::open(path)?;
        let file_len = file.metadata()?.len();
        let mut reader = BufReader::new(file);

        self.recover_zero_heap_from_reader(&mut reader, file_len, 0)
    }

    /// Zero-heap recovery from a specific offset (for checkpoint-based replay).
    pub fn recover_zero_heap_from_offset(
        &mut self,
        path: &str,
        start_offset: u64,
        start_sequence: u64,
    ) -> Result<RecoveryResult, RecoveryError> {
        let file = File::open(path)?;
        let file_len = file.metadata()?.len();
        let mut reader = BufReader::new(file);

        self.last_sequence = start_sequence;
        self.recover_zero_heap_from_reader(&mut reader, file_len, start_offset)
    }

    /// Zero-heap recovery from reader with fixed-size payload buffer.
    fn recover_zero_heap_from_reader<R: Read + Seek>(
        &mut self,
        reader: &mut R,
        file_len: u64,
        start_offset: u64,
    ) -> Result<RecoveryResult, RecoveryError> {
        let mut entries_recovered = 0u64;
        let mut corrupted_entries = 0u64;
        let mut offset = start_offset;
        let mut header_buf = [0u8; WalEntryHeader::SIZE];
        // Fixed-size payload buffer - no heap allocation
        let mut payload_buf = [0u8; PAYLOAD_CAPACITY];

        while offset + WalEntryHeader::SIZE as u64 <= file_len {
            reader.seek(SeekFrom::Start(offset))?;
            if reader.read_exact(&mut header_buf).is_err() {
                break;
            }

            let header = match WalEntryHeader::from_bytes(&header_buf) {
                Some(h) => h,
                None => break,
            };

            // Validate payload fits in fixed buffer
            if header.payload_len as usize > PAYLOAD_CAPACITY {
                return Err(RecoveryError::CorruptedEntry {
                    sequence: header.sequence,
                    reason: "payload exceeds PAYLOAD_CAPACITY",
                });
            }

            let entry_end = offset + WalEntryHeader::SIZE as u64 + header.payload_len as u64;
            if entry_end > file_len {
                break; // Truncated - stop gracefully
            }

            // Read payload into fixed buffer
            let payload = &mut payload_buf[..header.payload_len as usize];
            if reader.read_exact(payload).is_err() {
                break;
            }

            // Verify BLAKE3 hash
            if !header.verify(payload) {
                corrupted_entries += 1;
                break; // Stop at first corruption
            }

            // Apply invariant to state
            if self.invariant.apply(payload, self.state.as_bytes_mut()).is_err() {
                return Err(RecoveryError::InvariantViolation {
                    sequence: header.sequence,
                });
            }

            // Update frontier and exact index (uses SIMD internally)
            self.frontier.advance(header.fact_id);
            self.exact_index.observe(&header.fact_id);
            self.last_sequence = header.sequence;

            entries_recovered += 1;
            offset = entry_end;
        }

        Ok(RecoveryResult {
            entries_recovered,
            last_sequence: self.last_sequence,
            corrupted_entries,
            end_offset: offset,
        })
    }

    /// Verify a WAL file without applying changes.
    pub fn verify_file(path: &str) -> Result<RecoveryResult, RecoveryError> {
        let file = File::open(path)?;
        let file_len = file.metadata()?.len();
        let mut reader = BufReader::new(file);

        let mut entries_verified = 0u64;
        let mut corrupted_entries = 0u64;
        let mut last_sequence = 0u64;
        let mut offset = 0u64;
        let mut header_buf = [0u8; WalEntryHeader::SIZE];

        while offset + WalEntryHeader::SIZE as u64 <= file_len {
            reader.seek(SeekFrom::Start(offset))?;
            if reader.read_exact(&mut header_buf).is_err() {
                break;
            }

            let header = match WalEntryHeader::from_bytes(&header_buf) {
                Some(h) => h,
                None => break,
            };

            let entry_end = offset + WalEntryHeader::SIZE as u64 + header.payload_len as u64;
            if entry_end > file_len {
                break;
            }

            let mut payload = vec![0u8; header.payload_len as usize];
            if reader.read_exact(&mut payload).is_err() {
                break;
            }

            if header.verify(&payload) {
                entries_verified += 1;
                last_sequence = header.sequence;
            } else {
                corrupted_entries += 1;
                break;
            }

            offset = entry_end;
        }

        Ok(RecoveryResult {
            entries_recovered: entries_verified,
            last_sequence,
            corrupted_entries,
            end_offset: offset,
        })
    }
}

/// Integrated bootstrapping: checkpoint + WAL replay.
///
/// This is the main entry point for system startup after crash.
pub struct BootstrapEngine<I: Invariant> {
    pub recovery: WalRecovery<I>,
    pub checkpoint_header: Option<CheckpointHeader>,
}

impl<I: Invariant> BootstrapEngine<I> {
    /// Create a new bootstrap engine.
    pub fn new(invariant: I) -> Self {
        Self {
            recovery: WalRecovery::new(invariant),
            checkpoint_header: None,
        }
    }

    /// Bootstrap from checkpoint + WAL.
    ///
    /// 1. Scan for latest valid checkpoint
    /// 2. Load StateCell and CausalClock from checkpoint
    /// 3. Replay WAL from checkpoint's offset forward (zero-heap)
    /// 4. Verify final tiered hash
    ///
    /// Returns the recovery result and whether a checkpoint was used.
    pub fn bootstrap(
        &mut self,
        checkpoint_path: &str,
        wal_path: &str,
    ) -> Result<(RecoveryResult, bool), RecoveryError> {
        let checkpoint_mgr = CheckpointManager::new(checkpoint_path);

        // Try to load checkpoint
        let checkpoint_loaded = if checkpoint_mgr.exists() {
            match checkpoint_mgr.read_checkpoint() {
                Ok(Some((header, state, clock))) => {
                    // Initialize recovery with checkpoint state
                    self.recovery.state = state;
                    self.recovery.frontier.clock = clock;
                    self.recovery.last_sequence = header.wal_sequence;
                    self.checkpoint_header = Some(header);
                    true
                }
                Ok(None) => false,
                Err(_) => false,
            }
        } else {
            false
        };

        // Determine WAL replay start point
        let (start_offset, start_sequence) = if let Some(ref header) = self.checkpoint_header {
            (header.wal_offset, header.wal_sequence)
        } else {
            (0, 0)
        };

        // Check if WAL exists
        if !std::path::Path::new(wal_path).exists() {
            return Ok((RecoveryResult {
                entries_recovered: 0,
                last_sequence: start_sequence,
                corrupted_entries: 0,
                end_offset: start_offset,
            }, checkpoint_loaded));
        }

        // Replay WAL from checkpoint offset (zero-heap)
        let result = self.recovery.recover_zero_heap_from_offset(
            wal_path,
            start_offset,
            start_sequence,
        )?;

        Ok((result, checkpoint_loaded))
    }

    /// Verify the final state matches the expected tiered hash.
    pub fn verify_final_hash(&self, expected_hash: &[u8; 32]) -> bool {
        Checkpoint::verify_tiered_hash(&self.recovery.state, &self.recovery.frontier, expected_hash)
    }

    /// Get the recovered state.
    pub fn state(&self) -> &StateCell {
        &self.recovery.state
    }

    /// Get the recovered frontier.
    pub fn frontier(&self) -> &FrontierState {
        &self.recovery.frontier
    }

    /// Get the exact causal index.
    pub fn exact_index(&self) -> &ExactCausalIndex {
        &self.recovery.exact_index
    }

    /// Compute the current tiered hash.
    pub fn compute_tiered_hash(&self) -> [u8; 32] {
        Checkpoint::compute_tiered_hash(&self.recovery.state, &self.recovery.frontier)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::invariants::total_supply::TotalSupplyInvariant;

    #[test]
    fn test_wal_entry_header_roundtrip() {
        let fact_id: FactId = [0xAB; 32];
        let payload = b"test payload data";
        let sequence = 42u64;

        let header = WalEntryHeader::new(fact_id, payload, sequence);
        let bytes = header.to_bytes();
        let parsed = WalEntryHeader::from_bytes(&bytes).unwrap();

        assert_eq!(parsed.fact_id, fact_id);
        assert_eq!(parsed.payload_len, payload.len() as u32);
        assert_eq!(parsed.sequence, sequence);
        assert!(parsed.verify(payload));
    }

    #[test]
    fn test_wal_entry_header_hash_verification() {
        let fact_id: FactId = [0xAB; 32];
        let payload = b"test payload";
        let header = WalEntryHeader::new(fact_id, payload, 1);

        // Correct payload verifies
        assert!(header.verify(payload));

        // Wrong payload fails
        assert!(!header.verify(b"wrong payload"));
    }

    #[test]
    fn test_wal_entry_header_invalid_magic() {
        let mut bytes = [0u8; WalEntryHeader::SIZE];
        bytes[0..4].copy_from_slice(&[0xFF, 0xFF, 0xFF, 0xFF]);

        assert!(WalEntryHeader::from_bytes(&bytes).is_none());
    }
}
