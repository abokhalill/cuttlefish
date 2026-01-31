//! Checkpoints for re-anchoring. Tiered BLAKE3: H(state) || H(frontier) → commitment.

use super::frontier::{Frontier, FrontierState};
use super::state::StateCell;
use super::topology::CausalClock;
use zerocopy::{FromBytes, Immutable, IntoBytes, KnownLayout};

pub const MAX_ATTESTATIONS: usize = 8;
pub const DEFAULT_QUORUM: usize = 5;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum CheckpointError {
    InsufficientQuorum = 1,
    StateHashMismatch = 2,
    StaleCheckpoint = 3,
    InvalidAttestation = 4,
}

pub type PubKey = [u8; 32];
pub type Signature = [u8; 64];

#[derive(Debug, Clone, Copy, FromBytes, IntoBytes, KnownLayout, Immutable)]
#[repr(C)]
pub struct Attestation {
    pub validator: PubKey,
    pub signature: Signature,
}

impl Attestation {
    #[inline(always)]
    pub const fn empty() -> Self {
        Self {
            validator: [0u8; 32],
            signature: [0u8; 64],
        }
    }

    /// TODO: Replace with ed25519.
    #[inline(always)]
    pub fn verify(&self, state_hash: &[u8; 32]) -> bool {
        for (i, &byte) in state_hash.iter().enumerate() {
            if self.signature[i] != (self.validator[i] ^ byte) {
                return false;
            }
        }
        true
    }

    #[inline(always)]
    pub fn mock_sign(validator: PubKey, state_hash: &[u8; 32]) -> Self {
        let mut signature = [0u8; 64];
        for i in 0..32 {
            signature[i] = validator[i] ^ state_hash[i];
        }
        Self { validator, signature }
    }
}

#[derive(Debug, Clone, Copy)]
#[repr(C)]
pub struct ProofEnvelope {
    pub attestations: [Attestation; MAX_ATTESTATIONS],
    pub attestation_mask: u8,
    pub quorum_threshold: u8,
    _pad: [u8; 6],
}

impl ProofEnvelope {
    #[inline(always)]
    pub const fn new(quorum_threshold: u8) -> Self {
        Self {
            attestations: [Attestation::empty(); MAX_ATTESTATIONS],
            attestation_mask: 0,
            quorum_threshold,
            _pad: [0u8; 6],
        }
    }

    #[inline(always)]
    pub fn add_attestation(&mut self, index: usize, attestation: Attestation) -> bool {
        if index >= MAX_ATTESTATIONS {
            return false;
        }
        self.attestations[index] = attestation;
        self.attestation_mask |= 1 << index;
        true
    }

    #[inline(always)]
    pub fn count_valid(&self, state_hash: &[u8; 32]) -> usize {
        let mut count = 0usize;
        for i in 0..MAX_ATTESTATIONS {
            if (self.attestation_mask >> i) & 1 == 1 && self.attestations[i].verify(state_hash) {
                count += 1;
            }
        }
        count
    }

    #[inline(always)]
    pub fn verify_quorum(&self, state_hash: &[u8; 32]) -> bool {
        self.count_valid(state_hash) >= self.quorum_threshold as usize
    }
}

impl Default for ProofEnvelope {
    fn default() -> Self {
        Self::new(DEFAULT_QUORUM as u8)
    }
}

/// On-disk checkpoint header format.
#[derive(Debug, Clone, Copy)]
#[repr(C)]
pub struct CheckpointHeader {
    /// Magic bytes for checkpoint validation.
    pub magic: [u8; 4],
    /// Version number.
    pub version: u32,
    /// WAL sequence number at checkpoint time.
    pub wal_sequence: u64,
    /// WAL file offset at checkpoint time (for truncation).
    pub wal_offset: u64,
    /// Tiered BLAKE3 hash of (State || Frontier).
    pub tiered_hash: [u8; 32],
    /// Timestamp (unix epoch seconds).
    pub timestamp: u64,
}

impl CheckpointHeader {
    pub const SIZE: usize = 64;
    pub const MAGIC: [u8; 4] = [0xCF, 0x15, 0xC0, 0x01]; // "Cuttlefish Checkpoint"
    pub const VERSION: u32 = 1;

    /// Create a new checkpoint header.
    pub fn new(wal_sequence: u64, wal_offset: u64, tiered_hash: [u8; 32]) -> Self {
        Self {
            magic: Self::MAGIC,
            version: Self::VERSION,
            wal_sequence,
            wal_offset,
            tiered_hash,
            #[cfg(feature = "std")]
            timestamp: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map(|d| d.as_secs())
                .unwrap_or(0),
            #[cfg(not(feature = "std"))]
            timestamp: 0,
        }
    }

    /// Serialize to bytes.
    pub fn to_bytes(&self) -> [u8; Self::SIZE] {
        let mut buf = [0u8; Self::SIZE];
        buf[0..4].copy_from_slice(&self.magic);
        buf[4..8].copy_from_slice(&self.version.to_le_bytes());
        buf[8..16].copy_from_slice(&self.wal_sequence.to_le_bytes());
        buf[16..24].copy_from_slice(&self.wal_offset.to_le_bytes());
        buf[24..56].copy_from_slice(&self.tiered_hash);
        buf[56..64].copy_from_slice(&self.timestamp.to_le_bytes());
        buf
    }

    /// Parse from bytes.
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        if bytes.len() < Self::SIZE {
            return None;
        }

        let mut magic = [0u8; 4];
        magic.copy_from_slice(&bytes[0..4]);
        if magic != Self::MAGIC {
            return None;
        }

        let version = u32::from_le_bytes([bytes[4], bytes[5], bytes[6], bytes[7]]);
        let wal_sequence = u64::from_le_bytes([
            bytes[8], bytes[9], bytes[10], bytes[11],
            bytes[12], bytes[13], bytes[14], bytes[15],
        ]);
        let wal_offset = u64::from_le_bytes([
            bytes[16], bytes[17], bytes[18], bytes[19],
            bytes[20], bytes[21], bytes[22], bytes[23],
        ]);

        let mut tiered_hash = [0u8; 32];
        tiered_hash.copy_from_slice(&bytes[24..56]);

        let timestamp = u64::from_le_bytes([
            bytes[56], bytes[57], bytes[58], bytes[59],
            bytes[60], bytes[61], bytes[62], bytes[63],
        ]);

        Some(Self {
            magic,
            version,
            wal_sequence,
            wal_offset,
            tiered_hash,
            timestamp,
        })
    }
}

/// Summary fact for re-anchoring: state snapshot + frontier + quorum proof.
#[derive(Debug, Clone)]
#[repr(C, align(64))]
pub struct Checkpoint {
    pub frontier: Frontier,
    pub clock: CausalClock,
    pub state_hash: [u8; 32],
    pub state: StateCell,
    pub proof: ProofEnvelope,
    /// WAL sequence at checkpoint creation.
    pub wal_sequence: u64,
    /// WAL offset at checkpoint creation.
    pub wal_offset: u64,
}

impl Checkpoint {
    #[inline(always)]
    pub fn new(
        frontier: Frontier,
        clock: CausalClock,
        state: StateCell,
        state_hash: [u8; 32],
        proof: ProofEnvelope,
    ) -> Self {
        Self {
            frontier,
            clock,
            state_hash,
            state,
            proof,
            wal_sequence: 0,
            wal_offset: 0,
        }
    }

    /// Create a checkpoint from a TwoLaneKernel.
    ///
    /// Captures (A, S) - the Frontier and State - and computes tiered BLAKE3 hash.
    /// This is a "summary fact" that can be gossipped for partition recovery.
    pub fn create<I: crate::core::invariant::Invariant>(
        kernel: &crate::core::kernel::TwoLaneKernel<I>,
        wal_sequence: u64,
        wal_offset: u64,
    ) -> Self {
        let state = *kernel.state();
        let frontier = kernel.frontier.frontier.clone();
        let clock = kernel.frontier.clock;

        // Compute tiered hash: H(State || Frontier)
        let tiered_hash = Self::compute_tiered_hash(&state, &kernel.frontier);

        Self {
            frontier,
            clock,
            state_hash: tiered_hash,
            state,
            proof: ProofEnvelope::default(),
            wal_sequence,
            wal_offset,
        }
    }

    /// Create checkpoint header for on-disk storage.
    pub fn to_header(&self) -> CheckpointHeader {
        CheckpointHeader::new(self.wal_sequence, self.wal_offset, self.state_hash)
    }

    #[inline(always)]
    pub fn verify(&self) -> Result<(), CheckpointError> {
        if !self.proof.verify_quorum(&self.state_hash) {
            return Err(CheckpointError::InsufficientQuorum);
        }
        Ok(())
    }

    /// Verify the checkpoint's tiered hash matches its state and frontier.
    pub fn verify_integrity(&self) -> bool {
        let frontier_state = FrontierState {
            clock: self.clock,
            frontier: self.frontier.clone(),
        };
        Self::verify_tiered_hash(&self.state, &frontier_state, &self.state_hash)
    }

    /// Compute BLAKE3 hash of StateCell only.
    /// Use `compute_tiered_hash` for full state+frontier commitment.
    #[inline]
    pub fn compute_state_hash(state: &StateCell) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new();
        hasher.update(state.as_bytes());
        *hasher.finalize().as_bytes()
    }

    /// Compute tiered BLAKE3 hash of StateCell + FrontierState.
    ///
    /// Construction:
    /// 1. H1 = BLAKE3(StateCell)
    /// 2. H2 = BLAKE3(CausalClock || Frontier)
    /// 3. Result = BLAKE3(H1 || H2)
    ///
    /// This binds state to causality cryptographically.
    #[inline]
    pub fn compute_tiered_hash(state: &StateCell, frontier: &FrontierState) -> [u8; 32] {
        // Tier 1: Hash state
        let state_hash = Self::compute_state_hash(state);

        // Tier 2: Hash frontier (clock + fact IDs)
        let mut frontier_hasher = blake3::Hasher::new();
        frontier_hasher.update(frontier.clock.as_bytes());
        for fact_id in frontier.frontier.iter() {
            frontier_hasher.update(fact_id);
        }
        let frontier_hash = frontier_hasher.finalize();

        // Tier 3: Combine
        let mut final_hasher = blake3::Hasher::new();
        final_hasher.update(&state_hash);
        final_hasher.update(frontier_hash.as_bytes());
        *final_hasher.finalize().as_bytes()
    }

    #[cfg(feature = "std")]
    #[inline]
    pub fn compute_hash_from_reader<R: std::io::Read>(reader: &mut R) -> std::io::Result<[u8; 32]> {
        let mut hasher = blake3::Hasher::new();
        hasher.update_reader(reader)?;
        Ok(*hasher.finalize().as_bytes())
    }

    /// Verify that a state hash matches the current state.
    #[inline]
    pub fn verify_state_hash(state: &StateCell, expected: &[u8; 32]) -> bool {
        let computed = Self::compute_state_hash(state);
        // Constant-time comparison
        let mut diff = 0u8;
        for i in 0..32 {
            diff |= computed[i] ^ expected[i];
        }
        diff == 0
    }

    /// Verify tiered hash matches state + frontier.
    #[inline]
    pub fn verify_tiered_hash(
        state: &StateCell,
        frontier: &FrontierState,
        expected: &[u8; 32],
    ) -> bool {
        let computed = Self::compute_tiered_hash(state, frontier);
        let mut diff = 0u8;
        for i in 0..32 {
            diff |= computed[i] ^ expected[i];
        }
        diff == 0
    }
}

/// BLAKE3-based WAL entry hasher for integrity verification.
pub struct WalHasher {
    hasher: blake3::Hasher,
}

impl WalHasher {
    /// Create a new WAL hasher.
    #[inline]
    pub fn new() -> Self {
        Self {
            hasher: blake3::Hasher::new(),
        }
    }

    /// Update with a WAL entry (fact_id + payload).
    #[inline]
    pub fn update_entry(&mut self, fact_id: &[u8; 32], payload: &[u8]) {
        self.hasher.update(fact_id);
        self.hasher.update(&(payload.len() as u32).to_le_bytes());
        self.hasher.update(payload);
    }

    /// Update with raw bytes.
    #[inline]
    pub fn update(&mut self, data: &[u8]) {
        self.hasher.update(data);
    }

    /// Finalize and return the hash.
    #[inline]
    pub fn finalize(self) -> [u8; 32] {
        *self.hasher.finalize().as_bytes()
    }

    /// Finalize and reset for reuse.
    #[inline]
    pub fn finalize_reset(&mut self) -> [u8; 32] {
        let hash = *self.hasher.finalize().as_bytes();
        self.hasher.reset();
        hash
    }
}

impl Default for WalHasher {
    fn default() -> Self {
        Self::new()
    }
}

/// WAL truncation utilities for checkpoint-based pruning.
#[cfg(all(feature = "std", target_os = "linux"))]
pub mod wal_truncate {
    use std::fs::File;
    use std::os::unix::io::AsRawFd;

    /// Punch a hole in the WAL file from start to the checkpoint offset.
    /// Uses fallocate(FALLOC_FL_PUNCH_HOLE) to release disk space.
    ///
    /// # Safety
    /// The offset must be block-aligned (typically 4K) for best results.
    pub fn punch_hole(file: &File, offset: u64) -> std::io::Result<()> {
        use std::io::Error;

        if offset == 0 {
            return Ok(());
        }

        // FALLOC_FL_PUNCH_HOLE | FALLOC_FL_KEEP_SIZE
        const FALLOC_FL_PUNCH_HOLE: i32 = 0x02;
        const FALLOC_FL_KEEP_SIZE: i32 = 0x01;

        let ret = unsafe {
            libc::fallocate(
                file.as_raw_fd(),
                FALLOC_FL_PUNCH_HOLE | FALLOC_FL_KEEP_SIZE,
                0, // Start from beginning
                offset as libc::off_t,
            )
        };

        if ret == 0 {
            Ok(())
        } else {
            Err(Error::other(format!("fallocate failed: {}", std::io::Error::last_os_error())))
        }
    }

    /// Truncate WAL file to the given offset (simple truncation).
    pub fn truncate_to(file: &File, offset: u64) -> std::io::Result<()> {
        file.set_len(offset)
    }
}

/// Checkpoint file manager for writing and reading checkpoints.
#[cfg(feature = "std")]
pub struct CheckpointManager {
    checkpoint_path: String,
}

#[cfg(feature = "std")]
impl CheckpointManager {
    /// Create a new checkpoint manager.
    pub fn new(checkpoint_path: &str) -> Self {
        Self {
            checkpoint_path: checkpoint_path.to_string(),
        }
    }

    /// Write a checkpoint to disk.
    pub fn write_checkpoint(&self, checkpoint: &Checkpoint) -> std::io::Result<()> {
        use std::io::Write;

        let mut file = std::fs::File::create(&self.checkpoint_path)?;

        // Write header
        let header = checkpoint.to_header();
        file.write_all(&header.to_bytes())?;

        // Write state cell (64 bytes)
        file.write_all(checkpoint.state.as_bytes())?;

        // Write clock (64 bytes)
        file.write_all(checkpoint.clock.as_bytes())?;

        // Write frontier facts
        for fact_id in checkpoint.frontier.iter() {
            file.write_all(fact_id)?;
        }

        file.sync_all()?;
        Ok(())
    }

    /// Read the latest checkpoint from disk.
    /// Returns None if checkpoint is missing, corrupt, or fails integrity verification.
    pub fn read_checkpoint(&self) -> std::io::Result<Option<(CheckpointHeader, StateCell, CausalClock)>> {
        use std::io::Read;

        let mut file = match std::fs::File::open(&self.checkpoint_path) {
            Ok(f) => f,
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(None),
            Err(e) => return Err(e),
        };

        let mut header_buf = [0u8; CheckpointHeader::SIZE];
        file.read_exact(&mut header_buf)?;

        let header = match CheckpointHeader::from_bytes(&header_buf) {
            Some(h) => h,
            None => return Ok(None),
        };

        let mut state_buf = [0u8; 64];
        file.read_exact(&mut state_buf)?;
        let mut state = StateCell::new();
        state.as_slice_mut().copy_from_slice(&state_buf);

        let mut clock_buf = [0u8; 64];
        file.read_exact(&mut clock_buf)?;
        let clock = match CausalClock::read_from_bytes(&clock_buf) {
            Ok(c) => c,
            Err(_) => return Ok(None),
        };

        let mut frontier_facts: Frontier = Frontier::new();
        let mut fact_buf = [0u8; 32];
        while file.read_exact(&mut fact_buf).is_ok() {
            if frontier_facts.len() < frontier_facts.capacity() {
                frontier_facts.push(fact_buf);
            }
        }

        let frontier_state = FrontierState {
            clock,
            frontier: frontier_facts,
        };
        let computed_hash = Checkpoint::compute_tiered_hash(&state, &frontier_state);

        let mut diff = 0u8;
        for (i, &byte) in computed_hash.iter().enumerate() {
            diff |= byte ^ header.tiered_hash[i];
        }
        if diff != 0 {
            return Ok(None);
        }

        Ok(Some((header, state, clock)))
    }

    /// Check if a checkpoint file exists.
    pub fn exists(&self) -> bool {
        std::path::Path::new(&self.checkpoint_path).exists()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_attestation_verify() {
        let validator: PubKey = [0xAB; 32];
        let state_hash: [u8; 32] = [0xCD; 32];

        let attestation = Attestation::mock_sign(validator, &state_hash);
        assert!(attestation.verify(&state_hash));

        let wrong_hash: [u8; 32] = [0xFF; 32];
        assert!(!attestation.verify(&wrong_hash));
    }

    #[test]
    fn test_proof_envelope_quorum() {
        let state_hash: [u8; 32] = [0xAB; 32];
        let mut proof = ProofEnvelope::new(3);

        // Add 2 attestations - below quorum
        for i in 0..2 {
            let mut validator = [0u8; 32];
            validator[0] = i as u8;
            let attestation = Attestation::mock_sign(validator, &state_hash);
            proof.add_attestation(i, attestation);
        }

        assert!(!proof.verify_quorum(&state_hash));
        assert_eq!(proof.count_valid(&state_hash), 2);

        // Add 3rd attestation - meets quorum
        let mut validator = [0u8; 32];
        validator[0] = 2;
        let attestation = Attestation::mock_sign(validator, &state_hash);
        proof.add_attestation(2, attestation);

        assert!(proof.verify_quorum(&state_hash));
        assert_eq!(proof.count_valid(&state_hash), 3);
    }

    #[test]
    fn test_checkpoint_verify() {
        let state = StateCell::new();
        let state_hash = Checkpoint::compute_state_hash(&state);

        let mut proof = ProofEnvelope::new(2);
        for i in 0..2 {
            let mut validator = [0u8; 32];
            validator[0] = i as u8;
            let attestation = Attestation::mock_sign(validator, &state_hash);
            proof.add_attestation(i, attestation);
        }

        let checkpoint = Checkpoint::new(
            Frontier::new_const(),
            CausalClock::new(),
            state,
            state_hash,
            proof,
        );

        assert!(checkpoint.verify().is_ok());
    }

    #[test]
    fn test_blake3_state_hash() {
        let state = StateCell::new();
        let hash1 = Checkpoint::compute_state_hash(&state);
        let hash2 = Checkpoint::compute_state_hash(&state);

        // Deterministic
        assert_eq!(hash1, hash2);

        // Not all zeros (actual hash)
        assert_ne!(hash1, [0u8; 32]);

        // Verify works
        assert!(Checkpoint::verify_state_hash(&state, &hash1));
        assert!(!Checkpoint::verify_state_hash(&state, &[0xFF; 32]));
    }

    #[test]
    fn test_blake3_tiered_hash() {
        let state = StateCell::new();
        let frontier = FrontierState::new();

        let hash1 = Checkpoint::compute_tiered_hash(&state, &frontier);
        let hash2 = Checkpoint::compute_tiered_hash(&state, &frontier);

        // Deterministic
        assert_eq!(hash1, hash2);

        // Different from state-only hash
        let state_hash = Checkpoint::compute_state_hash(&state);
        assert_ne!(hash1, state_hash);

        // Verify works
        assert!(Checkpoint::verify_tiered_hash(&state, &frontier, &hash1));
        assert!(!Checkpoint::verify_tiered_hash(&state, &frontier, &[0xFF; 32]));
    }

    #[test]
    fn test_blake3_tiered_hash_changes_with_frontier() {
        let state = StateCell::new();
        let mut frontier1 = FrontierState::new();
        let mut frontier2 = FrontierState::new();

        // Advance frontier2 with a fact
        let fact_id: [u8; 32] = [0xAB; 32];
        frontier2.advance(fact_id);

        let hash1 = Checkpoint::compute_tiered_hash(&state, &frontier1);
        let hash2 = Checkpoint::compute_tiered_hash(&state, &frontier2);

        // Different frontiers produce different hashes
        assert_ne!(hash1, hash2);
    }

    #[test]
    fn test_wal_hasher() {
        let mut hasher = WalHasher::new();

        let fact_id: [u8; 32] = [0xAB; 32];
        let payload = b"test payload";

        hasher.update_entry(&fact_id, payload);
        let hash1 = hasher.finalize();

        // Recreate and verify determinism
        let mut hasher2 = WalHasher::new();
        hasher2.update_entry(&fact_id, payload);
        let hash2 = hasher2.finalize();

        assert_eq!(hash1, hash2);
        assert_ne!(hash1, [0u8; 32]);
    }

    #[test]
    fn test_wal_hasher_reset() {
        let mut hasher = WalHasher::new();

        let fact_id: [u8; 32] = [0xAB; 32];
        let payload = b"test payload";

        hasher.update_entry(&fact_id, payload);
        let hash1 = hasher.finalize_reset();

        // After reset, same input produces same hash
        hasher.update_entry(&fact_id, payload);
        let hash2 = hasher.finalize_reset();

        assert_eq!(hash1, hash2);
    }
}
