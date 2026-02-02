//! Hard Shutdown Stress Test
//!
//! This test validates crash recovery by:
//! 1. Admitting 1 million facts at maximum speed
//! 2. Writing to a WAL file with BLAKE3 hashes
//! 3. Simulating a "hard shutdown" (truncating mid-write)
//! 4. Recovering from the WAL and verifying exact FrontierState match

#![cfg(all(feature = "persistence", target_os = "linux"))]

use std::fs::{self, File};
use std::io::{BufWriter, Write};
use std::time::Instant;

use ctfs::core::checkpoint::Checkpoint;
use ctfs::core::frontier::FrontierState;
use ctfs::core::kernel::TwoLaneKernel;
use ctfs::core::persistence::recovery::{WalEntryHeader, WalRecovery};
use ctfs::core::state::StateCell;
use ctfs::core::topology::{ExactCausalIndex, FactId};
use ctfs::invariants::total_supply::{ConservationState, TotalSupplyInvariant};
use zerocopy::IntoBytes;

fn make_conservation_state(balance: i128, min: i128, max: i128) -> StateCell {
    let state = ConservationState::new(balance, min, max);
    let mut cell = StateCell::new();
    cell.as_slice_mut().copy_from_slice(state.as_bytes());
    cell
}

fn make_payload(delta: i128) -> [u8; 16] {
    let mut buf = [0u8; 16];
    buf.copy_from_slice(&delta.to_le_bytes());
    buf
}

/// Write facts to a WAL file with BLAKE3 hashes.
fn write_wal_file(path: &str, facts: &[(FactId, Vec<u8>)]) -> std::io::Result<()> {
    let file = File::create(path)?;
    let mut writer = BufWriter::new(file);

    for (sequence, (fact_id, payload)) in facts.iter().enumerate() {
        let header = WalEntryHeader::new(*fact_id, payload, sequence as u64);
        writer.write_all(&header.to_bytes())?;
        writer.write_all(payload)?;
    }

    writer.flush()?;
    Ok(())
}

/// Simulate hard shutdown by truncating the WAL file mid-entry.
fn truncate_wal_file(path: &str, keep_entries: usize, partial_bytes: usize) -> std::io::Result<()> {
    let metadata = fs::metadata(path)?;
    let file_len = metadata.len();

    // Calculate offset for truncation
    let entry_size = WalEntryHeader::SIZE + 16; // header + payload
    let full_entries_size = keep_entries * entry_size;
    let truncate_at = full_entries_size + partial_bytes;

    if truncate_at < file_len as usize {
        let file = File::options().write(true).open(path)?;
        file.set_len(truncate_at as u64)?;
    }

    Ok(())
}

#[test]
fn test_wal_write_and_recovery_small() {
    let temp_dir = std::env::temp_dir();
    let wal_path = temp_dir.join("cuttlefish_test_small.wal");
    let wal_path_str = wal_path.to_str().unwrap();

    // Clean up any previous test file
    let _ = fs::remove_file(&wal_path);

    // Create 100 facts
    let mut facts: Vec<(FactId, Vec<u8>)> = Vec::new();
    for i in 0u64..100 {
        let mut fact_id = [0u8; 32];
        fact_id[..8].copy_from_slice(&i.to_le_bytes());
        let payload = make_payload(1);
        facts.push((fact_id, payload.to_vec()));
    }

    // Write WAL
    write_wal_file(wal_path_str, &facts).unwrap();

    // Recover from WAL
    let state = make_conservation_state(0, i128::MIN, i128::MAX);
    let mut recovery = WalRecovery::new(TotalSupplyInvariant::new());
    recovery.state = state;

    let result = recovery.recover_from_file(wal_path_str).unwrap();

    assert_eq!(result.entries_recovered, 100);
    assert_eq!(result.last_sequence, 99);
    assert_eq!(result.corrupted_entries, 0);

    // Verify all facts are in the exact index
    for (fact_id, _) in &facts {
        assert!(recovery.exact_index.contains(fact_id));
    }

    // Clean up
    let _ = fs::remove_file(&wal_path);
}

#[test]
fn test_wal_recovery_after_truncation() {
    let temp_dir = std::env::temp_dir();
    let wal_path = temp_dir.join("cuttlefish_test_truncated.wal");
    let wal_path_str = wal_path.to_str().unwrap();

    let _ = fs::remove_file(&wal_path);

    // Create 100 facts
    let mut facts: Vec<(FactId, Vec<u8>)> = Vec::new();
    for i in 0u64..100 {
        let mut fact_id = [0u8; 32];
        fact_id[..8].copy_from_slice(&i.to_le_bytes());
        let payload = make_payload(1);
        facts.push((fact_id, payload.to_vec()));
    }

    // Write WAL
    write_wal_file(wal_path_str, &facts).unwrap();

    // Simulate hard shutdown: truncate after 50 complete entries + 10 bytes of partial entry
    truncate_wal_file(wal_path_str, 50, 10).unwrap();

    // Recover from truncated WAL
    let state = make_conservation_state(0, i128::MIN, i128::MAX);
    let mut recovery = WalRecovery::new(TotalSupplyInvariant::new());
    recovery.state = state;

    let result = recovery.recover_from_file(wal_path_str).unwrap();

    // Should recover exactly 50 entries (the complete ones)
    assert_eq!(result.entries_recovered, 50);
    assert_eq!(result.last_sequence, 49);

    // First 50 facts should be in index
    for i in 0..50 {
        assert!(recovery.exact_index.contains(&facts[i].0));
    }

    // Facts 50-99 should NOT be in index
    for i in 50..100 {
        assert!(!recovery.exact_index.contains(&facts[i].0));
    }

    let _ = fs::remove_file(&wal_path);
}

#[test]
fn test_wal_recovery_matches_kernel_state() {
    let temp_dir = std::env::temp_dir();
    let wal_path = temp_dir.join("cuttlefish_test_match.wal");
    let wal_path_str = wal_path.to_str().unwrap();

    let _ = fs::remove_file(&wal_path);

    // Create kernel and admit facts
    let state = make_conservation_state(0, i128::MIN, i128::MAX);
    let mut kernel = TwoLaneKernel::with_state(TotalSupplyInvariant::new(), state.clone());

    let mut facts: Vec<(FactId, Vec<u8>)> = Vec::new();
    for i in 0u64..1000 {
        let mut fact_id = [0u8; 32];
        fact_id[..8].copy_from_slice(&i.to_le_bytes());
        let payload = make_payload(1);

        kernel.admit(&fact_id, &[], &payload).unwrap();
        facts.push((fact_id, payload.to_vec()));
    }

    // Capture kernel state hash
    let kernel_state_hash = Checkpoint::compute_state_hash(kernel.state());
    let kernel_tiered_hash = Checkpoint::compute_tiered_hash(kernel.state(), &kernel.frontier);

    // Write WAL
    write_wal_file(wal_path_str, &facts).unwrap();

    // Recover from WAL
    let fresh_state = make_conservation_state(0, i128::MIN, i128::MAX);
    let mut recovery = WalRecovery::new(TotalSupplyInvariant::new());
    recovery.state = fresh_state;

    let result = recovery.recover_from_file(wal_path_str).unwrap();
    assert_eq!(result.entries_recovered, 1000);

    // Compute recovered state hash
    let recovered_state_hash = Checkpoint::compute_state_hash(&recovery.state);
    let recovered_tiered_hash =
        Checkpoint::compute_tiered_hash(&recovery.state, &recovery.frontier);

    // State hashes MUST match exactly
    assert_eq!(
        kernel_state_hash, recovered_state_hash,
        "State hash mismatch after recovery"
    );

    // Tiered hashes MUST match exactly
    assert_eq!(
        kernel_tiered_hash, recovered_tiered_hash,
        "Tiered hash mismatch after recovery"
    );

    // Exact index contains recent facts (older ones may be compacted)
    // The critical invariant is that the STATE matches, not that all facts are in the index
    // The index is a bounded structure that compacts old entries
    assert!(recovery.exact_index.len() > 0);

    let _ = fs::remove_file(&wal_path);
}

#[test]
fn test_high_volume_stress() {
    let temp_dir = std::env::temp_dir();
    let wal_path = temp_dir.join("cuttlefish_stress.wal");
    let wal_path_str = wal_path.to_str().unwrap();

    let _ = fs::remove_file(&wal_path);

    // Reduced count for test speed (use 100K instead of 1M for CI)
    let fact_count = 100_000u64;

    println!("Stress test: {} facts", fact_count);

    // Phase 1: Admit facts to kernel
    let start = Instant::now();
    let state = make_conservation_state(0, i128::MIN, i128::MAX);
    let mut kernel = TwoLaneKernel::with_state(TotalSupplyInvariant::new(), state.clone());

    let mut facts: Vec<(FactId, Vec<u8>)> = Vec::with_capacity(fact_count as usize);
    for i in 0u64..fact_count {
        let mut fact_id = [0u8; 32];
        fact_id[..8].copy_from_slice(&i.to_le_bytes());
        let payload = make_payload(1);

        kernel.admit(&fact_id, &[], &payload).unwrap();
        facts.push((fact_id, payload.to_vec()));
    }

    let admit_time = start.elapsed();
    println!(
        "Admitted {} facts in {:?} ({:.0} facts/sec)",
        fact_count,
        admit_time,
        fact_count as f64 / admit_time.as_secs_f64()
    );

    // Capture kernel state
    let kernel_state_hash = Checkpoint::compute_state_hash(kernel.state());

    // Phase 2: Write WAL
    let start = Instant::now();
    write_wal_file(wal_path_str, &facts).unwrap();
    let write_time = start.elapsed();
    println!(
        "Wrote WAL in {:?} ({:.0} entries/sec)",
        write_time,
        fact_count as f64 / write_time.as_secs_f64()
    );

    // Phase 3: Recover from WAL
    let start = Instant::now();
    let fresh_state = make_conservation_state(0, i128::MIN, i128::MAX);
    let mut recovery = WalRecovery::new(TotalSupplyInvariant::new());
    recovery.state = fresh_state;

    let result = recovery.recover_from_file(wal_path_str).unwrap();
    let recover_time = start.elapsed();

    println!(
        "Recovered {} entries in {:?} ({:.0} entries/sec)",
        result.entries_recovered,
        recover_time,
        result.entries_recovered as f64 / recover_time.as_secs_f64()
    );

    // Verify
    assert_eq!(result.entries_recovered, fact_count);
    assert_eq!(result.corrupted_entries, 0);

    let recovered_state_hash = Checkpoint::compute_state_hash(&recovery.state);
    assert_eq!(kernel_state_hash, recovered_state_hash);

    // Verify exact index has entries (compaction limits total count)
    // The critical invariant is state hash match, not index completeness
    assert!(recovery.exact_index.len() > 0);

    let _ = fs::remove_file(&wal_path);
}

#[test]
fn test_corrupted_hash_detection() {
    let temp_dir = std::env::temp_dir();
    let wal_path = temp_dir.join("cuttlefish_corrupt.wal");
    let wal_path_str = wal_path.to_str().unwrap();

    let _ = fs::remove_file(&wal_path);

    // Create 10 facts
    let mut facts: Vec<(FactId, Vec<u8>)> = Vec::new();
    for i in 0u64..10 {
        let mut fact_id = [0u8; 32];
        fact_id[..8].copy_from_slice(&i.to_le_bytes());
        let payload = make_payload(1);
        facts.push((fact_id, payload.to_vec()));
    }

    // Write WAL
    write_wal_file(wal_path_str, &facts).unwrap();

    // Corrupt the 6th entry's payload (flip a byte)
    {
        use std::io::{Seek, SeekFrom};
        let mut file = File::options()
            .read(true)
            .write(true)
            .open(&wal_path)
            .unwrap();
        let entry_size = WalEntryHeader::SIZE + 16;
        let corrupt_offset = 5 * entry_size + WalEntryHeader::SIZE + 5; // 6th entry, 5 bytes into payload
        file.seek(SeekFrom::Start(corrupt_offset as u64)).unwrap();
        file.write_all(&[0xFF]).unwrap();
    }

    // Recover - should stop at corrupted entry
    let state = make_conservation_state(0, i128::MIN, i128::MAX);
    let mut recovery = WalRecovery::new(TotalSupplyInvariant::new());
    recovery.state = state;

    let result = recovery.recover_from_file(wal_path_str).unwrap();

    // Should recover only 5 entries (before corruption)
    assert_eq!(result.entries_recovered, 5);
    assert_eq!(result.corrupted_entries, 1);

    let _ = fs::remove_file(&wal_path);
}
