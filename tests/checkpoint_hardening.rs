//! Tests for checkpoint integrity verification hardening.

#[cfg(feature = "persistence")]
mod checkpoint_tests {
    use cuttlefish::core::checkpoint::{Checkpoint, CheckpointHeader, CheckpointManager};
    use cuttlefish::core::frontier::FrontierState;
    use cuttlefish::core::state::StateCell;
    use std::fs;
    use zerocopy::IntoBytes;

    #[test]
    fn test_checkpoint_integrity_verification() {
        let tmp_path = "/tmp/cuttlefish_test_checkpoint_integrity.ckpt";
        let _ = fs::remove_file(tmp_path);

        let mut state = StateCell::new();
        state.as_slice_mut()[0..8].copy_from_slice(&42u64.to_le_bytes());

        let mut frontier_state = FrontierState::new();
        frontier_state.advance([0xAAu8; 32]);
        frontier_state.advance([0xBBu8; 32]);

        let tiered_hash = Checkpoint::compute_tiered_hash(&state, &frontier_state);

        let header = CheckpointHeader::new(100, 4096, tiered_hash);
        let header_bytes = header.to_bytes();

        {
            use std::io::Write;
            let mut file = fs::File::create(tmp_path).unwrap();
            file.write_all(&header_bytes).unwrap();
            file.write_all(state.as_bytes()).unwrap();
            file.write_all(frontier_state.clock.as_bytes()).unwrap();
            for fact_id in frontier_state.frontier.iter() {
                file.write_all(fact_id).unwrap();
            }
            file.sync_all().unwrap();
        }

        let manager = CheckpointManager::new(tmp_path);
        let result = manager.read_checkpoint().unwrap();
        assert!(result.is_some());

        let (read_header, read_state, _read_clock) = result.unwrap();
        assert_eq!(read_header.wal_sequence, 100);
        assert_eq!(read_state.as_bytes()[0..8], state.as_bytes()[0..8]);

        fs::remove_file(tmp_path).unwrap();
    }

    #[test]
    fn test_checkpoint_rejects_corrupted_state() {
        let tmp_path = "/tmp/cuttlefish_test_checkpoint_corrupt.ckpt";
        let _ = fs::remove_file(tmp_path);

        let mut state = StateCell::new();
        state.as_slice_mut()[0..8].copy_from_slice(&42u64.to_le_bytes());

        let mut frontier_state = FrontierState::new();
        frontier_state.advance([0xCCu8; 32]);

        let tiered_hash = Checkpoint::compute_tiered_hash(&state, &frontier_state);
        let header = CheckpointHeader::new(200, 8192, tiered_hash);

        let mut corrupted_state = state;
        corrupted_state.as_slice_mut()[0] = 0xFF;

        {
            use std::io::Write;
            let mut file = fs::File::create(tmp_path).unwrap();
            file.write_all(&header.to_bytes()).unwrap();
            file.write_all(corrupted_state.as_bytes()).unwrap();
            file.write_all(frontier_state.clock.as_bytes()).unwrap();
            for fact_id in frontier_state.frontier.iter() {
                file.write_all(fact_id).unwrap();
            }
            file.sync_all().unwrap();
        }

        let manager = CheckpointManager::new(tmp_path);
        let result = manager.read_checkpoint().unwrap();
        assert!(result.is_none(), "Corrupted state should be rejected");

        fs::remove_file(tmp_path).unwrap();
    }

    #[test]
    fn test_checkpoint_rejects_corrupted_hash() {
        let tmp_path = "/tmp/cuttlefish_test_checkpoint_bad_hash.ckpt";
        let _ = fs::remove_file(tmp_path);

        let mut state = StateCell::new();
        state.as_slice_mut()[0..8].copy_from_slice(&99u64.to_le_bytes());

        let frontier_state = FrontierState::new();

        let bad_hash = [0xFFu8; 32];
        let header = CheckpointHeader::new(300, 12288, bad_hash);

        {
            use std::io::Write;
            let mut file = fs::File::create(tmp_path).unwrap();
            file.write_all(&header.to_bytes()).unwrap();
            file.write_all(state.as_bytes()).unwrap();
            file.write_all(frontier_state.clock.as_bytes()).unwrap();
            file.sync_all().unwrap();
        }

        let manager = CheckpointManager::new(tmp_path);
        let result = manager.read_checkpoint().unwrap();
        assert!(result.is_none(), "Bad hash should be rejected");

        fs::remove_file(tmp_path).unwrap();
    }

    #[test]
    fn test_checkpoint_rejects_truncated_file() {
        let tmp_path = "/tmp/cuttlefish_test_checkpoint_truncated.ckpt";
        let _ = fs::remove_file(tmp_path);

        let mut state = StateCell::new();
        state.as_slice_mut()[0..8].copy_from_slice(&77u64.to_le_bytes());

        let frontier_state = FrontierState::new();
        let tiered_hash = Checkpoint::compute_tiered_hash(&state, &frontier_state);
        let header = CheckpointHeader::new(400, 16384, tiered_hash);

        {
            use std::io::Write;
            let mut file = fs::File::create(tmp_path).unwrap();
            file.write_all(&header.to_bytes()).unwrap();
            file.write_all(&state.as_bytes()[0..32]).unwrap();
            file.sync_all().unwrap();
        }

        let manager = CheckpointManager::new(tmp_path);
        let result = manager.read_checkpoint();
        assert!(
            result.is_err() || result.unwrap().is_none(),
            "Truncated file should fail"
        );

        fs::remove_file(tmp_path).unwrap();
    }

    #[test]
    fn test_tiered_hash_deterministic() {
        let mut state = StateCell::new();
        state.as_slice_mut()[0..8].copy_from_slice(&123u64.to_le_bytes());

        let mut frontier_state = FrontierState::new();
        frontier_state.advance([0x11u8; 32]);

        let hash1 = Checkpoint::compute_tiered_hash(&state, &frontier_state);
        let hash2 = Checkpoint::compute_tiered_hash(&state, &frontier_state);

        assert_eq!(hash1, hash2, "Tiered hash should be deterministic");
    }

    #[test]
    fn test_tiered_hash_changes_with_state() {
        let mut state1 = StateCell::new();
        state1.as_slice_mut()[0..8].copy_from_slice(&1u64.to_le_bytes());

        let mut state2 = StateCell::new();
        state2.as_slice_mut()[0..8].copy_from_slice(&2u64.to_le_bytes());

        let frontier_state = FrontierState::new();

        let hash1 = Checkpoint::compute_tiered_hash(&state1, &frontier_state);
        let hash2 = Checkpoint::compute_tiered_hash(&state2, &frontier_state);

        assert_ne!(
            hash1, hash2,
            "Different state should produce different hash"
        );
    }

    #[test]
    fn test_tiered_hash_changes_with_frontier() {
        let state = StateCell::new();

        let mut frontier1 = FrontierState::new();
        frontier1.advance([0x11u8; 32]);

        let mut frontier2 = FrontierState::new();
        frontier2.advance([0x22u8; 32]);

        let hash1 = Checkpoint::compute_tiered_hash(&state, &frontier1);
        let hash2 = Checkpoint::compute_tiered_hash(&state, &frontier2);

        assert_ne!(
            hash1, hash2,
            "Different frontier should produce different hash"
        );
    }
}
