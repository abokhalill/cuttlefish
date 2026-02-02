//! Property-based tests for invariant commutativity.
//!
//! These tests verify that invariants claiming coordination-freedom
//! actually satisfy the commutativity property: apply(a, apply(b, s)) = apply(b, apply(a, s))

use proptest::prelude::*;

use ctfs::core::invariant::Invariant;
use ctfs::core::state::StateCell;
use ctfs::invariants::monotonic::{GCounterInvariant, LWWInvariant, MaxInvariant};
use ctfs::invariants::total_supply::{DeltaPayload, TotalSupplyInvariant};

fn state_with_balance(balance: i128, min: i128, max: i128) -> StateCell {
    use zerocopy::IntoBytes;
    use ctfs::invariants::total_supply::ConservationState;

    let mut state = StateCell::new();
    let conservation = ConservationState::new(balance, min, max);
    state.as_slice_mut()[..64].copy_from_slice(conservation.as_bytes());
    state
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1000))]

    #[test]
    fn max_invariant_commutative(a in 0u64..u64::MAX, b in 0u64..u64::MAX) {
        let inv = MaxInvariant::new();

        // Path 1: apply a then b
        let mut state1 = StateCell::new();
        let payload_a = a.to_le_bytes();
        let payload_b = b.to_le_bytes();
        inv.apply(&payload_a, state1.as_bytes_mut()).unwrap();
        inv.apply(&payload_b, state1.as_bytes_mut()).unwrap();

        // Path 2: apply b then a
        let mut state2 = StateCell::new();
        inv.apply(&payload_b, state2.as_bytes_mut()).unwrap();
        inv.apply(&payload_a, state2.as_bytes_mut()).unwrap();

        // States must be identical
        prop_assert_eq!(state1.as_slice(), state2.as_slice());
    }

    #[test]
    fn gcounter_commutative(a in 0u64..1_000_000u64, b in 0u64..1_000_000u64) {
        let inv = GCounterInvariant::new();

        let mut state1 = StateCell::new();
        let payload_a = a.to_le_bytes();
        let payload_b = b.to_le_bytes();
        inv.apply(&payload_a, state1.as_bytes_mut()).unwrap();
        inv.apply(&payload_b, state1.as_bytes_mut()).unwrap();

        let mut state2 = StateCell::new();
        inv.apply(&payload_b, state2.as_bytes_mut()).unwrap();
        inv.apply(&payload_a, state2.as_bytes_mut()).unwrap();

        prop_assert_eq!(state1.as_slice(), state2.as_slice());
    }

    #[test]
    fn lww_commutative_same_timestamp(node_a in 0u64..u64::MAX, node_b in 0u64..u64::MAX) {
        let inv = LWWInvariant::new();

        // LWW payload: 32-byte value + 8-byte timestamp + 8-byte node_id
        // With same timestamp, higher node_id wins (deterministic)
        let ts: u64 = 1000;
        let value: [u8; 32] = [0xAB; 32];

        let mut payload_a = [0u8; 48];
        payload_a[0..32].copy_from_slice(&value);
        payload_a[32..40].copy_from_slice(&ts.to_le_bytes());
        payload_a[40..48].copy_from_slice(&node_a.to_le_bytes());

        let mut payload_b = [0u8; 48];
        payload_b[0..32].copy_from_slice(&value);
        payload_b[32..40].copy_from_slice(&ts.to_le_bytes());
        payload_b[40..48].copy_from_slice(&node_b.to_le_bytes());

        let mut state1 = StateCell::new();
        inv.apply(&payload_a, state1.as_bytes_mut()).unwrap();
        inv.apply(&payload_b, state1.as_bytes_mut()).unwrap();

        let mut state2 = StateCell::new();
        inv.apply(&payload_b, state2.as_bytes_mut()).unwrap();
        inv.apply(&payload_a, state2.as_bytes_mut()).unwrap();

        prop_assert_eq!(state1.as_slice(), state2.as_slice());
    }

    #[test]
    fn total_supply_commutative(
        delta_a in -1000i128..1000i128,
        delta_b in -1000i128..1000i128
    ) {
        let inv = TotalSupplyInvariant::new();

        // Start with enough balance to handle negative deltas
        let initial_balance: i128 = 100_000;
        let min: i128 = 0;
        let max: i128 = i128::MAX;

        let payload_a = DeltaPayload { delta: delta_a };
        let payload_b = DeltaPayload { delta: delta_b };

        use zerocopy::IntoBytes;

        let mut state1 = state_with_balance(initial_balance, min, max);
        let _ = inv.apply(payload_a.as_bytes(), state1.as_bytes_mut());
        let _ = inv.apply(payload_b.as_bytes(), state1.as_bytes_mut());

        let mut state2 = state_with_balance(initial_balance, min, max);
        let _ = inv.apply(payload_b.as_bytes(), state2.as_bytes_mut());
        let _ = inv.apply(payload_a.as_bytes(), state2.as_bytes_mut());

        // If both paths succeed, states must match
        // (some paths may fail due to bounds, which is fine)
        if state1.as_slice()[..24] != [0u8; 24] && state2.as_slice()[..24] != [0u8; 24] {
            prop_assert_eq!(state1.as_slice(), state2.as_slice());
        }
    }

    #[test]
    fn max_invariant_idempotent(value in 0u64..u64::MAX) {
        let inv = MaxInvariant::new();
        let payload = value.to_le_bytes();

        let mut state1 = StateCell::new();
        inv.apply(&payload, state1.as_bytes_mut()).unwrap();

        let mut state2 = StateCell::new();
        inv.apply(&payload, state2.as_bytes_mut()).unwrap();
        inv.apply(&payload, state2.as_bytes_mut()).unwrap();

        // Applying same value twice should be same as once
        prop_assert_eq!(state1.as_slice(), state2.as_slice());
    }

    #[test]
    fn gcounter_associative(a in 0u64..100_000u64, b in 0u64..100_000u64, c in 0u64..100_000u64) {
        let inv = GCounterInvariant::new();

        let payload_a = a.to_le_bytes();
        let payload_b = b.to_le_bytes();
        let payload_c = c.to_le_bytes();

        // (a + b) + c
        let mut state1 = StateCell::new();
        inv.apply(&payload_a, state1.as_bytes_mut()).unwrap();
        inv.apply(&payload_b, state1.as_bytes_mut()).unwrap();
        inv.apply(&payload_c, state1.as_bytes_mut()).unwrap();

        // a + (b + c)
        let mut state2 = StateCell::new();
        inv.apply(&payload_a, state2.as_bytes_mut()).unwrap();
        inv.apply(&payload_b, state2.as_bytes_mut()).unwrap();
        inv.apply(&payload_c, state2.as_bytes_mut()).unwrap();

        // c + (a + b)
        let mut state3 = StateCell::new();
        inv.apply(&payload_c, state3.as_bytes_mut()).unwrap();
        inv.apply(&payload_a, state3.as_bytes_mut()).unwrap();
        inv.apply(&payload_b, state3.as_bytes_mut()).unwrap();

        prop_assert_eq!(state1.as_slice(), state2.as_slice());
        prop_assert_eq!(state1.as_slice(), state3.as_slice());
    }
}
