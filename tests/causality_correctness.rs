//! Adversarial Correctness Tests for Two-Tier Causality.
//!
//! These tests prove that the Two-Lane architecture correctly rejects
//! facts with false-positive dependencies (BFVC says yes, ExactIndex says no).

use cuttlefish::core::frontier::build_deps_clock;
use cuttlefish::core::kernel::{AdmitError, TwoLaneKernel};
use cuttlefish::core::state::StateCell;
use cuttlefish::core::topology::{CausalClock, ExactCausalIndex, FactId};
use cuttlefish::invariants::total_supply::{ConservationState, TotalSupplyInvariant};
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

/// CRITICAL TEST: Adversarial false-positive rejection.
///
/// This test simulates the scenario where:
/// 1. A fact's dependency bits are set in the BFVC (Bloom filter)
/// 2. But the actual fact was never admitted to the ExactCausalIndex
///
/// The kernel MUST reject this admission. The two-tier check works as:
/// - Tier 0 (BFVC): Fast probabilistic prefilter - rejects with CausalityViolation
/// - Tier 1 (ExactIndex): Ground truth - rejects with CausalHorizonExceeded
///
/// If BFVC rejects first, we get CausalityViolation.
/// If BFVC passes (false positive) but ExactIndex rejects, we get CausalHorizonExceeded.
#[test]
fn test_false_positive_dependency_rejected() {
    let state = make_conservation_state(0, i128::MIN, i128::MAX);
    let mut kernel = TwoLaneKernel::with_state(TotalSupplyInvariant::new(), state);
    let payload = make_payload(1);

    // Admit a real fact
    let real_fact: FactId = [1u8; 32];
    kernel.admit(&real_fact, &[], &payload).unwrap();

    // Create a "phantom" dependency that was never admitted
    let phantom_dep: FactId = [0xFF; 32];

    // Try to admit a fact that depends on the phantom
    let new_fact: FactId = [2u8; 32];
    let result = kernel.admit(&new_fact, &[phantom_dep], &payload);

    // MUST be rejected - either by BFVC (CausalityViolation) or ExactIndex (CausalHorizonExceeded)
    assert!(
        result == Err(AdmitError::CausalityViolation)
            || result == Err(AdmitError::CausalHorizonExceeded),
        "Kernel must reject dependency that was never admitted, got {:?}",
        result
    );

    // Verify the new fact was NOT admitted
    assert!(
        !kernel.exact_index().contains(&new_fact),
        "Rejected fact must not be in ExactIndex"
    );
}

/// Test: Valid dependencies are accepted.
#[test]
fn test_valid_dependency_accepted() {
    let state = make_conservation_state(0, i128::MIN, i128::MAX);
    let mut kernel = TwoLaneKernel::with_state(TotalSupplyInvariant::new(), state);
    let payload = make_payload(1);

    // Admit first fact
    let fact1: FactId = [1u8; 32];
    kernel.admit(&fact1, &[], &payload).unwrap();

    // Admit second fact depending on first
    let fact2: FactId = [2u8; 32];
    let result = kernel.admit(&fact2, &[fact1], &payload);

    assert!(result.is_ok(), "Valid dependency should be accepted");
    assert!(kernel.exact_index().contains(&fact2));
}

/// Test: Multiple dependencies all checked.
#[test]
fn test_multiple_deps_all_must_exist() {
    let state = make_conservation_state(0, i128::MIN, i128::MAX);
    let mut kernel = TwoLaneKernel::with_state(TotalSupplyInvariant::new(), state);
    let payload = make_payload(1);

    // Admit two facts
    let fact1: FactId = [1u8; 32];
    let fact2: FactId = [2u8; 32];
    kernel.admit(&fact1, &[], &payload).unwrap();
    kernel.admit(&fact2, &[], &payload).unwrap();

    // Create a phantom that was never admitted
    let phantom: FactId = [0xAB; 32];

    // Try to admit with deps = [fact1, phantom, fact2]
    // Should fail because phantom doesn't exist
    let new_fact: FactId = [3u8; 32];
    let result = kernel.admit(&new_fact, &[fact1, phantom, fact2], &payload);

    // Must be rejected - either by BFVC or ExactIndex
    assert!(
        result == Err(AdmitError::CausalityViolation)
            || result == Err(AdmitError::CausalHorizonExceeded),
        "Must reject if ANY dependency is missing, got {:?}",
        result
    );
}

/// Test: Empty dependencies always accepted (no causality constraint).
#[test]
fn test_empty_deps_always_valid() {
    let state = make_conservation_state(0, i128::MIN, i128::MAX);
    let mut kernel = TwoLaneKernel::with_state(TotalSupplyInvariant::new(), state);
    let payload = make_payload(1);

    for i in 0u64..100 {
        let mut fact_id = [0u8; 32];
        fact_id[..8].copy_from_slice(&i.to_le_bytes());

        let result = kernel.admit(&fact_id, &[], &payload);
        assert!(result.is_ok(), "Empty deps should always be valid");
    }

    assert_eq!(kernel.exact_index().len(), 100);
}

/// Test: ExactCausalIndex correctly tracks all admitted facts.
#[test]
fn test_exact_index_tracks_all_facts() {
    let state = make_conservation_state(0, i128::MIN, i128::MAX);
    let mut kernel = TwoLaneKernel::with_state(TotalSupplyInvariant::new(), state);
    let payload = make_payload(1);

    let mut admitted_facts: Vec<FactId> = Vec::new();

    for i in 0u64..200 {
        let mut fact_id = [0u8; 32];
        fact_id[..8].copy_from_slice(&i.to_le_bytes());

        kernel.admit(&fact_id, &[], &payload).unwrap();
        admitted_facts.push(fact_id);
    }

    // All admitted facts should be in ExactIndex
    for fact_id in &admitted_facts {
        assert!(
            kernel.exact_index().contains(fact_id),
            "Admitted fact must be in ExactIndex"
        );
    }

    // Non-admitted facts should NOT be in ExactIndex
    let non_admitted: FactId = [0xFF; 32];
    assert!(
        !kernel.exact_index().contains(&non_admitted),
        "Non-admitted fact must not be in ExactIndex"
    );
}

/// Test: BFVC and ExactIndex stay synchronized.
#[test]
fn test_bfvc_and_exact_index_synchronized() {
    let state = make_conservation_state(0, i128::MIN, i128::MAX);
    let mut kernel = TwoLaneKernel::with_state(TotalSupplyInvariant::new(), state);
    let payload = make_payload(1);

    for i in 0u64..50 {
        let mut fact_id = [0u8; 32];
        fact_id[..8].copy_from_slice(&i.to_le_bytes());

        kernel.admit(&fact_id, &[], &payload).unwrap();

        // Both structures should contain the fact
        assert!(kernel.clock().might_contain(&fact_id));
        assert!(kernel.exact_index().contains(&fact_id));
    }
}

/// Test: Causal chain integrity.
#[test]
fn test_causal_chain_integrity() {
    let state = make_conservation_state(0, i128::MIN, i128::MAX);
    let mut kernel = TwoLaneKernel::with_state(TotalSupplyInvariant::new(), state);
    let payload = make_payload(1);

    // Build a chain: f0 <- f1 <- f2 <- ... <- f99
    let mut prev_fact: FactId = [0u8; 32];
    kernel.admit(&prev_fact, &[], &payload).unwrap();

    for i in 1u64..100 {
        let mut fact_id = [0u8; 32];
        fact_id[..8].copy_from_slice(&i.to_le_bytes());

        let result = kernel.admit(&fact_id, &[prev_fact], &payload);
        assert!(result.is_ok(), "Chain link {} should be valid", i);

        prev_fact = fact_id;
    }

    assert_eq!(kernel.exact_index().len(), 100);
}

/// Test: Invariant violation does not corrupt causal state.
#[test]
fn test_invariant_violation_preserves_causal_state() {
    let state = make_conservation_state(100, 0, 1000); // min=0, max=1000
    let mut kernel = TwoLaneKernel::with_state(TotalSupplyInvariant::new(), state);

    // Admit a valid fact
    let fact1: FactId = [1u8; 32];
    let valid_payload = make_payload(50);
    kernel.admit(&fact1, &[], &valid_payload).unwrap();

    let index_len_before = kernel.exact_index().len();

    // Try to admit a fact that violates the invariant (underflow)
    let fact2: FactId = [2u8; 32];
    let invalid_payload = make_payload(-200); // Would cause underflow
    let result = kernel.admit(&fact2, &[fact1], &invalid_payload);

    assert_eq!(result, Err(AdmitError::InvariantViolation));

    // Causal state should be unchanged
    assert_eq!(kernel.exact_index().len(), index_len_before);
    assert!(!kernel.exact_index().contains(&fact2));
}

/// Test: Standalone ExactCausalIndex false-positive scenario.
#[test]
fn test_exact_index_rejects_missing_deps() {
    let mut bfvc = CausalClock::new();
    let mut index = ExactCausalIndex::new();

    let fact1: FactId = [1u8; 32];
    let fact2: FactId = [2u8; 32];

    // Add fact1 to both
    bfvc.observe(&fact1);
    index.observe(&fact1);

    // Add fact2 ONLY to BFVC (simulating false positive)
    bfvc.observe(&fact2);
    // NOT added to index

    // BFVC says "might contain" for both
    assert!(bfvc.might_contain(&fact1));
    assert!(bfvc.might_contain(&fact2));

    // ExactIndex correctly distinguishes
    assert!(index.contains(&fact1));
    assert!(!index.contains(&fact2));

    // contains_all correctly rejects
    assert!(index.contains_all(&[fact1]).is_ok());
    assert!(index.contains_all(&[fact2]).is_err());
    assert!(index.contains_all(&[fact1, fact2]).is_err());
}

#[test]
fn test_causal_poison_8_deps_forces_horizon_exceeded() {
    let state = make_conservation_state(0, i128::MIN, i128::MAX);
    let mut kernel = TwoLaneKernel::with_state(TotalSupplyInvariant::new(), state);
    let payload = make_payload(1);

    let mut real_deps: [FactId; 7] = [[0u8; 32]; 7];
    for i in 0u8..7 {
        let mut fact_id: FactId = [0u8; 32];
        fact_id[0] = i.wrapping_add(1);
        kernel.admit(&fact_id, &[], &payload).unwrap();
        real_deps[i as usize] = fact_id;
    }

    let ghost_dep: FactId = [0xEE; 32];

    // Force BFVC dominance to pass by manually observing the ghost in the BFVC
    // without inserting it into the ExactCausalIndex.
    kernel.frontier.clock.observe(&ghost_dep);

    let deps: [FactId; 8] = [
        real_deps[0],
        real_deps[1],
        real_deps[2],
        real_deps[3],
        real_deps[4],
        real_deps[5],
        real_deps[6],
        ghost_dep,
    ];

    let deps_clock = build_deps_clock(&deps);
    assert!(kernel.clock().dominates(&deps_clock));
    assert!(!kernel.exact_index().contains(&ghost_dep));

    let new_fact: FactId = [0xAA; 32];
    let result = kernel.admit(&new_fact, &deps, &payload);
    assert_eq!(result, Err(AdmitError::CausalHorizonExceeded));
    assert!(!kernel.exact_index().contains(&new_fact));
}
