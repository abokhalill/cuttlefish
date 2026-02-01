//! Property-Based Tests for Algebraic Invariant Properties
//!
//! These tests verify the formal algebraic properties claimed in the specification:
//! - Commutativity
//! - Idempotence
//! - Associativity (for lattice operations)
//! - Convergence

use ctfs::algebra::lattice::{GSetLattice, JoinSemilattice, MaxU64, PNCounter};
use ctfs::algebra::proofs::{CommutativityProof, ConvergenceWitness, IdempotenceProof};
use ctfs::core::invariant::Invariant;
use ctfs::invariants::graph::GGraphInvariant;
use ctfs::invariants::monotonic::{GCounterInvariant, LWWInvariant, MaxInvariant};
use ctfs::invariants::total_supply::TotalSupplyInvariant;
use ctfs::invariants::uniqueness::UniquenessInvariant;

// ============================================================================
// Commutativity Tests
// ============================================================================

#[test]
fn test_total_supply_commutativity() {
    let inv = TotalSupplyInvariant::new();

    // Initialize state: balance=500, min=0, max=1000
    let mut initial = [0u8; 64];
    initial[0..16].copy_from_slice(&500i128.to_le_bytes());
    initial[16..32].copy_from_slice(&0i128.to_le_bytes());
    initial[32..48].copy_from_slice(&1000i128.to_le_bytes());

    // Test multiple delta pairs
    let test_cases: [(i128, i128); 5] = [(10, 20), (-50, 100), (0, 0), (100, -100), (1, -1)];

    for (d1, d2) in test_cases {
        let delta_a = d1.to_le_bytes();
        let delta_b = d2.to_le_bytes();

        let proof = CommutativityProof::verify(&initial, &delta_a, &delta_b, |delta, state| {
            inv.apply(delta, state).map_err(|_| ())
        });

        assert!(
            proof.is_valid(),
            "TotalSupply should be commutative for deltas ({}, {})",
            d1,
            d2
        );
    }
}

#[test]
fn test_max_invariant_commutativity() {
    let inv = MaxInvariant::new();

    let mut initial = [0u8; 64];
    initial[0..8].copy_from_slice(&50u64.to_le_bytes());

    let test_cases: [(u64, u64); 4] = [(100, 200), (200, 100), (50, 50), (0, 1000)];

    for (v1, v2) in test_cases {
        let mut delta_a = [0u8; 16];
        let mut delta_b = [0u8; 16];
        delta_a[0..8].copy_from_slice(&v1.to_le_bytes());
        delta_b[0..8].copy_from_slice(&v2.to_le_bytes());

        let proof = CommutativityProof::verify(&initial, &delta_a, &delta_b, |delta, state| {
            inv.apply(delta, state).map_err(|_| ())
        });

        assert!(
            proof.is_valid(),
            "MaxInvariant should be commutative for values ({}, {})",
            v1,
            v2
        );
    }
}

#[test]
fn test_gcounter_commutativity() {
    let inv = GCounterInvariant::new();

    let initial = [0u8; 64];

    let test_cases: [(u64, u64); 4] = [(10, 20), (100, 1), (0, 0), (1, 1)];

    for (d1, d2) in test_cases {
        let mut delta_a = [0u8; 16];
        let mut delta_b = [0u8; 16];
        delta_a[0..8].copy_from_slice(&d1.to_le_bytes());
        delta_b[0..8].copy_from_slice(&d2.to_le_bytes());

        let proof = CommutativityProof::verify(&initial, &delta_a, &delta_b, |delta, state| {
            inv.apply(delta, state).map_err(|_| ())
        });

        assert!(
            proof.is_valid(),
            "GCounter should be commutative for deltas ({}, {})",
            d1,
            d2
        );
    }
}

#[test]
fn test_ggraph_commutativity() {
    let inv = GGraphInvariant::new();

    // Initialize: 8 vertices, undirected
    let mut initial = [0u8; 64];
    initial[32] = 8; // vertex_count

    // Test adding different edges in different orders
    let test_cases: [((u8, u8), (u8, u8)); 4] = [
        ((0, 1), (2, 3)),
        ((1, 2), (3, 4)),
        ((0, 7), (1, 6)),
        ((0, 0), (1, 1)), // Self-loops (will fail, but consistently)
    ];

    for ((f1, t1), (f2, t2)) in test_cases {
        let mut delta_a = [0u8; 16];
        let mut delta_b = [0u8; 16];
        delta_a[0] = f1;
        delta_a[1] = t1;
        delta_b[0] = f2;
        delta_b[1] = t2;

        // Skip self-loops for this test (they're rejected)
        if f1 == t1 || f2 == t2 {
            continue;
        }

        let proof = CommutativityProof::verify(&initial, &delta_a, &delta_b, |delta, state| {
            inv.apply(delta, state).map_err(|_| ())
        });

        assert!(
            proof.is_valid(),
            "GGraph should be commutative for edges ({}->{}) and ({}->{})",
            f1,
            t1,
            f2,
            t2
        );
    }
}

// ============================================================================
// Idempotence Tests
// ============================================================================

#[test]
fn test_max_invariant_idempotence() {
    let inv = MaxInvariant::new();

    let mut initial = [0u8; 64];
    initial[0..8].copy_from_slice(&50u64.to_le_bytes());

    let test_values: [u64; 4] = [100, 25, 50, 0];

    for v in test_values {
        let mut delta = [0u8; 16];
        delta[0..8].copy_from_slice(&v.to_le_bytes());

        let proof = IdempotenceProof::verify(&initial, &delta, |d, state| {
            inv.apply(d, state).map_err(|_| ())
        });

        assert!(
            proof.is_valid(),
            "MaxInvariant should be idempotent for value {}",
            v
        );
    }
}

#[test]
fn test_uniqueness_idempotence() {
    let inv = UniquenessInvariant::new();

    let initial = [0u8; 64];

    // Note: UniquenessInvariant rejects duplicates, so idempotence means
    // the second application fails but state remains unchanged
    for element_id in [0u16, 42, 100, 511] {
        let mut delta = [0u8; 16];
        delta[0..2].copy_from_slice(&element_id.to_le_bytes());

        // Apply once
        let mut state = initial;
        let _ = inv.apply(&delta, &mut state);
        let state_after_once = state;

        // Apply again (should fail but not change state)
        let _ = inv.apply(&delta, &mut state);
        let state_after_twice = state;

        assert_eq!(
            state_after_once, state_after_twice,
            "Uniqueness should be idempotent (state unchanged after duplicate)"
        );
    }
}

#[test]
fn test_ggraph_idempotence() {
    let inv = GGraphInvariant::new();

    let mut initial = [0u8; 64];
    initial[32] = 8; // vertex_count

    let edges: [(u8, u8); 4] = [(0, 1), (2, 3), (4, 5), (6, 7)];

    for (from, to) in edges {
        let mut delta = [0u8; 16];
        delta[0] = from;
        delta[1] = to;

        let proof = IdempotenceProof::verify(&initial, &delta, |d, state| {
            inv.apply(d, state).map_err(|_| ())
        });

        assert!(
            proof.is_valid(),
            "GGraph should be idempotent for edge {}->{}",
            from,
            to
        );
    }
}

// ============================================================================
// Lattice Property Tests
// ============================================================================

#[test]
fn test_max_u64_lattice_laws() {
    // Commutativity: a ⊔ b = b ⊔ a
    let a = MaxU64(10);
    let b = MaxU64(20);
    assert_eq!(a.join(&b), b.join(&a));

    // Associativity: (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c)
    let c = MaxU64(15);
    assert_eq!(a.join(&b).join(&c), a.join(&b.join(&c)));

    // Idempotence: a ⊔ a = a
    assert_eq!(a.join(&a), a);

    // Order: a ≤ b iff a ⊔ b = b
    assert!(a.leq(&b));
    assert_eq!(a.join(&b), b);
}

#[test]
fn test_gset_lattice_laws() {
    let mut a = GSetLattice::new();
    let mut b = GSetLattice::new();
    let mut c = GSetLattice::new();

    a.insert(1);
    a.insert(5);
    b.insert(3);
    b.insert(5);
    c.insert(7);

    // Commutativity
    assert_eq!(a.join(&b), b.join(&a));

    // Associativity
    assert_eq!(a.join(&b).join(&c), a.join(&b.join(&c)));

    // Idempotence
    assert_eq!(a.join(&a), a);

    // Subset order
    let mut subset = GSetLattice::new();
    subset.insert(1);
    assert!(subset.leq(&a));
}

#[test]
fn test_pn_counter_lattice() {
    let mut c1 = PNCounter::new();
    let mut c2 = PNCounter::new();

    c1.increment(10);
    c2.increment(5);
    c2.decrement(3);

    // Join should take max of each component
    let joined = c1.join(&c2);
    assert_eq!(joined.positive, 10);
    assert_eq!(joined.negative, 3);
    assert_eq!(joined.value(), 7);

    // Commutativity
    assert_eq!(c1.join(&c2), c2.join(&c1));
}

// ============================================================================
// Convergence Tests
// ============================================================================

#[test]
fn test_total_supply_convergence() {
    let inv = TotalSupplyInvariant::new();

    // Initialize state: balance=500, min=0, max=1000
    let mut initial = [0u8; 64];
    initial[0..16].copy_from_slice(&500i128.to_le_bytes());
    initial[16..32].copy_from_slice(&0i128.to_le_bytes());
    initial[32..48].copy_from_slice(&1000i128.to_le_bytes());

    // Multiple deltas that should converge regardless of order
    let deltas: [[u8; 16]; 4] = [
        10i128.to_le_bytes(),
        20i128.to_le_bytes(),
        (-5i128).to_le_bytes(),
        15i128.to_le_bytes(),
    ];

    let witness = ConvergenceWitness::verify(
        &initial,
        &deltas,
        |delta, state| inv.apply(delta, state).map_err(|_| ()),
        10,
    );

    assert!(
        witness.is_valid(),
        "TotalSupply should converge for any application order"
    );

    // Verify final balance: 500 + 10 + 20 - 5 + 15 = 540
    let final_balance = i128::from_le_bytes(witness.final_state[0..16].try_into().unwrap());
    assert_eq!(final_balance, 540);
}

#[test]
fn test_gcounter_convergence() {
    let inv = GCounterInvariant::new();

    let initial = [0u8; 64];

    let deltas: [[u8; 16]; 4] = {
        let mut d = [[0u8; 16]; 4];
        d[0][0..8].copy_from_slice(&10u64.to_le_bytes());
        d[1][0..8].copy_from_slice(&20u64.to_le_bytes());
        d[2][0..8].copy_from_slice(&30u64.to_le_bytes());
        d[3][0..8].copy_from_slice(&40u64.to_le_bytes());
        d
    };

    let witness = ConvergenceWitness::verify(
        &initial,
        &deltas,
        |delta, state| inv.apply(delta, state).map_err(|_| ()),
        10,
    );

    assert!(witness.is_valid(), "GCounter should converge");

    // Final count: 10 + 20 + 30 + 40 = 100
    let final_count = u64::from_le_bytes(witness.final_state[0..8].try_into().unwrap());
    assert_eq!(final_count, 100);
}

#[test]
fn test_max_convergence() {
    let inv = MaxInvariant::new();

    let initial = [0u8; 64];

    let deltas: [[u8; 16]; 4] = {
        let mut d = [[0u8; 16]; 4];
        d[0][0..8].copy_from_slice(&50u64.to_le_bytes());
        d[1][0..8].copy_from_slice(&100u64.to_le_bytes());
        d[2][0..8].copy_from_slice(&25u64.to_le_bytes());
        d[3][0..8].copy_from_slice(&75u64.to_le_bytes());
        d
    };

    let witness = ConvergenceWitness::verify(
        &initial,
        &deltas,
        |delta, state| inv.apply(delta, state).map_err(|_| ()),
        10,
    );

    assert!(witness.is_valid(), "Max should converge");

    // Final value: max(50, 100, 25, 75) = 100
    let final_value = u64::from_le_bytes(witness.final_state[0..8].try_into().unwrap());
    assert_eq!(final_value, 100);
}

// ============================================================================
// Composition Tests
// ============================================================================

#[test]
fn test_composition_preserves_commutativity() {
    use ctfs::algebra::composition::ComposedInvariant;

    let composed = ComposedInvariant::new(TotalSupplyInvariant::new(), GCounterInvariant::new());

    // Initialize state: TotalSupply (64 bytes) + GCounter (64 bytes)
    let mut initial = [0u8; 128];
    // TotalSupply: balance=500, min=0, max=1000
    initial[0..16].copy_from_slice(&500i128.to_le_bytes());
    initial[16..32].copy_from_slice(&0i128.to_le_bytes());
    initial[32..48].copy_from_slice(&1000i128.to_le_bytes());
    // GCounter: starts at 0

    // Test commutativity of composed operations
    let payload1_a = 10i128.to_le_bytes();
    let mut payload1_b = [0u8; 16];
    payload1_b[0..8].copy_from_slice(&5u64.to_le_bytes());

    let payload2_a = 20i128.to_le_bytes();
    let mut payload2_b = [0u8; 16];
    payload2_b[0..8].copy_from_slice(&10u64.to_le_bytes());

    // Order 1: apply (payload1_a, payload1_b) then (payload2_a, payload2_b)
    let mut state1 = initial;
    composed
        .apply_split(&payload1_a, &payload1_b, &mut state1)
        .unwrap();
    composed
        .apply_split(&payload2_a, &payload2_b, &mut state1)
        .unwrap();

    // Order 2: apply (payload2_a, payload2_b) then (payload1_a, payload1_b)
    let mut state2 = initial;
    composed
        .apply_split(&payload2_a, &payload2_b, &mut state2)
        .unwrap();
    composed
        .apply_split(&payload1_a, &payload1_b, &mut state2)
        .unwrap();

    // States should be identical
    assert_eq!(state1, state2, "Composed invariant should be commutative");
}

// ============================================================================
// Stress Tests
// ============================================================================

#[test]
fn test_high_volume_commutativity() {
    let inv = TotalSupplyInvariant::new();

    // Initialize state
    let mut initial = [0u8; 64];
    initial[0..16].copy_from_slice(&500000i128.to_le_bytes());
    initial[16..32].copy_from_slice(&0i128.to_le_bytes());
    initial[32..48].copy_from_slice(&1000000i128.to_le_bytes());

    // Generate 100 random-ish deltas
    let mut deltas: Vec<i128> = Vec::new();
    for i in 0..100 {
        let delta = ((i as i128 * 17) % 1000) - 500; // Range: -500 to 499
        deltas.push(delta);
    }

    // Apply in forward order
    let mut state_forward = initial;
    for d in &deltas {
        let payload = d.to_le_bytes();
        let _ = inv.apply(&payload, &mut state_forward);
    }

    // Apply in reverse order
    let mut state_reverse = initial;
    for d in deltas.iter().rev() {
        let payload = d.to_le_bytes();
        let _ = inv.apply(&payload, &mut state_reverse);
    }

    // Should converge to same state
    assert_eq!(
        state_forward, state_reverse,
        "High-volume operations should converge"
    );
}
