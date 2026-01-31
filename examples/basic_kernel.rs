//! Basic kernel usage: admit facts, check causality, query state.

use ctfs::core::topology::FactId;
use ctfs::core::{AdmitError, Kernel, StateCell};
use ctfs::invariants::total_supply::{ConservationState, TotalSupplyInvariant};
use zerocopy::IntoBytes;

fn main() {
    // 1. Initialize state: balance=1000, min=0, max=1_000_000
    let initial = ConservationState::new(1000, 0, 1_000_000);
    let mut cell = StateCell::new();
    cell.as_slice_mut().copy_from_slice(initial.as_bytes());

    // 2. Create kernel with invariant
    let mut kernel = Kernel::with_state(TotalSupplyInvariant::new(), cell);

    // 3. Admit facts (state transitions)
    let fact1: FactId = [1u8; 32];
    let delta1 = 500i128.to_le_bytes(); // +500
    kernel
        .admit_raw(&fact1, &[], &delta1)
        .expect("fact1 should succeed");

    // 4. Admit with causal dependency
    let fact2: FactId = [2u8; 32];
    let delta2 = (-200i128).to_le_bytes(); // -200
    kernel
        .admit_raw(&fact2, &[fact1], &delta2)
        .expect("fact2 depends on fact1");

    // 5. Query final state
    let state = kernel.state().cast_ref::<ConservationState>().unwrap();
    println!("Final balance: {}", state.balance); // 1300

    // 6. Invariant violation: would go below min
    let fact3: FactId = [3u8; 32];
    let bad_delta = (-2000i128).to_le_bytes();
    match kernel.admit_raw(&fact3, &[fact2], &bad_delta) {
        Err(AdmitError::InvariantViolation) => println!("Rejected: would underflow"),
        _ => panic!("should have been rejected"),
    }

    // 7. Causality violation: unknown dependency
    let unknown: FactId = [99u8; 32];
    let fact4: FactId = [4u8; 32];
    match kernel.admit_raw(&fact4, &[unknown], &delta1) {
        Err(AdmitError::CausalityViolation) => println!("Rejected: unknown dependency"),
        _ => panic!("should have been rejected"),
    }

    println!("Basic kernel example complete.");
}
