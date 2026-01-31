//! TwoLaneKernel: BFVC + ExactCausalIndex for precise dependency tracking.

use ctfs::core::kernel::{TwoLaneKernel, AdmitError};
use ctfs::core::StateCell;
use ctfs::core::topology::FactId;
use ctfs::invariants::total_supply::{ConservationState, TotalSupplyInvariant};
use zerocopy::IntoBytes;

fn main() {
    // 1. Initialize state
    let initial = ConservationState::new(10_000, 0, 1_000_000);
    let mut cell = StateCell::new();
    cell.as_slice_mut().copy_from_slice(initial.as_bytes());

    // 2. TwoLaneKernel: Bloom filter (fast) + ExactCausalIndex (precise)
    let mut kernel = TwoLaneKernel::with_state(TotalSupplyInvariant::new(), cell);

    // 3. Admit a chain of facts
    let mut prev_fact: Option<FactId> = None;
    for i in 0..100u32 {
        let mut fact_id = [0u8; 32];
        fact_id[0..4].copy_from_slice(&i.to_le_bytes());

        let delta = 10i128.to_le_bytes();
        let deps: &[FactId] = match &prev_fact {
            Some(f) => core::slice::from_ref(f),
            None => &[],
        };

        kernel.admit(&fact_id, deps, &delta).expect("admit");
        prev_fact = Some(fact_id);
    }

    // 4. Query state
    let state = kernel.state().cast_ref::<ConservationState>().unwrap();
    println!("Balance after 100 facts: {}", state.balance); // 11000

    // 5. ExactCausalIndex rejects facts with dependencies outside the horizon
    // (horizon is 1024 facts by default)
    let old_fact: FactId = [0u8; 32]; // fact 0
    let new_fact: FactId = [200u8; 32];
    let delta = 1i128.to_le_bytes();

    // This works because fact 0 is still in the ExactCausalIndex
    match kernel.admit(&new_fact, &[old_fact], &delta) {
        Ok(()) => println!("Dependency on fact 0 accepted"),
        Err(AdmitError::CausalHorizonExceeded) => println!("Fact 0 evicted from horizon"),
        Err(e) => println!("Other error: {:?}", e),
    }

    println!("TwoLaneKernel example complete.");
}
