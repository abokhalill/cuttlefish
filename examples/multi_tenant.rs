//! Multi-tenant kernel: isolated causal domains per tenant.

use ctfs::core::{TenantKernel, StateCell, AdmitError};
use ctfs::core::topology::FactId;
use ctfs::invariants::total_supply::{ConservationState, TotalSupplyInvariant};
use zerocopy::IntoBytes;

fn main() {
    // 1. Create multi-tenant kernel
    let mut kernel = TenantKernel::new(TotalSupplyInvariant::new());

    // 2. Register tenants with isolated state
    let alice_state = ConservationState::new(10_000, 0, 100_000);
    let bob_state = ConservationState::new(5_000, 0, 50_000);

    let mut alice_cell = StateCell::new();
    alice_cell.as_slice_mut().copy_from_slice(alice_state.as_bytes());

    let mut bob_cell = StateCell::new();
    bob_cell.as_slice_mut().copy_from_slice(bob_state.as_bytes());

    kernel.register_tenant(1, alice_cell).expect("register alice");
    kernel.register_tenant(2, bob_cell).expect("register bob");

    // 3. Alice admits facts
    let alice_fact1: FactId = [1u8; 32];
    let alice_delta = 1000i128.to_le_bytes();
    kernel.admit(1, &alice_fact1, &[], &alice_delta).expect("alice fact1");

    // 4. Bob admits facts (independent causal domain)
    let bob_fact1: FactId = [2u8; 32];
    let bob_delta = (-500i128).to_le_bytes();
    kernel.admit(2, &bob_fact1, &[], &bob_delta).expect("bob fact1");

    // 5. Cross-tenant dependency is REJECTED (isolated domains)
    let alice_fact2: FactId = [3u8; 32];
    match kernel.admit(1, &alice_fact2, &[bob_fact1], &alice_delta) {
        Err(AdmitError::CausalityViolation) => {
            println!("Cross-tenant dependency rejected (as expected)");
        }
        _ => panic!("should reject cross-tenant dependency"),
    }

    // 6. Same-tenant dependency works
    let alice_fact3: FactId = [4u8; 32];
    kernel.admit(1, &alice_fact3, &[alice_fact1], &alice_delta).expect("alice fact3");

    // 7. Check isolated saturation
    let alice_sat = kernel.saturation(1).unwrap();
    let bob_sat = kernel.saturation(2).unwrap();
    println!("Alice Bloom saturation: {:.2}%", alice_sat * 100.0);
    println!("Bob Bloom saturation: {:.2}%", bob_sat * 100.0);

    // 8. Query isolated state
    let alice_balance = kernel.state(1).unwrap()
        .cast_ref::<ConservationState>().unwrap().balance;
    let bob_balance = kernel.state(2).unwrap()
        .cast_ref::<ConservationState>().unwrap().balance;

    println!("Alice balance: {}", alice_balance); // 12000
    println!("Bob balance: {}", bob_balance);     // 4500

    println!("Multi-tenant example complete.");
}
