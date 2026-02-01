//! Compile-time test to ensure core functionality works without std.
//!
//! This test file is compiled with `--no-default-features` to verify
//! that the crate's core paths don't accidentally pull in std dependencies.

#![cfg(not(feature = "std"))]

use ctfs::core::invariant::{AlgebraicClass, Invariant};
use ctfs::core::kernel::Kernel;
use ctfs::core::topology::{CausalClock, ExactCausalIndex, FactId};
use ctfs::invariants::monotonic::MaxInvariant;

#[test]
fn test_no_std_kernel_compiles() {
    let kernel = Kernel::new(MaxInvariant::new());
    let _ = kernel.clock();
}

#[test]
fn test_no_std_invariant_algebraic_class() {
    let inv = MaxInvariant::new();
    assert_eq!(inv.algebraic_class(), Some(AlgebraicClass::Lattice));
    assert!(inv.is_coordination_free());
}

#[test]
fn test_no_std_causal_clock() {
    let mut clock = CausalClock::new();
    let fact_id: FactId = [1u8; 32];
    clock.observe(&fact_id);
    assert!(clock.might_contain(&fact_id));
}

#[test]
fn test_no_std_exact_index() {
    let mut index = ExactCausalIndex::new();
    let fact_id: FactId = [2u8; 32];
    index.insert(&fact_id);
    assert!(index.contains(&fact_id));
}
