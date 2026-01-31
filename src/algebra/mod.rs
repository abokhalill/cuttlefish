//! Invariant algebra. Commutative → no coordination. That's the whole trick.

pub mod classes;
pub mod composition;
pub mod lattice;
pub mod proofs;

#[cfg(feature = "std")]
pub mod causal_consistency;

pub use classes::{
    AlgebraicClass, BoundedInvariant, CommutativeInvariant, GroupInvariant, IdempotentInvariant,
    LatticeInvariant, MonotonicInvariant,
};
pub use composition::{ComposedInvariant, ParallelComposition};
pub use lattice::{BoundedLattice, JoinSemilattice, LatticeMerge, MeetSemilattice};
pub use proofs::{CommutativityProof, ConvergenceWitness, CoordinationClass};

#[cfg(feature = "std")]
pub use causal_consistency::{
    verify_acc_theorem, AccProofWitness, CausalFact, CausalOrderValidator,
    CausallyConsistentInvariant,
};
