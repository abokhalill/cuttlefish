//! Invariant algebra. Commutative → no coordination. That's the whole trick.

pub mod classes;
pub mod lattice;
pub mod proofs;
pub mod composition;
pub mod causal_consistency;

pub use classes::{
    AlgebraicClass, CommutativeInvariant, IdempotentInvariant, GroupInvariant,
    LatticeInvariant, BoundedInvariant, MonotonicInvariant,
};
pub use lattice::{JoinSemilattice, MeetSemilattice, BoundedLattice, LatticeMerge};
pub use composition::{ComposedInvariant, ParallelComposition};
pub use proofs::{ConvergenceWitness, CommutativityProof, CoordinationClass};
pub use causal_consistency::{
    CausallyConsistentInvariant, AccProofWitness, CausalFact, 
    CausalOrderValidator, verify_acc_theorem,
};
