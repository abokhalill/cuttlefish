//! Causal consistency at 40ns. Algebraic invariants without coordination.
//!
//! Commutative ops don't need consensus. Non-commutative ops fail fast at admission.
//! pretty much the entire the entire trick.

#![cfg_attr(not(feature = "std"), no_std)]
#![deny(unsafe_op_in_unsafe_fn)]

pub mod algebra;
pub mod core;
pub mod invariants;

#[cfg(feature = "networking")]
pub mod network;

/// Prelude for convenient imports of primary API types.
pub mod prelude {
    pub use crate::core::kernel::{CausalMode, DualKernel, EscalatingKernel, MultiKernel};
    pub use crate::core::topology::{resolve_conflict, wins_conflict, PreciseClock};
    pub use crate::core::{
        AdmitError, AlgebraicClass, CausalClock, Checkpoint, CheckpointError, Fact, FactHeader,
        FactId, Frontier, FrontierState, Horizon, Invariant, InvariantError, Kernel, PruningPolicy,
        ReAnchorError, StateCell, View,
    };
}

// Re-export primary types at crate root for convenience.
pub use core::kernel::{CausalMode, DualKernel, EscalatingKernel, MultiKernel};
pub use core::topology::{resolve_conflict, wins_conflict, PreciseClock};
pub use core::{
    AdmitError, AlgebraicClass, CausalClock, Checkpoint, CheckpointError, Fact, FactHeader, FactId,
    Frontier, FrontierState, Horizon, Invariant, InvariantError, Kernel, PruningPolicy,
    ReAnchorError, StateCell, View,
};
