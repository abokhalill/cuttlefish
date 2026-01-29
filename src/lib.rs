#![cfg_attr(not(feature = "std"), no_std)]
#![deny(unsafe_op_in_unsafe_fn)]

pub mod core;
pub mod invariants;
pub mod algebra;

#[cfg(feature = "networking")]
pub mod network;

/// Prelude for convenient imports of primary API types.
pub mod prelude {
    pub use crate::core::{
        AdmitError, CausalClock, Checkpoint, CheckpointError, Fact, FactHeader, FactId,
        Frontier, FrontierState, Horizon, Invariant, InvariantError, Kernel, PruningPolicy,
        ReAnchorError, StateCell, View,
    };
    pub use crate::core::kernel::{CausalMode, DualKernel, EscalatingKernel, MultiKernel};
    pub use crate::core::topology::{PreciseClock, resolve_conflict, wins_conflict};
}

// Re-export primary types at crate root for convenience.
pub use core::{
    AdmitError, CausalClock, Checkpoint, CheckpointError, Fact, FactHeader, FactId,
    Frontier, FrontierState, Horizon, Invariant, InvariantError, Kernel, PruningPolicy,
    ReAnchorError, StateCell, View,
};
pub use core::kernel::{CausalMode, DualKernel, EscalatingKernel, MultiKernel};
pub use core::topology::{PreciseClock, resolve_conflict, wins_conflict};
