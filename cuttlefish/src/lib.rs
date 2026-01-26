//! # Cuttlefish
//!
//! An invariant-centric, causally ordered state kernel optimized for
//! sub-100ns Δ_I application latency.
//!
//! ## Core Philosophy
//!
//! Correctness is a property of mathematics, not execution order.
//! Performance is bounded by constant-time delta application rather
//! than coordination latency.
//!
//! ## Primary API Surface
//!
//! - [`Kernel`] - Single-invariant fact admission with re-anchoring support
//! - [`EscalatingKernel`] - Auto-escalating kernel with BFVC saturation handling
//! - [`Fact`] - Immutable, content-addressed state transition record
//! - [`View`] - Point-in-time read: V = (Frontier, State)
//! - [`Checkpoint`] - Summary fact for horizon truncation and re-anchoring
//!
//! ## Invariant Classes
//!
//! - **Class A (Conservation)**: [`TotalSupplyInvariant`] - Commutative group operations
//! - **Class B (Uniqueness)**: [`UniquenessInvariant`] - Idempotent set membership
//!
//! ## Design Constraints
//!
//! - **Zero allocation** in hot path (no Box, Vec, HashMap)
//! - **POD-only** with `#[repr(C, align(64))]` for cache-line alignment
//! - **i128 fixed-point** arithmetic (no floating-point in Δ_I)
//! - **Branchless** operations where possible
//!
//! ## Example
//!
//! ```rust
//! use cuttlefish::prelude::*;
//! use cuttlefish::invariants::total_supply::{ConservationState, TotalSupplyInvariant};
//! use zerocopy::IntoBytes;
//!
//! // Initialize state with balance=0, min=i128::MIN, max=i128::MAX
//! let state = ConservationState::new(0, i128::MIN, i128::MAX);
//! let mut cell = StateCell::new();
//! cell.as_slice_mut().copy_from_slice(state.as_bytes());
//!
//! // Create kernel with conservation invariant
//! let mut kernel = Kernel::with_state(TotalSupplyInvariant::new(), cell);
//!
//! // Admit a fact that adds 100 to the balance
//! let fact_id = [0u8; 32];
//! let payload = 100i128.to_le_bytes();
//! kernel.admit_raw(&fact_id, &[], &payload).unwrap();
//! ```

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
