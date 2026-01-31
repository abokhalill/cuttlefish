//! The guts. Kernels, clocks, state cells, persistence.

pub mod checkpoint;
pub mod fact;
pub mod frontier;
pub mod horizon;
pub mod invariant;
pub mod kernel;
pub mod state;
pub mod topology;
pub mod view;

#[cfg(all(feature = "persistence", target_os = "linux"))]
pub mod persistence;

pub use checkpoint::{Attestation, Checkpoint, CheckpointError, ProofEnvelope};
pub use fact::{Fact, FactHeader};
pub use frontier::{Frontier, FrontierState, MAX_FRONTIER_WIDTH};
pub use horizon::{Horizon, PruningPolicy};
pub use invariant::{Invariant, InvariantError};
pub use kernel::{
    AdmitError, DurableStatus, Kernel, ReAnchorError, TenantDomain, TenantId, TenantKernel,
    MAX_TENANTS,
};

#[cfg(all(feature = "persistence", target_os = "linux"))]
pub use kernel::{DurableHandle, TwoLaneDurableKernel};
pub use state::StateCell;
pub use topology::{CausalClock, FactId};
pub use view::View;
