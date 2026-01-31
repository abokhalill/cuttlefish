//! Built-in invariants. Use these or roll your own.
//!
//! - [`TotalSupplyInvariant`]: Conservation with bounds. Think token balances.
//! - [`UniquenessInvariant`]: Reject duplicates. 512-bit bitset.
//! - [`monotonic`]: Max, GCounter, LWW, BoundedGCounter. Lattice-based, always converge.
//! - [`graph`]: Grow-only graph with degree constraints.

pub mod graph;
pub mod monotonic;
pub mod total_supply;
pub mod uniqueness;

pub use total_supply::TotalSupplyInvariant;
pub use uniqueness::UniquenessInvariant;
