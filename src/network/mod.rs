//! Network layer for causal state synchronization between nodes.
//!
//! Provides gossip-based clock exchange and fact replication over TCP/UDP.
//! Feature-gated: `networking`.
//!
//! Two-Lane Architecture Support:
//! - Zero-copy broadcast using WALArena slot references
//! - Fixed-format frames to eliminate heap allocation
//! - SendBuffer for batched, aligned network writes

mod protocol;
mod worker;

pub use protocol::{
    MessageType, NetworkMessage, WireHeader, WIRE_MAGIC, WIRE_VERSION,
};
pub use worker::{
    BroadcastEntry, BroadcastFrame, NetworkConfig, NetworkWorker, PeerAddr,
    SendBuffer,
};

#[cfg(all(feature = "persistence", target_os = "linux"))]
pub use worker::{
    ZeroCopyBroadcastEntry, ZeroCopyCommand,
    ZeroCopyNetworkWorker, ZeroCopyNetworkHandle,
};
