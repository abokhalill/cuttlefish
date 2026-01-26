//! Async persistence layer using io_uring (Linux only).
//!
//! Provides lock-free SPSC buffer for fact queueing and io_uring-based
//! async writes with CRC32C checksums. Feature-gated: `persistence`.
//!
//! Two-Lane Architecture:
//! - WALArena: 4K-aligned staging arena for zero-copy payload ownership.
//! - SPSC: Lock-free queue passing SlotIndex references to io_uring worker.

pub mod arena;
pub mod recovery;
mod ring;
mod worker;

pub use arena::{
    ArenaError, ArenaSlot, SlotHeader, SlotIndex, SlotState, WALArena,
    ARENA_SIZE, INVALID_SLOT, PAYLOAD_CAPACITY, SLOTS_PER_ARENA, SLOT_SIZE,
    REFCOUNT_DUAL, REFCOUNT_FREE, REFCOUNT_NETWORK_ONLY, REFCOUNT_PERSIST_ONLY,
};
pub use recovery::{BootstrapEngine, RecoveryError, RecoveryResult, WalEntryHeader, WalRecovery};
pub use ring::{PersistenceEntry, SPSCBuffer, SPSCConsumer, SPSCProducer};
pub use worker::{
    ArenaPersistenceWorker, ArenaSlotEntry, PersistenceFrontier, PersistenceWorker, SubmissionBuffer,
};
