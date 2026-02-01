//! Fact admission. Causality check → invariant apply → frontier advance.
//!
//! Pick your kernel based on your needs:
//! - [`Kernel`]: Bloom filter only. Fast, probabilistic.
//! - [`TwoLaneKernel`]: Bloom + Robin Hood exact index. Production-grade.
//! - [`EscalatingKernel`]: Auto-switches at 40% Bloom saturation.
//! - [`TenantKernel`]: Isolated causal domains per tenant. No cross-contamination.

use super::checkpoint::{Checkpoint, CheckpointError};
use super::fact::Fact;
use super::frontier::{build_deps_clock, check_dominance, FrontierState};
use super::invariant::{Invariant, InvariantError};
use super::state::{StateCell, STATE_CELL_SIZE};
use super::topology::{CausalClock, FactId, PreciseClock, ESCALATION_THRESHOLD};
use super::view::View;

/// Admission failed. Check the variant for why.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum AdmitError {
    /// Dependency not in causal history.
    CausalityViolation = 1,
    /// Invariant rejected the payload.
    InvariantViolation = 2,
    /// Couldn't parse the fact.
    MalformedFact = 3,
    /// Bloom saturated, need precise deps.
    PreciseDepsRequired = 4,
    #[cfg(all(feature = "persistence", target_os = "linux"))]
    /// WAL buffer full. Back off.
    BufferFull = 5,
    /// Dependency too old, evicted from index.
    CausalHorizonExceeded = 6,
    /// No free slots in WAL arena.
    ArenaFull = 7,
    /// Payload exceeds slot size.
    PayloadTooLarge = 8,
}

/// When do you want your ACK?
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum AckMode {
    /// In-memory only. Fast, volatile.
    Volatile = 0,
    /// Queued to WAL. Might lose on crash.
    WALSubmitted = 1,
    /// fsync'd. Survives power loss.
    Durable = 2,
}

/// Poll this to check if your fact hit disk.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum DurableStatus {
    /// Still in flight.
    Pending = 0,
    /// On disk. You're safe.
    Durable = 1,
}

/// Bloom (fast, probabilistic) or Precise (exact, slower).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum CausalMode {
    /// 512-bit Bloom filter. O(1) but false positives possible.
    Fast = 0,
    /// Robin Hood hash table. Exact but bounded horizon.
    Precise = 1,
}

impl From<InvariantError> for AdmitError {
    #[inline(always)]
    fn from(_: InvariantError) -> Self {
        AdmitError::InvariantViolation
    }
}

/// The basic kernel. Bloom filter causality, single invariant.
///
/// 13ns admission with no deps. 40ns with deps. Good enough for most cases.
pub struct Kernel<I: Invariant> {
    pub frontier: FrontierState,
    pub state: StateCell,
    pub invariant: I,
}

impl<I: Invariant> Kernel<I> {
    #[inline(always)]
    pub const fn new(invariant: I) -> Self {
        Self {
            frontier: FrontierState::new(),
            state: StateCell::new(),
            invariant,
        }
    }

    #[inline(always)]
    pub fn with_state(invariant: I, state: StateCell) -> Self {
        Self {
            frontier: FrontierState::new(),
            state,
            invariant,
        }
    }

    #[inline(always)]
    pub fn admit(&mut self, fact: &Fact<'_>) -> Result<(), AdmitError> {
        let deps = fact.deps();

        if !deps.is_empty() {
            let deps_clock = build_deps_clock(deps);
            if !check_dominance(&self.frontier.clock, &deps_clock) {
                return Err(AdmitError::CausalityViolation);
            }
        }

        self.invariant
            .apply(fact.payload(), self.state.as_bytes_mut())
            .map_err(|_| AdmitError::InvariantViolation)?;

        self.frontier.advance(*fact.id());

        Ok(())
    }

    #[inline(always)]
    pub fn admit_raw(
        &mut self,
        fact_id: &FactId,
        deps: &[FactId],
        payload: &[u8],
    ) -> Result<(), AdmitError> {
        if !deps.is_empty() {
            let deps_clock = build_deps_clock(deps);
            if !check_dominance(&self.frontier.clock, &deps_clock) {
                return Err(AdmitError::CausalityViolation);
            }
        }

        self.invariant
            .apply(payload, self.state.as_bytes_mut())
            .map_err(|_| AdmitError::InvariantViolation)?;

        self.frontier.advance(*fact_id);

        Ok(())
    }

    #[inline(always)]
    pub fn admit_unchecked_deps(
        &mut self,
        fact_id: &FactId,
        payload: &[u8],
    ) -> Result<(), AdmitError> {
        self.invariant
            .apply(payload, self.state.as_bytes_mut())
            .map_err(|_| AdmitError::InvariantViolation)?;

        self.frontier.advance(*fact_id);

        Ok(())
    }

    #[inline(always)]
    pub fn clock(&self) -> &CausalClock {
        &self.frontier.clock
    }

    #[inline(always)]
    pub fn state(&self) -> &StateCell {
        &self.state
    }

    #[inline(always)]
    pub fn saturation(&self) -> f32 {
        self.frontier.clock.saturation()
    }

    #[inline(always)]
    pub fn query(&self, requirement: &CausalClock) -> Option<View> {
        if self.frontier.clock.dominates(requirement) {
            Some(View {
                frontier: self.frontier.clone(),
                state: self.state,
            })
        } else {
            None
        }
    }

    #[inline]
    pub fn re_anchor(
        &mut self,
        checkpoint: &Checkpoint,
        new_facts: &[(&FactId, &[u8])],
    ) -> Result<(), ReAnchorError> {
        checkpoint
            .verify()
            .map_err(ReAnchorError::CheckpointInvalid)?;

        let computed_hash = Checkpoint::compute_state_hash(&checkpoint.state);
        if computed_hash != checkpoint.state_hash {
            return Err(ReAnchorError::CheckpointInvalid(
                CheckpointError::StateHashMismatch,
            ));
        }

        self.state
            .as_bytes_mut()
            .copy_from_slice(checkpoint.state.as_bytes());

        self.frontier.frontier.clear();
        for fact_id in checkpoint.frontier.iter() {
            self.frontier.frontier.push(*fact_id);
        }
        self.frontier.clock = checkpoint.clock;

        for (fact_id, payload) in new_facts {
            self.admit_unchecked_deps(fact_id, payload)
                .map_err(ReAnchorError::ReplayFailed)?;
        }

        Ok(())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReAnchorError {
    CheckpointInvalid(CheckpointError),
    ReplayFailed(AdmitError),
}

use super::topology::ExactCausalIndex;

/// Two-tier causality: BFVC prefilter + ExactIndex ground truth.
pub struct TwoLaneKernel<I: Invariant> {
    pub frontier: FrontierState,
    pub state: StateCell,
    pub invariant: I,
    pub exact_index: ExactCausalIndex,
}

impl<I: Invariant> TwoLaneKernel<I> {
    pub fn new(invariant: I) -> Self {
        Self {
            frontier: FrontierState::new(),
            state: StateCell::new(),
            invariant,
            exact_index: ExactCausalIndex::new(),
        }
    }

    pub fn with_state(invariant: I, state: StateCell) -> Self {
        Self {
            frontier: FrontierState::new(),
            state,
            invariant,
            exact_index: ExactCausalIndex::new(),
        }
    }

    #[inline]
    pub fn admit(
        &mut self,
        fact_id: &FactId,
        deps: &[FactId],
        payload: &[u8],
    ) -> Result<(), AdmitError> {
        if !deps.is_empty() {
            let deps_clock = build_deps_clock(deps);
            if !check_dominance(&self.frontier.clock, &deps_clock) {
                return Err(AdmitError::CausalityViolation);
            }

            self.exact_index
                .contains_all_simd(deps)
                .map_err(|_| AdmitError::CausalHorizonExceeded)?;
        }

        self.invariant
            .apply(payload, self.state.as_bytes_mut())
            .map_err(|_| AdmitError::InvariantViolation)?;

        self.frontier.advance(*fact_id);
        self.exact_index.observe(fact_id);

        Ok(())
    }

    #[inline]
    pub fn admit_unchecked(&mut self, fact_id: &FactId, payload: &[u8]) -> Result<(), AdmitError> {
        self.invariant
            .apply(payload, self.state.as_bytes_mut())
            .map_err(|_| AdmitError::InvariantViolation)?;

        self.frontier.advance(*fact_id);
        self.exact_index.observe(fact_id);

        Ok(())
    }

    #[inline(always)]
    pub fn clock(&self) -> &CausalClock {
        &self.frontier.clock
    }

    #[inline(always)]
    pub fn state(&self) -> &StateCell {
        &self.state
    }

    #[inline(always)]
    pub fn exact_index(&self) -> &ExactCausalIndex {
        &self.exact_index
    }

    /// Query with causal requirement.
    #[inline]
    pub fn query(&self, requirement: &CausalClock) -> Option<View> {
        if self.frontier.clock.dominates(requirement) {
            Some(View {
                frontier: self.frontier.clone(),
                state: self.state,
            })
        } else {
            None
        }
    }
}

#[cfg(all(feature = "persistence", target_os = "linux"))]
pub use durable::DurableKernel;

#[cfg(all(feature = "persistence", target_os = "linux"))]
pub use two_lane_durable::{DurableHandle, TwoLaneDurableKernel};

#[cfg(all(feature = "persistence", target_os = "linux"))]
mod two_lane_durable {
    use super::*;
    use crate::core::persistence::{
        ArenaError, PersistenceEntry, PersistenceFrontier, SPSCProducer, SlotIndex, WALArena,
    };

    /// Handle for async durability checking. Replaces spin-loop blocking.
    #[derive(Clone, Copy)]
    pub struct DurableHandle<'a> {
        fact_id: FactId,
        slot_idx: SlotIndex,
        frontier: &'a PersistenceFrontier,
    }

    impl<'a> DurableHandle<'a> {
        #[inline(always)]
        pub fn poll(&self) -> DurableStatus {
            if self.frontier.clock().might_contain(&self.fact_id) {
                DurableStatus::Durable
            } else {
                DurableStatus::Pending
            }
        }

        #[inline(always)]
        pub fn is_durable(&self) -> bool {
            self.poll() == DurableStatus::Durable
        }

        #[inline]
        pub fn spin_wait(&self) {
            self.spin_wait_with_backoff(16)
        }

        #[inline]
        pub fn spin_wait_with_backoff(&self, max_spins: u32) {
            let mut spins = 1u32;
            while !self.is_durable() {
                for _ in 0..spins {
                    core::hint::spin_loop();
                }
                spins = spins.saturating_mul(2).min(max_spins);
            }
        }

        #[inline(always)]
        pub fn fact_id(&self) -> &FactId {
            &self.fact_id
        }

        #[inline(always)]
        pub fn slot_idx(&self) -> SlotIndex {
            self.slot_idx
        }
    }

    pub struct TwoLaneDurableKernel<'a, I: Invariant, const N: usize = 4096> {
        pub frontier: FrontierState,
        pub state: StateCell,
        pub invariant: I,
        pub exact_index: ExactCausalIndex,
        arena: &'a WALArena,
        producer: SPSCProducer<'a, N>,
        persistence_frontier: &'a PersistenceFrontier,
    }

    impl<'a, I: Invariant, const N: usize> TwoLaneDurableKernel<'a, I, N> {
        pub fn new(
            invariant: I,
            arena: &'a WALArena,
            producer: SPSCProducer<'a, N>,
            persistence_frontier: &'a PersistenceFrontier,
        ) -> Self {
            Self {
                frontier: FrontierState::new(),
                state: StateCell::new(),
                invariant,
                exact_index: ExactCausalIndex::new(),
                arena,
                producer,
                persistence_frontier,
            }
        }

        pub fn with_state(
            invariant: I,
            state: StateCell,
            arena: &'a WALArena,
            producer: SPSCProducer<'a, N>,
            persistence_frontier: &'a PersistenceFrontier,
        ) -> Self {
            Self {
                frontier: FrontierState::new(),
                state,
                invariant,
                exact_index: ExactCausalIndex::new(),
                arena,
                producer,
                persistence_frontier,
            }
        }

        #[inline]
        pub fn admit(
            &mut self,
            fact_id: &FactId,
            deps: &[FactId],
            payload: &[u8],
            ack_mode: AckMode,
        ) -> Result<SlotIndex, AdmitError> {
            let slot_idx = self.arena.acquire_slot().map_err(|e| match e {
                ArenaError::Full => AdmitError::ArenaFull,
                _ => AdmitError::MalformedFact,
            })?;

            if let Err(e) = self.arena.write_slot(slot_idx, fact_id, payload) {
                let _ = self.arena.release_slot(slot_idx);
                return Err(match e {
                    ArenaError::PayloadTooLarge => AdmitError::PayloadTooLarge,
                    _ => AdmitError::MalformedFact,
                });
            }

            if !deps.is_empty() {
                let deps_clock = build_deps_clock(deps);
                if !check_dominance(&self.frontier.clock, &deps_clock) {
                    let _ = self.arena.release_slot(slot_idx);
                    return Err(AdmitError::CausalityViolation);
                }

                if self.exact_index.contains_all_simd(deps).is_err() {
                    let _ = self.arena.release_slot(slot_idx);
                    return Err(AdmitError::CausalHorizonExceeded);
                }
            }

            if self
                .invariant
                .apply(payload, self.state.as_bytes_mut())
                .is_err()
            {
                let _ = self.arena.release_slot(slot_idx);
                return Err(AdmitError::InvariantViolation);
            }

            self.frontier.advance(*fact_id);
            self.exact_index.observe(fact_id);

            match ack_mode {
                AckMode::Volatile => {
                    let _ = self.arena.release_slot(slot_idx);
                }
                AckMode::WALSubmitted | AckMode::Durable => {
                    let header = self.arena.get_header(slot_idx).unwrap();
                    let entry = PersistenceEntry {
                        fact_id: *fact_id,
                        data_ptr: self.arena.slot_ptr(slot_idx) as usize,
                        data_len: header.payload_len,
                        sequence: header.sequence,
                    };

                    if self.producer.try_push(entry).is_err() {
                        let _ = self.arena.release_slot(slot_idx);
                        return Err(AdmitError::BufferFull);
                    }

                    if ack_mode == AckMode::Durable {
                        while !self.persistence_frontier.clock().might_contain(fact_id) {
                            core::hint::spin_loop();
                        }
                    }
                }
            }

            Ok(slot_idx)
        }

        /// Non-blocking durable admission. Returns handle for async durability polling.
        #[inline]
        pub fn admit_async(
            &mut self,
            fact_id: &FactId,
            deps: &[FactId],
            payload: &[u8],
        ) -> Result<DurableHandle<'a>, AdmitError> {
            let slot_idx = self.arena.acquire_slot().map_err(|e| match e {
                ArenaError::Full => AdmitError::ArenaFull,
                _ => AdmitError::MalformedFact,
            })?;

            if let Err(e) = self.arena.write_slot(slot_idx, fact_id, payload) {
                let _ = self.arena.release_slot(slot_idx);
                return Err(match e {
                    ArenaError::PayloadTooLarge => AdmitError::PayloadTooLarge,
                    _ => AdmitError::MalformedFact,
                });
            }

            if !deps.is_empty() {
                let deps_clock = build_deps_clock(deps);
                if !check_dominance(&self.frontier.clock, &deps_clock) {
                    let _ = self.arena.release_slot(slot_idx);
                    return Err(AdmitError::CausalityViolation);
                }
                if self.exact_index.contains_all_simd(deps).is_err() {
                    let _ = self.arena.release_slot(slot_idx);
                    return Err(AdmitError::CausalHorizonExceeded);
                }
            }

            if self
                .invariant
                .apply(payload, self.state.as_bytes_mut())
                .is_err()
            {
                let _ = self.arena.release_slot(slot_idx);
                return Err(AdmitError::InvariantViolation);
            }

            self.frontier.advance(*fact_id);
            self.exact_index.observe(fact_id);

            let header = self.arena.get_header(slot_idx).unwrap();
            let entry = PersistenceEntry {
                fact_id: *fact_id,
                data_ptr: self.arena.slot_ptr(slot_idx) as usize,
                data_len: header.payload_len,
                sequence: header.sequence,
            };

            if self.producer.try_push(entry).is_err() {
                let _ = self.arena.release_slot(slot_idx);
                return Err(AdmitError::BufferFull);
            }

            Ok(DurableHandle {
                fact_id: *fact_id,
                slot_idx,
                frontier: self.persistence_frontier,
            })
        }

        #[inline]
        pub fn admit_volatile(
            &mut self,
            fact_id: &FactId,
            deps: &[FactId],
            payload: &[u8],
        ) -> Result<(), AdmitError> {
            if !deps.is_empty() {
                let deps_clock = build_deps_clock(deps);
                if !check_dominance(&self.frontier.clock, &deps_clock) {
                    return Err(AdmitError::CausalityViolation);
                }
                self.exact_index
                    .contains_all_simd(deps)
                    .map_err(|_| AdmitError::CausalHorizonExceeded)?;
            }

            self.invariant
                .apply(payload, self.state.as_bytes_mut())
                .map_err(|_| AdmitError::InvariantViolation)?;

            self.frontier.advance(*fact_id);
            self.exact_index.observe(fact_id);

            Ok(())
        }

        #[inline(always)]
        pub fn clock(&self) -> &CausalClock {
            &self.frontier.clock
        }

        #[inline(always)]
        pub fn state(&self) -> &StateCell {
            &self.state
        }

        #[inline(always)]
        pub fn persistence_frontier(&self) -> &PersistenceFrontier {
            self.persistence_frontier
        }

        #[inline(always)]
        pub fn arena(&self) -> &WALArena {
            self.arena
        }

        /// Query with durability requirement.
        #[inline]
        pub fn query_durable(&self, requirement: &CausalClock) -> Option<View> {
            if self.persistence_frontier.dominates(requirement) {
                Some(View {
                    frontier: self.frontier.clone(),
                    state: self.state,
                })
            } else {
                None
            }
        }
    }
}

#[cfg(all(feature = "persistence", target_os = "linux"))]
mod durable {
    use super::*;
    use crate::core::persistence::{PersistenceEntry, PersistenceFrontier, SPSCProducer};
    use core::sync::atomic::{AtomicU64, Ordering};

    /// Default SPSC buffer capacity (power of two).
    pub const PERSISTENCE_BUFFER_SIZE: usize = 4096;

    /// Kernel with integrated persistence via SPSC buffer.
    /// Producer side only—worker thread consumes and writes to disk.
    pub struct DurableKernel<'a, I: Invariant, const N: usize = PERSISTENCE_BUFFER_SIZE> {
        pub frontier: FrontierState,
        pub state: StateCell,
        pub invariant: I,
        producer: SPSCProducer<'a, N>,
        sequence: AtomicU64,
        persistence_frontier: &'a PersistenceFrontier,
    }

    impl<'a, I: Invariant, const N: usize> DurableKernel<'a, I, N> {
        pub fn new(
            invariant: I,
            producer: SPSCProducer<'a, N>,
            persistence_frontier: &'a PersistenceFrontier,
        ) -> Self {
            Self {
                frontier: FrontierState::new(),
                state: StateCell::new(),
                invariant,
                producer,
                sequence: AtomicU64::new(0),
                persistence_frontier,
            }
        }

        pub fn with_state(
            invariant: I,
            state: StateCell,
            producer: SPSCProducer<'a, N>,
            persistence_frontier: &'a PersistenceFrontier,
        ) -> Self {
            Self {
                frontier: FrontierState::new(),
                state,
                invariant,
                producer,
                sequence: AtomicU64::new(0),
                persistence_frontier,
            }
        }

        #[inline]
        pub fn admit_durable(
            &mut self,
            fact_id: &FactId,
            deps: &[FactId],
            payload: &[u8],
        ) -> Result<(), AdmitError> {
            if !deps.is_empty() {
                let deps_clock = build_deps_clock(deps);
                if !check_dominance(&self.frontier.clock, &deps_clock) {
                    return Err(AdmitError::CausalityViolation);
                }
            }

            self.invariant
                .apply(payload, self.state.as_bytes_mut())
                .map_err(|_| AdmitError::InvariantViolation)?;

            let seq = self.sequence.fetch_add(1, Ordering::Relaxed);
            let entry = PersistenceEntry {
                fact_id: *fact_id,
                data_ptr: payload.as_ptr() as usize,
                data_len: payload.len() as u32,
                sequence: seq,
            };

            self.producer
                .try_push(entry)
                .map_err(|_| AdmitError::BufferFull)?;
            self.frontier.advance(*fact_id);

            Ok(())
        }

        #[inline(always)]
        pub fn clock(&self) -> &CausalClock {
            &self.frontier.clock
        }

        #[inline(always)]
        pub fn state(&self) -> &StateCell {
            &self.state
        }

        #[inline(always)]
        pub fn persistence_frontier(&self) -> &PersistenceFrontier {
            self.persistence_frontier
        }

        #[inline]
        pub fn query_durable(&self, requirement: &CausalClock) -> Option<View> {
            if self.persistence_frontier.dominates(requirement) {
                Some(View {
                    frontier: self.frontier.clone(),
                    state: self.state,
                })
            } else {
                None
            }
        }

        #[inline]
        pub fn query(&self, requirement: &CausalClock) -> Option<View> {
            if self.frontier.clock.dominates(requirement) {
                Some(View {
                    frontier: self.frontier.clone(),
                    state: self.state,
                })
            } else {
                None
            }
        }

        #[inline(always)]
        pub fn buffer_len(&self) -> usize {
            self.producer.len()
        }

        #[inline(always)]
        pub fn is_buffer_full(&self) -> bool {
            self.producer.is_full()
        }
    }
}

#[cfg(feature = "networking")]
pub use networking::{
    BroadcastBuffer, BroadcastConsumer, BroadcastProducer, NetworkingKernel, BROADCAST_BUFFER_SIZE,
};

#[cfg(feature = "networking")]
mod networking {
    use super::*;
    use core::cell::UnsafeCell;
    use core::sync::atomic::{AtomicUsize, Ordering};

    #[repr(align(64))]
    struct CachePadded<T>(T);

    #[derive(Clone, Copy)]
    #[repr(C)]
    pub struct BroadcastEntry {
        pub fact_id: FactId,
    }

    impl BroadcastEntry {
        pub const fn empty() -> Self {
            Self { fact_id: [0u8; 32] }
        }
    }

    pub struct BroadcastBuffer<const N: usize> {
        buffer: UnsafeCell<[BroadcastEntry; N]>,
        head: CachePadded<AtomicUsize>,
        tail: CachePadded<AtomicUsize>,
    }

    unsafe impl<const N: usize> Send for BroadcastBuffer<N> {}
    unsafe impl<const N: usize> Sync for BroadcastBuffer<N> {}

    impl<const N: usize> BroadcastBuffer<N> {
        const MASK: usize = N - 1;

        pub fn new() -> Self {
            Self {
                buffer: UnsafeCell::new([BroadcastEntry::empty(); N]),
                head: CachePadded(AtomicUsize::new(0)),
                tail: CachePadded(AtomicUsize::new(0)),
            }
        }

        pub fn split(&self) -> (BroadcastProducer<'_, N>, BroadcastConsumer<'_, N>) {
            (
                BroadcastProducer { ring: self },
                BroadcastConsumer { ring: self },
            )
        }
    }

    impl<const N: usize> Default for BroadcastBuffer<N> {
        fn default() -> Self {
            Self::new()
        }
    }

    pub struct BroadcastProducer<'a, const N: usize> {
        ring: &'a BroadcastBuffer<N>,
    }

    impl<'a, const N: usize> BroadcastProducer<'a, N> {
        #[inline(always)]
        pub fn try_push(&self, fact_id: FactId) -> Result<(), FactId> {
            let head = self.ring.head.0.load(Ordering::Relaxed);
            let tail = self.ring.tail.0.load(Ordering::Acquire);

            if head.wrapping_sub(tail) >= N {
                return Err(fact_id);
            }

            unsafe {
                let slot = &mut (*self.ring.buffer.get())[head & BroadcastBuffer::<N>::MASK];
                slot.fact_id = fact_id;
            }

            self.ring
                .head
                .0
                .store(head.wrapping_add(1), Ordering::Release);
            Ok(())
        }

        #[inline(always)]
        pub fn is_full(&self) -> bool {
            let head = self.ring.head.0.load(Ordering::Relaxed);
            let tail = self.ring.tail.0.load(Ordering::Acquire);
            head.wrapping_sub(tail) >= N
        }
    }

    pub struct BroadcastConsumer<'a, const N: usize> {
        ring: &'a BroadcastBuffer<N>,
    }

    impl<'a, const N: usize> BroadcastConsumer<'a, N> {
        #[inline(always)]
        pub fn try_pop(&self) -> Option<FactId> {
            let tail = self.ring.tail.0.load(Ordering::Relaxed);
            let head = self.ring.head.0.load(Ordering::Acquire);

            if tail == head {
                return None;
            }

            let fact_id =
                unsafe { (*self.ring.buffer.get())[tail & BroadcastBuffer::<N>::MASK].fact_id };

            self.ring
                .tail
                .0
                .store(tail.wrapping_add(1), Ordering::Release);
            Some(fact_id)
        }
    }

    pub const BROADCAST_BUFFER_SIZE: usize = 4096;

    pub struct NetworkingKernel<'a, I: Invariant, const N: usize = BROADCAST_BUFFER_SIZE> {
        pub frontier: FrontierState,
        pub state: StateCell,
        pub invariant: I,
        broadcast: BroadcastProducer<'a, N>,
    }

    impl<'a, I: Invariant, const N: usize> NetworkingKernel<'a, I, N> {
        pub fn new(invariant: I, broadcast: BroadcastProducer<'a, N>) -> Self {
            Self {
                frontier: FrontierState::new(),
                state: StateCell::new(),
                invariant,
                broadcast,
            }
        }

        pub fn with_state(
            invariant: I,
            state: StateCell,
            broadcast: BroadcastProducer<'a, N>,
        ) -> Self {
            Self {
                frontier: FrontierState::new(),
                state,
                invariant,
                broadcast,
            }
        }

        #[inline]
        pub fn admit_broadcast(
            &mut self,
            fact_id: &FactId,
            deps: &[FactId],
            payload: &[u8],
        ) -> Result<(), AdmitError> {
            if !deps.is_empty() {
                let deps_clock = build_deps_clock(deps);
                if !check_dominance(&self.frontier.clock, &deps_clock) {
                    return Err(AdmitError::CausalityViolation);
                }
            }

            self.invariant
                .apply(payload, self.state.as_bytes_mut())
                .map_err(|_| AdmitError::InvariantViolation)?;

            let _ = self.broadcast.try_push(*fact_id);

            self.frontier.advance(*fact_id);
            Ok(())
        }

        #[inline(always)]
        pub fn clock(&self) -> &CausalClock {
            &self.frontier.clock
        }

        #[inline(always)]
        pub fn state(&self) -> &StateCell {
            &self.state
        }

        #[inline(always)]
        pub fn is_broadcast_full(&self) -> bool {
            self.broadcast.is_full()
        }
    }
}

/// Auto-escalating kernel: BFVC → PreciseClock when saturation ≥ 40%.
pub struct EscalatingKernel<I: Invariant> {
    pub frontier: FrontierState,
    pub state: StateCell,
    pub invariant: I,
    pub precise: PreciseClock,
    pub mode: CausalMode,
}

impl<I: Invariant> EscalatingKernel<I> {
    #[inline(always)]
    pub fn new(invariant: I) -> Self {
        Self {
            frontier: FrontierState::new(),
            state: StateCell::new(),
            invariant,
            precise: PreciseClock::new(),
            mode: CausalMode::Fast,
        }
    }

    #[inline(always)]
    pub fn with_state(invariant: I, state: StateCell) -> Self {
        Self {
            frontier: FrontierState::new(),
            state,
            invariant,
            precise: PreciseClock::new(),
            mode: CausalMode::Fast,
        }
    }

    #[inline(always)]
    fn check_escalation(&mut self) {
        if self.mode == CausalMode::Fast && self.frontier.clock.saturation() >= ESCALATION_THRESHOLD
        {
            self.mode = CausalMode::Precise;
        }
    }

    #[inline]
    pub fn admit(
        &mut self,
        fact_id: &FactId,
        deps: &[FactId],
        payload: &[u8],
    ) -> Result<(), AdmitError> {
        self.check_escalation();

        match self.mode {
            CausalMode::Fast => self.admit_fast(fact_id, deps, payload),
            CausalMode::Precise => self.admit_precise(fact_id, deps, payload),
        }
    }

    #[inline(always)]
    fn admit_fast(
        &mut self,
        fact_id: &FactId,
        deps: &[FactId],
        payload: &[u8],
    ) -> Result<(), AdmitError> {
        if !deps.is_empty() {
            let deps_clock = build_deps_clock(deps);
            if !check_dominance(&self.frontier.clock, &deps_clock) {
                return Err(AdmitError::CausalityViolation);
            }
        }

        self.invariant
            .apply(payload, self.state.as_bytes_mut())
            .map_err(|_| AdmitError::InvariantViolation)?;

        self.frontier.advance(*fact_id);
        self.precise.observe(fact_id);

        Ok(())
    }

    #[inline]
    fn admit_precise(
        &mut self,
        fact_id: &FactId,
        deps: &[FactId],
        payload: &[u8],
    ) -> Result<(), AdmitError> {
        if !deps.is_empty() && !self.precise.contains_all(deps) {
            return Err(AdmitError::CausalityViolation);
        }

        self.invariant
            .apply(payload, self.state.as_bytes_mut())
            .map_err(|_| AdmitError::InvariantViolation)?;

        self.frontier.advance(*fact_id);
        self.precise.observe(fact_id);

        Ok(())
    }

    #[inline(always)]
    pub fn clock(&self) -> &CausalClock {
        &self.frontier.clock
    }

    #[inline(always)]
    pub fn state(&self) -> &StateCell {
        &self.state
    }

    #[inline(always)]
    pub fn saturation(&self) -> f32 {
        self.frontier.clock.saturation()
    }

    #[inline(always)]
    pub fn current_mode(&self) -> CausalMode {
        self.mode
    }

    #[inline(always)]
    pub fn escalate(&mut self) {
        self.mode = CausalMode::Precise;
    }

    #[inline(always)]
    pub fn reset_mode(&mut self) {
        self.mode = CausalMode::Fast;
        self.precise.clear();
    }
}

pub const MAX_INVARIANTS: usize = 8;
pub const MAX_TENANTS: usize = 16;

pub type TenantId = u16;

pub type InvariantFn = fn(payload: &[u8], state: &mut [u8]) -> Result<(), InvariantError>;

#[derive(Clone)]
pub struct MultiKernel {
    pub frontier: FrontierState,
    pub states: [StateCell; MAX_INVARIANTS],
    pub invariants: [Option<InvariantFn>; MAX_INVARIANTS],
    pub invariant_count: usize,
}

impl MultiKernel {
    #[inline(always)]
    pub fn new() -> Self {
        Self {
            frontier: FrontierState::new(),
            states: [StateCell::new(); MAX_INVARIANTS],
            invariants: [None; MAX_INVARIANTS],
            invariant_count: 0,
        }
    }

    #[inline(always)]
    pub fn register(
        &mut self,
        invariant_fn: InvariantFn,
        initial_state: StateCell,
    ) -> Option<usize> {
        if self.invariant_count >= MAX_INVARIANTS {
            return None;
        }
        let idx = self.invariant_count;
        self.states[idx] = initial_state;
        self.invariants[idx] = Some(invariant_fn);
        self.invariant_count += 1;
        Some(idx)
    }

    #[inline(always)]
    pub fn admit_multi(
        &mut self,
        fact_id: &FactId,
        deps: &[FactId],
        payloads: &[&[u8]],
    ) -> Result<(), AdmitError> {
        if payloads.len() != self.invariant_count {
            return Err(AdmitError::MalformedFact);
        }

        if !deps.is_empty() {
            let deps_clock = build_deps_clock(deps);
            if !check_dominance(&self.frontier.clock, &deps_clock) {
                return Err(AdmitError::CausalityViolation);
            }
        }

        let mut scratch: [[u8; STATE_CELL_SIZE]; MAX_INVARIANTS] =
            [[0u8; STATE_CELL_SIZE]; MAX_INVARIANTS];
        for (i, s) in scratch.iter_mut().enumerate().take(self.invariant_count) {
            s.copy_from_slice(self.states[i].as_bytes());
        }

        for (i, s) in scratch.iter_mut().enumerate().take(self.invariant_count) {
            if let Some(inv_fn) = self.invariants[i] {
                if inv_fn(payloads[i], s).is_err() {
                    return Err(AdmitError::InvariantViolation);
                }
            }
        }

        for (i, s) in scratch.iter().enumerate().take(self.invariant_count) {
            self.states[i].as_bytes_mut().copy_from_slice(s);
        }

        self.frontier.advance(*fact_id);
        Ok(())
    }

    #[inline(always)]
    pub fn query(&self, requirement: &CausalClock) -> bool {
        self.frontier.clock.dominates(requirement)
    }

    #[inline(always)]
    pub fn state(&self, index: usize) -> Option<&StateCell> {
        if index < self.invariant_count {
            Some(&self.states[index])
        } else {
            None
        }
    }

    #[inline(always)]
    pub fn clock(&self) -> &CausalClock {
        &self.frontier.clock
    }
}

impl Default for MultiKernel {
    fn default() -> Self {
        Self::new()
    }
}

#[repr(C, align(64))]
pub struct DualKernel<I1: Invariant + Copy, I2: Invariant + Copy> {
    pub frontier: FrontierState,
    pub state1: StateCell,
    pub state2: StateCell,
    pub inv1: I1,
    pub inv2: I2,
}

impl<I1: Invariant + Copy, I2: Invariant + Copy> DualKernel<I1, I2> {
    #[inline(always)]
    pub fn new(inv1: I1, state1: StateCell, inv2: I2, state2: StateCell) -> Self {
        Self {
            frontier: FrontierState::new(),
            state1,
            state2,
            inv1,
            inv2,
        }
    }

    #[inline(always)]
    pub fn admit(
        &mut self,
        fact_id: &FactId,
        deps: &[FactId],
        payload1: &[u8],
        payload2: &[u8],
    ) -> Result<(), AdmitError> {
        if !deps.is_empty() {
            let deps_clock = build_deps_clock(deps);
            if !check_dominance(&self.frontier.clock, &deps_clock) {
                return Err(AdmitError::CausalityViolation);
            }
        }

        let mut scratch1 = *self.state1.as_bytes();
        let mut scratch2 = *self.state2.as_bytes();

        self.inv1
            .apply(payload1, &mut scratch1)
            .map_err(|_| AdmitError::InvariantViolation)?;

        self.inv2
            .apply(payload2, &mut scratch2)
            .map_err(|_| AdmitError::InvariantViolation)?;

        self.state1.as_bytes_mut().copy_from_slice(&scratch1);
        self.state2.as_bytes_mut().copy_from_slice(&scratch2);

        self.frontier.advance(*fact_id);
        Ok(())
    }

    #[inline(always)]
    pub fn query(&self, requirement: &CausalClock) -> bool {
        self.frontier.clock.dominates(requirement)
    }

    #[inline(always)]
    pub fn clock(&self) -> &CausalClock {
        &self.frontier.clock
    }
}

/// Per-tenant causal domain. Isolated FrontierState + ExactCausalIndex.
#[repr(C, align(64))]
pub struct TenantDomain {
    pub frontier: FrontierState,
    pub exact_index: ExactCausalIndex,
    pub tenant_id: TenantId,
    pub active: bool,
    _pad: [u8; 44],
}

impl TenantDomain {
    #[inline(always)]
    pub const fn empty() -> Self {
        Self {
            frontier: FrontierState::new(),
            exact_index: ExactCausalIndex::new(),
            tenant_id: 0,
            active: false,
            _pad: [0u8; 44],
        }
    }

    #[inline(always)]
    pub fn init(&mut self, tenant_id: TenantId) {
        self.frontier = FrontierState::new();
        self.exact_index = ExactCausalIndex::new();
        self.tenant_id = tenant_id;
        self.active = true;
    }

    #[inline(always)]
    pub fn saturation(&self) -> f32 {
        self.frontier.clock.saturation()
    }
}

/// Multi-tenant kernel with isolated causal domains per tenant.
pub struct TenantKernel<I: Invariant> {
    pub domains: [TenantDomain; MAX_TENANTS],
    pub states: [StateCell; MAX_TENANTS],
    pub invariant: I,
    pub tenant_count: usize,
}

impl<I: Invariant + Clone> TenantKernel<I> {
    pub fn new(invariant: I) -> Self {
        const EMPTY_DOMAIN: TenantDomain = TenantDomain::empty();
        Self {
            domains: [EMPTY_DOMAIN; MAX_TENANTS],
            states: [StateCell::new(); MAX_TENANTS],
            invariant,
            tenant_count: 0,
        }
    }

    #[inline]
    pub fn register_tenant(
        &mut self,
        tenant_id: TenantId,
        initial_state: StateCell,
    ) -> Option<usize> {
        if self.tenant_count >= MAX_TENANTS {
            return None;
        }
        let idx = self.tenant_count;
        self.domains[idx].init(tenant_id);
        self.states[idx] = initial_state;
        self.tenant_count += 1;
        Some(idx)
    }

    #[inline]
    fn find_tenant(&self, tenant_id: TenantId) -> Option<usize> {
        (0..self.tenant_count)
            .find(|&i| self.domains[i].active && self.domains[i].tenant_id == tenant_id)
    }

    #[inline]
    pub fn admit(
        &mut self,
        tenant_id: TenantId,
        fact_id: &FactId,
        deps: &[FactId],
        payload: &[u8],
    ) -> Result<(), AdmitError> {
        let idx = self
            .find_tenant(tenant_id)
            .ok_or(AdmitError::MalformedFact)?;
        let domain = &mut self.domains[idx];

        if !deps.is_empty() {
            let deps_clock = build_deps_clock(deps);
            if !check_dominance(&domain.frontier.clock, &deps_clock) {
                return Err(AdmitError::CausalityViolation);
            }
            if domain.exact_index.contains_all(deps).is_err() {
                return Err(AdmitError::CausalHorizonExceeded);
            }
        }

        self.invariant
            .apply(payload, self.states[idx].as_bytes_mut())
            .map_err(|_| AdmitError::InvariantViolation)?;

        domain.frontier.advance(*fact_id);
        domain.exact_index.insert(fact_id);

        Ok(())
    }

    #[inline(always)]
    pub fn clock(&self, tenant_id: TenantId) -> Option<&CausalClock> {
        self.find_tenant(tenant_id)
            .map(|idx| &self.domains[idx].frontier.clock)
    }

    #[inline(always)]
    pub fn state(&self, tenant_id: TenantId) -> Option<&StateCell> {
        self.find_tenant(tenant_id).map(|idx| &self.states[idx])
    }

    #[inline(always)]
    pub fn saturation(&self, tenant_id: TenantId) -> Option<f32> {
        self.find_tenant(tenant_id)
            .map(|idx| self.domains[idx].saturation())
    }

    #[inline(always)]
    pub fn query(&self, tenant_id: TenantId, requirement: &CausalClock) -> bool {
        self.find_tenant(tenant_id)
            .map(|idx| self.domains[idx].frontier.clock.dominates(requirement))
            .unwrap_or(false)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::invariants::total_supply::{ConservationState, DeltaPayload, TotalSupplyInvariant};
    use zerocopy::IntoBytes;

    fn make_state_cell(balance: i128, min: i128, max: i128) -> StateCell {
        let state = ConservationState::new(balance, min, max);
        let mut cell = StateCell::new();
        cell.as_slice_mut().copy_from_slice(state.as_bytes());
        cell
    }

    fn make_payload(delta: i128) -> [u8; 16] {
        let payload = DeltaPayload { delta };
        let mut buf = [0u8; 16];
        buf.copy_from_slice(payload.as_bytes());
        buf
    }

    #[test]
    fn test_kernel_admit_no_deps() {
        let state = make_state_cell(100, 0, 1000);
        let mut kernel = Kernel::with_state(TotalSupplyInvariant::new(), state);

        let fact_id: FactId = [1u8; 32];
        let payload = make_payload(50);

        let result = kernel.admit_raw(&fact_id, &[], &payload);
        assert!(result.is_ok());

        let s = kernel.state.cast_ref::<ConservationState>().unwrap();
        assert_eq!(s.balance, 150);
    }

    #[test]
    fn test_kernel_admit_with_deps() {
        let state = make_state_cell(100, 0, 1000);
        let mut kernel = Kernel::with_state(TotalSupplyInvariant::new(), state);

        let fact1: FactId = [1u8; 32];
        let payload1 = make_payload(50);
        kernel.admit_raw(&fact1, &[], &payload1).unwrap();

        let fact2: FactId = [2u8; 32];
        let payload2 = make_payload(25);
        let result = kernel.admit_raw(&fact2, &[fact1], &payload2);
        assert!(result.is_ok());

        let s = kernel.state.cast_ref::<ConservationState>().unwrap();
        assert_eq!(s.balance, 175);
    }

    #[test]
    fn test_kernel_causality_violation() {
        let state = make_state_cell(100, 0, 1000);
        let mut kernel = Kernel::with_state(TotalSupplyInvariant::new(), state);

        let unknown_dep: FactId = [99u8; 32];
        let fact_id: FactId = [1u8; 32];
        let payload = make_payload(50);

        let result = kernel.admit_raw(&fact_id, &[unknown_dep], &payload);
        assert_eq!(result, Err(AdmitError::CausalityViolation));
    }

    #[test]
    fn test_kernel_invariant_violation() {
        let state = make_state_cell(100, 0, 1000);
        let mut kernel = Kernel::with_state(TotalSupplyInvariant::new(), state);

        let fact_id: FactId = [1u8; 32];
        let payload = make_payload(-200);

        let result = kernel.admit_raw(&fact_id, &[], &payload);
        assert_eq!(result, Err(AdmitError::InvariantViolation));
    }

    #[test]
    fn test_tenant_kernel_isolation() {
        let mut kernel = TenantKernel::new(TotalSupplyInvariant::new());

        let state_a = make_state_cell(100, 0, 1000);
        let state_b = make_state_cell(500, 0, 2000);

        kernel.register_tenant(1, state_a).unwrap();
        kernel.register_tenant(2, state_b).unwrap();

        // Tenant 1: admit fact
        let fact_a1: FactId = [1u8; 32];
        let payload_a1 = make_payload(50);
        kernel.admit(1, &fact_a1, &[], &payload_a1).unwrap();

        // Tenant 2: admit fact (independent causal domain)
        let fact_b1: FactId = [2u8; 32];
        let payload_b1 = make_payload(100);
        kernel.admit(2, &fact_b1, &[], &payload_b1).unwrap();

        // Verify isolated state
        let s_a = kernel
            .state(1)
            .unwrap()
            .cast_ref::<ConservationState>()
            .unwrap();
        let s_b = kernel
            .state(2)
            .unwrap()
            .cast_ref::<ConservationState>()
            .unwrap();
        assert_eq!(s_a.balance, 150);
        assert_eq!(s_b.balance, 600);

        // Tenant 1: cannot depend on Tenant 2's fact (isolated causal domains)
        let fact_a2: FactId = [3u8; 32];
        let payload_a2 = make_payload(10);
        let result = kernel.admit(1, &fact_a2, &[fact_b1], &payload_a2);
        assert_eq!(result, Err(AdmitError::CausalityViolation));

        // Tenant 1: can depend on own fact
        let result = kernel.admit(1, &fact_a2, &[fact_a1], &payload_a2);
        assert!(result.is_ok());
    }

    #[test]
    fn test_tenant_kernel_saturation_isolation() {
        let mut kernel = TenantKernel::new(TotalSupplyInvariant::new());

        let state = make_state_cell(0, i128::MIN, i128::MAX);
        kernel.register_tenant(1, state).unwrap();
        kernel.register_tenant(2, state).unwrap();

        // Saturate tenant 1's Bloom filter
        for i in 0..200u32 {
            let mut fact_id = [0u8; 32];
            fact_id[0..4].copy_from_slice(&i.to_le_bytes());
            let payload = make_payload(1);
            kernel.admit(1, &fact_id, &[], &payload).unwrap();
        }

        // Tenant 1 should have high saturation
        let sat_1 = kernel.saturation(1).unwrap();
        // Tenant 2 should have zero saturation (isolated)
        let sat_2 = kernel.saturation(2).unwrap();

        assert!(sat_1 > 0.1);
        assert_eq!(sat_2, 0.0);
    }
}
