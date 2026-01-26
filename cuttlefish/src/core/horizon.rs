//! Causal horizon: the boundary beyond which facts are pruned.
//! Facts referencing deps beyond horizon require re-anchoring.

use super::topology::{CausalClock, FactId};

pub const DEFAULT_HORIZON_DEPTH: u64 = 1000;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum PruningPolicy {
    NeverPrune = 0,
    DepthBased = 1,
    EpochBased = 2,
}

impl Default for PruningPolicy {
    fn default() -> Self {
        Self::DepthBased
    }
}

#[derive(Debug, Clone, Copy)]
#[repr(C, align(64))]
pub struct Horizon {
    pub oldest_fact: FactId,
    pub horizon_clock: CausalClock,
    pub depth: u64,
    pub policy: PruningPolicy,
    pub prune_depth: u64,
    _pad: [u8; 23],
}

const _: () = {
    assert!(core::mem::size_of::<Horizon>() == 192);
    assert!(core::mem::align_of::<Horizon>() == 64);
};

impl Horizon {
    #[inline(always)]
    pub const fn new() -> Self {
        Self {
            oldest_fact: [0u8; 32],
            horizon_clock: CausalClock::new(),
            depth: 0,
            policy: PruningPolicy::DepthBased,
            prune_depth: DEFAULT_HORIZON_DEPTH,
            _pad: [0u8; 23],
        }
    }

    #[inline(always)]
    pub fn with_policy(policy: PruningPolicy, prune_depth: u64) -> Self {
        Self {
            oldest_fact: [0u8; 32],
            horizon_clock: CausalClock::new(),
            depth: 0,
            policy,
            prune_depth,
            _pad: [0u8; 23],
        }
    }

    #[inline(always)]
    pub fn deps_within_horizon(&self, deps_clock: &CausalClock) -> bool {
        self.horizon_clock.dominates(deps_clock)
    }

    #[inline(always)]
    pub fn observe(&mut self, fact_id: &FactId) {
        self.horizon_clock.observe(fact_id);
        self.depth = self.depth.saturating_add(1);
    }

    #[inline(always)]
    pub fn should_prune(&self) -> bool {
        match self.policy {
            PruningPolicy::NeverPrune => false,
            PruningPolicy::DepthBased => self.depth > self.prune_depth,
            PruningPolicy::EpochBased => self.depth > self.prune_depth,
        }
    }

    #[inline(always)]
    pub fn advance_to(&mut self, new_oldest: FactId, new_clock: CausalClock, new_depth: u64) {
        self.oldest_fact = new_oldest;
        self.horizon_clock = new_clock;
        self.depth = new_depth;
    }

    #[inline(always)]
    pub fn reset_from_checkpoint(&mut self, checkpoint_clock: CausalClock) {
        self.horizon_clock = checkpoint_clock;
        self.depth = 0;
    }

    #[inline(always)]
    pub fn saturation(&self) -> f32 {
        self.horizon_clock.saturation()
    }
}

impl Default for Horizon {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_horizon_size_alignment() {
        assert_eq!(core::mem::align_of::<Horizon>(), 64);
    }

    #[test]
    fn test_horizon_observe() {
        let mut horizon = Horizon::new();
        let fact_id: FactId = [1u8; 32];

        horizon.observe(&fact_id);

        assert_eq!(horizon.depth, 1);
        assert!(horizon.horizon_clock.might_contain(&fact_id));
    }

    #[test]
    fn test_deps_within_horizon() {
        let mut horizon = Horizon::new();
        let fact1: FactId = [1u8; 32];
        let fact2: FactId = [2u8; 32];

        horizon.observe(&fact1);
        horizon.observe(&fact2);

        let mut deps_clock = CausalClock::new();
        deps_clock.observe(&fact1);

        assert!(horizon.deps_within_horizon(&deps_clock));

        let mut unknown_clock = CausalClock::new();
        unknown_clock.observe(&[99u8; 32]);

        assert!(!horizon.deps_within_horizon(&unknown_clock));
    }

    #[test]
    fn test_should_prune() {
        let mut horizon = Horizon::with_policy(PruningPolicy::DepthBased, 10);

        for i in 0..10 {
            let mut fact_id = [0u8; 32];
            fact_id[0] = i;
            horizon.observe(&fact_id);
        }

        assert!(!horizon.should_prune());

        horizon.observe(&[11u8; 32]);
        assert!(horizon.should_prune());
    }

    #[test]
    fn test_never_prune_policy() {
        let mut horizon = Horizon::with_policy(PruningPolicy::NeverPrune, 0);

        for i in 0..100 {
            let mut fact_id = [0u8; 32];
            fact_id[0] = i;
            horizon.observe(&fact_id);
        }

        assert!(!horizon.should_prune());
    }
}
