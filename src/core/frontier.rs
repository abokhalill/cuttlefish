//! Frontier: the minimal antichain of maximal observed FactIds.

use arrayvec::ArrayVec;
use super::topology::{CausalClock, FactId};

/// Antichain width limit—keeps frontier operations O(1).
pub const MAX_FRONTIER_WIDTH: usize = 8;

pub type Frontier = ArrayVec<FactId, MAX_FRONTIER_WIDTH>;

#[derive(Debug, Clone)]
#[repr(C, align(64))]
pub struct FrontierState {
    pub frontier: Frontier,
    pub clock: CausalClock,
}

impl FrontierState {
    #[inline(always)]
    pub const fn new() -> Self {
        Self {
            frontier: ArrayVec::new_const(),
            clock: CausalClock::new(),
        }
    }

    #[inline(always)]
    pub fn observe(&mut self, fact_id: &FactId) {
        self.clock.observe(fact_id);
    }

    #[inline(always)]
    pub fn advance(&mut self, fact_id: FactId) {
        self.clock.observe(&fact_id);

        if self.frontier.len() < MAX_FRONTIER_WIDTH {
            self.frontier.push(fact_id);
        } else {
            self.frontier[0] = fact_id;
        }
    }

    #[inline(always)]
    pub fn dominates_clock(&self, target: &CausalClock) -> bool {
        self.clock.dominates(target)
    }
}

impl Default for FrontierState {
    #[inline(always)]
    fn default() -> Self {
        Self::new()
    }
}

#[inline(always)]
pub fn check_dominance(frontier_clock: &CausalClock, deps_clock: &CausalClock) -> bool {
    frontier_clock.dominates(deps_clock)
}

#[inline(always)]
pub fn build_deps_clock(deps: &[FactId]) -> CausalClock {
    let mut clock = CausalClock::new();
    for dep in deps {
        clock.observe(dep);
    }
    clock
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_frontier_state_new() {
        let state = FrontierState::new();
        assert!(state.frontier.is_empty());
        assert_eq!(state.clock.popcount(), 0);
    }

    #[test]
    fn test_frontier_advance() {
        let mut state = FrontierState::new();
        let fact_id: FactId = [0xAB; 32];

        state.advance(fact_id);

        assert_eq!(state.frontier.len(), 1);
        assert!(state.clock.might_contain(&fact_id));
    }

    #[test]
    fn test_check_dominance() {
        let mut frontier_clock = CausalClock::new();
        let mut deps_clock = CausalClock::new();

        let fact1: FactId = [1u8; 32];
        let fact2: FactId = [2u8; 32];

        frontier_clock.observe(&fact1);
        frontier_clock.observe(&fact2);

        deps_clock.observe(&fact1);

        assert!(check_dominance(&frontier_clock, &deps_clock));
    }

    #[test]
    fn test_build_deps_clock() {
        let deps = [
            [1u8; 32],
            [2u8; 32],
        ];

        let clock = build_deps_clock(&deps);

        assert!(clock.might_contain(&deps[0]));
        assert!(clock.might_contain(&deps[1]));
    }
}
