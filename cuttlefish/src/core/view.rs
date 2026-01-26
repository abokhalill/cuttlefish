//! View: point-in-time read abstraction V = (Frontier, State).

use super::frontier::FrontierState;
use super::state::StateCell;
use super::topology::CausalClock;

#[derive(Debug, Clone)]
pub struct View {
    pub frontier: FrontierState,
    pub state: StateCell,
}

impl View {
    #[inline(always)]
    pub const fn new() -> Self {
        Self {
            frontier: FrontierState::new(),
            state: StateCell::new(),
        }
    }

    #[inline(always)]
    pub fn with_state(state: StateCell) -> Self {
        Self {
            frontier: FrontierState::new(),
            state,
        }
    }

    #[inline(always)]
    pub fn clock(&self) -> &CausalClock {
        &self.frontier.clock
    }

    #[inline(always)]
    pub fn satisfies(&self, requirement: &CausalClock) -> bool {
        self.frontier.clock.dominates(requirement)
    }

    #[inline(always)]
    pub fn state(&self) -> &StateCell {
        &self.state
    }

    #[inline(always)]
    pub fn state_mut(&mut self) -> &mut StateCell {
        &mut self.state
    }
}

impl Default for View {
    #[inline(always)]
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::topology::FactId;

    #[test]
    fn test_view_satisfies_empty() {
        let view = View::new();
        let empty_req = CausalClock::new();
        assert!(view.satisfies(&empty_req));
    }

    #[test]
    fn test_view_satisfies_with_facts() {
        let mut view = View::new();
        let fact1: FactId = [1u8; 32];
        let fact2: FactId = [2u8; 32];

        view.frontier.advance(fact1);
        view.frontier.advance(fact2);

        let mut requirement = CausalClock::new();
        requirement.observe(&fact1);

        assert!(view.satisfies(&requirement));
    }

    #[test]
    fn test_view_not_satisfies() {
        let mut view = View::new();
        let fact1: FactId = [1u8; 32];
        let fact2: FactId = [2u8; 32];

        view.frontier.advance(fact1);

        let mut requirement = CausalClock::new();
        requirement.observe(&fact2);

        assert!(!view.satisfies(&requirement));
    }
}
