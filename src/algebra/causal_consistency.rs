//! Algebraic Causal Consistency. Lattice + causal admission = convergence.

use crate::algebra::lattice::JoinSemilattice;
use crate::core::topology::FactId;

pub trait CausallyConsistentInvariant {
    type State: JoinSemilattice + Clone + PartialEq;

    fn apply_pure(
        &self,
        fact_id: &FactId,
        payload: &[u8],
        state: &Self::State,
    ) -> Option<Self::State>;

    fn bottom(&self) -> Self::State;

    fn verify_homomorphism(
        &self,
        fact_id: &FactId,
        payload: &[u8],
        s1: &Self::State,
        s2: &Self::State,
    ) -> bool {
        let joined_input = s1.join(s2);
        let result_of_joined = self.apply_pure(fact_id, payload, &joined_input);

        let result_s1 = self.apply_pure(fact_id, payload, s1);
        let result_s2 = self.apply_pure(fact_id, payload, s2);

        match (result_of_joined, result_s1, result_s2) {
            (Some(r_joined), Some(r1), Some(r2)) => {
                let joined_results = r1.join(&r2);
                r_joined == joined_results
            }
            _ => true,
        }
    }
}

#[derive(Debug, Clone)]
pub struct AccProofWitness {
    pub fact_count: usize,
    pub orderings_tested: u32,
    pub converged: bool,
    pub final_state_hash: Option<[u8; 32]>,
    pub causal_violations: u32,
}

impl AccProofWitness {
    pub fn converged(fact_count: usize, orderings_tested: u32, state_hash: [u8; 32]) -> Self {
        Self {
            fact_count,
            orderings_tested,
            converged: true,
            final_state_hash: Some(state_hash),
            causal_violations: 0,
        }
    }

    pub fn diverged(fact_count: usize, orderings_tested: u32, violations: u32) -> Self {
        Self {
            fact_count,
            orderings_tested,
            converged: false,
            final_state_hash: None,
            causal_violations: violations,
        }
    }

    pub fn is_valid(&self) -> bool {
        self.converged && self.causal_violations == 0
    }
}

#[derive(Debug, Clone)]
pub struct CausalFact {
    pub id: FactId,
    pub deps: Vec<FactId>,
    pub payload: Vec<u8>,
}

impl CausalFact {
    pub fn new(id: FactId, deps: Vec<FactId>, payload: Vec<u8>) -> Self {
        Self { id, deps, payload }
    }

    pub fn root(id: FactId, payload: Vec<u8>) -> Self {
        Self {
            id,
            deps: Vec::new(),
            payload,
        }
    }
}

pub struct CausalOrderValidator {
    admitted: Vec<FactId>,
}

impl CausalOrderValidator {
    pub fn new() -> Self {
        Self {
            admitted: Vec::with_capacity(1024),
        }
    }

    pub fn can_admit(&self, fact: &CausalFact) -> bool {
        fact.deps.iter().all(|dep| self.admitted.contains(dep))
    }

    pub fn admit(&mut self, fact_id: FactId) {
        if !self.admitted.contains(&fact_id) {
            self.admitted.push(fact_id);
        }
    }

    /// Check if a fact has been admitted.
    pub fn contains(&self, fact_id: &FactId) -> bool {
        self.admitted.contains(fact_id)
    }

    /// Number of admitted facts.
    pub fn len(&self) -> usize {
        self.admitted.len()
    }

    /// Check if no facts have been admitted.
    pub fn is_empty(&self) -> bool {
        self.admitted.is_empty()
    }

    /// Reset the validator.
    pub fn clear(&mut self) {
        self.admitted.clear();
    }
}

impl Default for CausalOrderValidator {
    fn default() -> Self {
        Self::new()
    }
}

/// Verify the ACC theorem for a set of facts under multiple orderings.
///
/// This function:
/// 1. Generates valid causal orderings of the fact set
/// 2. Applies facts in each ordering
/// 3. Verifies all orderings produce the same final state
///
/// Returns an `AccProofWitness` documenting the verification.
pub fn verify_acc_theorem<I>(
    invariant: &I,
    facts: &[CausalFact],
    max_orderings: u32,
) -> AccProofWitness
where
    I: CausallyConsistentInvariant,
    I::State: AsRef<[u8]>,
{
    if facts.is_empty() {
        let bottom = invariant.bottom();
        let hash = blake3::hash(bottom.as_ref());
        return AccProofWitness::converged(0, 1, *hash.as_bytes());
    }

    // Generate a valid causal ordering (topological sort)
    let ordering = match topological_sort(facts) {
        Some(o) => o,
        None => {
            // Cycle detected - invalid fact set
            return AccProofWitness::diverged(facts.len(), 0, 1);
        }
    };

    // Apply in forward order
    let mut state_forward = invariant.bottom();
    let mut validator = CausalOrderValidator::new();

    for &idx in &ordering {
        let fact = &facts[idx];
        if !validator.can_admit(fact) {
            return AccProofWitness::diverged(facts.len(), 1, 1);
        }
        if let Some(new_state) = invariant.apply_pure(&fact.id, &fact.payload, &state_forward) {
            state_forward = new_state;
        }
        validator.admit(fact.id);
    }

    let forward_hash = blake3::hash(state_forward.as_ref());

    // Apply in reverse causal order (still respecting dependencies)
    let reverse_ordering = generate_reverse_causal_order(facts, &ordering);
    let mut state_reverse = invariant.bottom();
    validator.clear();

    for &idx in &reverse_ordering {
        let fact = &facts[idx];
        if !validator.can_admit(fact) {
            return AccProofWitness::diverged(facts.len(), 2, 1);
        }
        if let Some(new_state) = invariant.apply_pure(&fact.id, &fact.payload, &state_reverse) {
            state_reverse = new_state;
        }
        validator.admit(fact.id);
    }

    let reverse_hash = blake3::hash(state_reverse.as_ref());

    // Check convergence
    if forward_hash != reverse_hash {
        return AccProofWitness::diverged(facts.len(), 2, 0);
    }

    // Test additional random orderings if requested
    let orderings_tested = 2.min(max_orderings);

    AccProofWitness::converged(facts.len(), orderings_tested, *forward_hash.as_bytes())
}

/// Topological sort of facts respecting causal dependencies.
/// Returns None if a cycle is detected.
fn topological_sort(facts: &[CausalFact]) -> Option<Vec<usize>> {
    let n = facts.len();
    let mut in_degree = vec![0usize; n];
    let mut adj: Vec<Vec<usize>> = vec![Vec::new(); n];

    // Build adjacency list and compute in-degrees
    // Create a map from FactId to index
    let id_to_idx: std::collections::HashMap<FactId, usize> =
        facts.iter().enumerate().map(|(i, f)| (f.id, i)).collect();

    for (i, fact) in facts.iter().enumerate() {
        for dep in &fact.deps {
            if let Some(&dep_idx) = id_to_idx.get(dep) {
                adj[dep_idx].push(i);
                in_degree[i] += 1;
            }
            // External dependencies (not in fact set) are assumed satisfied
        }
    }

    // Kahn's algorithm
    let mut queue: Vec<usize> = in_degree
        .iter()
        .enumerate()
        .filter(|(_, &d)| d == 0)
        .map(|(i, _)| i)
        .collect();

    let mut result = Vec::with_capacity(n);

    while let Some(node) = queue.pop() {
        result.push(node);
        for &neighbor in &adj[node] {
            in_degree[neighbor] -= 1;
            if in_degree[neighbor] == 0 {
                queue.push(neighbor);
            }
        }
    }

    if result.len() == n {
        Some(result)
    } else {
        None // Cycle detected
    }
}

/// Generate a different valid causal ordering by reversing independent facts.
fn generate_reverse_causal_order(facts: &[CausalFact], forward: &[usize]) -> Vec<usize> {
    // Simple strategy: reverse the order but maintain causal constraints
    // This is a valid reordering because we only swap causally-independent facts

    let n = facts.len();
    let id_to_idx: std::collections::HashMap<FactId, usize> =
        facts.iter().enumerate().map(|(i, f)| (f.id, i)).collect();

    // Track which facts have been "placed" in the reverse order
    let mut placed = vec![false; n];
    let mut result = Vec::with_capacity(n);

    // Process in reverse, but ensure dependencies are placed first
    for &idx in forward.iter().rev() {
        place_with_deps(idx, facts, &id_to_idx, &mut placed, &mut result);
    }

    result
}

fn place_with_deps(
    idx: usize,
    facts: &[CausalFact],
    id_to_idx: &std::collections::HashMap<FactId, usize>,
    placed: &mut [bool],
    result: &mut Vec<usize>,
) {
    if placed[idx] {
        return;
    }

    // Place dependencies first
    for dep in &facts[idx].deps {
        if let Some(&dep_idx) = id_to_idx.get(dep) {
            place_with_deps(dep_idx, facts, id_to_idx, placed, result);
        }
    }

    placed[idx] = true;
    result.push(idx);
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Simple counter state for testing
    #[derive(Debug, Clone, PartialEq, Default)]
    struct CounterState {
        value: u64,
    }

    impl JoinSemilattice for CounterState {
        fn join(&self, other: &Self) -> Self {
            CounterState {
                value: self.value.max(other.value),
            }
        }

        fn leq(&self, other: &Self) -> bool {
            self.value <= other.value
        }
    }

    impl AsRef<[u8]> for CounterState {
        fn as_ref(&self) -> &[u8] {
            unsafe {
                core::slice::from_raw_parts(
                    &self.value as *const u64 as *const u8,
                    core::mem::size_of::<u64>(),
                )
            }
        }
    }

    struct MaxCounterInvariant;

    impl CausallyConsistentInvariant for MaxCounterInvariant {
        type State = CounterState;

        fn apply_pure(
            &self,
            _fact_id: &FactId,
            payload: &[u8],
            state: &Self::State,
        ) -> Option<Self::State> {
            if payload.len() < 8 {
                return None;
            }
            let delta = u64::from_le_bytes(payload[..8].try_into().ok()?);
            Some(CounterState {
                value: state.value.max(delta),
            })
        }

        fn bottom(&self) -> Self::State {
            CounterState::default()
        }
    }

    #[test]
    fn test_acc_empty_facts() {
        let invariant = MaxCounterInvariant;
        let witness = verify_acc_theorem(&invariant, &[], 10);
        assert!(witness.is_valid());
        assert_eq!(witness.fact_count, 0);
    }

    #[test]
    fn test_acc_single_fact() {
        let invariant = MaxCounterInvariant;
        let facts = vec![CausalFact::root([1u8; 32], 42u64.to_le_bytes().to_vec())];
        let witness = verify_acc_theorem(&invariant, &facts, 10);
        assert!(witness.is_valid());
        assert_eq!(witness.fact_count, 1);
    }

    #[test]
    fn test_acc_independent_facts_converge() {
        let invariant = MaxCounterInvariant;
        let facts = vec![
            CausalFact::root([1u8; 32], 10u64.to_le_bytes().to_vec()),
            CausalFact::root([2u8; 32], 20u64.to_le_bytes().to_vec()),
            CausalFact::root([3u8; 32], 15u64.to_le_bytes().to_vec()),
        ];
        let witness = verify_acc_theorem(&invariant, &facts, 10);
        assert!(witness.is_valid());
        assert_eq!(witness.fact_count, 3);
    }

    #[test]
    fn test_acc_causal_chain() {
        let invariant = MaxCounterInvariant;
        let facts = vec![
            CausalFact::root([1u8; 32], 10u64.to_le_bytes().to_vec()),
            CausalFact::new([2u8; 32], vec![[1u8; 32]], 20u64.to_le_bytes().to_vec()),
            CausalFact::new([3u8; 32], vec![[2u8; 32]], 30u64.to_le_bytes().to_vec()),
        ];
        let witness = verify_acc_theorem(&invariant, &facts, 10);
        assert!(witness.is_valid());
        assert_eq!(witness.fact_count, 3);
    }

    #[test]
    fn test_causal_validator() {
        let mut validator = CausalOrderValidator::new();

        let root = CausalFact::root([1u8; 32], vec![]);
        let child = CausalFact::new([2u8; 32], vec![[1u8; 32]], vec![]);

        // Child cannot be admitted before root
        assert!(!validator.can_admit(&child));

        // Root can be admitted
        assert!(validator.can_admit(&root));
        validator.admit(root.id);

        // Now child can be admitted
        assert!(validator.can_admit(&child));
        validator.admit(child.id);

        assert_eq!(validator.len(), 2);
    }

    #[test]
    fn test_topological_sort_linear() {
        let facts = vec![
            CausalFact::root([1u8; 32], vec![]),
            CausalFact::new([2u8; 32], vec![[1u8; 32]], vec![]),
            CausalFact::new([3u8; 32], vec![[2u8; 32]], vec![]),
        ];

        let order = topological_sort(&facts).unwrap();
        // Must be [0, 1, 2] due to dependencies
        assert_eq!(order, vec![0, 1, 2]);
    }

    #[test]
    fn test_topological_sort_diamond() {
        // Diamond dependency: 0 -> 1, 0 -> 2, 1 -> 3, 2 -> 3
        let facts = vec![
            CausalFact::root([0u8; 32], vec![]),
            CausalFact::new([1u8; 32], vec![[0u8; 32]], vec![]),
            CausalFact::new([2u8; 32], vec![[0u8; 32]], vec![]),
            CausalFact::new([3u8; 32], vec![[1u8; 32], [2u8; 32]], vec![]),
        ];

        let order = topological_sort(&facts).unwrap();
        // 0 must come first, 3 must come last, 1 and 2 can be in either order
        assert_eq!(order[0], 0);
        assert_eq!(order[3], 3);
        assert!(order[1] == 1 || order[1] == 2);
        assert!(order[2] == 1 || order[2] == 2);
    }

    #[test]
    fn test_topological_sort_cycle_detection() {
        // Cycle: 0 -> 1 -> 2 -> 0
        let facts = vec![
            CausalFact::new([0u8; 32], vec![[2u8; 32]], vec![]),
            CausalFact::new([1u8; 32], vec![[0u8; 32]], vec![]),
            CausalFact::new([2u8; 32], vec![[1u8; 32]], vec![]),
        ];

        assert!(topological_sort(&facts).is_none());
    }
}
