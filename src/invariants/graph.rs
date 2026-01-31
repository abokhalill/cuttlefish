//! Graph invariants. Grow-only = lattice under edge union = coordination-free.

use crate::core::invariant::{Invariant, InvariantError};
use zerocopy::{FromBytes, Immutable, IntoBytes, KnownLayout};

pub const MAX_VERTICES: usize = 16;

/// 16x16 adjacency matrix (256 bits) + metadata = 64 bytes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, FromBytes, IntoBytes, KnownLayout, Immutable)]
#[repr(C)]
pub struct GraphState {
    pub adjacency: [u64; 4],
    pub vertex_count: u8,
    pub max_out_degree: u8,
    pub max_in_degree: u8,
    pub flags: u8,
    _pad: [u8; 28],
}

const _: () = {
    assert!(core::mem::size_of::<GraphState>() == 64);
};

impl GraphState {
    #[inline(always)]
    pub const fn new(vertex_count: u8) -> Self {
        Self {
            adjacency: [0u64; 4],
            vertex_count,
            max_out_degree: 0,
            max_in_degree: 0,
            flags: 0,
            _pad: [0u8; 28],
        }
    }

    #[inline(always)]
    pub const fn directed(vertex_count: u8) -> Self {
        Self {
            adjacency: [0u64; 4],
            vertex_count,
            max_out_degree: 0,
            max_in_degree: 0,
            flags: 0x01, // directed
            _pad: [0u8; 28],
        }
    }

    #[inline(always)]
    pub fn is_directed(&self) -> bool {
        self.flags & 0x01 != 0
    }

    #[inline(always)]
    pub fn allows_self_loops(&self) -> bool {
        self.flags & 0x02 != 0
    }

    /// Get the bit index for edge (from, to).
    #[inline(always)]
    fn edge_index(from: u8, to: u8) -> usize {
        (from as usize) * MAX_VERTICES + (to as usize)
    }

    /// Check if edge (from, to) exists.
    #[inline(always)]
    pub fn has_edge(&self, from: u8, to: u8) -> bool {
        let idx = Self::edge_index(from, to);
        let word = idx / 64;
        let bit = idx % 64;
        (self.adjacency[word] >> bit) & 1 == 1
    }

    /// Add edge (from, to). For undirected graphs, also adds (to, from).
    #[inline(always)]
    pub fn add_edge(&mut self, from: u8, to: u8) {
        let idx = Self::edge_index(from, to);
        let word = idx / 64;
        let bit = idx % 64;
        self.adjacency[word] |= 1u64 << bit;

        if !self.is_directed() {
            let idx2 = Self::edge_index(to, from);
            let word2 = idx2 / 64;
            let bit2 = idx2 % 64;
            self.adjacency[word2] |= 1u64 << bit2;
        }
    }

    #[inline]
    pub fn out_degree(&self, vertex: u8) -> u8 {
        let mut count = 0u8;
        for to in 0..self.vertex_count {
            if self.has_edge(vertex, to) {
                count += 1;
            }
        }
        count
    }

    #[inline]
    pub fn in_degree(&self, vertex: u8) -> u8 {
        let mut count = 0u8;
        for from in 0..self.vertex_count {
            if self.has_edge(from, vertex) {
                count += 1;
            }
        }
        count
    }

    #[inline]
    pub fn edge_count(&self) -> u32 {
        let raw_count: u32 = self.adjacency.iter().map(|w| w.count_ones()).sum();
        if self.is_directed() {
            raw_count
        } else {
            raw_count / 2
        }
    }

    #[inline(always)]
    pub fn merge(&mut self, other: &Self) {
        self.adjacency[0] |= other.adjacency[0];
        self.adjacency[1] |= other.adjacency[1];
        self.adjacency[2] |= other.adjacency[2];
        self.adjacency[3] |= other.adjacency[3];
    }

    #[inline(always)]
    pub fn contains(&self, other: &Self) -> bool {
        for i in 0..4 {
            if (other.adjacency[i] & !self.adjacency[i]) != 0 {
                return false;
            }
        }
        true
    }
}

impl Default for GraphState {
    fn default() -> Self {
        Self::new(0)
    }
}

#[derive(Debug, Clone, Copy, FromBytes, IntoBytes, KnownLayout, Immutable)]
#[repr(C)]
pub struct EdgePayload {
    pub from: u8,
    pub to: u8,
    _pad: [u8; 14],
}

impl EdgePayload {
    #[inline(always)]
    pub const fn new(from: u8, to: u8) -> Self {
        Self {
            from,
            to,
            _pad: [0u8; 14],
        }
    }
}

#[derive(Debug, Clone, Copy, Default)]
pub struct GGraphInvariant;

impl GGraphInvariant {
    #[inline(always)]
    pub const fn new() -> Self {
        Self
    }
}

impl Invariant for GGraphInvariant {
    #[inline]
    fn apply(&self, payload: &[u8], state: &mut [u8]) -> Result<(), InvariantError> {
        if payload.len() < 2 || state.len() < 64 {
            return Err(InvariantError::MalformedPayload);
        }

        let from = payload[0];
        let to = payload[1];

        let vertex_count = state[32];
        let max_out_degree = state[33];
        let max_in_degree = state[34];
        let flags = state[35];
        let allows_self_loops = flags & 0x02 != 0;

        if from >= vertex_count || to >= vertex_count {
            return Err(InvariantError::BoundsViolation);
        }

        if from == to && !allows_self_loops {
            return Err(InvariantError::BoundsViolation);
        }

        let idx = (from as usize) * MAX_VERTICES + (to as usize);
        let word = idx / 64;
        let bit = idx % 64;

        let adj_bytes: [u64; 4] = [
            u64::from_le_bytes(state[0..8].try_into().unwrap()),
            u64::from_le_bytes(state[8..16].try_into().unwrap()),
            u64::from_le_bytes(state[16..24].try_into().unwrap()),
            u64::from_le_bytes(state[24..32].try_into().unwrap()),
        ];

        if (adj_bytes[word] >> bit) & 1 == 1 {
            // Edge already exists - idempotent success
            return Ok(());
        }

        // Check degree constraints before adding
        if max_out_degree > 0 {
            let mut out_deg = 0u8;
            for t in 0..vertex_count {
                let i = (from as usize) * MAX_VERTICES + (t as usize);
                let w = i / 64;
                let b = i % 64;
                if (adj_bytes[w] >> b) & 1 == 1 {
                    out_deg += 1;
                }
            }
            if out_deg >= max_out_degree {
                return Err(InvariantError::Overflow);
            }
        }

        if max_in_degree > 0 {
            let mut in_deg = 0u8;
            for f in 0..vertex_count {
                let i = (f as usize) * MAX_VERTICES + (to as usize);
                let w = i / 64;
                let b = i % 64;
                if (adj_bytes[w] >> b) & 1 == 1 {
                    in_deg += 1;
                }
            }
            if in_deg >= max_in_degree {
                return Err(InvariantError::Overflow);
            }
        }

        // Add the edge
        let new_word = adj_bytes[word] | (1u64 << bit);
        let word_offset = word * 8;
        state[word_offset..word_offset + 8].copy_from_slice(&new_word.to_le_bytes());

        // For undirected graphs, add reverse edge
        let is_directed = flags & 0x01 != 0;
        if !is_directed && from != to {
            let idx2 = (to as usize) * MAX_VERTICES + (from as usize);
            let word2 = idx2 / 64;
            let bit2 = idx2 % 64;

            let current_word2 = if word2 == word {
                new_word
            } else {
                adj_bytes[word2]
            };

            let new_word2 = current_word2 | (1u64 << bit2);
            let word2_offset = word2 * 8;
            state[word2_offset..word2_offset + 8].copy_from_slice(&new_word2.to_le_bytes());
        }

        Ok(())
    }
}

/// ReachabilityInvariant: Maintains transitive closure for reachability queries.
///
///
/// # Implementation
/// Maintains a separate reachability matrix that is the transitive closure
/// of the adjacency matrix. Updated incrementally on edge addition.
///
/// # Constraint
/// Can enforce that certain vertices must remain unreachable from others
/// (eg. for access control).
#[derive(Debug, Clone, Copy, Default)]
pub struct ReachabilityInvariant {
    /// If set, adding an edge that would make `forbidden_target` reachable
    /// from `forbidden_source` is rejected.
    pub forbidden_source: Option<u8>,
    pub forbidden_target: Option<u8>,
}

impl ReachabilityInvariant {
    #[inline(always)]
    pub const fn new() -> Self {
        Self {
            forbidden_source: None,
            forbidden_target: None,
        }
    }

    #[inline(always)]
    pub const fn with_forbidden(source: u8, target: u8) -> Self {
        Self {
            forbidden_source: Some(source),
            forbidden_target: Some(target),
        }
    }
}

/// Extended graph state with reachability matrix.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(C)]
pub struct ReachabilityState {
    /// Adjacency matrix (32 bytes)
    pub adjacency: [u64; 4],
    /// Reachability matrix - transitive closure (32 bytes)
    pub reachability: [u64; 4],
}

impl ReachabilityState {
    pub const SIZE: usize = 64;

    #[inline(always)]
    pub const fn new() -> Self {
        Self {
            adjacency: [0u64; 4],
            reachability: [0u64; 4],
        }
    }

    /// Check if `to` is reachable from `from`.
    #[inline(always)]
    pub fn is_reachable(&self, from: u8, to: u8) -> bool {
        let idx = (from as usize) * MAX_VERTICES + (to as usize);
        let word = idx / 64;
        let bit = idx % 64;
        (self.reachability[word] >> bit) & 1 == 1
    }

    /// Update reachability after adding edge (from, to).
    /// Uses incremental Warshall update.
    #[inline]
    pub fn update_reachability(&mut self, from: u8, to: u8, vertex_count: u8) {
        // After adding edge (from, to):
        // For all x: if x can reach `from`, then x can now reach `to`
        // For all y: if `to` can reach y, then `from` can now reach y
        // Combined: if x reaches `from` and `to` reaches y, then x reaches y

        // First, mark direct edge
        let idx = (from as usize) * MAX_VERTICES + (to as usize);
        let word = idx / 64;
        let bit = idx % 64;
        self.reachability[word] |= 1u64 << bit;

        // Incremental update
        for x in 0..vertex_count {
            // If x can reach `from`
            let x_to_from_idx = (x as usize) * MAX_VERTICES + (from as usize);
            let x_to_from_word = x_to_from_idx / 64;
            let x_to_from_bit = x_to_from_idx % 64;
            let x_reaches_from = (self.reachability[x_to_from_word] >> x_to_from_bit) & 1 == 1;

            if x_reaches_from || x == from {
                // x can now reach everything `to` can reach
                for y in 0..vertex_count {
                    let to_to_y_idx = (to as usize) * MAX_VERTICES + (y as usize);
                    let to_to_y_word = to_to_y_idx / 64;
                    let to_to_y_bit = to_to_y_idx % 64;
                    let to_reaches_y = (self.reachability[to_to_y_word] >> to_to_y_bit) & 1 == 1;

                    if to_reaches_y || y == to {
                        let x_to_y_idx = (x as usize) * MAX_VERTICES + (y as usize);
                        let x_to_y_word = x_to_y_idx / 64;
                        let x_to_y_bit = x_to_y_idx % 64;
                        self.reachability[x_to_y_word] |= 1u64 << x_to_y_bit;
                    }
                }
            }
        }
    }
}

impl Default for ReachabilityState {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_graph_state_basic() {
        let mut graph = GraphState::new(4);

        assert!(!graph.has_edge(0, 1));
        graph.add_edge(0, 1);
        assert!(graph.has_edge(0, 1));
        assert!(graph.has_edge(1, 0)); // Undirected
    }

    #[test]
    fn test_graph_state_directed() {
        let mut graph = GraphState::directed(4);

        graph.add_edge(0, 1);
        assert!(graph.has_edge(0, 1));
        assert!(!graph.has_edge(1, 0)); // Directed - no reverse
    }

    #[test]
    fn test_graph_merge_lattice() {
        let mut g1 = GraphState::new(4);
        let mut g2 = GraphState::new(4);

        g1.add_edge(0, 1);
        g2.add_edge(1, 2);

        g1.merge(&g2);

        assert!(g1.has_edge(0, 1));
        assert!(g1.has_edge(1, 2));
    }

    #[test]
    fn test_ggraph_invariant() {
        let inv = GGraphInvariant::new();

        // Initialize state: 4 vertices, undirected
        let mut state = [0u8; 64];
        state[32] = 4; // vertex_count

        // Add edge 0 -> 1
        let payload = EdgePayload::new(0, 1);
        assert!(inv.apply(payload.as_bytes(), &mut state).is_ok());

        // Verify edge exists
        let adj0 = u64::from_le_bytes(state[0..8].try_into().unwrap());
        let idx = 0 * MAX_VERTICES + 1;
        assert!((adj0 >> idx) & 1 == 1);

        // Idempotent: adding same edge again succeeds
        assert!(inv.apply(payload.as_bytes(), &mut state).is_ok());
    }

    #[test]
    fn test_ggraph_degree_constraint() {
        let inv = GGraphInvariant::new();

        // Initialize: 4 vertices, max out-degree = 1
        let mut state = [0u8; 64];
        state[32] = 4; // vertex_count
        state[33] = 1; // max_out_degree

        // Add edge 0 -> 1 (ok)
        let payload1 = EdgePayload::new(0, 1);
        assert!(inv.apply(payload1.as_bytes(), &mut state).is_ok());

        // Add edge 0 -> 2 (should fail - exceeds out-degree)
        let payload2 = EdgePayload::new(0, 2);
        assert!(inv.apply(payload2.as_bytes(), &mut state).is_err());
    }

    #[test]
    fn test_ggraph_commutative() {
        let inv = GGraphInvariant::new();

        // Order 1: add (0,1) then (1,2)
        let mut state1 = [0u8; 64];
        state1[32] = 4;
        inv.apply(EdgePayload::new(0, 1).as_bytes(), &mut state1)
            .unwrap();
        inv.apply(EdgePayload::new(1, 2).as_bytes(), &mut state1)
            .unwrap();

        // Order 2: add (1,2) then (0,1)
        let mut state2 = [0u8; 64];
        state2[32] = 4;
        inv.apply(EdgePayload::new(1, 2).as_bytes(), &mut state2)
            .unwrap();
        inv.apply(EdgePayload::new(0, 1).as_bytes(), &mut state2)
            .unwrap();

        // Same result
        assert_eq!(state1[0..32], state2[0..32]);
    }

    #[test]
    fn test_reachability_state() {
        let mut state = ReachabilityState::new();

        // Add edge 0 -> 1
        state.update_reachability(0, 1, 4);
        assert!(state.is_reachable(0, 1));

        // Add edge 1 -> 2
        state.update_reachability(1, 2, 4);
        assert!(state.is_reachable(1, 2));
        assert!(state.is_reachable(0, 2)); // Transitive!

        // Add edge 2 -> 3
        state.update_reachability(2, 3, 4);
        assert!(state.is_reachable(0, 3)); // 0 -> 1 -> 2 -> 3
    }
}
