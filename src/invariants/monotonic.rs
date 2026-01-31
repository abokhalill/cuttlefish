//! Monotonic invariants. Lattice-based, always converge.

use crate::core::invariant::{Invariant, InvariantError};
use zerocopy::{FromBytes, Immutable, IntoBytes, KnownLayout};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[derive(FromBytes, IntoBytes, KnownLayout, Immutable)]
#[repr(C)]
pub struct MaxState {
    pub value: u64,
    _pad: [u8; 56],
}

impl Default for MaxState {
    fn default() -> Self {
        Self::new(0)
    }
}

const _: () = {
    assert!(core::mem::size_of::<MaxState>() == 64);
};

impl MaxState {
    #[inline(always)]
    pub const fn new(initial: u64) -> Self {
        Self {
            value: initial,
            _pad: [0u8; 56],
        }
    }
}

#[derive(Debug, Clone, Copy, Default)]
pub struct MaxInvariant;

impl MaxInvariant {
    #[inline(always)]
    pub const fn new() -> Self {
        Self
    }
}

impl Invariant for MaxInvariant {
    #[inline(always)]
    fn apply(&self, payload: &[u8], state: &mut [u8]) -> Result<(), InvariantError> {
        if payload.len() < 8 || state.len() < 64 {
            return Err(InvariantError::MalformedPayload);
        }

        let proposed = u64::from_le_bytes([
            payload[0], payload[1], payload[2], payload[3],
            payload[4], payload[5], payload[6], payload[7],
        ]);

        let current = u64::from_le_bytes([
            state[0], state[1], state[2], state[3],
            state[4], state[5], state[6], state[7],
        ]);

        // Monotonic: only update if proposed > current
        let new_value = current.max(proposed);
        state[0..8].copy_from_slice(&new_value.to_le_bytes());

        Ok(())
    }
}

// ============================================================================
// GCounter: Grow-Only Counter (Lattice-Based)
// ============================================================================

/// State for GCounter: per-node counters that only grow.
///
/// This is a simplified version with a single counter.
/// For distributed use, extend to per-node counters.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[derive(FromBytes, IntoBytes, KnownLayout, Immutable)]
#[repr(C)]
pub struct GCounterState {
    pub count: u64,
    _pad: [u8; 56],
}

impl Default for GCounterState {
    fn default() -> Self {
        Self::new()
    }
}

const _: () = {
    assert!(core::mem::size_of::<GCounterState>() == 64);
};

impl GCounterState {
    #[inline(always)]
    pub const fn new() -> Self {
        Self {
            count: 0,
            _pad: [0u8; 56],
        }
    }

    #[inline(always)]
    pub const fn with_value(count: u64) -> Self {
        Self {
            count,
            _pad: [0u8; 56],
        }
    }
}

#[derive(Debug, Clone, Copy, Default)]
pub struct GCounterInvariant;

impl GCounterInvariant {
    #[inline(always)]
    pub const fn new() -> Self {
        Self
    }
}

impl Invariant for GCounterInvariant {
    #[inline(always)]
    fn apply(&self, payload: &[u8], state: &mut [u8]) -> Result<(), InvariantError> {
        if payload.len() < 8 || state.len() < 64 {
            return Err(InvariantError::MalformedPayload);
        }

        let delta = u64::from_le_bytes([
            payload[0], payload[1], payload[2], payload[3],
            payload[4], payload[5], payload[6], payload[7],
        ]);

        let current = u64::from_le_bytes([
            state[0], state[1], state[2], state[3],
            state[4], state[5], state[6], state[7],
        ]);

        let new_count = current.saturating_add(delta);
        state[0..8].copy_from_slice(&new_count.to_le_bytes());

        Ok(())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[derive(FromBytes, IntoBytes, KnownLayout, Immutable)]
#[repr(C)]
pub struct LWWState {
    pub value: [u8; 32],
    pub timestamp: u64,
    pub node_id: u64,
    _pad: [u8; 16],
}

const _: () = {
    assert!(core::mem::size_of::<LWWState>() == 64);
};

impl LWWState {
    #[inline(always)]
    pub const fn new() -> Self {
        Self {
            value: [0u8; 32],
            timestamp: 0,
            node_id: 0,
            _pad: [0u8; 16],
        }
    }
}

#[derive(Debug, Clone, Copy)]
#[derive(FromBytes, IntoBytes, KnownLayout, Immutable)]
#[repr(C)]
pub struct LWWPayload {
    pub value: [u8; 32],
    pub timestamp: u64,
    pub node_id: u64,
}

/// LWW: higher (timestamp, node_id) wins.
#[derive(Debug, Clone, Copy, Default)]
pub struct LWWInvariant;

impl LWWInvariant {
    #[inline(always)]
    pub const fn new() -> Self {
        Self
    }
}

impl Invariant for LWWInvariant {
    #[inline(always)]
    fn apply(&self, payload: &[u8], state: &mut [u8]) -> Result<(), InvariantError> {
        if payload.len() < 48 || state.len() < 64 {
            return Err(InvariantError::MalformedPayload);
        }

        // Parse payload
        let mut new_value = [0u8; 32];
        new_value.copy_from_slice(&payload[0..32]);
        let new_timestamp = u64::from_le_bytes([
            payload[32], payload[33], payload[34], payload[35],
            payload[36], payload[37], payload[38], payload[39],
        ]);
        let new_node_id = u64::from_le_bytes([
            payload[40], payload[41], payload[42], payload[43],
            payload[44], payload[45], payload[46], payload[47],
        ]);

        // Parse current state
        let current_timestamp = u64::from_le_bytes([
            state[32], state[33], state[34], state[35],
            state[36], state[37], state[38], state[39],
        ]);
        let current_node_id = u64::from_le_bytes([
            state[40], state[41], state[42], state[43],
            state[44], state[45], state[46], state[47],
        ]);

        // Lexicographic comparison: (timestamp, node_id)
        let should_update = new_timestamp > current_timestamp
            || (new_timestamp == current_timestamp && new_node_id > current_node_id);

        if should_update {
            state[0..32].copy_from_slice(&new_value);
            state[32..40].copy_from_slice(&new_timestamp.to_le_bytes());
            state[40..48].copy_from_slice(&new_node_id.to_le_bytes());
        }

        Ok(())
    }
}

/// State for bounded semilattice with capacity tracking.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[derive(FromBytes, IntoBytes, KnownLayout, Immutable)]
#[repr(C)]
pub struct BoundedLatticeState {
    pub value: u64,
    pub capacity: u64,
    _pad: [u8; 48],
}

impl Default for BoundedLatticeState {
    fn default() -> Self {
        Self::new(u64::MAX)
    }
}

const _: () = {
    assert!(core::mem::size_of::<BoundedLatticeState>() == 64);
};

impl BoundedLatticeState {
    #[inline(always)]
    pub const fn new(capacity: u64) -> Self {
        Self {
            value: 0,
            capacity,
            _pad: [0u8; 48],
        }
    }

    #[inline(always)]
    pub fn headroom(&self) -> u64 {
        self.capacity.saturating_sub(self.value)
    }
}

/// BoundedGCounterInvariant: Grow-only counter with capacity limit.
///
/// # Properties
/// - **Algebraic Class**: BoundedCommutative
/// - **Coordination**: Scoped (only when near capacity)
/// - **Convergence**: Guaranteed within bounds
///
/// # Rejection
/// Rejects if adding delta would exceed capacity.
#[derive(Debug, Clone, Copy, Default)]
pub struct BoundedGCounterInvariant;

impl BoundedGCounterInvariant {
    #[inline(always)]
    pub const fn new() -> Self {
        Self
    }
}

impl Invariant for BoundedGCounterInvariant {
    #[inline(always)]
    fn apply(&self, payload: &[u8], state: &mut [u8]) -> Result<(), InvariantError> {
        if payload.len() < 8 || state.len() < 64 {
            return Err(InvariantError::MalformedPayload);
        }

        let delta = u64::from_le_bytes([
            payload[0], payload[1], payload[2], payload[3],
            payload[4], payload[5], payload[6], payload[7],
        ]);

        let current = u64::from_le_bytes([
            state[0], state[1], state[2], state[3],
            state[4], state[5], state[6], state[7],
        ]);

        let capacity = u64::from_le_bytes([
            state[8], state[9], state[10], state[11],
            state[12], state[13], state[14], state[15],
        ]);

        let new_value = current.saturating_add(delta);

        if new_value > capacity {
            return Err(InvariantError::Overflow);
        }

        state[0..8].copy_from_slice(&new_value.to_le_bytes());

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_max_invariant() {
        let inv = MaxInvariant::new();
        let mut state = [0u8; 64];
        state[0..8].copy_from_slice(&100u64.to_le_bytes());

        // Apply higher value
        let payload = 200u64.to_le_bytes();
        assert!(inv.apply(&payload, &mut state).is_ok());
        assert_eq!(u64::from_le_bytes(state[0..8].try_into().unwrap()), 200);

        // Apply lower value (no change)
        let payload = 50u64.to_le_bytes();
        assert!(inv.apply(&payload, &mut state).is_ok());
        assert_eq!(u64::from_le_bytes(state[0..8].try_into().unwrap()), 200);
    }

    #[test]
    fn test_max_invariant_idempotent() {
        let inv = MaxInvariant::new();
        let mut state = [0u8; 64];

        let payload = 100u64.to_le_bytes();

        // Apply twice
        inv.apply(&payload, &mut state).unwrap();
        let after_once = u64::from_le_bytes(state[0..8].try_into().unwrap());

        inv.apply(&payload, &mut state).unwrap();
        let after_twice = u64::from_le_bytes(state[0..8].try_into().unwrap());

        // Idempotent: same result
        assert_eq!(after_once, after_twice);
    }

    #[test]
    fn test_max_invariant_commutative() {
        let inv = MaxInvariant::new();

        // Order 1: 50 then 100
        let mut state1 = [0u8; 64];
        inv.apply(&50u64.to_le_bytes(), &mut state1).unwrap();
        inv.apply(&100u64.to_le_bytes(), &mut state1).unwrap();

        // Order 2: 100 then 50
        let mut state2 = [0u8; 64];
        inv.apply(&100u64.to_le_bytes(), &mut state2).unwrap();
        inv.apply(&50u64.to_le_bytes(), &mut state2).unwrap();

        // Same result
        assert_eq!(state1[0..8], state2[0..8]);
    }

    #[test]
    fn test_gcounter_invariant() {
        let inv = GCounterInvariant::new();
        let mut state = [0u8; 64];

        inv.apply(&10u64.to_le_bytes(), &mut state).unwrap();
        inv.apply(&20u64.to_le_bytes(), &mut state).unwrap();

        let count = u64::from_le_bytes(state[0..8].try_into().unwrap());
        assert_eq!(count, 30);
    }

    #[test]
    fn test_lww_invariant() {
        let inv = LWWInvariant::new();
        let mut state = [0u8; 64];

        // First write: timestamp=10, node=1
        let mut payload1 = [0u8; 48];
        payload1[0] = 0xAA; // value
        payload1[32..40].copy_from_slice(&10u64.to_le_bytes());
        payload1[40..48].copy_from_slice(&1u64.to_le_bytes());
        inv.apply(&payload1, &mut state).unwrap();

        // Second write: timestamp=5, node=2 (should NOT update - older)
        let mut payload2 = [0u8; 48];
        payload2[0] = 0xBB;
        payload2[32..40].copy_from_slice(&5u64.to_le_bytes());
        payload2[40..48].copy_from_slice(&2u64.to_le_bytes());
        inv.apply(&payload2, &mut state).unwrap();

        // Value should still be 0xAA
        assert_eq!(state[0], 0xAA);

        // Third write: timestamp=10, node=5 (should update - same ts, higher node)
        let mut payload3 = [0u8; 48];
        payload3[0] = 0xCC;
        payload3[32..40].copy_from_slice(&10u64.to_le_bytes());
        payload3[40..48].copy_from_slice(&5u64.to_le_bytes());
        inv.apply(&payload3, &mut state).unwrap();

        // Value should now be 0xCC
        assert_eq!(state[0], 0xCC);
    }

    #[test]
    fn test_bounded_gcounter() {
        let inv = BoundedGCounterInvariant::new();
        let mut state = [0u8; 64];
        state[8..16].copy_from_slice(&100u64.to_le_bytes()); // capacity = 100

        // Add 50 (ok)
        assert!(inv.apply(&50u64.to_le_bytes(), &mut state).is_ok());

        // Add 40 (ok, total = 90)
        assert!(inv.apply(&40u64.to_le_bytes(), &mut state).is_ok());

        // Add 20 (fail, would exceed capacity)
        assert!(inv.apply(&20u64.to_le_bytes(), &mut state).is_err());

        // Value should still be 90
        let count = u64::from_le_bytes(state[0..8].try_into().unwrap());
        assert_eq!(count, 90);
    }
}
