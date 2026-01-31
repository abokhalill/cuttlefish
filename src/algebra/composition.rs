//! Invariant composition. Parallel composition preserves algebraic properties.

use crate::core::invariant::{Invariant, InvariantError};
use super::classes::AlgebraicClass;

pub const MAX_COMPOSED_INVARIANTS: usize = 8;

#[derive(Clone)]
pub struct ParallelComposition<I: Invariant + Copy, const N: usize> {
    invariants: [Option<I>; N],
    count: usize,
    algebraic_class: AlgebraicClass,
}

impl<I: Invariant + Copy, const N: usize> ParallelComposition<I, N> {
    pub fn new() -> Self {
        Self {
            invariants: [None; N],
            count: 0,
            algebraic_class: AlgebraicClass::Commutative,
        }
    }

    pub fn add(&mut self, invariant: I) -> Result<usize, CompositionError> {
        if self.count >= N {
            return Err(CompositionError::CapacityExceeded);
        }
        let idx = self.count;
        self.invariants[idx] = Some(invariant);
        self.count += 1;
        Ok(idx)
    }

    pub fn add_with_class(
        &mut self,
        invariant: I,
        class: AlgebraicClass,
    ) -> Result<usize, CompositionError> {
        let idx = self.add(invariant)?;
        self.algebraic_class = Self::compose_classes(self.algebraic_class, class);
        Ok(idx)
    }

    fn compose_classes(a: AlgebraicClass, b: AlgebraicClass) -> AlgebraicClass {
        use AlgebraicClass::*;

        if matches!(a, Ordered) || matches!(b, Ordered) {
            return Ordered;
        }

        if matches!(a, BoundedCommutative) || matches!(b, BoundedCommutative) {
            return BoundedCommutative;
        }

        if matches!(a, Group) || matches!(b, Group) {
            return Group;
        }

        if matches!(a, Commutative) || matches!(b, Commutative) {
            return Commutative;
        }

        if matches!(a, CommutativeIdempotent) || matches!(b, CommutativeIdempotent) {
            return CommutativeIdempotent;
        }

        Lattice
    }

    #[inline(always)]
    pub fn len(&self) -> usize {
        self.count
    }

    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.count == 0
    }

    #[inline(always)]
    pub fn algebraic_class(&self) -> AlgebraicClass {
        self.algebraic_class
    }

    #[inline(always)]
    pub fn is_coordination_free(&self) -> bool {
        self.algebraic_class.is_coordination_free()
    }
}

impl<I: Invariant + Copy, const N: usize> Default for ParallelComposition<I, N> {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CompositionError {
    CapacityExceeded,
    PayloadMismatch,
    StateMismatch,
}

#[derive(Clone, Copy)]
pub struct ComposedInvariant<I1: Invariant + Copy, I2: Invariant + Copy> {
    pub inv1: I1,
    pub inv2: I2,
}

impl<I1: Invariant + Copy, I2: Invariant + Copy> ComposedInvariant<I1, I2> {
    #[inline(always)]
    pub const fn new(inv1: I1, inv2: I2) -> Self {
        Self { inv1, inv2 }
    }

    #[inline]
    pub fn apply_split(
        &self,
        payload1: &[u8],
        payload2: &[u8],
        state: &mut [u8],
    ) -> Result<(), InvariantError> {
        if state.len() < 128 {
            return Err(InvariantError::MalformedPayload);
        }

        let mut scratch1 = [0u8; 64];
        let mut scratch2 = [0u8; 64];
        scratch1.copy_from_slice(&state[0..64]);
        scratch2.copy_from_slice(&state[64..128]);

        self.inv1.apply(payload1, &mut scratch1)?;
        self.inv2.apply(payload2, &mut scratch2)?;

        state[0..64].copy_from_slice(&scratch1);
        state[64..128].copy_from_slice(&scratch2);

        Ok(())
    }
}

#[derive(Clone, Copy)]
pub struct TripleComposition<I1, I2, I3>
where
    I1: Invariant + Copy,
    I2: Invariant + Copy,
    I3: Invariant + Copy,
{
    pub inv1: I1,
    pub inv2: I2,
    pub inv3: I3,
}

impl<I1, I2, I3> TripleComposition<I1, I2, I3>
where
    I1: Invariant + Copy,
    I2: Invariant + Copy,
    I3: Invariant + Copy,
{
    #[inline(always)]
    pub const fn new(inv1: I1, inv2: I2, inv3: I3) -> Self {
        Self { inv1, inv2, inv3 }
    }

    #[inline]
    pub fn apply_split(
        &self,
        payload1: &[u8],
        payload2: &[u8],
        payload3: &[u8],
        state: &mut [u8],
    ) -> Result<(), InvariantError> {
        if state.len() < 192 {
            return Err(InvariantError::MalformedPayload);
        }

        let mut scratch1 = [0u8; 64];
        let mut scratch2 = [0u8; 64];
        let mut scratch3 = [0u8; 64];
        scratch1.copy_from_slice(&state[0..64]);
        scratch2.copy_from_slice(&state[64..128]);
        scratch3.copy_from_slice(&state[128..192]);

        self.inv1.apply(payload1, &mut scratch1)?;
        self.inv2.apply(payload2, &mut scratch2)?;
        self.inv3.apply(payload3, &mut scratch3)?;

        state[0..64].copy_from_slice(&scratch1);
        state[64..128].copy_from_slice(&scratch2);
        state[128..192].copy_from_slice(&scratch3);

        Ok(())
    }
}

pub type InvariantApplyFn = fn(payload: &[u8], state: &mut [u8]) -> Result<(), InvariantError>;

/// Dynamic composition using function pointers.
///
/// Less efficient than static composition but allows runtime configuration.
#[derive(Clone)]
pub struct DynamicComposition {
    invariants: [Option<InvariantApplyFn>; MAX_COMPOSED_INVARIANTS],
    count: usize,
}

impl DynamicComposition {
    pub fn new() -> Self {
        Self {
            invariants: [None; MAX_COMPOSED_INVARIANTS],
            count: 0,
        }
    }

    pub fn add(&mut self, apply_fn: InvariantApplyFn) -> Result<usize, CompositionError> {
        if self.count >= MAX_COMPOSED_INVARIANTS {
            return Err(CompositionError::CapacityExceeded);
        }
        let idx = self.count;
        self.invariants[idx] = Some(apply_fn);
        self.count += 1;
        Ok(idx)
    }

    /// Apply all invariants atomically.
    ///
    /// Each invariant gets a 64-byte slice of state.
    /// Payloads are provided as a slice of slices.
    pub fn apply_all(
        &self,
        payloads: &[&[u8]],
        state: &mut [u8],
    ) -> Result<(), InvariantError> {
        if payloads.len() != self.count {
            return Err(InvariantError::MalformedPayload);
        }
        if state.len() < self.count * 64 {
            return Err(InvariantError::MalformedPayload);
        }

        // Create scratch space
        let mut scratch = [[0u8; 64]; MAX_COMPOSED_INVARIANTS];
        for i in 0..self.count {
            scratch[i].copy_from_slice(&state[i * 64..(i + 1) * 64]);
        }

        // Apply all invariants to scratch
        for i in 0..self.count {
            if let Some(apply_fn) = self.invariants[i] {
                apply_fn(payloads[i], &mut scratch[i])?;
            }
        }

        // All succeeded - commit
        for i in 0..self.count {
            state[i * 64..(i + 1) * 64].copy_from_slice(&scratch[i]);
        }

        Ok(())
    }

    #[inline(always)]
    pub fn len(&self) -> usize {
        self.count
    }

    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.count == 0
    }
}

impl Default for DynamicComposition {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::invariants::total_supply::TotalSupplyInvariant;
    use crate::invariants::uniqueness::UniquenessInvariant;

    #[test]
    fn test_composed_invariant_both_succeed() {
        let composed = ComposedInvariant::new(
            TotalSupplyInvariant::new(),
            UniquenessInvariant::new(),
        );

        // Initialize state: balance=100, min=0, max=1000, uniqueness=empty
        let mut state = [0u8; 128];
        state[0..16].copy_from_slice(&100i128.to_le_bytes()); // balance
        state[16..32].copy_from_slice(&0i128.to_le_bytes());   // min
        state[32..48].copy_from_slice(&1000i128.to_le_bytes()); // max

        // Payloads: add 50 to balance, mark element 42 as used
        let payload1 = 50i128.to_le_bytes();
        let mut payload2 = [0u8; 16];
        payload2[0..2].copy_from_slice(&42u16.to_le_bytes());

        let result = composed.apply_split(&payload1, &payload2, &mut state);
        assert!(result.is_ok());

        // Verify balance updated
        let balance = i128::from_le_bytes(state[0..16].try_into().unwrap());
        assert_eq!(balance, 150);
    }

    #[test]
    fn test_composed_invariant_first_fails() {
        let composed = ComposedInvariant::new(
            TotalSupplyInvariant::new(),
            UniquenessInvariant::new(),
        );

        let mut state = [0u8; 128];
        state[0..16].copy_from_slice(&100i128.to_le_bytes());
        state[16..32].copy_from_slice(&0i128.to_le_bytes());
        state[32..48].copy_from_slice(&1000i128.to_le_bytes());

        // Try to subtract 200 (would go below min=0)
        let payload1 = (-200i128).to_le_bytes();
        let mut payload2 = [0u8; 16];
        payload2[0..2].copy_from_slice(&42u16.to_le_bytes());

        let result = composed.apply_split(&payload1, &payload2, &mut state);
        assert!(result.is_err());

        // Verify state unchanged (atomic rollback)
        let balance = i128::from_le_bytes(state[0..16].try_into().unwrap());
        assert_eq!(balance, 100);
    }

    #[test]
    fn test_algebraic_class_composition() {
        use AlgebraicClass::*;

        // Commutative + Commutative = Commutative
        assert_eq!(
            ParallelComposition::<TotalSupplyInvariant, 4>::compose_classes(Commutative, Commutative),
            Commutative
        );

        // Commutative + Ordered = Ordered
        assert_eq!(
            ParallelComposition::<TotalSupplyInvariant, 4>::compose_classes(Commutative, Ordered),
            Ordered
        );

        // Lattice + Lattice = Lattice
        assert_eq!(
            ParallelComposition::<TotalSupplyInvariant, 4>::compose_classes(Lattice, Lattice),
            Lattice
        );

        // Lattice + Commutative = Commutative (weaker)
        assert_eq!(
            ParallelComposition::<TotalSupplyInvariant, 4>::compose_classes(Lattice, Commutative),
            Commutative
        );
    }
}
