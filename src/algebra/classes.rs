//! Algebraic classification. The hierarchy determines coordination scope.

use crate::core::invariant::{AlgebraicClass, Invariant, InvariantError};

pub use crate::core::invariant::AlgebraicClass as Class;

impl AlgebraicClass {
    #[inline(always)]
    pub const fn guarantees_sec(&self) -> bool {
        !matches!(self, AlgebraicClass::Ordered)
    }

    #[inline(always)]
    pub const fn coordination_scope(&self) -> CoordinationScope {
        match self {
            AlgebraicClass::Commutative
            | AlgebraicClass::CommutativeIdempotent
            | AlgebraicClass::Lattice
            | AlgebraicClass::Group => CoordinationScope::None,
            AlgebraicClass::BoundedCommutative => CoordinationScope::Scoped,
            AlgebraicClass::Ordered => CoordinationScope::Global,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum CoordinationScope {
    None = 0,
    Scoped = 1,
    Global = 2,
}

/// Δ(a, Δ(b, s)) = Δ(b, Δ(a, s)) → zero coordination.
pub trait CommutativeInvariant: Invariant {
    fn algebraic_class(&self) -> AlgebraicClass {
        AlgebraicClass::Commutative
    }

    fn identity(&self) -> Option<&[u8]> {
        None
    }
}

/// Δ(a, Δ(a, s)) = Δ(a, s) → duplicate-safe.
pub trait IdempotentInvariant: CommutativeInvariant {
    fn algebraic_class(&self) -> AlgebraicClass {
        AlgebraicClass::CommutativeIdempotent
    }
}

/// Has inverses. Enables compensation.
pub trait GroupInvariant: CommutativeInvariant {
    fn inverse(&self, delta: &[u8]) -> Result<[u8; 16], InvariantError>;

    fn algebraic_class(&self) -> AlgebraicClass {
        AlgebraicClass::Group
    }
}

/// Join-semilattice. Always converges.
pub trait LatticeInvariant: IdempotentInvariant {
    fn join(&self, state_a: &[u8], state_b: &[u8], result: &mut [u8])
        -> Result<(), InvariantError>;
    fn partial_order(&self, state_a: &[u8], state_b: &[u8]) -> bool;

    fn algebraic_class(&self) -> AlgebraicClass {
        AlgebraicClass::Lattice
    }
}

/// Bounded state space. May need escrow at boundaries.
pub trait BoundedInvariant: CommutativeInvariant {
    fn would_exceed_bounds(&self, delta: &[u8], state: &[u8]) -> bool;
    fn headroom(&self, state: &[u8]) -> i128;

    fn algebraic_class(&self) -> AlgebraicClass {
        AlgebraicClass::BoundedCommutative
    }
}

/// State only moves one direction.
pub trait MonotonicInvariant: LatticeInvariant {
    fn direction(&self) -> MonotonicDirection;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum MonotonicDirection {
    Increasing = 0,
    Decreasing = 1,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_algebraic_class_coordination() {
        assert!(AlgebraicClass::Commutative.is_coordination_free());
        assert!(AlgebraicClass::CommutativeIdempotent.is_coordination_free());
        assert!(AlgebraicClass::Lattice.is_coordination_free());
        assert!(AlgebraicClass::Group.is_coordination_free());
        assert!(!AlgebraicClass::BoundedCommutative.is_coordination_free());
        assert!(!AlgebraicClass::Ordered.is_coordination_free());
    }

    #[test]
    fn test_coordination_scope() {
        assert_eq!(
            AlgebraicClass::Commutative.coordination_scope(),
            CoordinationScope::None
        );
        assert_eq!(
            AlgebraicClass::BoundedCommutative.coordination_scope(),
            CoordinationScope::Scoped
        );
        assert_eq!(
            AlgebraicClass::Ordered.coordination_scope(),
            CoordinationScope::Global
        );
    }

    #[test]
    fn test_sec_guarantees() {
        assert!(AlgebraicClass::Commutative.guarantees_sec());
        assert!(AlgebraicClass::BoundedCommutative.guarantees_sec());
        assert!(!AlgebraicClass::Ordered.guarantees_sec());
    }
}
