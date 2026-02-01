//! Invariant trait. Pure, O(1), no allocations. Commutative = no coordination.

/// Why your invariant said no.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum InvariantError {
    /// Would exceed upper bound.
    Overflow = 1,
    /// Would go below lower bound.
    Underflow = 2,
    /// Generic constraint violation.
    BoundsViolation = 3,
    /// Couldn't parse payload.
    MalformedPayload = 4,
    /// Already seen this element.
    DuplicateElement = 5,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum AlgebraicClass {
    /// Δ(a, Δ(b, s)) = Δ(b, Δ(a, s)) → coordination-free.
    Commutative = 0,
    /// Commutative + Δ(a, Δ(a, s)) = Δ(a, s) → duplicate-safe.
    CommutativeIdempotent = 1,
    /// Join-semilattice. Always converges.
    Lattice = 2,
    /// Has inverses. Enables compensation.
    Group = 3,
    /// Commutative but bounded state space. May need escrow.
    BoundedCommutative = 4,
    /// Requires total ordering. Needs consensus.
    Ordered = 5,
}

impl AlgebraicClass {
    #[inline(always)]
    pub const fn is_coordination_free(&self) -> bool {
        matches!(
            self,
            AlgebraicClass::Commutative
                | AlgebraicClass::CommutativeIdempotent
                | AlgebraicClass::Lattice
                | AlgebraicClass::Group
        )
    }
}

/// The core abstraction. Implement this for your state machine.
///
/// Rules:
/// - Pure function. Same input = same output. Always.
/// - O(1). No loops over unbounded data.
/// - No allocations. Work in-place on the state slice.
/// - Override `algebraic_class()` to declare coordination-freedom.
pub trait Invariant {
    fn apply(&self, payload: &[u8], state: &mut [u8]) -> Result<(), InvariantError>;

    fn algebraic_class(&self) -> Option<AlgebraicClass> {
        None
    }

    fn is_coordination_free(&self) -> bool {
        self.algebraic_class()
            .map(|c| c.is_coordination_free())
            .unwrap_or(false)
    }
}

pub trait StaticInvariant: Invariant + Copy + 'static {}

impl<T: Invariant + Copy + 'static> StaticInvariant for T {}
