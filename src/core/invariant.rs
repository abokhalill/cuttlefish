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
    /// already seen this element.
    DuplicateElement = 5,
}

/// The core abstraction. Implement this for your state machine.
///
/// Rules:
/// - Pure function. Same input = same output. Always.
/// - O(1). No loops over unbounded data.
/// - No allocations. Work in-place on the state slice.
/// - Commutative? You get coordination-free replication for free.
pub trait Invariant {
    fn apply(&self, payload: &[u8], state: &mut [u8]) -> Result<(), InvariantError>;
}

pub trait StaticInvariant: Invariant + Copy + 'static {}

impl<T: Invariant + Copy + 'static> StaticInvariant for T {}
