//! Invariant trait: Δ_I application must be pure, O(1), allocation-free.

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum InvariantError {
    Overflow = 1,
    Underflow = 2,
    BoundsViolation = 3,
    MalformedPayload = 4,
    DuplicateElement = 5,
}

pub trait Invariant {
    fn apply(&self, payload: &[u8], state: &mut [u8]) -> Result<(), InvariantError>;
}

pub trait StaticInvariant: Invariant + Copy + 'static {}

impl<T: Invariant + Copy + 'static> StaticInvariant for T {}
