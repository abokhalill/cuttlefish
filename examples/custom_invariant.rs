//! Custom invariant: implement your own algebraic constraint.

use ctfs::core::topology::FactId;
use ctfs::core::{AdmitError, Invariant, InvariantError, Kernel, StateCell};
use zerocopy::{FromBytes, Immutable, IntoBytes, KnownLayout};

/// State: tracks a value that can only increase (monotonic).
#[derive(Debug, Clone, Copy, FromBytes, IntoBytes, KnownLayout, Immutable)]
#[repr(C)]
struct MonotonicCounter {
    value: u64,
    _pad: [u8; 56], // StateCell is 64 bytes
}

impl MonotonicCounter {
    fn new(initial: u64) -> Self {
        Self {
            value: initial,
            _pad: [0u8; 56],
        }
    }
}

/// Invariant: value can only increase. Rejects decrements.
#[derive(Clone, Copy)]
struct MonotonicInvariant;

impl Invariant for MonotonicInvariant {
    fn apply(&self, payload: &[u8], state: &mut [u8]) -> Result<(), InvariantError> {
        if payload.len() < 8 || state.len() < 64 {
            return Err(InvariantError::MalformedPayload);
        }

        let proposed = u64::from_le_bytes(payload[0..8].try_into().unwrap());
        let current = u64::from_le_bytes(state[0..8].try_into().unwrap());

        // Monotonic: only accept if proposed >= current
        if proposed < current {
            return Err(InvariantError::Underflow);
        }

        state[0..8].copy_from_slice(&proposed.to_le_bytes());
        Ok(())
    }
}

fn main() {
    // 1. Initialize state
    let initial = MonotonicCounter::new(100);
    let mut cell = StateCell::new();
    cell.as_slice_mut().copy_from_slice(initial.as_bytes());

    let mut kernel = Kernel::with_state(MonotonicInvariant, cell);

    // 2. Increase works
    let fact1: FactId = [1u8; 32];
    let payload1 = 150u64.to_le_bytes();
    kernel
        .admit_raw(&fact1, &[], &payload1)
        .expect("increase to 150");

    // 3. Same value works (idempotent)
    let fact2: FactId = [2u8; 32];
    let payload2 = 150u64.to_le_bytes();
    kernel
        .admit_raw(&fact2, &[fact1], &payload2)
        .expect("stay at 150");

    // 4. Decrease is rejected
    let fact3: FactId = [3u8; 32];
    let payload3 = 100u64.to_le_bytes();
    match kernel.admit_raw(&fact3, &[fact2], &payload3) {
        Err(AdmitError::InvariantViolation) => println!("Decrease rejected (as expected)"),
        _ => panic!("should reject decrease"),
    }

    // 5. Query final state
    let state = kernel.state().cast_ref::<MonotonicCounter>().unwrap();
    println!("Final value: {}", state.value); // 150

    println!("Custom invariant example complete.");
}
