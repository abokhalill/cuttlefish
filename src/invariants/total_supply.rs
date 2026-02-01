use crate::core::invariant::{AlgebraicClass, Invariant, InvariantError};
use zerocopy::{FromBytes, Immutable, IntoBytes, KnownLayout};

#[derive(Debug, Clone, Copy, FromBytes, IntoBytes, KnownLayout, Immutable)]
#[repr(C)]
pub struct ConservationState {
    pub balance: i128,
    pub min: i128,
    pub max: i128,
    _pad: [u8; 16],
}

const _: () = {
    assert!(core::mem::size_of::<ConservationState>() == 64);
};

impl ConservationState {
    #[inline(always)]
    pub const fn new(initial: i128, min: i128, max: i128) -> Self {
        Self {
            balance: initial,
            min,
            max,
            _pad: [0u8; 16],
        }
    }
}

impl Default for ConservationState {
    #[inline(always)]
    fn default() -> Self {
        Self::new(0, i128::MIN, i128::MAX)
    }
}

#[derive(Debug, Clone, Copy, FromBytes, IntoBytes, KnownLayout, Immutable)]
#[repr(C)]
pub struct DeltaPayload {
    pub delta: i128,
}

#[derive(Debug, Clone, Copy, Default)]
pub struct TotalSupplyInvariant;

impl TotalSupplyInvariant {
    #[inline(always)]
    pub const fn new() -> Self {
        Self
    }
}

impl Invariant for TotalSupplyInvariant {
    #[inline(always)]
    fn apply(&self, payload: &[u8], state: &mut [u8]) -> Result<(), InvariantError> {
        if payload.len() < 16 || state.len() < 64 {
            return Err(InvariantError::MalformedPayload);
        }

        let delta = i128::from_le_bytes([
            payload[0],
            payload[1],
            payload[2],
            payload[3],
            payload[4],
            payload[5],
            payload[6],
            payload[7],
            payload[8],
            payload[9],
            payload[10],
            payload[11],
            payload[12],
            payload[13],
            payload[14],
            payload[15],
        ]);

        let balance = i128::from_le_bytes([
            state[0], state[1], state[2], state[3], state[4], state[5], state[6], state[7],
            state[8], state[9], state[10], state[11], state[12], state[13], state[14], state[15],
        ]);

        let min = i128::from_le_bytes([
            state[16], state[17], state[18], state[19], state[20], state[21], state[22], state[23],
            state[24], state[25], state[26], state[27], state[28], state[29], state[30], state[31],
        ]);

        let max = i128::from_le_bytes([
            state[32], state[33], state[34], state[35], state[36], state[37], state[38], state[39],
            state[40], state[41], state[42], state[43], state[44], state[45], state[46], state[47],
        ]);

        let new_balance = balance.wrapping_add(delta);

        let underflow = (new_balance < min) as u8;
        let overflow = (new_balance > max) as u8;

        let error_code = underflow * (InvariantError::Underflow as u8)
            + overflow * (InvariantError::Overflow as u8);

        if error_code != 0 {
            return Err(unsafe { core::mem::transmute::<u8, InvariantError>(error_code) });
        }

        let new_bytes = new_balance.to_le_bytes();
        state[0..16].copy_from_slice(&new_bytes);

        Ok(())
    }

    #[inline(always)]
    fn algebraic_class(&self) -> Option<AlgebraicClass> {
        Some(AlgebraicClass::Group)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[repr(C, align(16))]
    struct AlignedState([u8; 64]);

    #[repr(C, align(16))]
    struct AlignedDelta([u8; 16]);

    fn make_state(balance: i128, min: i128, max: i128) -> AlignedState {
        let state = ConservationState::new(balance, min, max);
        let mut buf = AlignedState([0u8; 64]);
        buf.0.copy_from_slice(state.as_bytes());
        buf
    }

    fn make_delta(delta: i128) -> AlignedDelta {
        let payload = DeltaPayload { delta };
        let mut buf = AlignedDelta([0u8; 16]);
        buf.0.copy_from_slice(payload.as_bytes());
        buf
    }

    #[test]
    fn test_conservation_add() {
        let invariant = TotalSupplyInvariant::new();
        let mut state = make_state(100, 0, 1000);
        let payload = make_delta(50);

        let result = invariant.apply(&payload.0, &mut state.0);
        assert!(result.is_ok());

        let s = ConservationState::ref_from_bytes(&state.0).unwrap();
        assert_eq!(s.balance, 150);
    }

    #[test]
    fn test_conservation_subtract() {
        let invariant = TotalSupplyInvariant::new();
        let mut state = make_state(100, 0, 1000);
        let payload = make_delta(-50);

        let result = invariant.apply(&payload.0, &mut state.0);
        assert!(result.is_ok());

        let s = ConservationState::ref_from_bytes(&state.0).unwrap();
        assert_eq!(s.balance, 50);
    }

    #[test]
    fn test_conservation_underflow() {
        let invariant = TotalSupplyInvariant::new();
        let mut state = make_state(100, 0, 1000);
        let payload = make_delta(-200);

        let result = invariant.apply(&payload.0, &mut state.0);
        assert_eq!(result, Err(InvariantError::Underflow));

        let s = ConservationState::ref_from_bytes(&state.0).unwrap();
        assert_eq!(s.balance, 100);
    }

    #[test]
    fn test_conservation_overflow() {
        let invariant = TotalSupplyInvariant::new();
        let mut state = make_state(900, 0, 1000);
        let payload = make_delta(200);

        let result = invariant.apply(&payload.0, &mut state.0);
        assert_eq!(result, Err(InvariantError::Overflow));

        let s = ConservationState::ref_from_bytes(&state.0).unwrap();
        assert_eq!(s.balance, 900);
    }
}
