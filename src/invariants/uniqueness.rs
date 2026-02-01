use crate::core::invariant::{AlgebraicClass, Invariant, InvariantError};
use zerocopy::{FromBytes, Immutable, IntoBytes, KnownLayout};

pub const UNIQUENESS_BITS: usize = 512;
pub const UNIQUENESS_WORDS: usize = 8;

#[derive(Debug, Clone, Copy, FromBytes, IntoBytes, KnownLayout, Immutable, PartialEq, Eq)]
#[repr(C)]
pub struct UniquenessState {
    pub bits: [u64; UNIQUENESS_WORDS],
}

const _: () = {
    assert!(core::mem::size_of::<UniquenessState>() == 64);
};

impl UniquenessState {
    #[inline(always)]
    pub const fn new() -> Self {
        Self {
            bits: [0u64; UNIQUENESS_WORDS],
        }
    }

    #[inline(always)]
    pub fn is_set(&self, index: u16) -> bool {
        let idx = (index as usize) & 0x1FF;
        let word = idx >> 6;
        let bit = idx & 63;
        (self.bits[word] >> bit) & 1 == 1
    }

    #[inline(always)]
    pub fn set(&mut self, index: u16) {
        let idx = (index as usize) & 0x1FF;
        let word = idx >> 6;
        let bit = idx & 63;
        self.bits[word] |= 1u64 << bit;
    }

    #[inline(always)]
    pub fn popcount(&self) -> u32 {
        self.bits[0].count_ones()
            + self.bits[1].count_ones()
            + self.bits[2].count_ones()
            + self.bits[3].count_ones()
            + self.bits[4].count_ones()
            + self.bits[5].count_ones()
            + self.bits[6].count_ones()
            + self.bits[7].count_ones()
    }
}

impl Default for UniquenessState {
    #[inline(always)]
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug, Clone, Copy, FromBytes, IntoBytes, KnownLayout, Immutable)]
#[repr(C)]
pub struct UniquenessPayload {
    pub element_id: u16,
    _pad: [u8; 14],
}

impl UniquenessPayload {
    #[inline(always)]
    pub const fn new(element_id: u16) -> Self {
        Self {
            element_id,
            _pad: [0u8; 14],
        }
    }
}

#[derive(Debug, Clone, Copy, Default)]
pub struct UniquenessInvariant;

impl UniquenessInvariant {
    #[inline(always)]
    pub const fn new() -> Self {
        Self
    }
}

impl Invariant for UniquenessInvariant {
    #[inline(always)]
    fn apply(&self, payload: &[u8], state: &mut [u8]) -> Result<(), InvariantError> {
        if payload.len() < 2 || state.len() < 64 {
            return Err(InvariantError::MalformedPayload);
        }

        let element_id = u16::from_le_bytes([payload[0], payload[1]]);
        let idx = (element_id as usize) & 0x1FF;
        let word = idx >> 6;
        let bit = idx & 63;

        let word_offset = word * 8;
        let current_word = u64::from_le_bytes([
            state[word_offset],
            state[word_offset + 1],
            state[word_offset + 2],
            state[word_offset + 3],
            state[word_offset + 4],
            state[word_offset + 5],
            state[word_offset + 6],
            state[word_offset + 7],
        ]);

        let is_set = (current_word >> bit) & 1;
        if is_set == 1 {
            return Err(InvariantError::DuplicateElement);
        }

        let new_word = current_word | (1u64 << bit);
        let new_bytes = new_word.to_le_bytes();
        state[word_offset..word_offset + 8].copy_from_slice(&new_bytes);

        Ok(())
    }

    #[inline(always)]
    fn algebraic_class(&self) -> Option<AlgebraicClass> {
        Some(AlgebraicClass::CommutativeIdempotent)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_state() -> [u8; 64] {
        [0u8; 64]
    }

    fn make_payload(element_id: u16) -> [u8; 16] {
        let payload = UniquenessPayload::new(element_id);
        let mut buf = [0u8; 16];
        buf.copy_from_slice(payload.as_bytes());
        buf
    }

    fn is_bit_set(state: &[u8], index: u16) -> bool {
        let idx = (index as usize) & 0x1FF;
        let word = idx >> 6;
        let bit = idx & 63;
        let word_offset = word * 8;
        let current_word = u64::from_le_bytes([
            state[word_offset],
            state[word_offset + 1],
            state[word_offset + 2],
            state[word_offset + 3],
            state[word_offset + 4],
            state[word_offset + 5],
            state[word_offset + 6],
            state[word_offset + 7],
        ]);
        (current_word >> bit) & 1 == 1
    }

    #[test]
    fn test_uniqueness_first_use() {
        let invariant = UniquenessInvariant::new();
        let mut state = make_state();
        let payload = make_payload(42);

        let result = invariant.apply(&payload, &mut state);
        assert!(result.is_ok());
        assert!(is_bit_set(&state, 42));
    }

    #[test]
    fn test_uniqueness_duplicate() {
        let invariant = UniquenessInvariant::new();
        let mut state = make_state();
        let payload = make_payload(42);

        invariant.apply(&payload, &mut state).unwrap();

        let result = invariant.apply(&payload, &mut state);
        assert_eq!(result, Err(InvariantError::DuplicateElement));
    }

    #[test]
    fn test_uniqueness_different_ids() {
        let invariant = UniquenessInvariant::new();
        let mut state = make_state();

        let payload1 = make_payload(10);
        let payload2 = make_payload(20);

        assert!(invariant.apply(&payload1, &mut state).is_ok());
        assert!(invariant.apply(&payload2, &mut state).is_ok());

        assert!(is_bit_set(&state, 10));
        assert!(is_bit_set(&state, 20));
    }
}
