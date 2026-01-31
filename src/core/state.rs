//! StateCell: 64-byte cache-aligned POD. No pointers, no heap.

use zerocopy::{FromBytes, Immutable, IntoBytes, KnownLayout};

/// One cache line. Fits in L1.
pub const STATE_CELL_SIZE: usize = 64;

/// 64-byte state container. Cache-line aligned, zerocopy-compatible.
///
/// Cast to your state struct with `cast_ref()`. Keep it POD.
#[derive(Debug, Clone, Copy)]
#[repr(C, align(64))]
pub struct StateCell {
    data: [u8; STATE_CELL_SIZE],
}

const _: () = {
    assert!(core::mem::size_of::<StateCell>() == 64);
    assert!(core::mem::align_of::<StateCell>() == 64);
};

impl StateCell {
    #[inline(always)]
    pub const fn new() -> Self {
        Self {
            data: [0u8; STATE_CELL_SIZE],
        }
    }

    #[inline(always)]
    pub const fn from_bytes(data: [u8; STATE_CELL_SIZE]) -> Self {
        Self { data }
    }

    #[inline(always)]
    pub fn as_bytes(&self) -> &[u8; STATE_CELL_SIZE] {
        &self.data
    }

    #[inline(always)]
    pub fn as_bytes_mut(&mut self) -> &mut [u8; STATE_CELL_SIZE] {
        &mut self.data
    }

    #[inline(always)]
    pub fn as_slice(&self) -> &[u8] {
        &self.data
    }

    #[inline(always)]
    pub fn as_slice_mut(&mut self) -> &mut [u8] {
        &mut self.data
    }

    #[inline(always)]
    pub fn cast_ref<T>(&self) -> Option<&T>
    where
        T: FromBytes + KnownLayout + Immutable,
    {
        T::ref_from_bytes(&self.data).ok()
    }

    #[inline(always)]
    pub fn cast_mut<T>(&mut self) -> Option<&mut T>
    where
        T: FromBytes + IntoBytes + KnownLayout,
    {
        T::mut_from_bytes(&mut self.data).ok()
    }

    #[inline(always)]
    pub fn write<T>(&mut self, value: &T)
    where
        T: IntoBytes + Immutable,
    {
        let src = value.as_bytes();
        let len = src.len().min(STATE_CELL_SIZE);
        self.data[..len].copy_from_slice(&src[..len]);
    }

    #[inline(always)]
    pub fn zero(&mut self) {
        self.data = [0u8; STATE_CELL_SIZE];
    }
}

impl Default for StateCell {
    #[inline(always)]
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zerocopy::{FromBytes, Immutable, IntoBytes, KnownLayout};

    #[derive(Debug, Clone, Copy, PartialEq, Eq, FromBytes, IntoBytes, KnownLayout, Immutable)]
    #[repr(C)]
    struct TestState {
        balance: i128,
        nonce: u64,
        _pad: [u8; 40],
    }

    #[test]
    fn test_state_cell_cast() {
        let mut cell = StateCell::new();

        {
            let state = cell.cast_mut::<TestState>().unwrap();
            state.balance = 1000;
            state.nonce = 42;
        }

        let state = cell.cast_ref::<TestState>().unwrap();
        assert_eq!(state.balance, 1000);
        assert_eq!(state.nonce, 42);
    }

    #[test]
    fn test_state_cell_size() {
        assert_eq!(core::mem::size_of::<StateCell>(), 64);
        assert_eq!(core::mem::align_of::<StateCell>(), 64);
    }
}
