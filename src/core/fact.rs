//! Fact: immutable, content-addressed state transition record.
//! Layout: [FactHeader:64][deps:N*32][payload:M]

use zerocopy::{FromBytes, Immutable, IntoBytes, KnownLayout};
use super::topology::FactId;

pub const MAX_DEPS: usize = 8;

#[derive(Debug, Clone, Copy, FromBytes, IntoBytes, KnownLayout, Immutable)]
#[repr(C, align(64))]
pub struct FactHeader {
    pub id: FactId,
    pub deps_count: u32,
    pub payload_len: u32,
    _pad: [u8; 24],
}

const _: () = {
    assert!(core::mem::size_of::<FactHeader>() == 64);
    assert!(core::mem::align_of::<FactHeader>() == 64);
};

impl FactHeader {
    #[inline(always)]
    pub const fn new(id: FactId, deps_count: u32, payload_len: u32) -> Self {
        Self {
            id,
            deps_count,
            payload_len,
            _pad: [0u8; 24],
        }
    }

    #[inline(always)]
    pub const fn deps_size(&self) -> usize {
        (self.deps_count as usize) * 32
    }

    #[inline(always)]
    pub const fn total_size(&self) -> usize {
        64 + self.deps_size() + (self.payload_len as usize)
    }
}

#[derive(Debug)]
pub struct Fact<'a> {
    header: &'a FactHeader,
    deps: &'a [FactId],
    payload: &'a [u8],
}

impl<'a> Fact<'a> {
    #[inline]
    pub fn from_bytes(buffer: &'a [u8]) -> Option<Self> {
        if buffer.len() < 64 {
            return None;
        }

        let header = FactHeader::ref_from_bytes(&buffer[..64]).ok()?;

        let deps_end = 64 + header.deps_size();
        let total = header.total_size();

        if buffer.len() < total {
            return None;
        }

        let deps_bytes = &buffer[64..deps_end];
        let deps: &[FactId] = if header.deps_count == 0 {
            &[]
        } else {
            let (prefix, deps_slice, _suffix) = unsafe { deps_bytes.align_to::<FactId>() };
            if !prefix.is_empty() || deps_slice.len() != header.deps_count as usize {
                return None;
            }
            deps_slice
        };

        let payload = &buffer[deps_end..total];

        Some(Self {
            header,
            deps,
            payload,
        })
    }

    #[inline(always)]
    pub const fn header(&self) -> &FactHeader {
        self.header
    }

    #[inline(always)]
    pub const fn id(&self) -> &FactId {
        &self.header.id
    }

    #[inline(always)]
    pub const fn deps(&self) -> &[FactId] {
        self.deps
    }

    #[inline(always)]
    pub const fn payload(&self) -> &[u8] {
        self.payload
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_header_size_and_alignment() {
        assert_eq!(core::mem::size_of::<FactHeader>(), 64);
        assert_eq!(core::mem::align_of::<FactHeader>(), 64);
    }

    #[test]
    fn test_fact_parsing() {
        #[repr(C, align(64))]
        struct AlignedBuffer([u8; 128]);

        let mut buf = AlignedBuffer([0u8; 128]);
        let header = FactHeader::new([1u8; 32], 0, 16);
        buf.0[..64].copy_from_slice(header.as_bytes());
        buf.0[64..80].copy_from_slice(&[0xAB; 16]);

        let fact = Fact::from_bytes(&buf.0[..80]).expect("parse failed");
        assert_eq!(fact.id(), &[1u8; 32]);
        assert_eq!(fact.deps().len(), 0);
        assert_eq!(fact.payload(), &[0xAB; 16]);
    }
}
