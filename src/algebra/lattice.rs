//! Lattice primitives. Join = LUB, associative + commutative + idempotent = convergence.

use zerocopy::{FromBytes, Immutable, IntoBytes, KnownLayout};

pub trait JoinSemilattice: Sized {
    fn join(&self, other: &Self) -> Self;
    fn leq(&self, other: &Self) -> bool;
}

pub trait MeetSemilattice: Sized {
    fn meet(&self, other: &Self) -> Self;
}

pub trait BoundedLattice: JoinSemilattice + MeetSemilattice {
    fn bottom() -> Self;
    fn top() -> Self;
}

pub trait LatticeMerge {
    fn merge(&mut self, other: &Self);
    fn dominates(&self, other: &Self) -> bool;
}

/// Max-lattice. The workhorse.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Default)]
#[derive(FromBytes, IntoBytes, KnownLayout, Immutable)]
#[repr(C)]
pub struct MaxU64(pub u64);

impl JoinSemilattice for MaxU64 {
    #[inline(always)]
    fn join(&self, other: &Self) -> Self {
        MaxU64(self.0.max(other.0))
    }

    #[inline(always)]
    fn leq(&self, other: &Self) -> bool {
        self.0 <= other.0
    }
}

impl MeetSemilattice for MaxU64 {
    #[inline(always)]
    fn meet(&self, other: &Self) -> Self {
        MaxU64(self.0.min(other.0))
    }
}

impl BoundedLattice for MaxU64 {
    #[inline(always)]
    fn bottom() -> Self {
        MaxU64(0)
    }

    #[inline(always)]
    fn top() -> Self {
        MaxU64(u64::MAX)
    }
}

impl LatticeMerge for MaxU64 {
    #[inline(always)]
    fn merge(&mut self, other: &Self) {
        self.0 = self.0.max(other.0);
    }

    #[inline(always)]
    fn dominates(&self, other: &Self) -> bool {
        self.0 >= other.0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Default)]
#[derive(FromBytes, IntoBytes, KnownLayout, Immutable)]
#[repr(C)]
pub struct MaxU128(pub u128);

impl JoinSemilattice for MaxU128 {
    #[inline(always)]
    fn join(&self, other: &Self) -> Self {
        MaxU128(self.0.max(other.0))
    }

    #[inline(always)]
    fn leq(&self, other: &Self) -> bool {
        self.0 <= other.0
    }
}

impl MeetSemilattice for MaxU128 {
    #[inline(always)]
    fn meet(&self, other: &Self) -> Self {
        MaxU128(self.0.min(other.0))
    }
}

impl BoundedLattice for MaxU128 {
    fn bottom() -> Self {
        MaxU128(0)
    }

    fn top() -> Self {
        MaxU128(u128::MAX)
    }
}

impl LatticeMerge for MaxU128 {
    #[inline(always)]
    fn merge(&mut self, other: &Self) {
        self.0 = self.0.max(other.0);
    }

    #[inline(always)]
    fn dominates(&self, other: &Self) -> bool {
        self.0 >= other.0
    }
}

/// GSet via 512-bit bitset. Join = OR.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[derive(FromBytes, IntoBytes, KnownLayout, Immutable)]
#[repr(C)]
pub struct GSetLattice {
    pub bits: [u64; 8],
}

impl GSetLattice {
    pub const CAPACITY: usize = 512;

    #[inline(always)]
    pub const fn new() -> Self {
        Self { bits: [0u64; 8] }
    }

    #[inline(always)]
    pub fn insert(&mut self, element: u16) {
        let idx = (element as usize) & 0x1FF;
        let word = idx >> 6;
        let bit = idx & 63;
        self.bits[word] |= 1u64 << bit;
    }

    #[inline(always)]
    pub fn contains(&self, element: u16) -> bool {
        let idx = (element as usize) & 0x1FF;
        let word = idx >> 6;
        let bit = idx & 63;
        (self.bits[word] >> bit) & 1 == 1
    }

    #[inline(always)]
    pub fn cardinality(&self) -> u32 {
        self.bits.iter().map(|w| w.count_ones()).sum()
    }
}

impl JoinSemilattice for GSetLattice {
    #[inline(always)]
    fn join(&self, other: &Self) -> Self {
        Self {
            bits: [
                self.bits[0] | other.bits[0],
                self.bits[1] | other.bits[1],
                self.bits[2] | other.bits[2],
                self.bits[3] | other.bits[3],
                self.bits[4] | other.bits[4],
                self.bits[5] | other.bits[5],
                self.bits[6] | other.bits[6],
                self.bits[7] | other.bits[7],
            ],
        }
    }

    #[inline(always)]
    fn leq(&self, other: &Self) -> bool {
        for i in 0..8 {
            if (self.bits[i] & !other.bits[i]) != 0 {
                return false;
            }
        }
        true
    }
}

impl MeetSemilattice for GSetLattice {
    #[inline(always)]
    fn meet(&self, other: &Self) -> Self {
        Self {
            bits: [
                self.bits[0] & other.bits[0],
                self.bits[1] & other.bits[1],
                self.bits[2] & other.bits[2],
                self.bits[3] & other.bits[3],
                self.bits[4] & other.bits[4],
                self.bits[5] & other.bits[5],
                self.bits[6] & other.bits[6],
                self.bits[7] & other.bits[7],
            ],
        }
    }
}

impl BoundedLattice for GSetLattice {
    fn bottom() -> Self {
        Self::new()
    }

    fn top() -> Self {
        Self {
            bits: [u64::MAX; 8],
        }
    }
}

impl LatticeMerge for GSetLattice {
    #[inline(always)]
    fn merge(&mut self, other: &Self) {
        for i in 0..8 {
            self.bits[i] |= other.bits[i];
        }
    }

    #[inline(always)]
    fn dominates(&self, other: &Self) -> bool {
        other.leq(self)
    }
}

/// PN-Counter: value = positive - negative. Join = component-wise max.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[derive(FromBytes, IntoBytes, KnownLayout, Immutable)]
#[repr(C)]
pub struct PNCounter {
    pub positive: u64,
    pub negative: u64,
}

impl PNCounter {
    #[inline(always)]
    pub const fn new() -> Self {
        Self {
            positive: 0,
            negative: 0,
        }
    }

    #[inline(always)]
    pub const fn with_value(positive: u64, negative: u64) -> Self {
        Self { positive, negative }
    }

    #[inline(always)]
    pub fn increment(&mut self, amount: u64) {
        self.positive = self.positive.saturating_add(amount);
    }

    #[inline(always)]
    pub fn decrement(&mut self, amount: u64) {
        self.negative = self.negative.saturating_add(amount);
    }

    #[inline(always)]
    pub fn value(&self) -> i64 {
        (self.positive as i64).saturating_sub(self.negative as i64)
    }
}

impl JoinSemilattice for PNCounter {
    #[inline(always)]
    fn join(&self, other: &Self) -> Self {
        Self {
            positive: self.positive.max(other.positive),
            negative: self.negative.max(other.negative),
        }
    }

    #[inline(always)]
    fn leq(&self, other: &Self) -> bool {
        self.positive <= other.positive && self.negative <= other.negative
    }
}

impl LatticeMerge for PNCounter {
    #[inline(always)]
    fn merge(&mut self, other: &Self) {
        self.positive = self.positive.max(other.positive);
        self.negative = self.negative.max(other.negative);
    }

    #[inline(always)]
    fn dominates(&self, other: &Self) -> bool {
        self.positive >= other.positive && self.negative >= other.negative
    }
}

/// Lex pair for deterministic tie-breaking.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[derive(FromBytes, IntoBytes, KnownLayout, Immutable)]
#[repr(C)]
pub struct LexPair {
    pub value: u64,
    pub tiebreaker: u64,
}

impl LexPair {
    #[inline(always)]
    pub const fn new(value: u64, tiebreaker: u64) -> Self {
        Self { value, tiebreaker }
    }
}

impl JoinSemilattice for LexPair {
    #[inline(always)]
    fn join(&self, other: &Self) -> Self {
        if self.value > other.value {
            *self
        } else if other.value > self.value {
            *other
        } else if self.tiebreaker >= other.tiebreaker {
            *self
        } else {
            *other
        }
    }

    #[inline(always)]
    fn leq(&self, other: &Self) -> bool {
        self.value < other.value
            || (self.value == other.value && self.tiebreaker <= other.tiebreaker)
    }
}

impl LatticeMerge for LexPair {
    #[inline(always)]
    fn merge(&mut self, other: &Self) {
        *self = self.join(other);
    }

    #[inline(always)]
    fn dominates(&self, other: &Self) -> bool {
        other.leq(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_max_u64_lattice_laws() {
        let a = MaxU64(5);
        let b = MaxU64(10);
        let c = MaxU64(7);
        assert_eq!(a.join(&b), b.join(&a));
        assert_eq!(a.join(&b).join(&c), a.join(&b.join(&c)));
        assert_eq!(a.join(&a), a);
        assert!(a.leq(&b));
        assert!(!b.leq(&a));
    }

    #[test]
    fn test_gset_lattice_laws() {
        let mut a = GSetLattice::new();
        let mut b = GSetLattice::new();
        a.insert(1);
        a.insert(5);
        b.insert(3);
        b.insert(5);
        let joined = a.join(&b);
        assert!(joined.contains(1));
        assert!(joined.contains(3));
        assert!(joined.contains(5));
        assert_eq!(a.join(&b), b.join(&a));
        assert_eq!(a.join(&a), a);
    }

    #[test]
    fn test_pn_counter() {
        let mut c1 = PNCounter::new();
        let mut c2 = PNCounter::new();
        c1.increment(10);
        c2.increment(5);
        c2.decrement(3);
        c1.merge(&c2);
        assert_eq!(c1.value(), 7);
    }

    #[test]
    fn test_lex_pair_deterministic() {
        let a = LexPair::new(10, 1);
        let b = LexPair::new(10, 2);
        let joined = a.join(&b);
        assert_eq!(joined.tiebreaker, 2);
        assert_eq!(a.join(&b), b.join(&a));
    }
}
