//! Causal topology. BFVC for speed, ExactIndex for correctness.

use zerocopy::{FromBytes, Immutable, IntoBytes, KnownLayout};

pub type FactId = [u8; 32];

/// 512-bit Bloom filter. 3-hash, MurmurHash3 finalizer. Escalate at 40% saturation.
#[derive(Debug, Clone, Copy, FromBytes, IntoBytes, KnownLayout, Immutable, PartialEq, Eq)]
#[repr(C, align(64))]
pub struct CausalClock {
    bits: [u64; 8],
}

const _: () = {
    assert!(core::mem::size_of::<CausalClock>() == 64);
    assert!(core::mem::align_of::<CausalClock>() == 64);
};

impl CausalClock {
    pub const BITS: usize = 512;

    #[inline(always)]
    pub const fn new() -> Self {
        Self { bits: [0u64; 8] }
    }

    #[inline(always)]
    fn hash_to_indices(fact_id: &FactId) -> (usize, usize, usize) {
        let h0 = Self::mix64(u64::from_le_bytes([
            fact_id[0], fact_id[1], fact_id[2], fact_id[3],
            fact_id[4], fact_id[5], fact_id[6], fact_id[7],
        ]));
        let h1 = Self::mix64(u64::from_le_bytes([
            fact_id[8], fact_id[9], fact_id[10], fact_id[11],
            fact_id[12], fact_id[13], fact_id[14], fact_id[15],
        ]));
        let h2 = Self::mix64(u64::from_le_bytes([
            fact_id[16], fact_id[17], fact_id[18], fact_id[19],
            fact_id[20], fact_id[21], fact_id[22], fact_id[23],
        ]));

        let idx0 = (h0 as usize) & 0x1FF;
        let idx1 = (h1 as usize) & 0x1FF;
        let idx2 = (h2 as usize) & 0x1FF;

        (idx0, idx1, idx2)
    }

    #[inline(always)]
    const fn mix64(mut x: u64) -> u64 {
        x ^= x >> 33;
        x = x.wrapping_mul(0xff51afd7ed558ccd);
        x ^= x >> 33;
        x = x.wrapping_mul(0xc4ceb9fe1a85ec53);
        x ^= x >> 33;
        x
    }

    #[inline(always)]
    pub fn observe(&mut self, fact_id: &FactId) {
        let (idx0, idx1, idx2) = Self::hash_to_indices(fact_id);

        let word0 = idx0 >> 6;
        let bit0 = idx0 & 63;
        self.bits[word0] |= 1u64 << bit0;

        let word1 = idx1 >> 6;
        let bit1 = idx1 & 63;
        self.bits[word1] |= 1u64 << bit1;

        let word2 = idx2 >> 6;
        let bit2 = idx2 & 63;
        self.bits[word2] |= 1u64 << bit2;
    }

    #[inline(always)]
    pub fn might_contain(&self, fact_id: &FactId) -> bool {
        let (idx0, idx1, idx2) = Self::hash_to_indices(fact_id);

        let word0 = idx0 >> 6;
        let bit0 = idx0 & 63;
        let has0 = (self.bits[word0] >> bit0) & 1;

        let word1 = idx1 >> 6;
        let bit1 = idx1 & 63;
        let has1 = (self.bits[word1] >> bit1) & 1;

        let word2 = idx2 >> 6;
        let bit2 = idx2 & 63;
        let has2 = (self.bits[word2] >> bit2) & 1;

        (has0 & has1 & has2) == 1
    }

    /// Branchless superset check.
    #[inline(always)]
    pub fn dominates(&self, other: &Self) -> bool {
        let missing = (other.bits[0] & !self.bits[0])
            | (other.bits[1] & !self.bits[1])
            | (other.bits[2] & !self.bits[2])
            | (other.bits[3] & !self.bits[3])
            | (other.bits[4] & !self.bits[4])
            | (other.bits[5] & !self.bits[5])
            | (other.bits[6] & !self.bits[6])
            | (other.bits[7] & !self.bits[7]);
        missing == 0
    }

    #[inline(always)]
    pub fn merge(&mut self, other: &Self) {
        self.bits[0] |= other.bits[0];
        self.bits[1] |= other.bits[1];
        self.bits[2] |= other.bits[2];
        self.bits[3] |= other.bits[3];
        self.bits[4] |= other.bits[4];
        self.bits[5] |= other.bits[5];
        self.bits[6] |= other.bits[6];
        self.bits[7] |= other.bits[7];
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

    #[inline(always)]
    pub fn saturation(&self) -> f32 {
        (self.popcount() as f32) / (Self::BITS as f32)
    }

    #[inline(always)]
    pub const fn as_bits(&self) -> &[u64; 8] {
        &self.bits
    }
}

impl Default for CausalClock {
    #[inline(always)]
    fn default() -> Self {
        Self::new()
    }
}

pub const ESCALATION_THRESHOLD: f32 = 0.4;

pub const PRECISE_CLOCK_CAPACITY: usize = 16;

/// Exact tracking, FIFO eviction. O(n) but n ≤ 16.
#[derive(Debug, Clone)]
#[repr(C, align(64))]
pub struct PreciseClock {
    ancestors: [FactId; PRECISE_CLOCK_CAPACITY],
    count: u8,
    _pad: [u8; 31],
}

const _: () = {
    assert!(core::mem::size_of::<PreciseClock>() == 576);
    assert!(core::mem::align_of::<PreciseClock>() == 64);
};

impl PreciseClock {
    #[inline(always)]
    pub const fn new() -> Self {
        Self {
            ancestors: [[0u8; 32]; PRECISE_CLOCK_CAPACITY],
            count: 0,
            _pad: [0u8; 31],
        }
    }

    #[inline]
    pub fn observe(&mut self, fact_id: &FactId) {
        if self.count as usize >= PRECISE_CLOCK_CAPACITY {
            for i in 0..(PRECISE_CLOCK_CAPACITY - 1) {
                self.ancestors[i] = self.ancestors[i + 1];
            }
            self.ancestors[PRECISE_CLOCK_CAPACITY - 1] = *fact_id;
        } else {
            self.ancestors[self.count as usize] = *fact_id;
            self.count += 1;
        }
    }

    #[inline]
    pub fn contains_all(&self, deps: &[FactId]) -> bool {
        for dep in deps {
            if !self.contains(dep) {
                return false;
            }
        }
        true
    }

    #[inline]
    pub fn contains(&self, fact_id: &FactId) -> bool {
        let count = self.count as usize;
        for i in 0..count {
            if &self.ancestors[i] == fact_id {
                return true;
            }
        }
        false
    }

    #[inline(always)]
    pub fn len(&self) -> usize {
        self.count as usize
    }

    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.count == 0
    }

    #[inline(always)]
    pub fn is_full(&self) -> bool {
        self.count as usize >= PRECISE_CLOCK_CAPACITY
    }

    #[inline(always)]
    pub fn ancestors(&self) -> &[FactId] {
        &self.ancestors[..self.count as usize]
    }

    #[inline(always)]
    pub fn clear(&mut self) {
        self.count = 0;
    }

    #[inline]
    pub fn import_from_slice(&mut self, facts: &[FactId]) {
        self.count = 0;
        let limit = facts.len().min(PRECISE_CLOCK_CAPACITY);
        for i in 0..limit {
            self.ancestors[i] = facts[i];
        }
        self.count = limit as u8;
    }
}

impl Default for PreciseClock {
    #[inline(always)]
    fn default() -> Self {
        Self::new()
    }
}

pub const EXACT_INDEX_CAPACITY: usize = 1024;
const EXACT_INDEX_MASK: usize = EXACT_INDEX_CAPACITY - 1;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum SlotState {
    Empty = 0,
    Occupied = 1,
    Tombstone = 2,
}

#[derive(Debug, Clone, Copy)]
#[repr(C)]
pub struct IndexSlot {
    pub fact_id: FactId,
    pub state: SlotState,
    pub psl: u8,  // Probe Sequence Length for Robin Hood
    _pad: [u8; 2],
}

const _: () = {
    assert!(core::mem::size_of::<IndexSlot>() == 36);
};

impl IndexSlot {
    #[inline(always)]
    pub const fn empty() -> Self {
        Self {
            fact_id: [0u8; 32],
            state: SlotState::Empty,
            psl: 0,
            _pad: [0u8; 2],
        }
    }

    #[inline(always)]
    pub const fn is_empty(&self) -> bool {
        matches!(self.state, SlotState::Empty)
    }

    #[inline(always)]
    pub const fn is_occupied(&self) -> bool {
        matches!(self.state, SlotState::Occupied)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CausalHorizonExceeded;

/// Robin Hood hash set. 1024 slots. Ground truth for causal deps.
#[derive(Debug, Clone)]
#[repr(C, align(64))]
pub struct ExactCausalIndex {
    slots: [IndexSlot; EXACT_INDEX_CAPACITY],
    count: u32,
    oldest_sequence: u64,
    _pad: [u8; 44],
}

const _: () = { assert!(core::mem::align_of::<ExactCausalIndex>() == 64); };

impl ExactCausalIndex {
    pub fn new() -> Self {
        Self {
            slots: [IndexSlot::empty(); EXACT_INDEX_CAPACITY],
            count: 0,
            oldest_sequence: 0,
            _pad: [0u8; 44],
        }
    }

    #[inline(always)]
    fn hash_to_index(fact_id: &FactId) -> usize {
        let h = u64::from_le_bytes([
            fact_id[0], fact_id[1], fact_id[2], fact_id[3],
            fact_id[4], fact_id[5], fact_id[6], fact_id[7],
        ]);
        let mixed = CausalClock::mix64(h);
        (mixed as usize) & EXACT_INDEX_MASK
    }

    #[inline]
    pub fn insert(&mut self, fact_id: &FactId) -> bool {
        if self.contains(fact_id) {
            return false;
        }

        if self.count as usize >= (EXACT_INDEX_CAPACITY * 3 / 4) {
            self.compact();
        }

        let mut idx = Self::hash_to_index(fact_id);
        let mut current_fact = *fact_id;
        let mut current_psl: u8 = 0;

        loop {
            let slot = &mut self.slots[idx];

            if slot.is_empty() || slot.state == SlotState::Tombstone {
                slot.fact_id = current_fact;
                slot.state = SlotState::Occupied;
                slot.psl = current_psl;
                self.count += 1;
                return true;
            }

            if current_psl > slot.psl {
                core::mem::swap(&mut current_fact, &mut slot.fact_id);
                core::mem::swap(&mut current_psl, &mut slot.psl);
            }

            idx = (idx + 1) & EXACT_INDEX_MASK;
            current_psl = current_psl.saturating_add(1);

            if current_psl > 128 {
                return false;
            }
        }
    }

    #[inline]
    pub fn contains(&self, fact_id: &FactId) -> bool {
        let mut idx = Self::hash_to_index(fact_id);
        let mut psl: u8 = 0;

        loop {
            let slot = &self.slots[idx];

            if slot.is_empty() {
                return false;
            }

            if slot.is_occupied() && &slot.fact_id == fact_id {
                return true;
            }

            if psl > slot.psl {
                return false;
            }

            idx = (idx + 1) & EXACT_INDEX_MASK;
            psl = psl.saturating_add(1);

            if psl > 128 {
                return false;
            }
        }
    }

    #[inline]
    pub fn contains_all(&self, deps: &[FactId]) -> Result<(), CausalHorizonExceeded> {
        for dep in deps {
            if !self.contains(dep) {
                return Err(CausalHorizonExceeded);
            }
        }
        Ok(())
    }

    #[inline]
    #[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
    pub fn contains_simd(&self, fact_id: &FactId) -> bool {
        use core::arch::x86_64::*;

        let mut idx = Self::hash_to_index(fact_id);
        let mut psl: u8 = 0;

        let target = unsafe { _mm256_loadu_si256(fact_id.as_ptr() as *const __m256i) };

        loop {
            if idx + 4 <= EXACT_INDEX_CAPACITY {
                let slot0 = &self.slots[idx];
                let slot1 = &self.slots[idx + 1];
                let slot2 = &self.slots[idx + 2];
                let slot3 = &self.slots[idx + 3];

                if slot0.is_empty() {
                    return false;
                }

                if slot0.is_occupied() {
                    let candidate = unsafe {
                        _mm256_loadu_si256(slot0.fact_id.as_ptr() as *const __m256i)
                    };
                    let cmp = unsafe { _mm256_cmpeq_epi8(target, candidate) };
                    let mask = unsafe { _mm256_movemask_epi8(cmp) };
                    if mask == -1i32 {
                        return true;
                    }
                }

                if psl > slot0.psl {
                    return false;
                }

                if slot1.is_occupied() {
                    let candidate = unsafe {
                        _mm256_loadu_si256(slot1.fact_id.as_ptr() as *const __m256i)
                    };
                    let cmp = unsafe { _mm256_cmpeq_epi8(target, candidate) };
                    if unsafe { _mm256_movemask_epi8(cmp) } == -1i32 {
                        return true;
                    }
                } else if slot1.is_empty() {
                    return false;
                }

                if slot2.is_occupied() {
                    let candidate = unsafe {
                        _mm256_loadu_si256(slot2.fact_id.as_ptr() as *const __m256i)
                    };
                    let cmp = unsafe { _mm256_cmpeq_epi8(target, candidate) };
                    if unsafe { _mm256_movemask_epi8(cmp) } == -1i32 {
                        return true;
                    }
                } else if slot2.is_empty() {
                    return false;
                }

                if slot3.is_occupied() {
                    let candidate = unsafe {
                        _mm256_loadu_si256(slot3.fact_id.as_ptr() as *const __m256i)
                    };
                    let cmp = unsafe { _mm256_cmpeq_epi8(target, candidate) };
                    if unsafe { _mm256_movemask_epi8(cmp) } == -1i32 {
                        return true;
                    }
                } else if slot3.is_empty() {
                    return false;
                }

                idx = (idx + 4) & EXACT_INDEX_MASK;
                psl = psl.saturating_add(4);
            } else {
                return self.contains_scalar_from(fact_id, idx, psl);
            }

            if psl > 128 {
                return false;
            }
        }
    }

    #[inline]
    fn contains_scalar_from(&self, fact_id: &FactId, start_idx: usize, start_psl: u8) -> bool {
        let mut idx = start_idx;
        let mut psl = start_psl;

        loop {
            let slot = &self.slots[idx];

            if slot.is_empty() {
                return false;
            }

            if slot.is_occupied() && &slot.fact_id == fact_id {
                return true;
            }

            if psl > slot.psl {
                return false;
            }

            idx = (idx + 1) & EXACT_INDEX_MASK;
            psl = psl.saturating_add(1);

            if psl > 128 {
                return false;
            }
        }
    }

    /// SIMD contains - scalar fallback for non-x86_64 or non-AVX2.
    #[inline]
    #[cfg(not(all(target_arch = "x86_64", target_feature = "avx2")))]
    pub fn contains_simd(&self, fact_id: &FactId) -> bool {
        self.contains(fact_id)
    }

    /// Check all dependencies using SIMD-accelerated lookup.
    #[inline]
    pub fn contains_all_simd(&self, deps: &[FactId]) -> Result<(), CausalHorizonExceeded> {
        for dep in deps {
            if !self.contains_simd(dep) {
                return Err(CausalHorizonExceeded);
            }
        }
        Ok(())
    }

    /// Observe a fact (insert it into the index).
    #[inline(always)]
    pub fn observe(&mut self, fact_id: &FactId) {
        self.insert(fact_id);
    }

    /// Number of facts in the index.
    #[inline(always)]
    pub fn len(&self) -> usize {
        self.count as usize
    }

    /// Check if empty.
    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.count == 0
    }

    /// Load factor (0.0 to 1.0).
    #[inline(always)]
    pub fn load_factor(&self) -> f32 {
        (self.count as f32) / (EXACT_INDEX_CAPACITY as f32)
    }

    /// Compact the table by removing tombstones and rehashing.
    /// This is called when load factor exceeds threshold.
    fn compact(&mut self) {
        // Collect all occupied entries
        let mut entries: [Option<FactId>; EXACT_INDEX_CAPACITY] = [None; EXACT_INDEX_CAPACITY];
        let mut entry_count = 0usize;

        for slot in &self.slots {
            if slot.is_occupied() {
                entries[entry_count] = Some(slot.fact_id);
                entry_count += 1;
            }
        }

        // If still too full, evict oldest 25% (FIFO approximation via slot order)
        let target_count = EXACT_INDEX_CAPACITY / 2;
        let keep_count = if entry_count > target_count {
            target_count
        } else {
            entry_count
        };

        // Clear and reinsert (keeping most recent entries)
        self.slots = [IndexSlot::empty(); EXACT_INDEX_CAPACITY];
        self.count = 0;

        let skip = entry_count.saturating_sub(keep_count);
        for i in skip..entry_count {
            if let Some(fact_id) = entries[i] {
                self.insert(&fact_id);
            }
        }

        self.oldest_sequence = self.oldest_sequence.saturating_add(skip as u64);
    }

    /// Clear the entire index.
    pub fn clear(&mut self) {
        self.slots = [IndexSlot::empty(); EXACT_INDEX_CAPACITY];
        self.count = 0;
    }
}

impl Default for ExactCausalIndex {
    fn default() -> Self {
        Self::new()
    }
}

/// Deterministic conflict resolution: lexicographic "lowest hash wins".
/// All nodes resolve concurrent conflicts identically without coordination.
#[inline(always)]
pub fn resolve_conflict(a: &FactId, b: &FactId) -> core::cmp::Ordering {
    for i in 0..32 {
        match a[i].cmp(&b[i]) {
            core::cmp::Ordering::Equal => continue,
            other => return other,
        }
    }
    core::cmp::Ordering::Equal
}

#[inline(always)]
pub fn wins_conflict(a: &FactId, b: &FactId) -> bool {
    resolve_conflict(a, b) == core::cmp::Ordering::Less
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_causal_clock_size() {
        assert_eq!(core::mem::size_of::<CausalClock>(), 64);
        assert_eq!(core::mem::align_of::<CausalClock>(), 64);
    }

    #[test]
    fn test_observe_and_contain() {
        let mut clock = CausalClock::new();
        let fact_id: FactId = [0xAB; 32];

        assert!(!clock.might_contain(&fact_id));
        clock.observe(&fact_id);
        assert!(clock.might_contain(&fact_id));
    }

    #[test]
    fn test_dominates() {
        let mut clock_a = CausalClock::new();
        let mut clock_b = CausalClock::new();

        let fact1: FactId = [1u8; 32];
        let fact2: FactId = [2u8; 32];

        clock_a.observe(&fact1);
        clock_a.observe(&fact2);

        clock_b.observe(&fact1);

        assert!(clock_a.dominates(&clock_b));
        assert!(!clock_b.dominates(&clock_a));
    }

    #[test]
    fn test_saturation() {
        let clock = CausalClock::new();
        assert_eq!(clock.saturation(), 0.0);

        let mut clock2 = CausalClock::new();
        for i in 0..100 {
            let mut fact_id = [0u8; 32];
            fact_id[0] = i;
            clock2.observe(&fact_id);
        }
        assert!(clock2.saturation() > 0.0);
        assert!(clock2.saturation() < 1.0);
    }

    #[test]
    fn test_merge() {
        let mut clock_a = CausalClock::new();
        let mut clock_b = CausalClock::new();

        let fact1: FactId = [1u8; 32];
        let fact2: FactId = [2u8; 32];

        clock_a.observe(&fact1);
        clock_b.observe(&fact2);

        clock_a.merge(&clock_b);

        assert!(clock_a.might_contain(&fact1));
        assert!(clock_a.might_contain(&fact2));
    }

    #[test]
    fn test_precise_clock_size() {
        assert_eq!(core::mem::size_of::<PreciseClock>(), 576);
        assert_eq!(core::mem::align_of::<PreciseClock>(), 64);
    }

    #[test]
    fn test_precise_clock_observe() {
        let mut clock = PreciseClock::new();
        let fact1: FactId = [1u8; 32];
        let fact2: FactId = [2u8; 32];

        assert!(clock.is_empty());
        clock.observe(&fact1);
        assert_eq!(clock.len(), 1);
        assert!(clock.contains(&fact1));

        clock.observe(&fact2);
        assert_eq!(clock.len(), 2);
        assert!(clock.contains(&fact2));
    }

    #[test]
    fn test_precise_clock_contains_all() {
        let mut clock = PreciseClock::new();
        let facts: [FactId; 4] = [[1u8; 32], [2u8; 32], [3u8; 32], [4u8; 32]];

        for f in &facts {
            clock.observe(f);
        }

        assert!(clock.contains_all(&facts[..2]));
        assert!(clock.contains_all(&facts));

        let unknown: FactId = [99u8; 32];
        assert!(!clock.contains_all(&[unknown]));
    }

    #[test]
    fn test_precise_clock_eviction() {
        let mut clock = PreciseClock::new();

        // Fill to capacity
        for i in 0..PRECISE_CLOCK_CAPACITY {
            let mut fact_id = [0u8; 32];
            fact_id[0] = i as u8;
            clock.observe(&fact_id);
        }

        assert!(clock.is_full());
        let first: FactId = [0u8; 32];
        assert!(clock.contains(&first));

        // Add one more - should evict first
        let new_fact: FactId = [0xFF; 32];
        clock.observe(&new_fact);

        assert!(clock.is_full());
        assert!(!clock.contains(&first)); // Evicted
        assert!(clock.contains(&new_fact));
    }

    #[test]
    fn test_conflict_resolution() {
        let low: FactId = [0x00; 32];
        let high: FactId = [0xFF; 32];

        assert!(wins_conflict(&low, &high));
        assert!(!wins_conflict(&high, &low));
        assert!(!wins_conflict(&low, &low)); // Equal doesn't win
    }

    #[test]
    fn test_conflict_resolution_deterministic() {
        let mut a: FactId = [0x00; 32];
        let mut b: FactId = [0x00; 32];
        a[15] = 0x01;
        b[15] = 0x02;

        // a < b lexicographically
        assert!(wins_conflict(&a, &b));
        assert!(!wins_conflict(&b, &a));
    }

    #[test]
    fn test_exact_index_size() {
        assert_eq!(core::mem::size_of::<ExactCausalIndex>(), 36928);
        assert_eq!(core::mem::align_of::<ExactCausalIndex>(), 64);
    }

    #[test]
    fn test_exact_index_insert_contains() {
        let mut index = ExactCausalIndex::new();
        let fact1: FactId = [1u8; 32];
        let fact2: FactId = [2u8; 32];

        assert!(index.is_empty());
        assert!(!index.contains(&fact1));

        assert!(index.insert(&fact1));
        assert_eq!(index.len(), 1);
        assert!(index.contains(&fact1));
        assert!(!index.contains(&fact2));

        assert!(index.insert(&fact2));
        assert_eq!(index.len(), 2);
        assert!(index.contains(&fact2));

        // Duplicate insert returns false
        assert!(!index.insert(&fact1));
        assert_eq!(index.len(), 2);
    }

    #[test]
    fn test_exact_index_contains_all() {
        let mut index = ExactCausalIndex::new();
        let facts: [FactId; 4] = [[1u8; 32], [2u8; 32], [3u8; 32], [4u8; 32]];

        for f in &facts {
            index.insert(f);
        }

        assert!(index.contains_all(&facts[..2]).is_ok());
        assert!(index.contains_all(&facts).is_ok());

        let unknown: FactId = [99u8; 32];
        assert_eq!(index.contains_all(&[unknown]), Err(CausalHorizonExceeded));
    }

    #[test]
    fn test_exact_index_many_inserts() {
        let mut index = ExactCausalIndex::new();

        // Insert 500 unique facts
        for i in 0u64..500 {
            let mut fact_id = [0u8; 32];
            fact_id[..8].copy_from_slice(&i.to_le_bytes());
            assert!(index.insert(&fact_id));
        }

        assert_eq!(index.len(), 500);

        // Verify all are present
        for i in 0u64..500 {
            let mut fact_id = [0u8; 32];
            fact_id[..8].copy_from_slice(&i.to_le_bytes());
            assert!(index.contains(&fact_id));
        }
    }

    #[test]
    fn test_exact_index_compaction() {
        let mut index = ExactCausalIndex::new();

        // Fill past 75% threshold to trigger compaction
        for i in 0u64..800 {
            let mut fact_id = [0u8; 32];
            fact_id[..8].copy_from_slice(&i.to_le_bytes());
            index.insert(&fact_id);
        }

        // After compaction, count should be reduced
        // Compaction keeps ~50% of entries
        assert!(index.len() <= EXACT_INDEX_CAPACITY * 3 / 4);
        assert!(index.len() > 0);

        // Verify the index is still functional
        let mut new_fact = [0u8; 32];
        new_fact[..8].copy_from_slice(&900u64.to_le_bytes());
        assert!(index.insert(&new_fact));
        assert!(index.contains(&new_fact));
    }

    #[test]
    fn test_exact_index_false_positive_rejection() {
        // This is the critical correctness test:
        // BFVC might say "yes" but ExactIndex must say "no" for missing deps
        let mut bfvc = CausalClock::new();
        let mut index = ExactCausalIndex::new();

        let fact1: FactId = [1u8; 32];
        let fact2: FactId = [2u8; 32];

        // Add fact1 to both
        bfvc.observe(&fact1);
        index.observe(&fact1);

        // Add fact2 ONLY to BFVC (simulating false positive scenario)
        bfvc.observe(&fact2);
        // NOT added to index

        // BFVC says "might contain" for both
        assert!(bfvc.might_contain(&fact1));
        assert!(bfvc.might_contain(&fact2));

        // ExactIndex correctly rejects fact2
        assert!(index.contains(&fact1));
        assert!(!index.contains(&fact2));
        assert_eq!(index.contains_all(&[fact2]), Err(CausalHorizonExceeded));
    }

    #[test]
    fn test_exact_index_contains_simd() {
        let mut index = ExactCausalIndex::new();

        // Insert 100 facts
        for i in 0u64..100 {
            let mut fact_id = [0u8; 32];
            fact_id[..8].copy_from_slice(&i.to_le_bytes());
            index.insert(&fact_id);
        }

        // Verify SIMD contains matches scalar contains
        for i in 0u64..100 {
            let mut fact_id = [0u8; 32];
            fact_id[..8].copy_from_slice(&i.to_le_bytes());
            assert_eq!(index.contains(&fact_id), index.contains_simd(&fact_id));
        }

        // Verify non-existent facts return false
        for i in 100u64..200 {
            let mut fact_id = [0u8; 32];
            fact_id[..8].copy_from_slice(&i.to_le_bytes());
            assert!(!index.contains_simd(&fact_id));
        }
    }

    #[test]
    fn test_exact_index_contains_all_simd() {
        let mut index = ExactCausalIndex::new();
        let facts: [FactId; 4] = [[1u8; 32], [2u8; 32], [3u8; 32], [4u8; 32]];

        for f in &facts {
            index.insert(f);
        }

        // SIMD version should match scalar version
        assert!(index.contains_all_simd(&facts).is_ok());
        assert!(index.contains_all_simd(&facts[..2]).is_ok());

        let unknown: FactId = [99u8; 32];
        assert_eq!(index.contains_all_simd(&[unknown]), Err(CausalHorizonExceeded));
    }
}
