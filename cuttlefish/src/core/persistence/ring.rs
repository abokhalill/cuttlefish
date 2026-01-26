//! Lock-free SPSC ring buffer for persistence entries.
//! Zero-allocation after init, cache-line padded head/tail.

use core::cell::UnsafeCell;
use core::sync::atomic::{AtomicUsize, Ordering};

/// Cache-line aligned wrapper to prevent false sharing.
#[repr(align(64))]
pub struct CachePadded<T>(pub T);

impl<T> CachePadded<T> {
    pub const fn new(val: T) -> Self {
        Self(val)
    }
}

impl<T> core::ops::Deref for CachePadded<T> {
    type Target = T;
    #[inline(always)]
    fn deref(&self) -> &T {
        &self.0
    }
}

impl<T> core::ops::DerefMut for CachePadded<T> {
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut T {
        &mut self.0
    }
}

/// Entry pushed to persistence queue.
#[derive(Clone, Copy, Debug)]
#[repr(C)]
pub struct PersistenceEntry {
    pub fact_id: [u8; 32],
    pub data_ptr: usize,
    pub data_len: u32,
    pub sequence: u64,
}

impl PersistenceEntry {
    pub const fn empty() -> Self {
        Self {
            fact_id: [0u8; 32],
            data_ptr: 0,
            data_len: 0,
            sequence: 0,
        }
    }
}

const _: () = {
    assert!(core::mem::size_of::<PersistenceEntry>() == 56);
};

/// Fixed-capacity SPSC ring buffer. Power-of-two capacity for fast modulo.
pub struct SPSCBuffer<const N: usize> {
    buffer: UnsafeCell<[PersistenceEntry; N]>,
    head: CachePadded<AtomicUsize>,
    tail: CachePadded<AtomicUsize>,
}

unsafe impl<const N: usize> Send for SPSCBuffer<N> {}
unsafe impl<const N: usize> Sync for SPSCBuffer<N> {}

impl<const N: usize> SPSCBuffer<N> {
    const MASK: usize = N - 1;

    const _ASSERT_POWER_OF_TWO: () = {
        assert!(N > 0 && (N & (N - 1)) == 0, "N must be power of two");
    };

    pub fn new() -> Self {
        let _ = Self::_ASSERT_POWER_OF_TWO;
        Self {
            buffer: UnsafeCell::new([PersistenceEntry::empty(); N]),
            head: CachePadded::new(AtomicUsize::new(0)),
            tail: CachePadded::new(AtomicUsize::new(0)),
        }
    }

    /// Split into producer/consumer handles. Only call once.
    pub fn split(&self) -> (SPSCProducer<'_, N>, SPSCConsumer<'_, N>) {
        (SPSCProducer { ring: self }, SPSCConsumer { ring: self })
    }
}

impl<const N: usize> Default for SPSCBuffer<N> {
    fn default() -> Self {
        Self::new()
    }
}

/// Producer handle for SPSC buffer.
pub struct SPSCProducer<'a, const N: usize> {
    ring: &'a SPSCBuffer<N>,
}

impl<'a, const N: usize> SPSCProducer<'a, N> {
    /// Try to push an entry. Returns Err if buffer is full.
    #[inline]
    pub fn try_push(&self, entry: PersistenceEntry) -> Result<(), PersistenceEntry> {
        let head = self.ring.head.load(Ordering::Relaxed);
        let tail = self.ring.tail.load(Ordering::Acquire);

        // Full when head - tail == N
        if head.wrapping_sub(tail) >= N {
            return Err(entry);
        }

        unsafe {
            let slot = &mut (*self.ring.buffer.get())[head & SPSCBuffer::<N>::MASK];
            *slot = entry;
        }

        self.ring.head.store(head.wrapping_add(1), Ordering::Release);
        Ok(())
    }

    #[inline(always)]
    pub fn is_full(&self) -> bool {
        let head = self.ring.head.load(Ordering::Relaxed);
        let tail = self.ring.tail.load(Ordering::Acquire);
        head.wrapping_sub(tail) >= N
    }

    #[inline(always)]
    pub fn len(&self) -> usize {
        let head = self.ring.head.load(Ordering::Relaxed);
        let tail = self.ring.tail.load(Ordering::Acquire);
        head.wrapping_sub(tail)
    }
}

/// Consumer handle for SPSC buffer.
pub struct SPSCConsumer<'a, const N: usize> {
    ring: &'a SPSCBuffer<N>,
}

impl<'a, const N: usize> SPSCConsumer<'a, N> {
    /// Try to pop an entry. Returns None if buffer is empty.
    #[inline]
    pub fn try_pop(&self) -> Option<PersistenceEntry> {
        let tail = self.ring.tail.load(Ordering::Relaxed);
        let head = self.ring.head.load(Ordering::Acquire);

        if tail == head {
            return None;
        }

        let entry = unsafe {
            let slot = &(*self.ring.buffer.get())[tail & SPSCBuffer::<N>::MASK];
            *slot
        };

        self.ring.tail.store(tail.wrapping_add(1), Ordering::Release);
        Some(entry)
    }

    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        let tail = self.ring.tail.load(Ordering::Relaxed);
        let head = self.ring.head.load(Ordering::Acquire);
        tail == head
    }

    #[inline(always)]
    pub fn len(&self) -> usize {
        let tail = self.ring.tail.load(Ordering::Relaxed);
        let head = self.ring.head.load(Ordering::Acquire);
        head.wrapping_sub(tail)
    }

    /// Drain up to `max` entries into the provided buffer.
    #[inline]
    pub fn drain_into(&self, out: &mut [PersistenceEntry], max: usize) -> usize {
        let mut count = 0;
        let limit = max.min(out.len());
        while count < limit {
            match self.try_pop() {
                Some(entry) => {
                    out[count] = entry;
                    count += 1;
                }
                None => break,
            }
        }
        count
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_spsc_push_pop() {
        let buffer: SPSCBuffer<16> = SPSCBuffer::new();
        let (producer, consumer) = buffer.split();

        let entry = PersistenceEntry {
            fact_id: [1u8; 32],
            data_ptr: 0x1000,
            data_len: 64,
            sequence: 1,
        };

        assert!(producer.try_push(entry).is_ok());
        assert_eq!(producer.len(), 1);

        let popped = consumer.try_pop().unwrap();
        assert_eq!(popped.fact_id, [1u8; 32]);
        assert_eq!(popped.sequence, 1);
        assert!(consumer.is_empty());
    }

    #[test]
    fn test_spsc_full() {
        let buffer: SPSCBuffer<4> = SPSCBuffer::new();
        let (producer, consumer) = buffer.split();

        for i in 0..4 {
            let mut entry = PersistenceEntry::empty();
            entry.sequence = i;
            assert!(producer.try_push(entry).is_ok());
        }

        assert!(producer.is_full());

        let mut entry = PersistenceEntry::empty();
        entry.sequence = 99;
        assert!(producer.try_push(entry).is_err());

        let _ = consumer.try_pop();
        assert!(!producer.is_full());
    }

    #[test]
    fn test_spsc_drain() {
        let buffer: SPSCBuffer<16> = SPSCBuffer::new();
        let (producer, consumer) = buffer.split();

        for i in 0..8 {
            let mut entry = PersistenceEntry::empty();
            entry.sequence = i;
            producer.try_push(entry).unwrap();
        }

        let mut out = [PersistenceEntry::empty(); 16];
        let count = consumer.drain_into(&mut out, 5);
        assert_eq!(count, 5);
        assert_eq!(out[0].sequence, 0);
        assert_eq!(out[4].sequence, 4);
        assert_eq!(consumer.len(), 3);
    }
}
