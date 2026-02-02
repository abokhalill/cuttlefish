//! Lightweight metrics. No allocations, no locks, just atomics.

use core::sync::atomic::{AtomicU64, Ordering};

#[cfg(feature = "std")]
pub mod prometheus;

#[cfg(feature = "networking")]
pub mod http;

#[cfg(feature = "std")]
pub use prometheus::{MetricsScraper, PrometheusExporter};

#[cfg(feature = "networking")]
pub use http::MetricsServer;

/// 64-bucket histogram. Power-of-two scale: bucket[i] = count of samples < 2^(i+3) ns.
/// Bucket 0: <8ns, Bucket 1: <16ns, ..., Bucket 63: ≥2^66ns (overflow).
/// Cache-line aligned to avoid false sharing.
#[repr(C, align(64))]
pub struct LatencyHistogram {
    buckets: [AtomicU64; 64],
}

impl LatencyHistogram {
    pub const fn new() -> Self {
        #[allow(clippy::declare_interior_mutable_const)]
        const ZERO: AtomicU64 = AtomicU64::new(0);
        Self {
            buckets: [ZERO; 64],
        }
    }

    /// Record a latency sample. Branchless bucket selection, ~2 cycles.
    #[inline(always)]
    pub fn record(&self, latency_ns: u64) {
        let bucket = Self::bucket_for(latency_ns);
        self.buckets[bucket].fetch_add(1, Ordering::Relaxed);
    }

    /// Bucket index for a given latency. Power-of-two scale starting at 8ns.
    #[inline(always)]
    pub const fn bucket_for(latency_ns: u64) -> usize {
        if latency_ns < 8 {
            0
        } else {
            let bits = 64 - latency_ns.leading_zeros() as usize;
            let idx = bits - 3;
            if idx > 63 {
                63
            } else {
                idx
            }
        }
    }

    /// Upper bound (exclusive) for bucket i in nanoseconds.
    #[inline(always)]
    pub const fn bucket_le(bucket: usize) -> u64 {
        if bucket >= 61 {
            // Avoid overflow: bucket 61 = 2^64, bucket 62+ = MAX
            u64::MAX
        } else {
            1u64 << (bucket + 3)
        }
    }

    /// Get count for a specific bucket.
    #[inline(always)]
    pub fn bucket_count(&self, bucket: usize) -> u64 {
        self.buckets[bucket.min(63)].load(Ordering::Relaxed)
    }

    /// Total samples across all buckets.
    pub fn total(&self) -> u64 {
        self.buckets.iter().map(|b| b.load(Ordering::Relaxed)).sum()
    }

    /// Snapshot all buckets.
    pub fn snapshot(&self) -> [u64; 64] {
        let mut out = [0u64; 64];
        for (i, b) in self.buckets.iter().enumerate() {
            out[i] = b.load(Ordering::Relaxed);
        }
        out
    }

    /// Compute percentile (0-100). Returns bucket upper bound.
    pub fn percentile(&self, pct: u8) -> u64 {
        let total = self.total();
        if total == 0 {
            return 0;
        }
        let target = (total as u128 * pct as u128 / 100) as u64;
        let mut cumulative = 0u64;
        for i in 0..64 {
            cumulative += self.bucket_count(i);
            if cumulative >= target {
                return Self::bucket_le(i);
            }
        }
        Self::bucket_le(63)
    }

    /// p50, p90, p99 in one pass.
    pub fn percentiles(&self) -> (u64, u64, u64) {
        let total = self.total();
        if total == 0 {
            return (0, 0, 0);
        }
        let t50 = (total as u128 * 50 / 100) as u64;
        let t90 = (total as u128 * 90 / 100) as u64;
        let t99 = (total as u128 * 99 / 100) as u64;

        let mut cumulative = 0u64;
        let mut p50 = 0u64;
        let mut p90 = 0u64;
        let mut p99 = 0u64;

        for i in 0..64 {
            cumulative += self.bucket_count(i);
            let le = Self::bucket_le(i);
            if p50 == 0 && cumulative >= t50 {
                p50 = le;
            }
            if p90 == 0 && cumulative >= t90 {
                p90 = le;
            }
            if p99 == 0 && cumulative >= t99 {
                p99 = le;
                break;
            }
        }
        (p50, p90, p99)
    }
}

impl Default for LatencyHistogram {
    fn default() -> Self {
        Self::new()
    }
}

/// Admission metrics. All counters are monotonic.
#[derive(Debug)]
pub struct AdmissionMetrics {
    pub admits: AtomicU64,
    pub rejections: AtomicU64,
    pub causality_violations: AtomicU64,
    pub invariant_violations: AtomicU64,
    pub total_latency_ns: AtomicU64,
    pub max_latency_ns: AtomicU64,
}

impl AdmissionMetrics {
    pub const fn new() -> Self {
        Self {
            admits: AtomicU64::new(0),
            rejections: AtomicU64::new(0),
            causality_violations: AtomicU64::new(0),
            invariant_violations: AtomicU64::new(0),
            total_latency_ns: AtomicU64::new(0),
            max_latency_ns: AtomicU64::new(0),
        }
    }

    #[inline(always)]
    pub fn record_admit(&self, latency_ns: u64) {
        self.admits.fetch_add(1, Ordering::Relaxed);
        self.total_latency_ns
            .fetch_add(latency_ns, Ordering::Relaxed);
        self.update_max_latency(latency_ns);
    }

    #[inline(always)]
    pub fn record_rejection(&self) {
        self.rejections.fetch_add(1, Ordering::Relaxed);
    }

    #[inline(always)]
    pub fn record_causality_violation(&self) {
        self.causality_violations.fetch_add(1, Ordering::Relaxed);
        self.rejections.fetch_add(1, Ordering::Relaxed);
    }

    #[inline(always)]
    pub fn record_invariant_violation(&self) {
        self.invariant_violations.fetch_add(1, Ordering::Relaxed);
        self.rejections.fetch_add(1, Ordering::Relaxed);
    }

    #[inline(always)]
    fn update_max_latency(&self, latency_ns: u64) {
        let mut current = self.max_latency_ns.load(Ordering::Relaxed);
        while latency_ns > current {
            match self.max_latency_ns.compare_exchange_weak(
                current,
                latency_ns,
                Ordering::Relaxed,
                Ordering::Relaxed,
            ) {
                Ok(_) => break,
                Err(c) => current = c,
            }
        }
    }

    pub fn admits(&self) -> u64 {
        self.admits.load(Ordering::Relaxed)
    }

    pub fn rejections(&self) -> u64 {
        self.rejections.load(Ordering::Relaxed)
    }

    pub fn avg_latency_ns(&self) -> u64 {
        let admits = self.admits();
        if admits == 0 {
            0
        } else {
            self.total_latency_ns.load(Ordering::Relaxed) / admits
        }
    }

    pub fn max_latency_ns(&self) -> u64 {
        self.max_latency_ns.load(Ordering::Relaxed)
    }

    pub fn snapshot(&self) -> MetricsSnapshot {
        MetricsSnapshot {
            admits: self.admits(),
            rejections: self.rejections(),
            causality_violations: self.causality_violations.load(Ordering::Relaxed),
            invariant_violations: self.invariant_violations.load(Ordering::Relaxed),
            avg_latency_ns: self.avg_latency_ns(),
            max_latency_ns: self.max_latency_ns(),
        }
    }
}

impl Default for AdmissionMetrics {
    fn default() -> Self {
        Self::new()
    }
}

/// WAL/persistence metrics.
#[derive(Debug)]
pub struct PersistenceMetrics {
    pub writes: AtomicU64,
    pub bytes_written: AtomicU64,
    pub fsyncs: AtomicU64,
    pub total_write_latency_ns: AtomicU64,
    pub max_write_latency_ns: AtomicU64,
}

impl PersistenceMetrics {
    pub const fn new() -> Self {
        Self {
            writes: AtomicU64::new(0),
            bytes_written: AtomicU64::new(0),
            fsyncs: AtomicU64::new(0),
            total_write_latency_ns: AtomicU64::new(0),
            max_write_latency_ns: AtomicU64::new(0),
        }
    }

    #[inline(always)]
    pub fn record_write(&self, bytes: u64, latency_ns: u64) {
        self.writes.fetch_add(1, Ordering::Relaxed);
        self.bytes_written.fetch_add(bytes, Ordering::Relaxed);
        self.total_write_latency_ns
            .fetch_add(latency_ns, Ordering::Relaxed);
        self.update_max_latency(latency_ns);
    }

    #[inline(always)]
    pub fn record_fsync(&self) {
        self.fsyncs.fetch_add(1, Ordering::Relaxed);
    }

    #[inline(always)]
    fn update_max_latency(&self, latency_ns: u64) {
        let mut current = self.max_write_latency_ns.load(Ordering::Relaxed);
        while latency_ns > current {
            match self.max_write_latency_ns.compare_exchange_weak(
                current,
                latency_ns,
                Ordering::Relaxed,
                Ordering::Relaxed,
            ) {
                Ok(_) => break,
                Err(c) => current = c,
            }
        }
    }

    pub fn writes(&self) -> u64 {
        self.writes.load(Ordering::Relaxed)
    }

    pub fn bytes_written(&self) -> u64 {
        self.bytes_written.load(Ordering::Relaxed)
    }

    pub fn throughput_bytes_per_write(&self) -> u64 {
        let writes = self.writes();
        if writes == 0 {
            0
        } else {
            self.bytes_written() / writes
        }
    }

    pub fn avg_write_latency_ns(&self) -> u64 {
        let writes = self.writes();
        if writes == 0 {
            0
        } else {
            self.total_write_latency_ns.load(Ordering::Relaxed) / writes
        }
    }
}

impl Default for PersistenceMetrics {
    fn default() -> Self {
        Self::new()
    }
}

/// Immutable snapshot for export.
#[derive(Debug, Clone, Copy)]
pub struct MetricsSnapshot {
    pub admits: u64,
    pub rejections: u64,
    pub causality_violations: u64,
    pub invariant_violations: u64,
    pub avg_latency_ns: u64,
    pub max_latency_ns: u64,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_histogram_bucket_assignment() {
        assert_eq!(LatencyHistogram::bucket_for(0), 0);
        assert_eq!(LatencyHistogram::bucket_for(7), 0);
        assert_eq!(LatencyHistogram::bucket_for(8), 1);
        assert_eq!(LatencyHistogram::bucket_for(15), 1);
        assert_eq!(LatencyHistogram::bucket_for(16), 2);
        assert_eq!(LatencyHistogram::bucket_for(1000), 7);
        assert_eq!(LatencyHistogram::bucket_for(1_000_000), 17);
    }

    #[test]
    fn test_histogram_record_and_percentiles() {
        let h = LatencyHistogram::new();
        for _ in 0..100 {
            h.record(100);
        }
        assert_eq!(h.total(), 100);
        assert_eq!(h.bucket_count(4), 100);

        let (p50, p90, p99) = h.percentiles();
        assert_eq!(p50, 128);
        assert_eq!(p90, 128);
        assert_eq!(p99, 128);
    }

    #[test]
    fn test_admission_metrics() {
        let m = AdmissionMetrics::new();
        m.record_admit(100);
        m.record_admit(200);
        m.record_admit(50);

        assert_eq!(m.admits(), 3);
        assert_eq!(m.avg_latency_ns(), 116);
        assert_eq!(m.max_latency_ns(), 200);
    }

    #[test]
    fn test_rejection_tracking() {
        let m = AdmissionMetrics::new();
        m.record_causality_violation();
        m.record_invariant_violation();
        m.record_rejection();

        assert_eq!(m.rejections(), 3);
        assert_eq!(m.snapshot().causality_violations, 1);
        assert_eq!(m.snapshot().invariant_violations, 1);
    }

    #[test]
    fn test_persistence_metrics() {
        let m = PersistenceMetrics::new();
        m.record_write(4096, 1000);
        m.record_write(4096, 2000);
        m.record_fsync();

        assert_eq!(m.writes(), 2);
        assert_eq!(m.bytes_written(), 8192);
        assert_eq!(m.throughput_bytes_per_write(), 4096);
        assert_eq!(m.avg_write_latency_ns(), 1500);
    }
}
