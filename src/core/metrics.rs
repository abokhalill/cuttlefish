//! Lightweight metrics. No allocations, no locks, just atomics.

use core::sync::atomic::{AtomicU64, Ordering};

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
        self.total_latency_ns.fetch_add(latency_ns, Ordering::Relaxed);
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
        self.total_write_latency_ns.fetch_add(latency_ns, Ordering::Relaxed);
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
    fn test_admission_metrics() {
        let m = AdmissionMetrics::new();
        m.record_admit(100);
        m.record_admit(200);
        m.record_admit(50);

        assert_eq!(m.admits(), 3);
        assert_eq!(m.avg_latency_ns(), 116); // (100+200+50)/3
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
