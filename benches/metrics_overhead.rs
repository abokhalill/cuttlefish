//! Benchmark: prove metrics overhead < 8ns.

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use std::sync::Arc;

use ctfs::core::kernel::TwoLaneKernel;
use ctfs::core::metrics::LatencyHistogram;
use ctfs::core::topology::FactId;
use ctfs::invariants::monotonic::GCounterInvariant;

fn make_fact_id(seed: u64) -> FactId {
    let mut id = [0u8; 32];
    id[0..8].copy_from_slice(&seed.to_le_bytes());
    id
}

fn bench_admit_baseline(c: &mut Criterion) {
    let inv = GCounterInvariant::new();
    let mut kernel = TwoLaneKernel::new(inv);
    let payload = 1u64.to_le_bytes();
    let mut seed = 0u64;

    c.bench_function("admit_baseline", |b| {
        b.iter(|| {
            seed += 1;
            let fact_id = make_fact_id(seed);
            black_box(kernel.admit(black_box(&fact_id), black_box(&[]), black_box(&payload)))
        })
    });
}

fn bench_admit_instrumented(c: &mut Criterion) {
    let inv = GCounterInvariant::new();
    let mut kernel = TwoLaneKernel::new(inv);
    let histogram = Arc::new(LatencyHistogram::new());
    let payload = 1u64.to_le_bytes();
    let mut seed = 0u64;

    c.bench_function("admit_instrumented", |b| {
        b.iter(|| {
            seed += 1;
            let fact_id = make_fact_id(seed);
            black_box(kernel.admit_instrumented(
                black_box(&fact_id),
                black_box(&[]),
                black_box(&payload),
                &histogram,
            ))
        })
    });
}

fn bench_histogram_record(c: &mut Criterion) {
    let histogram = LatencyHistogram::new();

    c.bench_function("histogram_record", |b| {
        b.iter(|| {
            histogram.record(black_box(100));
        })
    });
}

fn bench_nanos_now(c: &mut Criterion) {
    c.bench_function("nanos_now_rdtsc", |b| {
        b.iter(|| {
            #[cfg(target_arch = "x86_64")]
            {
                black_box(unsafe { core::arch::x86_64::_rdtsc() })
            }
            #[cfg(not(target_arch = "x86_64"))]
            {
                use std::time::Instant;
                static START: std::sync::OnceLock<Instant> = std::sync::OnceLock::new();
                let start = START.get_or_init(Instant::now);
                black_box(start.elapsed().as_nanos() as u64)
            }
        })
    });
}

criterion_group!(
    benches,
    bench_admit_baseline,
    bench_admit_instrumented,
    bench_histogram_record,
    bench_nanos_now,
);
criterion_main!(benches);
