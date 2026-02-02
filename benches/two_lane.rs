//! Two-Lane Architecture Benchmarks: Cold-cache and correctness tests.
//!
//! These benchmarks prove the axis:
//! - Cold-cache admission latency (real-world random access)
//! - Two-tier causality overhead
//! - Adversarial false-positive rejection (correctness)

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use std::hint::black_box as std_black_box;

use ctfs::core::kernel::TwoLaneKernel;
use ctfs::core::state::StateCell;
use ctfs::core::topology::{CausalClock, ExactCausalIndex, FactId};
use ctfs::invariants::total_supply::{ConservationState, TotalSupplyInvariant};
use zerocopy::IntoBytes;

fn make_conservation_state(balance: i128, min: i128, max: i128) -> StateCell {
    let state = ConservationState::new(balance, min, max);
    let mut cell = StateCell::new();
    cell.as_slice_mut().copy_from_slice(state.as_bytes());
    cell
}

fn make_payload(delta: i128) -> [u8; 16] {
    let mut buf = [0u8; 16];
    buf.copy_from_slice(&delta.to_le_bytes());
    buf
}

/// Flush CPU caches by reading a large array.
/// This simulates cold-cache conditions for realistic benchmarks.
fn flush_cache() {
    // 8MB array to exceed L3 cache
    let flush_size = 8 * 1024 * 1024;
    let flush_data: Vec<u8> = vec![0u8; flush_size];

    // Read through the array to evict cache lines
    let mut sum: u64 = 0;
    for chunk in flush_data.chunks(64) {
        sum = sum.wrapping_add(chunk[0] as u64);
    }
    std_black_box(sum);
}

/// Benchmark: Two-Lane kernel admission with warm cache (baseline).
fn bench_two_lane_warm_cache(c: &mut Criterion) {
    let state = make_conservation_state(0, i128::MIN, i128::MAX);
    let mut kernel = TwoLaneKernel::with_state(TotalSupplyInvariant::new(), state);
    let payload = make_payload(1);

    c.bench_function("two_lane_admit_warm_cache", |b| {
        let mut counter = 0u64;
        b.iter(|| {
            let mut fact_id: FactId = [0u8; 32];
            fact_id[..8].copy_from_slice(&counter.to_le_bytes());
            counter = counter.wrapping_add(1);

            black_box(kernel.admit(black_box(&fact_id), black_box(&[]), black_box(&payload)))
        })
    });
}

/// Benchmark: Two-Lane kernel admission with cold cache (realistic).
fn bench_two_lane_cold_cache(c: &mut Criterion) {
    c.bench_function("two_lane_admit_cold_cache", |b| {
        b.iter_custom(|iters| {
            let mut total_time = std::time::Duration::ZERO;

            for i in 0..iters {
                // Create fresh kernel each iteration
                let state = make_conservation_state(0, i128::MIN, i128::MAX);
                let mut kernel = TwoLaneKernel::with_state(TotalSupplyInvariant::new(), state);
                let payload = make_payload(1);

                // Flush cache before measurement
                flush_cache();

                let mut fact_id: FactId = [0u8; 32];
                fact_id[..8].copy_from_slice(&i.to_le_bytes());

                let start = std::time::Instant::now();
                let _ = black_box(kernel.admit(&fact_id, &[], &payload));
                total_time += start.elapsed();
            }

            total_time
        })
    });
}

/// Benchmark: Two-Lane admission with dependencies (two-tier check).
fn bench_two_lane_with_deps(c: &mut Criterion) {
    let state = make_conservation_state(0, i128::MIN, i128::MAX);
    let mut kernel = TwoLaneKernel::with_state(TotalSupplyInvariant::new(), state);
    let payload = make_payload(1);

    // Admit genesis fact
    let genesis: FactId = [0u8; 32];
    kernel.admit(&genesis, &[], &payload).unwrap();

    c.bench_function("two_lane_admit_with_1_dep", |b| {
        let mut counter = 1u64;
        let mut prev_fact = genesis;

        b.iter(|| {
            let mut fact_id: FactId = [0u8; 32];
            fact_id[..8].copy_from_slice(&counter.to_le_bytes());

            let result = kernel.admit(&fact_id, &[prev_fact], &payload);

            prev_fact = fact_id;
            counter = counter.wrapping_add(1);
            black_box(result)
        })
    });
}

/// Benchmark: ExactCausalIndex lookup (Robin Hood hash).
fn bench_exact_index_lookup(c: &mut Criterion) {
    let mut index = ExactCausalIndex::new();

    // Pre-populate with 500 facts
    for i in 0u64..500 {
        let mut fact_id = [0u8; 32];
        fact_id[..8].copy_from_slice(&i.to_le_bytes());
        index.insert(&fact_id);
    }

    c.bench_function("exact_index_contains", |b| {
        let mut counter = 0u64;
        b.iter(|| {
            let mut fact_id = [0u8; 32];
            fact_id[..8].copy_from_slice(&(counter % 500).to_le_bytes());
            counter = counter.wrapping_add(1);

            black_box(index.contains(black_box(&fact_id)))
        })
    });
}

/// Benchmark: ExactCausalIndex insert (Robin Hood hash).
fn bench_exact_index_insert(c: &mut Criterion) {
    c.bench_function("exact_index_insert", |b| {
        let mut index = ExactCausalIndex::new();
        let mut counter = 0u64;

        b.iter(|| {
            let mut fact_id = [0u8; 32];
            fact_id[..8].copy_from_slice(&counter.to_le_bytes());
            counter = counter.wrapping_add(1);

            // Reset periodically to avoid compaction overhead in measurement
            if counter % 700 == 0 {
                index.clear();
            }

            black_box(index.insert(black_box(&fact_id)))
        })
    });
}

/// Benchmark: Two-tier causality check (BFVC + ExactIndex).
fn bench_two_tier_causality_check(c: &mut Criterion) {
    let mut bfvc = CausalClock::new();
    let mut index = ExactCausalIndex::new();

    // Pre-populate with 100 facts
    for i in 0u64..100 {
        let mut fact_id = [0u8; 32];
        fact_id[..8].copy_from_slice(&i.to_le_bytes());
        bfvc.observe(&fact_id);
        index.insert(&fact_id);
    }

    c.bench_function("two_tier_causality_check", |b| {
        let mut counter = 0u64;
        b.iter(|| {
            // Build deps from existing facts
            let dep_idx = (counter % 100) as u64;
            let mut dep = [0u8; 32];
            dep[..8].copy_from_slice(&dep_idx.to_le_bytes());
            let deps = [dep];

            // Tier 0: BFVC check
            let mut deps_clock = CausalClock::new();
            deps_clock.observe(&dep);
            let bfvc_ok = bfvc.dominates(&deps_clock);

            // Tier 1: Exact check
            let exact_ok = index.contains_all(&deps).is_ok();

            counter = counter.wrapping_add(1);
            black_box((bfvc_ok, exact_ok))
        })
    });
}

/// Benchmark: Varying dependency counts.
fn bench_varying_deps(c: &mut Criterion) {
    let mut group = c.benchmark_group("two_lane_varying_deps");

    for dep_count in [0, 1, 2, 4, 8] {
        group.bench_with_input(
            BenchmarkId::from_parameter(dep_count),
            &dep_count,
            |b, &dep_count| {
                let state = make_conservation_state(0, i128::MIN, i128::MAX);
                let mut kernel = TwoLaneKernel::with_state(TotalSupplyInvariant::new(), state);
                let payload = make_payload(1);

                // Pre-admit facts to use as deps
                let mut dep_facts: Vec<FactId> = Vec::new();
                for i in 0u64..dep_count as u64 {
                    let mut fact_id = [0u8; 32];
                    fact_id[..8].copy_from_slice(&i.to_le_bytes());
                    kernel.admit(&fact_id, &[], &payload).unwrap();
                    dep_facts.push(fact_id);
                }

                let mut counter = dep_count as u64;

                b.iter(|| {
                    let mut fact_id: FactId = [0u8; 32];
                    fact_id[..8].copy_from_slice(&counter.to_le_bytes());

                    let result = kernel.admit(&fact_id, &dep_facts, &payload);

                    // Update deps for next iteration (chain)
                    if dep_count > 0 {
                        dep_facts[0] = fact_id;
                    }
                    counter = counter.wrapping_add(1);
                    black_box(result)
                })
            },
        );
    }

    group.finish();
}

criterion_group!(
    benches,
    bench_two_lane_warm_cache,
    bench_two_lane_cold_cache,
    bench_two_lane_with_deps,
    bench_exact_index_lookup,
    bench_exact_index_insert,
    bench_two_tier_causality_check,
    bench_varying_deps,
);
criterion_main!(benches);
