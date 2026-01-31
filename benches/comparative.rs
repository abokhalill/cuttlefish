//! Comparative benchmarks vs raw ops, atomics, mutex.

use criterion::{black_box, criterion_group, criterion_main, Criterion, Throughput};
use std::sync::atomic::{AtomicI64, Ordering};
use std::sync::Mutex;

use cuttlefish::algebra::lattice::{GSetLattice, JoinSemilattice, LatticeMerge, MaxU64};
use cuttlefish::core::kernel::Kernel;
use cuttlefish::core::state::StateCell;
use cuttlefish::core::topology::FactId;
use cuttlefish::invariants::graph::GGraphInvariant;
use cuttlefish::invariants::monotonic::{GCounterInvariant, MaxInvariant};
use cuttlefish::invariants::total_supply::{ConservationState, TotalSupplyInvariant};
use zerocopy::IntoBytes;

fn bench_raw_i128_add(c: &mut Criterion) {
    let mut value: i128 = 0;

    c.bench_function("baseline_raw_i128_add", |b| {
        b.iter(|| {
            value = black_box(value).wrapping_add(black_box(100));
            black_box(value)
        })
    });
}

fn bench_atomic_i64_add(c: &mut Criterion) {
    let counter = AtomicI64::new(0);

    c.bench_function("baseline_atomic_i64_add", |b| {
        b.iter(|| counter.fetch_add(black_box(1), Ordering::Relaxed))
    });
}

fn bench_mutex_i128_add(c: &mut Criterion) {
    let value = Mutex::new(0i128);

    c.bench_function("baseline_mutex_i128_add", |b| {
        b.iter(|| {
            let mut guard = value.lock().unwrap();
            *guard = guard.wrapping_add(black_box(100));
            black_box(*guard)
        })
    });
}

fn bench_cuttlefish_conservation(c: &mut Criterion) {
    let state = ConservationState::new(0, i128::MIN, i128::MAX);
    let mut cell = StateCell::new();
    cell.as_slice_mut().copy_from_slice(state.as_bytes());

    let mut kernel = Kernel::with_state(TotalSupplyInvariant::new(), cell);
    let mut fact_counter = 0u64;

    c.bench_function("cuttlefish_conservation_admit", |b| {
        b.iter(|| {
            fact_counter += 1;
            let mut fact_id: FactId = [0u8; 32];
            fact_id[0..8].copy_from_slice(&fact_counter.to_le_bytes());

            let payload = black_box(100i128).to_le_bytes();
            black_box(kernel.admit_raw(black_box(&fact_id), black_box(&[]), black_box(&payload)))
        })
    });
}

fn bench_cuttlefish_max(c: &mut Criterion) {
    let mut state = StateCell::new();
    let mut kernel = Kernel::with_state(MaxInvariant::new(), state);
    let mut fact_counter = 0u64;

    c.bench_function("cuttlefish_max_admit", |b| {
        b.iter(|| {
            fact_counter += 1;
            let mut fact_id: FactId = [0u8; 32];
            fact_id[0..8].copy_from_slice(&fact_counter.to_le_bytes());

            let mut payload = [0u8; 16];
            payload[0..8].copy_from_slice(&fact_counter.to_le_bytes());
            black_box(kernel.admit_raw(black_box(&fact_id), black_box(&[]), black_box(&payload)))
        })
    });
}

fn bench_cuttlefish_gcounter(c: &mut Criterion) {
    let state = StateCell::new();
    let mut kernel = Kernel::with_state(GCounterInvariant::new(), state);
    let mut fact_counter = 0u64;

    c.bench_function("cuttlefish_gcounter_admit", |b| {
        b.iter(|| {
            fact_counter += 1;
            let mut fact_id: FactId = [0u8; 32];
            fact_id[0..8].copy_from_slice(&fact_counter.to_le_bytes());

            let mut payload = [0u8; 16];
            payload[0..8].copy_from_slice(&1u64.to_le_bytes());
            black_box(kernel.admit_raw(black_box(&fact_id), black_box(&[]), black_box(&payload)))
        })
    });
}

fn bench_cuttlefish_graph(c: &mut Criterion) {
    let mut state = StateCell::new();
    state.as_slice_mut()[32] = 16;

    let mut kernel = Kernel::with_state(GGraphInvariant::new(), state);
    let mut fact_counter = 0u64;
    let mut edge_counter = 0u8;

    c.bench_function("cuttlefish_graph_edge_add", |b| {
        b.iter(|| {
            fact_counter += 1;
            edge_counter = (edge_counter + 1) % 15;

            let mut fact_id: FactId = [0u8; 32];
            fact_id[0..8].copy_from_slice(&fact_counter.to_le_bytes());

            let mut payload = [0u8; 16];
            payload[0] = edge_counter;
            payload[1] = (edge_counter + 1) % 16;

            black_box(kernel.admit_raw(black_box(&fact_id), black_box(&[]), black_box(&payload)))
        })
    });
}

fn bench_lattice_max_join(c: &mut Criterion) {
    let a = MaxU64(100);
    let b = MaxU64(200);

    c.bench_function("lattice_max_join", |b_iter| {
        b_iter.iter(|| black_box(black_box(a).join(black_box(&b))))
    });
}

fn bench_lattice_gset_join(c: &mut Criterion) {
    let mut a = GSetLattice::new();
    let mut b = GSetLattice::new();

    for i in 0..100 {
        a.insert(i);
        b.insert(i + 50);
    }

    c.bench_function("lattice_gset_join", |b_iter| {
        b_iter.iter(|| black_box(black_box(a).join(black_box(&b))))
    });
}

fn bench_lattice_gset_merge(c: &mut Criterion) {
    let mut b = GSetLattice::new();
    for i in 0..100 {
        b.insert(i + 50);
    }

    c.bench_function("lattice_gset_merge", |b_iter| {
        let mut a = GSetLattice::new();
        for i in 0..100 {
            a.insert(i);
        }

        b_iter.iter(|| {
            black_box(&mut a).merge(black_box(&b));
        })
    });
}

fn bench_throughput_conservation(c: &mut Criterion) {
    let mut group = c.benchmark_group("throughput");
    group.throughput(Throughput::Elements(1));

    let state = ConservationState::new(0, i128::MIN, i128::MAX);
    let mut cell = StateCell::new();
    cell.as_slice_mut().copy_from_slice(state.as_bytes());

    let mut kernel = Kernel::with_state(TotalSupplyInvariant::new(), cell);
    let mut fact_counter = 0u64;

    group.bench_function("conservation_ops_per_sec", |b| {
        b.iter(|| {
            fact_counter += 1;
            let mut fact_id: FactId = [0u8; 32];
            fact_id[0..8].copy_from_slice(&fact_counter.to_le_bytes());
            let payload = 1i128.to_le_bytes();
            kernel.admit_raw(&fact_id, &[], &payload)
        })
    });

    group.finish();
}

fn bench_causal_clock_observe(c: &mut Criterion) {
    use cuttlefish::core::topology::CausalClock;

    let mut clock = CausalClock::new();
    let mut counter = 0u64;

    c.bench_function("causal_clock_observe", |b| {
        b.iter(|| {
            counter += 1;
            let mut fact_id: FactId = [0u8; 32];
            fact_id[0..8].copy_from_slice(&counter.to_le_bytes());
            clock.observe(black_box(&fact_id));
        })
    });
}

fn bench_causal_clock_dominates(c: &mut Criterion) {
    use cuttlefish::core::topology::CausalClock;

    let mut clock_a = CausalClock::new();
    let mut clock_b = CausalClock::new();

    for i in 0u64..100 {
        let mut fact_id: FactId = [0u8; 32];
        fact_id[0..8].copy_from_slice(&i.to_le_bytes());
        clock_a.observe(&fact_id);
        if i < 50 {
            clock_b.observe(&fact_id);
        }
    }

    c.bench_function("causal_clock_dominates", |b| {
        b.iter(|| black_box(black_box(&clock_a).dominates(black_box(&clock_b))))
    });
}

fn bench_exact_index_insert(c: &mut Criterion) {
    use cuttlefish::core::topology::ExactCausalIndex;

    let mut index = ExactCausalIndex::new();
    let mut counter = 0u64;

    c.bench_function("exact_index_insert", |b| {
        b.iter(|| {
            counter += 1;
            let mut fact_id: FactId = [0u8; 32];
            fact_id[0..8].copy_from_slice(&counter.to_le_bytes());
            black_box(index.insert(black_box(&fact_id)))
        })
    });
}

fn bench_exact_index_contains(c: &mut Criterion) {
    use cuttlefish::core::topology::ExactCausalIndex;

    let mut index = ExactCausalIndex::new();

    for i in 0u64..500 {
        let mut fact_id: FactId = [0u8; 32];
        fact_id[0..8].copy_from_slice(&i.to_le_bytes());
        index.insert(&fact_id);
    }

    let mut counter = 0u64;

    c.bench_function("exact_index_contains", |b| {
        b.iter(|| {
            counter = (counter + 1) % 500;
            let mut fact_id: FactId = [0u8; 32];
            fact_id[0..8].copy_from_slice(&counter.to_le_bytes());
            black_box(index.contains(black_box(&fact_id)))
        })
    });
}

criterion_group!(
    baselines,
    bench_raw_i128_add,
    bench_atomic_i64_add,
    bench_mutex_i128_add,
);

criterion_group!(
    cuttlefish_invariants,
    bench_cuttlefish_conservation,
    bench_cuttlefish_max,
    bench_cuttlefish_gcounter,
    bench_cuttlefish_graph,
);

criterion_group!(
    lattice_ops,
    bench_lattice_max_join,
    bench_lattice_gset_join,
    bench_lattice_gset_merge,
);

criterion_group!(
    causal_ops,
    bench_causal_clock_observe,
    bench_causal_clock_dominates,
    bench_exact_index_insert,
    bench_exact_index_contains,
);

criterion_group!(throughput, bench_throughput_conservation,);

criterion_main!(
    baselines,
    cuttlefish_invariants,
    lattice_ops,
    causal_ops,
    throughput
);
