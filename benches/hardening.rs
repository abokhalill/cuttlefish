//! Benchmarks for hardened components: checkpoint hashing, state transitions, memory ordering.
//! Measures the overhead of security hardening vs raw performance.

use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId, Throughput};
use cuttlefish::core::checkpoint::{Checkpoint, CheckpointHeader, WalHasher};
use cuttlefish::core::state::StateCell;
use cuttlefish::core::frontier::FrontierState;
use cuttlefish::core::topology::CausalClock;
use zerocopy::IntoBytes;

fn bench_tiered_hash_computation(c: &mut Criterion) {
    let mut state = StateCell::new();
    state.as_slice_mut()[0..8].copy_from_slice(&0xDEADBEEFu64.to_le_bytes());

    let mut frontier = FrontierState::new();
    frontier.advance([0xAAu8; 32]);
    frontier.advance([0xBBu8; 32]);
    frontier.advance([0xCCu8; 32]);
    frontier.advance([0xDDu8; 32]);

    c.bench_function("checkpoint/tiered_hash", |b| {
        b.iter(|| {
            black_box(Checkpoint::compute_tiered_hash(
                black_box(&state),
                black_box(&frontier),
            ))
        })
    });
}

fn bench_state_hash_only(c: &mut Criterion) {
    let mut state = StateCell::new();
    state.as_slice_mut()[0..8].copy_from_slice(&0xCAFEBABEu64.to_le_bytes());

    c.bench_function("checkpoint/state_hash", |b| {
        b.iter(|| {
            black_box(Checkpoint::compute_state_hash(black_box(&state)))
        })
    });
}

fn bench_tiered_hash_verify(c: &mut Criterion) {
    let mut state = StateCell::new();
    state.as_slice_mut()[0..8].copy_from_slice(&0x12345678u64.to_le_bytes());

    let mut frontier = FrontierState::new();
    frontier.advance([0x11u8; 32]);
    frontier.advance([0x22u8; 32]);

    let expected_hash = Checkpoint::compute_tiered_hash(&state, &frontier);

    c.bench_function("checkpoint/verify_tiered_hash", |b| {
        b.iter(|| {
            black_box(Checkpoint::verify_tiered_hash(
                black_box(&state),
                black_box(&frontier),
                black_box(&expected_hash),
            ))
        })
    });
}

fn bench_checkpoint_header_serialization(c: &mut Criterion) {
    let hash = [0xABu8; 32];
    let header = CheckpointHeader::new(12345, 4096 * 100, hash);

    c.bench_function("checkpoint/header_to_bytes", |b| {
        b.iter(|| {
            black_box(header.to_bytes())
        })
    });
}

fn bench_checkpoint_header_parsing(c: &mut Criterion) {
    let hash = [0xCDu8; 32];
    let header = CheckpointHeader::new(67890, 4096 * 200, hash);
    let bytes = header.to_bytes();

    c.bench_function("checkpoint/header_from_bytes", |b| {
        b.iter(|| {
            black_box(CheckpointHeader::from_bytes(black_box(&bytes)))
        })
    });
}

fn bench_wal_hasher_entry(c: &mut Criterion) {
    let mut group = c.benchmark_group("wal_hasher");

    for payload_size in [32, 64, 128, 200].iter() {
        let fact_id = [0xEEu8; 32];
        let payload = vec![0xFFu8; *payload_size];

        group.throughput(Throughput::Bytes(*payload_size as u64 + 32));
        group.bench_with_input(
            BenchmarkId::new("update_entry", payload_size),
            payload_size,
            |b, _| {
                b.iter(|| {
                    let mut hasher = WalHasher::new();
                    hasher.update_entry(black_box(&fact_id), black_box(&payload));
                    black_box(hasher.finalize())
                })
            },
        );
    }
    group.finish();
}

fn bench_wal_hasher_batch(c: &mut Criterion) {
    let entries: Vec<([u8; 32], Vec<u8>)> = (0..100)
        .map(|i| {
            let mut fact_id = [0u8; 32];
            fact_id[0] = i as u8;
            (fact_id, vec![i as u8; 64])
        })
        .collect();

    c.bench_function("wal_hasher/batch_100_entries", |b| {
        b.iter(|| {
            let mut hasher = WalHasher::new();
            for (fact_id, payload) in &entries {
                hasher.update_entry(black_box(fact_id), black_box(payload));
            }
            black_box(hasher.finalize())
        })
    });
}

fn bench_causal_clock_observe(c: &mut Criterion) {
    let mut clock = CausalClock::new();
    let fact_ids: Vec<[u8; 32]> = (0..1000)
        .map(|i| {
            let mut id = [0u8; 32];
            id[0..8].copy_from_slice(&(i as u64).to_le_bytes());
            id
        })
        .collect();

    c.bench_function("causal_clock/observe", |b| {
        let mut idx = 0usize;
        b.iter(|| {
            clock.observe(black_box(&fact_ids[idx % 1000]));
            idx = idx.wrapping_add(1);
        })
    });
}

fn bench_causal_clock_dominates(c: &mut Criterion) {
    let mut clock1 = CausalClock::new();
    let mut clock2 = CausalClock::new();

    for i in 0..100u64 {
        let mut id = [0u8; 32];
        id[0..8].copy_from_slice(&i.to_le_bytes());
        clock1.observe(&id);
        if i < 50 {
            clock2.observe(&id);
        }
    }

    c.bench_function("causal_clock/dominates", |b| {
        b.iter(|| {
            black_box(clock1.dominates(black_box(&clock2)))
        })
    });
}

fn bench_frontier_advance(c: &mut Criterion) {
    let fact_ids: Vec<[u8; 32]> = (0..1000)
        .map(|i| {
            let mut id = [0u8; 32];
            id[0..8].copy_from_slice(&(i as u64).to_le_bytes());
            id
        })
        .collect();

    c.bench_function("frontier/advance", |b| {
        let mut frontier = FrontierState::new();
        let mut idx = 0usize;
        b.iter(|| {
            frontier.advance(black_box(fact_ids[idx % 1000]));
            idx = idx.wrapping_add(1);
        })
    });
}

fn bench_state_cell_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("state_cell");

    group.bench_function("new", |b| {
        b.iter(|| {
            black_box(StateCell::new())
        })
    });

    let state = StateCell::new();
    group.bench_function("as_bytes", |b| {
        b.iter(|| {
            black_box(state.as_bytes())
        })
    });

    let data = [0xABu8; 64];
    group.bench_function("copy_from_slice", |b| {
        b.iter(|| {
            let mut state = StateCell::new();
            state.as_slice_mut().copy_from_slice(black_box(&data));
            black_box(state)
        })
    });

    group.finish();
}

criterion_group!(
    hardening_benches,
    bench_tiered_hash_computation,
    bench_state_hash_only,
    bench_tiered_hash_verify,
    bench_checkpoint_header_serialization,
    bench_checkpoint_header_parsing,
    bench_wal_hasher_entry,
    bench_wal_hasher_batch,
    bench_causal_clock_observe,
    bench_causal_clock_dominates,
    bench_frontier_advance,
    bench_state_cell_operations,
);

criterion_main!(hardening_benches);
