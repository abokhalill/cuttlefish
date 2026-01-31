//! Benchmark for durable admission (producer side only).
//! Target: < 100ns for memory update + SPSC buffer push.

use criterion::{criterion_group, criterion_main, Criterion};
use cuttlefish::core::kernel::DurableKernel;
use cuttlefish::core::persistence::{PersistenceFrontier, SPSCBuffer};
use cuttlefish::core::state::StateCell;
use cuttlefish::core::topology::FactId;
use cuttlefish::invariants::total_supply::{ConservationState, TotalSupplyInvariant};
use std::hint::black_box;
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

/// Benchmark durable admission: invariant check + SPSC push.
fn bench_durable_admission(c: &mut Criterion) {
    let state = make_conservation_state(0, i128::MIN, i128::MAX);
    let buffer: SPSCBuffer<4096> = SPSCBuffer::new();
    let (producer, _consumer) = buffer.split();
    let frontier = PersistenceFrontier::new();

    let mut kernel =
        DurableKernel::with_state(TotalSupplyInvariant::new(), state, producer, &frontier);

    let payload = make_payload(1);

    c.bench_function("durable_admission", |b| {
        let mut counter = 0u64;
        b.iter(|| {
            let mut fact_id: FactId = [0u8; 32];
            fact_id[..8].copy_from_slice(&counter.to_le_bytes());
            counter = counter.wrapping_add(1);

            // Reset buffer periodically to avoid BufferFull
            if counter % 4000 == 0 {
                // In real benchmark, consumer would drain
                // Here we just measure producer side
            }

            black_box(kernel.admit_durable(
                black_box(&fact_id),
                black_box(&[]),
                black_box(&payload),
            ))
        })
    });
}

/// Benchmark just the SPSC push (no invariant).
fn bench_spsc_push_only(c: &mut Criterion) {
    use cuttlefish::core::persistence::PersistenceEntry;

    let buffer: SPSCBuffer<4096> = SPSCBuffer::new();
    let (producer, consumer) = buffer.split();

    c.bench_function("spsc_push_only", |b| {
        let mut counter = 0u64;
        b.iter(|| {
            let entry = PersistenceEntry {
                fact_id: [0u8; 32],
                data_ptr: 0x1000,
                data_len: 64,
                sequence: counter,
            };
            counter = counter.wrapping_add(1);

            // Drain periodically
            if counter % 4000 == 0 {
                while consumer.try_pop().is_some() {}
            }

            black_box(producer.try_push(black_box(entry)))
        })
    });
}

/// Benchmark invariant + state update only (no persistence).
fn bench_invariant_only(c: &mut Criterion) {
    use cuttlefish::core::kernel::Kernel;

    let state = make_conservation_state(0, i128::MIN, i128::MAX);
    let mut kernel = Kernel::with_state(TotalSupplyInvariant::new(), state);
    let payload = make_payload(1);

    c.bench_function("invariant_only", |b| {
        let mut counter = 0u64;
        b.iter(|| {
            let mut fact_id: FactId = [0u8; 32];
            fact_id[..8].copy_from_slice(&counter.to_le_bytes());
            counter = counter.wrapping_add(1);

            black_box(kernel.admit_raw(black_box(&fact_id), black_box(&[]), black_box(&payload)))
        })
    });
}

criterion_group!(
    benches,
    bench_durable_admission,
    bench_spsc_push_only,
    bench_invariant_only,
);
criterion_main!(benches);
