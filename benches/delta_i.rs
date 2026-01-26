use criterion::{black_box, criterion_group, criterion_main, Criterion};
use cuttlefish::core::invariant::Invariant;
use cuttlefish::invariants::total_supply::{ConservationState, DeltaPayload, TotalSupplyInvariant};
use zerocopy::IntoBytes;

fn bench_conservation_delta_i(c: &mut Criterion) {
    let invariant = TotalSupplyInvariant::new();

    let state = ConservationState::new(500_000_000, 0, 1_000_000_000);
    let mut state_buf = [0u8; 64];
    state_buf.copy_from_slice(state.as_bytes());

    let delta = DeltaPayload { delta: 100 };
    let payload_buf: [u8; 16] = {
        let mut buf = [0u8; 16];
        buf.copy_from_slice(delta.as_bytes());
        buf
    };

    c.bench_function("delta_i_conservation_apply", |b| {
        b.iter(|| {
            let mut state_copy = state_buf;
            black_box(invariant.apply(black_box(&payload_buf), black_box(&mut state_copy)))
        })
    });
}

fn bench_conservation_hot_path(c: &mut Criterion) {
    let invariant = TotalSupplyInvariant::new();

    let state = ConservationState::new(0, i128::MIN, i128::MAX);
    let mut state_buf = [0u8; 64];
    state_buf.copy_from_slice(state.as_bytes());

    let delta = DeltaPayload { delta: 1 };
    let payload_buf: [u8; 16] = {
        let mut buf = [0u8; 16];
        buf.copy_from_slice(delta.as_bytes());
        buf
    };

    c.bench_function("delta_i_conservation_unbounded", |b| {
        b.iter(|| {
            black_box(invariant.apply(black_box(&payload_buf), black_box(&mut state_buf)))
        })
    });
}

criterion_group!(benches, bench_conservation_delta_i, bench_conservation_hot_path);
criterion_main!(benches);
