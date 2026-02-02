use criterion::{black_box, criterion_group, criterion_main, Criterion};
use ctfs::core::frontier::build_deps_clock;
use ctfs::core::kernel::Kernel;
use ctfs::core::state::StateCell;
use ctfs::core::topology::{CausalClock, FactId};
use ctfs::invariants::total_supply::{ConservationState, DeltaPayload, TotalSupplyInvariant};
use zerocopy::IntoBytes;

fn make_state_cell(balance: i128, min: i128, max: i128) -> StateCell {
    let state = ConservationState::new(balance, min, max);
    let mut cell = StateCell::new();
    cell.as_slice_mut().copy_from_slice(state.as_bytes());
    cell
}

fn make_payload(delta: i128) -> [u8; 16] {
    let payload = DeltaPayload { delta };
    let mut buf = [0u8; 16];
    buf.copy_from_slice(payload.as_bytes());
    buf
}

fn bench_admit_fact_no_deps(c: &mut Criterion) {
    let state = make_state_cell(0, i128::MIN, i128::MAX);
    let mut kernel = Kernel::with_state(TotalSupplyInvariant::new(), state);

    let payload = make_payload(1);

    c.bench_function("kernel_admit_no_deps", |b| {
        let mut counter = 0u64;
        b.iter(|| {
            let mut fact_id: FactId = [0u8; 32];
            fact_id[..8].copy_from_slice(&counter.to_le_bytes());
            counter = counter.wrapping_add(1);

            black_box(kernel.admit_raw(black_box(&fact_id), black_box(&[]), black_box(&payload)))
        })
    });
}

fn bench_admit_fact_with_deps(c: &mut Criterion) {
    let state = make_state_cell(0, i128::MIN, i128::MAX);
    let mut kernel = Kernel::with_state(TotalSupplyInvariant::new(), state);

    let payload = make_payload(1);

    let mut prev_fact: FactId = [0u8; 32];
    kernel.admit_raw(&prev_fact, &[], &payload).unwrap();

    c.bench_function("kernel_admit_with_1_dep", |b| {
        let mut counter = 1u64;
        b.iter(|| {
            let mut fact_id: FactId = [0u8; 32];
            fact_id[..8].copy_from_slice(&counter.to_le_bytes());

            let result = black_box(kernel.admit_raw(
                black_box(&fact_id),
                black_box(&[prev_fact]),
                black_box(&payload),
            ));

            prev_fact = fact_id;
            counter = counter.wrapping_add(1);
            result
        })
    });
}

fn bench_causal_clock_observe(c: &mut Criterion) {
    let mut clock = CausalClock::new();
    let fact_id: FactId = [0xAB; 32];

    c.bench_function("causal_clock_observe", |b| {
        b.iter(|| black_box(clock.observe(black_box(&fact_id))))
    });
}

fn bench_causal_clock_dominates(c: &mut Criterion) {
    let mut clock_a = CausalClock::new();
    let mut clock_b = CausalClock::new();

    for i in 0..50u8 {
        let mut fact_id = [0u8; 32];
        fact_id[0] = i;
        clock_a.observe(&fact_id);
        if i < 25 {
            clock_b.observe(&fact_id);
        }
    }

    c.bench_function("causal_clock_dominates", |b| {
        b.iter(|| black_box(clock_a.dominates(black_box(&clock_b))))
    });
}

fn bench_build_deps_clock(c: &mut Criterion) {
    let deps: [FactId; 4] = [[1u8; 32], [2u8; 32], [3u8; 32], [4u8; 32]];

    c.bench_function("build_deps_clock_4", |b| {
        b.iter(|| black_box(build_deps_clock(black_box(&deps))))
    });
}

fn bench_full_admission_cycle(c: &mut Criterion) {
    c.bench_function("full_admission_cycle", |b| {
        let state = make_state_cell(0, i128::MIN, i128::MAX);
        let mut kernel = Kernel::with_state(TotalSupplyInvariant::new(), state);
        let payload = make_payload(1);

        let genesis: FactId = [0u8; 32];
        kernel.admit_raw(&genesis, &[], &payload).unwrap();

        let mut counter = 1u64;
        let mut prev_fact = genesis;

        b.iter(|| {
            let mut fact_id: FactId = [0u8; 32];
            fact_id[..8].copy_from_slice(&counter.to_le_bytes());

            let result = kernel.admit_raw(&fact_id, &[prev_fact], &payload);

            prev_fact = fact_id;
            counter = counter.wrapping_add(1);
            black_box(result)
        })
    });
}

criterion_group!(
    benches,
    bench_admit_fact_no_deps,
    bench_admit_fact_with_deps,
    bench_causal_clock_observe,
    bench_causal_clock_dominates,
    bench_build_deps_clock,
    bench_full_admission_cycle,
);
criterion_main!(benches);
