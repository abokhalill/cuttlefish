use criterion::{black_box, criterion_group, criterion_main, Criterion};
use cuttlefish::core::kernel::DualKernel;
use cuttlefish::core::state::StateCell;
use cuttlefish::core::topology::FactId;
use cuttlefish::invariants::total_supply::{ConservationState, TotalSupplyInvariant};
use cuttlefish::invariants::uniqueness::{UniquenessInvariant, UniquenessPayload};
use zerocopy::IntoBytes;

fn make_conservation_state(balance: i128, min: i128, max: i128) -> StateCell {
    let state = ConservationState::new(balance, min, max);
    let mut cell = StateCell::new();
    cell.as_slice_mut().copy_from_slice(state.as_bytes());
    cell
}

fn make_uniqueness_state() -> StateCell {
    StateCell::new()
}

fn make_conservation_payload(delta: i128) -> [u8; 16] {
    let mut buf = [0u8; 16];
    buf.copy_from_slice(&delta.to_le_bytes());
    buf
}

fn make_uniqueness_payload(element_id: u16) -> [u8; 16] {
    let payload = UniquenessPayload::new(element_id);
    let mut buf = [0u8; 16];
    buf.copy_from_slice(payload.as_bytes());
    buf
}

fn bench_dual_kernel_admit(c: &mut Criterion) {
    let conservation_state = make_conservation_state(0, i128::MIN, i128::MAX);
    let uniqueness_state = make_uniqueness_state();

    let mut kernel = DualKernel::new(
        TotalSupplyInvariant::new(),
        conservation_state,
        UniquenessInvariant::new(),
        uniqueness_state,
    );

    let conservation_payload = make_conservation_payload(1);

    c.bench_function("dual_kernel_admit_no_deps", |b| {
        let mut counter = 0u64;
        b.iter(|| {
            let mut fact_id: FactId = [0u8; 32];
            fact_id[..8].copy_from_slice(&counter.to_le_bytes());

            let uniqueness_payload = make_uniqueness_payload((counter & 0x1FF) as u16);

            let result = kernel.admit(
                black_box(&fact_id),
                black_box(&[]),
                black_box(&conservation_payload),
                black_box(&uniqueness_payload),
            );

            counter = counter.wrapping_add(1);
            black_box(result)
        })
    });
}

fn bench_dual_kernel_admit_with_dep(c: &mut Criterion) {
    let conservation_state = make_conservation_state(0, i128::MIN, i128::MAX);
    let uniqueness_state = make_uniqueness_state();

    let mut kernel = DualKernel::new(
        TotalSupplyInvariant::new(),
        conservation_state,
        UniquenessInvariant::new(),
        uniqueness_state,
    );

    let conservation_payload = make_conservation_payload(1);

    let genesis: FactId = [0u8; 32];
    let uniqueness_payload_genesis = make_uniqueness_payload(0);
    kernel
        .admit(
            &genesis,
            &[],
            &conservation_payload,
            &uniqueness_payload_genesis,
        )
        .unwrap();

    c.bench_function("dual_kernel_admit_with_1_dep", |b| {
        let mut counter = 1u64;
        let mut prev_fact = genesis;

        b.iter(|| {
            let mut fact_id: FactId = [0u8; 32];
            fact_id[..8].copy_from_slice(&counter.to_le_bytes());

            let uniqueness_payload = make_uniqueness_payload((counter & 0x1FF) as u16);

            let result = kernel.admit(
                black_box(&fact_id),
                black_box(&[prev_fact]),
                black_box(&conservation_payload),
                black_box(&uniqueness_payload),
            );

            prev_fact = fact_id;
            counter = counter.wrapping_add(1);
            black_box(result)
        })
    });
}

fn bench_multi_invariant_full_cycle(c: &mut Criterion) {
    c.bench_function("multi_invariant_full_admission", |b| {
        let conservation_state = make_conservation_state(0, i128::MIN, i128::MAX);
        let uniqueness_state = make_uniqueness_state();

        let mut kernel = DualKernel::new(
            TotalSupplyInvariant::new(),
            conservation_state,
            UniquenessInvariant::new(),
            uniqueness_state,
        );

        let conservation_payload = make_conservation_payload(1);

        let genesis: FactId = [0u8; 32];
        let uniqueness_payload_genesis = make_uniqueness_payload(0);
        kernel
            .admit(
                &genesis,
                &[],
                &conservation_payload,
                &uniqueness_payload_genesis,
            )
            .unwrap();

        let mut counter = 1u64;
        let mut prev_fact = genesis;

        b.iter(|| {
            let mut fact_id: FactId = [0u8; 32];
            fact_id[..8].copy_from_slice(&counter.to_le_bytes());

            let uniqueness_payload = make_uniqueness_payload((counter & 0x1FF) as u16);

            let result = kernel.admit(
                &fact_id,
                &[prev_fact],
                &conservation_payload,
                &uniqueness_payload,
            );

            prev_fact = fact_id;
            counter = counter.wrapping_add(1);
            black_box(result)
        })
    });
}

criterion_group!(
    benches,
    bench_dual_kernel_admit,
    bench_dual_kernel_admit_with_dep,
    bench_multi_invariant_full_cycle,
);
criterion_main!(benches);
