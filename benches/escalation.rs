//! Stress test benchmarks for BFVC saturation and escalation.
//!
//! Target: Even in precise mode, admission must stay < 1,000ns (1µs).

use criterion::{criterion_group, criterion_main, Criterion};
use ctfs::core::kernel::{CausalMode, EscalatingKernel};
use ctfs::core::state::StateCell;
use ctfs::core::topology::FactId;
use ctfs::invariants::total_supply::{ConservationState, TotalSupplyInvariant};
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

/// Benchmark admission in fast mode (low saturation).
fn bench_fast_mode_admission(c: &mut Criterion) {
    let state = make_conservation_state(0, i128::MIN, i128::MAX);
    let mut kernel = EscalatingKernel::with_state(TotalSupplyInvariant::new(), state);
    let payload = make_payload(1);

    c.bench_function("escalating_fast_mode", |b| {
        let mut counter = 0u64;
        b.iter(|| {
            let mut fact_id: FactId = [0u8; 32];
            fact_id[..8].copy_from_slice(&counter.to_le_bytes());
            counter = counter.wrapping_add(1);

            black_box(kernel.admit(black_box(&fact_id), black_box(&[]), black_box(&payload)))
        })
    });
}

/// Benchmark admission in precise mode (forced escalation).
fn bench_precise_mode_admission(c: &mut Criterion) {
    let state = make_conservation_state(0, i128::MIN, i128::MAX);
    let mut kernel = EscalatingKernel::with_state(TotalSupplyInvariant::new(), state);
    let payload = make_payload(1);

    // Force escalation
    kernel.escalate();
    assert_eq!(kernel.current_mode(), CausalMode::Precise);

    c.bench_function("escalating_precise_mode", |b| {
        let mut counter = 0u64;
        b.iter(|| {
            let mut fact_id: FactId = [0u8; 32];
            fact_id[..8].copy_from_slice(&counter.to_le_bytes());
            counter = counter.wrapping_add(1);

            black_box(kernel.admit(black_box(&fact_id), black_box(&[]), black_box(&payload)))
        })
    });
}

/// Benchmark precise mode with dependency checking.
fn bench_precise_mode_with_deps(c: &mut Criterion) {
    let state = make_conservation_state(0, i128::MIN, i128::MAX);
    let mut kernel = EscalatingKernel::with_state(TotalSupplyInvariant::new(), state);
    let payload = make_payload(1);

    // Admit genesis fact
    let genesis: FactId = [0u8; 32];
    kernel.admit(&genesis, &[], &payload).unwrap();

    // Force escalation
    kernel.escalate();

    c.bench_function("escalating_precise_with_deps", |b| {
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

/// Stress test: Rapid admission forcing saturation and escalation.
fn bench_saturated_admission(c: &mut Criterion) {
    c.bench_function("saturated_admission_10k", |b| {
        b.iter_custom(|iters| {
            let mut total_time = std::time::Duration::ZERO;

            for _ in 0..iters {
                let state = make_conservation_state(0, i128::MIN, i128::MAX);
                let mut kernel = EscalatingKernel::with_state(TotalSupplyInvariant::new(), state);
                let payload = make_payload(1);

                // Pre-saturate with 10,000 facts to force escalation
                for i in 0..10_000u64 {
                    let mut fact_id: FactId = [0u8; 32];
                    fact_id[..8].copy_from_slice(&i.to_le_bytes());
                    let _ = kernel.admit(&fact_id, &[], &payload);
                }

                // Now measure admission in saturated state
                let start = std::time::Instant::now();
                let mut fact_id: FactId = [0u8; 32];
                fact_id[..8].copy_from_slice(&10_001u64.to_le_bytes());
                let _ = black_box(kernel.admit(&fact_id, &[], &payload));
                total_time += start.elapsed();
            }

            total_time
        })
    });
}

/// Benchmark escalation transition point.
fn bench_escalation_transition(c: &mut Criterion) {
    c.bench_function("escalation_transition", |b| {
        let state = make_conservation_state(0, i128::MIN, i128::MAX);
        let mut kernel = EscalatingKernel::with_state(TotalSupplyInvariant::new(), state);
        let payload = make_payload(1);

        // Admit facts until just below escalation threshold
        // At 40% saturation of 512 bits = ~205 bits set
        // With 3 bits per fact, need ~68 unique facts minimum
        // But due to hash collisions, need more
        for i in 0..150u64 {
            let mut fact_id: FactId = [0u8; 32];
            fact_id[..8].copy_from_slice(&i.to_le_bytes());
            let _ = kernel.admit(&fact_id, &[], &payload);
        }

        let initial_mode = kernel.current_mode();

        b.iter(|| {
            // Reset for consistent measurement
            kernel.reset_mode();

            // Re-check escalation
            let mut fact_id: FactId = [0xFF; 32];
            let result = kernel.admit(&fact_id, &[], &payload);

            black_box((result, kernel.current_mode() != initial_mode))
        })
    });
}

/// Benchmark conflict resolution (deterministic tie-breaking).
fn bench_conflict_resolution(c: &mut Criterion) {
    use ctfs::core::topology::{resolve_conflict, wins_conflict};

    let fact_a: FactId = [0x11; 32];
    let fact_b: FactId = [0x22; 32];

    c.bench_function("conflict_resolution", |b| {
        b.iter(|| black_box(resolve_conflict(black_box(&fact_a), black_box(&fact_b))))
    });

    c.bench_function("wins_conflict", |b| {
        b.iter(|| black_box(wins_conflict(black_box(&fact_a), black_box(&fact_b))))
    });
}

criterion_group!(
    benches,
    bench_fast_mode_admission,
    bench_precise_mode_admission,
    bench_precise_mode_with_deps,
    bench_saturated_admission,
    bench_escalation_transition,
    bench_conflict_resolution,
);
criterion_main!(benches);
