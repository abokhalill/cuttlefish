//! Benchmarks for checkpoint verification and re-anchoring operations.
//!
//! Target: Verification + State Import < 5,000ns (5µs)

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use cuttlefish::core::checkpoint::{Attestation, Checkpoint, ProofEnvelope};
use cuttlefish::core::frontier::Frontier;
use cuttlefish::core::kernel::Kernel;
use cuttlefish::core::state::StateCell;
use cuttlefish::core::topology::{CausalClock, FactId};
use cuttlefish::invariants::total_supply::{ConservationState, TotalSupplyInvariant};
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

/// Create a valid checkpoint with quorum attestations.
fn make_checkpoint(state: StateCell, frontier: Frontier, clock: CausalClock) -> Checkpoint {
    let state_hash = Checkpoint::compute_state_hash(&state);

    // Create proof envelope with 5 valid attestations (meets default quorum)
    let mut proof = ProofEnvelope::new(5);
    for i in 0..5 {
        let mut validator = [0u8; 32];
        validator[0] = i as u8;
        let attestation = Attestation::mock_sign(validator, &state_hash);
        proof.add_attestation(i, attestation);
    }

    Checkpoint::new(frontier, clock, state, state_hash, proof)
}

fn bench_checkpoint_verify(c: &mut Criterion) {
    let state = make_conservation_state(1000, 0, i128::MAX);
    let checkpoint = make_checkpoint(state, Frontier::new_const(), CausalClock::new());

    c.bench_function("checkpoint_verify", |b| {
        b.iter(|| black_box(checkpoint.verify()))
    });
}

fn bench_reanchor_no_replay(c: &mut Criterion) {
    let initial_state = make_conservation_state(0, 0, i128::MAX);
    let mut kernel = Kernel::with_state(TotalSupplyInvariant::new(), initial_state);

    // Create checkpoint with some state
    let checkpoint_state = make_conservation_state(5000, 0, i128::MAX);
    let mut checkpoint_clock = CausalClock::new();
    let checkpoint_fact: FactId = [0xAB; 32];
    checkpoint_clock.observe(&checkpoint_fact);

    let mut frontier = Frontier::new_const();
    frontier.push(checkpoint_fact);

    let checkpoint = make_checkpoint(checkpoint_state, frontier, checkpoint_clock);

    c.bench_function("reanchor_no_replay", |b| {
        b.iter(|| {
            let result = kernel.re_anchor(black_box(&checkpoint), black_box(&[]));
            black_box(result)
        })
    });
}

fn bench_reanchor_with_replay_10(c: &mut Criterion) {
    let initial_state = make_conservation_state(0, 0, i128::MAX);

    // Create checkpoint
    let checkpoint_state = make_conservation_state(5000, 0, i128::MAX);
    let mut checkpoint_clock = CausalClock::new();
    let checkpoint_fact: FactId = [0xAB; 32];
    checkpoint_clock.observe(&checkpoint_fact);

    let mut frontier = Frontier::new_const();
    frontier.push(checkpoint_fact);

    let checkpoint = make_checkpoint(checkpoint_state, frontier, checkpoint_clock);

    // Prepare 10 new facts to replay
    let payload = make_payload(1);
    let new_facts: Vec<(FactId, [u8; 16])> = (0..10u64)
        .map(|i| {
            let mut fact_id = [0u8; 32];
            fact_id[..8].copy_from_slice(&i.to_le_bytes());
            (fact_id, payload)
        })
        .collect();

    c.bench_function("reanchor_replay_10_facts", |b| {
        let mut kernel = Kernel::with_state(TotalSupplyInvariant::new(), initial_state);

        b.iter(|| {
            // Convert to slice of references for the API
            let refs: Vec<(&FactId, &[u8])> =
                new_facts.iter().map(|(id, p)| (id, p.as_slice())).collect();

            let result = kernel.re_anchor(black_box(&checkpoint), black_box(&refs));
            black_box(result)
        })
    });
}

fn bench_reanchor_with_replay_100(c: &mut Criterion) {
    let initial_state = make_conservation_state(0, 0, i128::MAX);

    // Create checkpoint
    let checkpoint_state = make_conservation_state(5000, 0, i128::MAX);
    let mut checkpoint_clock = CausalClock::new();
    let checkpoint_fact: FactId = [0xAB; 32];
    checkpoint_clock.observe(&checkpoint_fact);

    let mut frontier = Frontier::new_const();
    frontier.push(checkpoint_fact);

    let checkpoint = make_checkpoint(checkpoint_state, frontier, checkpoint_clock);

    // Prepare 100 new facts to replay
    let payload = make_payload(1);
    let new_facts: Vec<(FactId, [u8; 16])> = (0..100u64)
        .map(|i| {
            let mut fact_id = [0u8; 32];
            fact_id[..8].copy_from_slice(&i.to_le_bytes());
            (fact_id, payload)
        })
        .collect();

    c.bench_function("reanchor_replay_100_facts", |b| {
        let mut kernel = Kernel::with_state(TotalSupplyInvariant::new(), initial_state);

        b.iter(|| {
            let refs: Vec<(&FactId, &[u8])> =
                new_facts.iter().map(|(id, p)| (id, p.as_slice())).collect();

            let result = kernel.re_anchor(black_box(&checkpoint), black_box(&refs));
            black_box(result)
        })
    });
}

fn bench_full_reanchor_cycle(c: &mut Criterion) {
    c.bench_function("full_reanchor_cycle", |b| {
        let initial_state = make_conservation_state(0, 0, i128::MAX);
        let mut kernel = Kernel::with_state(TotalSupplyInvariant::new(), initial_state);

        // Simulate: node was partitioned, missed 1000 facts
        // Checkpoint captures state after those 1000 facts
        let checkpoint_state = make_conservation_state(1_000_000, 0, i128::MAX);
        let mut checkpoint_clock = CausalClock::new();

        // Simulate checkpoint covering many facts
        for i in 0..100u8 {
            let mut fact_id = [0u8; 32];
            fact_id[0] = i;
            checkpoint_clock.observe(&fact_id);
        }

        let checkpoint_fact: FactId = [0xFF; 32];
        checkpoint_clock.observe(&checkpoint_fact);

        let mut frontier = Frontier::new_const();
        frontier.push(checkpoint_fact);

        let checkpoint = make_checkpoint(checkpoint_state, frontier, checkpoint_clock);

        // 10 new facts after checkpoint
        let payload = make_payload(100);
        let new_facts: Vec<(FactId, [u8; 16])> = (0..10u64)
            .map(|i| {
                let mut fact_id = [0u8; 32];
                fact_id[..8].copy_from_slice(&(i + 1000).to_le_bytes());
                (fact_id, payload)
            })
            .collect();

        b.iter(|| {
            let refs: Vec<(&FactId, &[u8])> =
                new_facts.iter().map(|(id, p)| (id, p.as_slice())).collect();

            let result = kernel.re_anchor(&checkpoint, &refs);
            black_box(result)
        })
    });
}

criterion_group!(
    benches,
    bench_checkpoint_verify,
    bench_reanchor_no_replay,
    bench_reanchor_with_replay_10,
    bench_reanchor_with_replay_100,
    bench_full_reanchor_cycle,
);
criterion_main!(benches);
