//! Simulated network benchmark: measures causal diffusion latency.
//! Target: Admit(Node A) -> Broadcast -> Serialize -> Deserialize -> Admit(Node B) < 1ms

use criterion::{criterion_group, criterion_main, Criterion};
use std::hint::black_box;
use std::sync::mpsc;
use std::thread;
use std::time::Instant;

use cuttlefish::core::kernel::{BroadcastBuffer, Kernel, BROADCAST_BUFFER_SIZE};
use cuttlefish::core::state::StateCell;
use cuttlefish::core::topology::{CausalClock, FactId};
use cuttlefish::invariants::total_supply::{ConservationState, TotalSupplyInvariant};
use cuttlefish::network::NetworkMessage;
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

/// Benchmark the full causal diffusion path (simulated, in-process).
fn bench_causal_diffusion(c: &mut Criterion) {
    c.bench_function("causal_diffusion_simulated", |b| {
        b.iter_custom(|iters| {
            let mut total_time = std::time::Duration::ZERO;

            for i in 0..iters {
                // Setup Node A
                let state_a = make_conservation_state(0, i128::MIN, i128::MAX);
                let mut kernel_a = Kernel::with_state(TotalSupplyInvariant::new(), state_a);

                // Setup Node B
                let state_b = make_conservation_state(0, i128::MIN, i128::MAX);
                let mut kernel_b = Kernel::with_state(TotalSupplyInvariant::new(), state_b);

                let payload = make_payload(1);
                let mut fact_id: FactId = [0u8; 32];
                fact_id[..8].copy_from_slice(&i.to_le_bytes());

                let start = Instant::now();

                // Step 1: Admit on Node A
                kernel_a.admit_raw(&fact_id, &[], &payload).unwrap();

                // Step 2: Serialize for network (PushFact message)
                let msg = NetworkMessage::PushFact {
                    fact_id,
                    payload: payload.to_vec(),
                };
                let wire_bytes = msg.encode();

                // Step 3: Deserialize on Node B
                let received = NetworkMessage::decode(&wire_bytes).unwrap();

                // Step 4: Admit on Node B
                if let NetworkMessage::PushFact { fact_id: id, payload: p } = received {
                    kernel_b.admit_raw(&id, &[], &p).unwrap();
                }

                total_time += start.elapsed();

                // Verify causal consistency
                assert!(kernel_b.clock().might_contain(&fact_id));
            }

            total_time
        })
    });
}

/// Benchmark just the serialization/deserialization overhead.
fn bench_wire_protocol_roundtrip(c: &mut Criterion) {
    let fact_id: FactId = [0xAB; 32];
    let payload = make_payload(100);

    c.bench_function("wire_protocol_roundtrip", |b| {
        b.iter(|| {
            let msg = NetworkMessage::PushFact {
                fact_id: black_box(fact_id),
                payload: black_box(payload.to_vec()),
            };
            let encoded = msg.encode();
            let decoded = NetworkMessage::decode(black_box(&encoded));
            black_box(decoded)
        })
    });
}

/// Benchmark gossip clock exchange.
fn bench_gossip_clock_roundtrip(c: &mut Criterion) {
    let mut clock = CausalClock::new();
    for i in 0..100 {
        let mut id = [0u8; 32];
        id[0] = i;
        clock.observe(&id);
    }

    c.bench_function("gossip_clock_roundtrip", |b| {
        b.iter(|| {
            let msg = NetworkMessage::GossipClock(black_box(clock));
            let encoded = msg.encode();
            let decoded = NetworkMessage::decode(black_box(&encoded));
            black_box(decoded)
        })
    });
}

/// Benchmark broadcast SPSC push latency (must stay < 15ns).
fn bench_broadcast_push(c: &mut Criterion) {
    let buffer: BroadcastBuffer<BROADCAST_BUFFER_SIZE> = BroadcastBuffer::new();
    let (producer, consumer) = buffer.split();

    c.bench_function("broadcast_spsc_push", |b| {
        let mut counter = 0u64;
        b.iter(|| {
            let mut fact_id: FactId = [0u8; 32];
            fact_id[..8].copy_from_slice(&counter.to_le_bytes());
            counter = counter.wrapping_add(1);

            // Drain periodically
            if counter % 4000 == 0 {
                while consumer.try_pop().is_some() {}
            }

            black_box(producer.try_push(black_box(fact_id)))
        })
    });
}

/// Multi-threaded diffusion simulation.
fn bench_threaded_diffusion(c: &mut Criterion) {
    c.bench_function("threaded_diffusion", |b| {
        b.iter_custom(|iters| {
            let mut total_time = std::time::Duration::ZERO;

            for i in 0..iters {
                let (tx, rx) = mpsc::channel::<Vec<u8>>();

                let payload = make_payload(1);
                let mut fact_id: FactId = [0u8; 32];
                fact_id[..8].copy_from_slice(&i.to_le_bytes());
                let payload_clone = payload;

                // Node B thread
                let handle = thread::spawn(move || {
                    let state_b = make_conservation_state(0, i128::MIN, i128::MAX);
                    let mut kernel_b = Kernel::with_state(TotalSupplyInvariant::new(), state_b);

                    let wire_bytes = rx.recv().unwrap();
                    let received = NetworkMessage::decode(&wire_bytes).unwrap();

                    if let NetworkMessage::PushFact { fact_id: id, payload: p } = received {
                        kernel_b.admit_raw(&id, &[], &p).unwrap();
                    }
                });

                // Node A: admit + serialize + send
                let state_a = make_conservation_state(0, i128::MIN, i128::MAX);
                let mut kernel_a = Kernel::with_state(TotalSupplyInvariant::new(), state_a);

                let start = Instant::now();

                kernel_a.admit_raw(&fact_id, &[], &payload_clone).unwrap();

                let msg = NetworkMessage::PushFact {
                    fact_id,
                    payload: payload_clone.to_vec(),
                };
                let wire_bytes = msg.encode();

                tx.send(wire_bytes).unwrap();
                handle.join().unwrap();

                total_time += start.elapsed();
            }

            total_time
        })
    });
}

criterion_group!(
    benches,
    bench_causal_diffusion,
    bench_wire_protocol_roundtrip,
    bench_gossip_clock_roundtrip,
    bench_broadcast_push,
    bench_threaded_diffusion,
);
criterion_main!(benches);
