//! Evaluation benchmarks. Latency, throughput, convergence.

use criterion::{
    black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput,
};
use std::time::{Duration, Instant};

use cuttlefish::core::checkpoint::Checkpoint;
use cuttlefish::core::kernel::TwoLaneKernel;
use cuttlefish::core::state::StateCell;
use cuttlefish::core::topology::{CausalClock, ExactCausalIndex, FactId};
use cuttlefish::invariants::total_supply::{ConservationState, TotalSupplyInvariant};
use zerocopy::IntoBytes;

fn make_conservation_state(balance: i128, min: i128, max: i128) -> StateCell {
    let state = ConservationState::new(balance, min, max);
    let mut cell = StateCell::new();
    cell.as_slice_mut().copy_from_slice(state.as_bytes());
    cell
}

fn make_payload(delta: i128) -> [u8; 16] {
    delta.to_le_bytes()
}

fn make_fact_id(index: u64) -> FactId {
    let mut id = [0u8; 32];
    id[0..8].copy_from_slice(&index.to_le_bytes());
    let hash = blake3::hash(&id);
    *hash.as_bytes()
}

struct SimpleLcg {
    state: u64,
}

impl SimpleLcg {
    fn new(seed: u64) -> Self {
        Self { state: seed }
    }

    fn next(&mut self) -> u64 {
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1);
        self.state
    }
}

/// O(n) baseline for comparison.
struct NaiveKernel {
    state: StateCell,
    admitted: Vec<FactId>,
    invariant: TotalSupplyInvariant,
}

impl NaiveKernel {
    fn new() -> Self {
        let state = make_conservation_state(0, i128::MIN, i128::MAX);
        Self {
            state,
            admitted: Vec::with_capacity(10000),
            invariant: TotalSupplyInvariant::new(),
        }
    }

    fn admit(&mut self, fact_id: &FactId, deps: &[FactId], payload: &[u8]) -> Result<(), ()> {
        // O(n*m) dependency check - linear scan for each dep
        for dep in deps {
            if !self.admitted.contains(dep) {
                return Err(());
            }
        }

        // Apply invariant
        use cuttlefish::core::invariant::Invariant;
        self.invariant
            .apply(payload, self.state.as_bytes_mut())
            .map_err(|_| ())?;

        self.admitted.push(*fact_id);
        Ok(())
    }

    fn state_hash(&self) -> [u8; 32] {
        Checkpoint::compute_state_hash(&self.state)
    }
}

fn bench_latency_distribution(c: &mut Criterion) {
    let mut group = c.benchmark_group("latency_distribution");
    group.sample_size(1000);

    group.bench_function("two_lane_kernel", |b| {
        let state = make_conservation_state(0, i128::MIN, i128::MAX);
        let mut kernel = TwoLaneKernel::with_state(TotalSupplyInvariant::new(), state);
        let payload = make_payload(1);
        let mut counter = 0u64;

        b.iter(|| {
            let fact_id = make_fact_id(counter);
            counter += 1;
            black_box(kernel.admit(&fact_id, &[], &payload))
        })
    });

    group.bench_function("naive_baseline", |b| {
        let mut kernel = NaiveKernel::new();
        let payload = make_payload(1);
        let mut counter = 0u64;

        b.iter(|| {
            let fact_id = make_fact_id(counter);
            counter += 1;
            black_box(kernel.admit(&fact_id, &[], &payload))
        })
    });

    group.finish();
}

fn bench_throughput(c: &mut Criterion) {
    let mut group = c.benchmark_group("throughput");

    for batch_size in [100, 1000, 10000] {
        group.throughput(Throughput::Elements(batch_size as u64));

        group.bench_with_input(
            BenchmarkId::new("two_lane_kernel", batch_size),
            &batch_size,
            |b, &size| {
                b.iter_custom(|iters| {
                    let mut total = Duration::ZERO;

                    for _ in 0..iters {
                        let state = make_conservation_state(0, i128::MIN, i128::MAX);
                        let mut kernel =
                            TwoLaneKernel::with_state(TotalSupplyInvariant::new(), state);
                        let payload = make_payload(1);

                        let start = Instant::now();
                        for i in 0..size {
                            let fact_id = make_fact_id(i as u64);
                            let _ = black_box(kernel.admit(&fact_id, &[], &payload));
                        }
                        total += start.elapsed();
                    }

                    total
                })
            },
        );

        group.bench_with_input(
            BenchmarkId::new("naive_baseline", batch_size),
            &batch_size,
            |b, &size| {
                b.iter_custom(|iters| {
                    let mut total = Duration::ZERO;

                    for _ in 0..iters {
                        let mut kernel = NaiveKernel::new();
                        let payload = make_payload(1);

                        let start = Instant::now();
                        for i in 0..size {
                            let fact_id = make_fact_id(i as u64);
                            let _ = black_box(kernel.admit(&fact_id, &[], &payload));
                        }
                        total += start.elapsed();
                    }

                    total
                })
            },
        );
    }

    group.finish();
}

fn bench_dependency_overhead(c: &mut Criterion) {
    let mut group = c.benchmark_group("dependency_overhead");

    for dep_count in [0, 1, 2, 4, 8] {
        group.bench_with_input(
            BenchmarkId::new("two_lane", dep_count),
            &dep_count,
            |b, &deps| {
                let state = make_conservation_state(0, i128::MIN, i128::MAX);
                let mut kernel =
                    TwoLaneKernel::with_state(TotalSupplyInvariant::new(), state);
                let payload = make_payload(1);

                let mut dep_ids: Vec<FactId> = Vec::new();
                for i in 0..deps {
                    let fact_id = make_fact_id(i as u64);
                    kernel.admit(&fact_id, &[], &payload).unwrap();
                    dep_ids.push(fact_id);
                }

                let mut counter = deps as u64;

                b.iter(|| {
                    let fact_id = make_fact_id(counter);
                    counter += 1;
                    let result = kernel.admit(&fact_id, &dep_ids, &payload);
                    if !dep_ids.is_empty() {
                        dep_ids[0] = fact_id;
                    }
                    black_box(result)
                })
            },
        );

        group.bench_with_input(
            BenchmarkId::new("naive", dep_count),
            &dep_count,
            |b, &deps| {
                let mut kernel = NaiveKernel::new();
                let payload = make_payload(1);

                let mut dep_ids: Vec<FactId> = Vec::new();
                for i in 0..deps {
                    let fact_id = make_fact_id(i as u64);
                    kernel.admit(&fact_id, &[], &payload).unwrap();
                    dep_ids.push(fact_id);
                }

                let mut counter = deps as u64;

                b.iter(|| {
                    let fact_id = make_fact_id(counter);
                    counter += 1;
                    let result = kernel.admit(&fact_id, &dep_ids, &payload);
                    if !dep_ids.is_empty() {
                        dep_ids[0] = fact_id;
                    }
                    black_box(result)
                })
            },
        );
    }

    group.finish();
}

fn bench_convergence_time(c: &mut Criterion) {
    let mut group = c.benchmark_group("convergence_time");
    group.sample_size(50);

    for node_count in [2, 3, 5] {
        for fact_count in [100, 500, 1000] {
            group.bench_with_input(
                BenchmarkId::new(format!("{}_nodes", node_count), fact_count),
                &(node_count, fact_count),
                |b, &(nodes, facts)| {
                    b.iter_custom(|iters| {
                        let mut total = Duration::ZERO;

                        for iter in 0..iters {
                            let mut rng = SimpleLcg::new(iter);
                            let payload = make_payload(1);

                            let fact_ids: Vec<FactId> =
                                (0..facts).map(|i| make_fact_id(i as u64)).collect();

                            let mut kernels: Vec<TwoLaneKernel<TotalSupplyInvariant>> = (0..nodes)
                                .map(|_| {
                                    let state = make_conservation_state(0, i128::MIN, i128::MAX);
                                    TwoLaneKernel::with_state(TotalSupplyInvariant::new(), state)
                                })
                                .collect();

                            let start = Instant::now();

                            for (node_idx, kernel) in kernels.iter_mut().enumerate() {
                                let mut order: Vec<usize> = (0..facts).collect();
                                let mut shuffle_rng = SimpleLcg::new(node_idx as u64 * 1000 + iter);
                                for i in (1..facts).rev() {
                                    let j = (shuffle_rng.next() % (i as u64 + 1)) as usize;
                                    order.swap(i, j);
                                }

                                for &idx in &order {
                                    let _ = kernel.admit(&fact_ids[idx], &[], &payload);
                                }
                            }

                            let hash0 = Checkpoint::compute_state_hash(kernels[0].state());
                            for kernel in &kernels[1..] {
                                let hash = Checkpoint::compute_state_hash(kernel.state());
                                assert_eq!(hash0, hash, "Convergence failure");
                            }

                            total += start.elapsed();
                        }

                        total
                    })
                },
            );
        }
    }

    group.finish();
}

fn bench_simd_vs_scalar(c: &mut Criterion) {
    let mut group = c.benchmark_group("simd_vs_scalar");

    let mut index = ExactCausalIndex::new();
    for i in 0u64..500 {
        let fact_id = make_fact_id(i);
        index.insert(&fact_id);
    }

    group.bench_function("contains_simd", |b| {
        let mut counter = 0u64;
        b.iter(|| {
            let fact_id = make_fact_id(counter % 500);
            counter += 1;
            black_box(index.contains_simd(&fact_id))
        })
    });

    group.bench_function("contains_scalar", |b| {
        let mut counter = 0u64;
        b.iter(|| {
            let fact_id = make_fact_id(counter % 500);
            counter += 1;
            black_box(index.contains(&fact_id))
        })
    });

    group.finish();
}

fn bench_memory_footprint(c: &mut Criterion) {
    let mut group = c.benchmark_group("memory_footprint");

    group.bench_function("report_sizes", |b| {
        b.iter(|| {
            let state_cell_size = std::mem::size_of::<StateCell>();
            let exact_index_size = std::mem::size_of::<ExactCausalIndex>();
            let causal_clock_size = std::mem::size_of::<CausalClock>();
            let kernel_size = std::mem::size_of::<TwoLaneKernel<TotalSupplyInvariant>>();

            black_box((state_cell_size, exact_index_size, causal_clock_size, kernel_size))
        })
    });

    println!("\n=== Memory Footprint ===");
    println!("StateCell:        {} bytes", std::mem::size_of::<StateCell>());
    println!("ExactCausalIndex: {} bytes", std::mem::size_of::<ExactCausalIndex>());
    println!("CausalClock:      {} bytes", std::mem::size_of::<CausalClock>());
    println!(
        "TwoLaneKernel:    {} bytes",
        std::mem::size_of::<TwoLaneKernel<TotalSupplyInvariant>>()
    );
    println!("========================\n");

    group.finish();
}

// ============================================================================
// Criterion Groups
// ============================================================================

criterion_group!(
    name = latency;
    config = Criterion::default().significance_level(0.01).sample_size(500);
    targets = bench_latency_distribution
);

criterion_group!(
    name = throughput;
    config = Criterion::default().sample_size(100);
    targets = bench_throughput
);

criterion_group!(
    name = dependencies;
    config = Criterion::default().sample_size(200);
    targets = bench_dependency_overhead
);

criterion_group!(
    name = convergence;
    config = Criterion::default().sample_size(50);
    targets = bench_convergence_time
);

criterion_group!(
    name = simd;
    config = Criterion::default().sample_size(500);
    targets = bench_simd_vs_scalar
);

criterion_group!(
    name = memory;
    config = Criterion::default().sample_size(10);
    targets = bench_memory_footprint
);

criterion_main!(latency, throughput, dependencies, convergence, simd, memory);
