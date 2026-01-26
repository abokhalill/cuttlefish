# Cuttlefish

**Coordination-free invariant enforcement at nanosecond scale.**

```
Fact → Causality Check → Δ_I Apply → Frontier Advance → Done
2ns per operation. 500M ops/sec. Zero coordination.
```

You define algebraic invariants. We enforce them without consensus, without locks, without coordination—unless the math says otherwise.

**The thesis:** Correctness is a property of algebra, not execution order. Commutative operations don't need coordination.

---

## Performance

| Operation | Latency | Throughput |
|-----------|---------|------------|
| Conservation Δ_I | 2.0 ns | 500M ops/sec |
| Max Δ_I | 1.9 ns | 526M ops/sec |
| BFVC dominance | 1.2 ns | 833M ops/sec |
| Exact causal lookup | 7.0 ns | 142M ops/sec |

15x faster than mutex. 100-1000x faster than traditional databases.

---

## Quick Start

```toml
[dependencies]
cuttlefish = "0.1.0"
```

```rust
use cuttlefish::core::kernel::TwoLaneKernel;
use cuttlefish::core::state::StateCell;
use cuttlefish::invariants::total_supply::{ConservationState, TotalSupplyInvariant};
use zerocopy::IntoBytes;

let state = ConservationState::new(0, i128::MIN, i128::MAX);
let mut cell = StateCell::new();
cell.as_slice_mut().copy_from_slice(state.as_bytes());

let mut kernel = TwoLaneKernel::with_state(TotalSupplyInvariant::new(), cell);

let fact_id: [u8; 32] = blake3::hash(b"fact-001").into();
let payload = 100i128.to_le_bytes();

kernel.admit(&fact_id, &[], &payload).unwrap();
```

---

## Core Concepts

**Facts** — Immutable, content-addressed state transitions forming a causal DAG.

**Invariants** — Algebraic constraints enforced via Δ_I: pure, O(1), allocation-free.

**Two-Tier Causality** — BFVC (512-bit Bloom filter, ~1ns) + ExactCausalIndex (Robin Hood, ~7ns).

**StateCell** — 64-byte cache-aligned POD. Bit-for-bit deterministic across nodes.

---

## Invariants

| Type | Description |
|------|-------------|
| `TotalSupplyInvariant` | Conservation with bounds |
| `MaxInvariant` | Monotonic high-water mark |
| `GCounterInvariant` | Grow-only counter |
| `LWWInvariant` | Last-Writer-Wins register |
| `GGraphInvariant` | Grow-only graph |

All commutative invariants require zero coordination.

---

## Kernels

| Kernel | Use Case |
|--------|----------|
| `Kernel<I>` | Single invariant, minimal overhead |
| `TwoLaneKernel<I>` | Two-tier causality, production-grade |
| `DurableKernel<I>` | Async persistence (io_uring) |
| `NetworkingKernel<I>` | Gossip replication |

---

## Features

```toml
default = ["std"]
persistence = ["std", "io-uring", "crc32fast"]  # Linux only
networking = ["std", "tokio", "crc32fast"]
```

---

## Benchmarks

```bash
cargo bench
```

---

## Design Constraints

**Forbidden in hot path:** heap allocation, mutex, syscalls, pointer chasing, O(n) scans.

**Required:** 64-byte alignment, branchless ops, SIMD-friendly layouts, pre-allocated arenas.

**Bit determinism:** Little-endian, fixed-width types, no floats, no std::collections.

---

## Non-Goals

SQL, secondary indexes, full-text search, global ordering, wall-clock time, arbitrary queries, dynamic schema, convenience APIs.

---

## License

MIT

