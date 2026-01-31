# Cuttlefish

**Causal consistency at nanosecond latency. Algebraic invariants without coordination.**

```
Fact → Bloom Clock Check → Invariant Apply → Frontier Advance
40ns end-to-end. 25M causally-ordered ops/sec. Zero consensus.
```

Distributed systems usually trade consistency for latency. Cuttlefish is a coordination-free state kernel that preserves strict invariants at the speed of your L1 cache.

**Thesis:** Correctness is defined as a property of algebra, not execution order. If your operations commute, you don't need coordination. If they don't, it tells you at admission time in nanoseconds.

---

## Performance

| Operation | Latency | Notes |
|-----------|---------|-------|
| Full admission cycle | 40 ns | Causality + invariant + frontier |
| Kernel admit (no deps) | 13 ns | Single invariant, no causal check |
| Causal clock dominance | 700 ps | SIMD Bloom filter comparison |
| Tiered hash verification | 280 ns | BLAKE3 checkpoint integrity |
| Durable admission | 5.2 ns | Staged to io_uring, async fsync |
| WAL hash (200B payload) | 230 ns | 940 MiB/s throughput |

**Comparison:** etcd pays 1-10ms for linearizable writes. CockroachDB pays 1-50ms. Cuttlefish pays 40ns for causal+ consistency.

---

## Quick Start

```toml
[dependencies]
ctfs = "1.0.0"
zerocopy = "0.8"
```

```rust
use ctfs::prelude::*;
use ctfs::invariants::total_supply::{ConservationState, TotalSupplyInvariant};
use zerocopy::IntoBytes;

// Initialize: balance=0, bounds=[MIN, MAX]
let state = ConservationState::new(0, i128::MIN, i128::MAX);
let mut cell = StateCell::new();
cell.as_slice_mut().copy_from_slice(state.as_bytes());

let mut kernel = Kernel::with_state(TotalSupplyInvariant::new(), cell);

// Admit a fact: +100 to balance
let fact_id: FactId = [0u8; 32];
let payload = 100i128.to_le_bytes();
kernel.admit_raw(&fact_id, &[], &payload).unwrap();
```

---

## Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                         Kernels                             │
├─────────────┬─────────────┬─────────────┬───────────────────┤
│   Kernel    │ TwoLane     │ Escalating  │ Durable/Network   │
│   (basic)   │ (BFVC+Exact)│ (auto-mode) │ (io_uring/gossip) │
├─────────────┴─────────────┴─────────────┴───────────────────┤
│                      Causal Layer                           │
├─────────────┬─────────────┬─────────────────────────────────┤
│ CausalClock │ PreciseClock│ ExactCausalIndex                │
│ (512b Bloom)│ (LRU exact) │ (Robin Hood, SIMD)              │
├─────────────┴─────────────┴─────────────────────────────────┤
│                    Invariant Layer                          │
├─────────────┬─────────────┬─────────────┬───────────────────┤
│ TotalSupply │ Max/GCounter│ Uniqueness  │ GGraph            │
│ (conserve)  │ (monotonic) │ (idempotent)│ (grow-only graph) │
├─────────────┴─────────────┴─────────────┴───────────────────┤
│                   Persistence Layer                         │
├─────────────┬─────────────┬─────────────────────────────────┤
│  WALArena   │ SPSC Buffer │ io_uring Worker                 │
│ (zero-copy) │ (lock-free) │ (async fsync)                   │
├─────────────┴─────────────┴─────────────────────────────────┤
│                   Checkpoint Layer                          │
├─────────────────────────────────────────────────────────────┤
│ Tiered BLAKE3 Hash │ Attestation │ Re-anchoring             │
└─────────────────────────────────────────────────────────────┘
```

---

## Examples

Run any example with `cargo run --example <name>`:

```bash
cargo run --example basic_kernel      # Basic fact admission and causality
cargo run --example multi_tenant      # Isolated causal domains per tenant
cargo run --example custom_invariant  # Implement your own invariant
cargo run --example two_lane_kernel   # BFVC + ExactCausalIndex
cargo run --example escalating_kernel # Auto-switch Bloom → Precise mode
cargo run --example graph_invariant   # Grow-only graph with constraints
```

### Basic Kernel

```rust
use ctfs::core::{Kernel, StateCell};
use ctfs::invariants::total_supply::{ConservationState, TotalSupplyInvariant};

// Initialize state
let state = ConservationState::new(1000, 0, 1_000_000);
let mut cell = StateCell::new();
cell.as_slice_mut().copy_from_slice(state.as_bytes());

let mut kernel = Kernel::with_state(TotalSupplyInvariant::new(), cell);

// Admit facts
let fact1: FactId = [1u8; 32];
kernel.admit_raw(&fact1, &[], &500i128.to_le_bytes()).unwrap();

// Admit with causal dependency
let fact2: FactId = [2u8; 32];
kernel.admit_raw(&fact2, &[fact1], &(-200i128).to_le_bytes()).unwrap();
```

### Multi-Tenant Isolation

```rust
use ctfs::core::TenantKernel;

let mut kernel = TenantKernel::new(TotalSupplyInvariant::new());

// Each tenant gets isolated causal state
kernel.register_tenant(1, alice_state).unwrap();
kernel.register_tenant(2, bob_state).unwrap();

// Cross-tenant dependencies are rejected
kernel.admit(1, &fact, &[bob_fact], &payload); // Error: CausalityViolation
```

### Custom Invariant

```rust
use ctfs::core::{Invariant, InvariantError};

struct MonotonicInvariant;

impl Invariant for MonotonicInvariant {
    fn apply(&self, payload: &[u8], state: &mut [u8]) -> Result<(), InvariantError> {
        let proposed = u64::from_le_bytes(payload[0..8].try_into().unwrap());
        let current = u64::from_le_bytes(state[0..8].try_into().unwrap());
        
        if proposed < current {
            return Err(InvariantError::Underflow);
        }
        state[0..8].copy_from_slice(&proposed.to_le_bytes());
        Ok(())
    }
}
```

---

## Core Concepts

### Facts
Immutable, content-addressed state transitions. Each fact has a 32-byte ID, optional causal dependencies, and a payload. Facts form a DAG, not a chain.

### Invariants
Algebraic constraints enforced at admission. Pure functions: `Δ_I(payload, state) → Result<(), Error>`. O(1), allocation-free, branchless where possible.

### Causal Clocks
512-bit Bloom filter vector clocks. Probabilistic but fast (~700ps dominance check). When saturation exceeds 40%, kernels escalate to precise tracking.

### StateCell
64-byte cache-aligned POD. Bit-for-bit deterministic. No pointers and no heap.

### Checkpoints
Tiered BLAKE3 hash of state + frontier. Verified on load—corrupt checkpoints are rejected.

---

## Kernels

| Kernel | Causality | Persistence | Use Case |
|--------|-----------|-------------|----------|
| `Kernel<I>` | BFVC only | None | Embedded, single-node |
| `TwoLaneKernel<I>` | BFVC + ExactIndex | None | Production, precise deps |
| `EscalatingKernel<I>` | Auto BFVC→Precise | None | Long-running, adaptive |
| `TenantKernel<I>` | Per-tenant BFVC+Exact | None | Multi-tenant isolation |
| `DurableKernel<I>` | BFVC | io_uring WAL | Crash-safe single-node |
| `TwoLaneDurableKernel<I>` | BFVC + ExactIndex | io_uring + Arena | Production crash-safe |
| `NetworkingKernel<I>` | BFVC | Broadcast buffer | Gossip replication |
| `MultiKernel` | BFVC | None | Multiple invariants |
| `DualKernel<I1, I2>` | BFVC | None | Two invariants, zero overhead |

### Async Durability (New)

`TwoLaneDurableKernel` now supports non-blocking durability via `DurableHandle`:

```rust
// Non-blocking: returns immediately with a handle
let handle = kernel.admit_async(&fact_id, &deps, &payload)?;

// Poll for durability (or use in async context)
while !handle.is_durable() {
    // Do other work...
}

// Or block if needed
handle.spin_wait();
```

---

## Invariants

| Invariant | Algebraic Class | Coordination |
|-----------|-----------------|--------------|
| `TotalSupplyInvariant` | Abelian group | None (commutative) |
| `MaxInvariant` | Join-semilattice | None (monotonic) |
| `GCounterInvariant` | Commutative monoid | None |
| `BoundedGCounterInvariant` | Bounded monoid | None until bound |
| `LWWInvariant` | Last-writer-wins | Tiebreaker only |
| `UniquenessInvariant` | Idempotent set | None |
| `GGraphInvariant` | Grow-only graph | None |

**Rule:** If `Δ_I(a) ∘ Δ_I(b) = Δ_I(b) ∘ Δ_I(a)`, no coordination required.

---

## Persistence

Linux-only. Requires `io_uring` (kernel 5.1+).

```toml
[dependencies]
ctfs = { version = "1.0.0", features = ["persistence"] }
```

### Components

- **WALArena**: 4K-aligned memory arena for zero-copy fact staging. 4096 slots, 256 bytes each.
- **SPSC Buffer**: Lock-free producer-consumer queue between kernel and persistence worker.
- **io_uring Worker**: Async batched writes with explicit fsync before advancing persistence frontier.
- **Checkpoints**: Periodic state snapshots with tiered BLAKE3 integrity verification.

### Durability Guarantees

Facts are durable when `persistence_frontier.dominates(fact_clock)`. The frontier advances only after `fsync` completes—not after write submission.

---

## Networking

```toml
[dependencies]
ctfs = { version = "1.0.0", features = ["networking"] }
```

Gossip-based replication via `NetworkingKernel`. Facts are broadcast to peers; causality is enforced on receipt. Convergence is guaranteed for commutative invariants.

---

## Benchmarks

```bash
# All benchmarks
cargo bench

# Specific suites
cargo bench --bench kernel
cargo bench --bench hardening
cargo bench --features persistence --bench durable_admission
```

### Selected Results (AMD Ryzen 7, Linux 6.x)

```
kernel_admit_no_deps      13.0 ns
full_admission_cycle      40.0 ns
causal_clock_dominates     0.7 ns
checkpoint/tiered_hash   280.0 ns
durable_admission          5.2 ns
wal_hasher/200B          230.0 ns  (940 MiB/s)
```

---

## Design Constraints

**Forbidden in hot path:**
- Heap allocation (`Box`, `Vec`, `HashMap`)
- Locks (`Mutex`, `RwLock`)
- Syscalls (except staged io_uring)
- Pointer chasing
- O(n) scans

**Required:**
- `#[repr(C, align(64))]` for cache-line alignment
- Fixed-width types (`i128`, `u64`, `[u8; 32]`)
- Little-endian byte order
- Branchless operations where possible
- SIMD-friendly memory layouts

**Bit determinism:** Same input → same output, byte-for-byte, across all nodes. No floats. No `std::collections`. No non-deterministic iteration.

---

## What it is NOT

- SQL or query languages
- Secondary indexes
- Full-text search
- Global total ordering
- Wall-clock timestamps
- Dynamic schema
- "Convenient" APIs that hide complexity

This is a kernel, not a database. Build your database on top.

---

## Theory

Cuttlefish is grounded in:

- **CALM Theorem**: Consistency As Logical Monotonicity. Monotonic programs don't need coordination.
- **CRDTs**: Conflict-free Replicated Data Types. Lattice-based merge semantics.
- **Bloom Clocks**: Probabilistic vector clocks with O(1) space and O(1) dominance checks.
- **Algebraic Effects**: Invariants as pure functions over state, composable via semiring operations.

If you want the math: [Alvaro et al., "Consistency Analysis in Bloom"](https://dsf.berkeley.edu/papers/cidr11-bloom.pdf)

---

## License

MIT

---

*"The fastest distributed system is the one that doesn't distribute."*
