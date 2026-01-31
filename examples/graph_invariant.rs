//! Graph invariant: grow-only graph with degree constraints.

use ctfs::core::{Kernel, StateCell, AdmitError};
use ctfs::core::topology::FactId;
use ctfs::invariants::graph::{GraphState, GGraphInvariant, EdgePayload};
use zerocopy::{IntoBytes, FromBytes};

fn main() {
    // 1. Initialize graph: 8 vertices, max out-degree=3, undirected
    let mut graph = GraphState::new(8);
    // Set max out-degree constraint
    let mut cell = StateCell::new();
    let graph_bytes = graph.as_bytes();
    cell.as_slice_mut()[..graph_bytes.len()].copy_from_slice(graph_bytes);
    cell.as_slice_mut()[33] = 3; // max_out_degree = 3

    let mut kernel = Kernel::with_state(GGraphInvariant::new(), cell);

    // 2. Add edges
    let edges = [(0, 1), (0, 2), (1, 3), (2, 3), (3, 4)];
    for (i, (from, to)) in edges.iter().enumerate() {
        let mut fact_id = [0u8; 32];
        fact_id[0] = i as u8;

        let payload = EdgePayload::new(*from, *to);
        kernel.admit_raw(&fact_id, &[], payload.as_bytes()).expect("add edge");
        println!("Added edge {} -> {}", from, to);
    }

    // 3. Query graph state
    let state = kernel.state();
    let graph: &GraphState = FromBytes::ref_from_bytes(state.as_bytes()).unwrap();
    println!("Edge count: {}", graph.edge_count());

    // 4. Degree constraint violation
    // Vertex 0 already has edges to 1 and 2. Adding 0->5, 0->6, 0->7 would exceed max_out_degree=3
    let fact_a: FactId = [100u8; 32];
    let fact_b: FactId = [101u8; 32];
    let fact_c: FactId = [102u8; 32];

    kernel.admit_raw(&fact_a, &[], EdgePayload::new(0, 5).as_bytes()).expect("0->5");
    println!("Added edge 0 -> 5 (out-degree now 3)");

    // This should fail: would exceed max out-degree
    match kernel.admit_raw(&fact_b, &[], EdgePayload::new(0, 6).as_bytes()) {
        Err(_) => println!("Edge 0 -> 6 rejected: max out-degree exceeded"),
        Ok(()) => println!("Edge 0 -> 6 accepted (no constraint or already at limit)"),
    }

    // 5. Idempotent: adding same edge again succeeds (no-op)
    let fact_dup: FactId = [200u8; 32];
    kernel.admit_raw(&fact_dup, &[], EdgePayload::new(0, 1).as_bytes())
        .expect("duplicate edge is idempotent");
    println!("Duplicate edge 0 -> 1 accepted (idempotent)");

    println!("Graph invariant example complete.");
}
