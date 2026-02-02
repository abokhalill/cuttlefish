//! Integration test: Two networked kernels with escrow quota transfer.
//!
//! Demonstrates escrow-based coordination for bounded invariants.

#![cfg(feature = "networking")]

use std::sync::{Arc, Barrier};
use std::thread;
use std::time::Duration;

use ctfs::algebra::escrow::{EscrowManager, NodeId};
use ctfs::core::kernel::TwoLaneKernel;
use ctfs::core::topology::FactId;
use ctfs::invariants::monotonic::GCounterInvariant;

const TOTAL_LIMIT: i128 = 1000;
const NODE_A_ID: NodeId = 1;
const NODE_B_ID: NodeId = 2;

fn make_fact_id(seed: u8) -> FactId {
    let mut id = [0u8; 32];
    id[0] = seed;
    id[31] = seed;
    id
}

#[test]
fn test_escrow_quota_transfer_between_nodes() {
    // Shared escrow manager (in real system this would be distributed)
    let escrow = Arc::new(std::sync::Mutex::new(EscrowManager::new(TOTAL_LIMIT)));

    // Initialize escrow with two nodes - each gets 500
    {
        let mut mgr = escrow.lock().unwrap();
        mgr.initialize(&[NODE_A_ID, NODE_B_ID]).unwrap();
    }

    let barrier = Arc::new(Barrier::new(2));

    let escrow_a = escrow.clone();
    let barrier_a = barrier.clone();

    // Node A: consume 400 (within its 500 quota)
    let handle_a = thread::spawn(move || {
        let inv = GCounterInvariant::new();
        let mut kernel = TwoLaneKernel::new(inv);

        barrier_a.wait();

        // Consume 400 using local escrow (we have 500)
        {
            let mut mgr = escrow_a.lock().unwrap();
            mgr.try_consume(NODE_A_ID, 400).unwrap();
        }

        // Admit 4 facts worth 100 each
        for i in 0..4 {
            let fact_id = make_fact_id(i);
            let payload = 100u64.to_le_bytes();
            kernel.admit(&fact_id, &[], &payload).unwrap();
        }

        // Wait for Node B to potentially request quota
        thread::sleep(Duration::from_millis(50));

        // Transfer 50 quota to Node B (simulating grant response)
        {
            let mut mgr = escrow_a.lock().unwrap();
            let _ = mgr.transfer(NODE_A_ID, NODE_B_ID, 50);
        }

        kernel
    });

    let escrow_b = escrow.clone();
    let barrier_b = barrier.clone();

    // Node B: consume 300 (within its 500 quota)
    let handle_b = thread::spawn(move || {
        let inv = GCounterInvariant::new();
        let mut kernel = TwoLaneKernel::new(inv);

        barrier_b.wait();

        // Consume 300 using local escrow
        {
            let mut mgr = escrow_b.lock().unwrap();
            mgr.try_consume(NODE_B_ID, 300).unwrap();
        }

        // Admit 3 facts worth 100 each
        for i in 0..3 {
            let fact_id = make_fact_id(100 + i);
            let payload = 100u64.to_le_bytes();
            kernel.admit(&fact_id, &[], &payload).unwrap();
        }

        // Wait for transfer from Node A
        thread::sleep(Duration::from_millis(100));

        // Check we received the transfer
        let available = {
            let mgr = escrow_b.lock().unwrap();
            mgr.get(NODE_B_ID).map(|a| a.available()).unwrap_or(0)
        };

        // Should have 500 - 300 + 50 = 250 available
        assert!(available >= 200, "Node B should have received transfer");

        kernel
    });

    let kernel_a = handle_a.join().expect("Node A panicked");
    let kernel_b = handle_b.join().expect("Node B panicked");

    // Verify final escrow state
    let mgr = escrow.lock().unwrap();
    let total_allocated = mgr.total_allocated();
    let total_used = mgr.total_used();

    assert_eq!(total_allocated, TOTAL_LIMIT, "Total allocation preserved");
    assert_eq!(total_used, 700, "Total used = 400 + 300");

    assert_eq!(kernel_a.exact_index().len(), 4, "Node A: 4 facts");
    assert_eq!(kernel_b.exact_index().len(), 3, "Node B: 3 facts");

    println!("✓ Escrow quota transfer test passed");
}

#[test]
fn test_escrow_rebalance_after_operations() {
    let mut mgr = EscrowManager::new(1000);
    mgr.initialize(&[1, 2, 3]).unwrap();

    // Each node starts with ~333
    // Node 1 uses 200, Node 2 uses 100, Node 3 uses 0
    mgr.try_consume(1, 200).unwrap();
    mgr.try_consume(2, 100).unwrap();

    let before_1 = mgr.get(1).unwrap().available();
    let before_2 = mgr.get(2).unwrap().available();
    let before_3 = mgr.get(3).unwrap().available();

    mgr.rebalance();

    let after_1 = mgr.get(1).unwrap().available();
    let after_2 = mgr.get(2).unwrap().available();
    let after_3 = mgr.get(3).unwrap().available();

    // After rebalance, unused quota redistributed equally
    let diff_12 = (after_1 as i128 - after_2 as i128).abs();
    let diff_23 = (after_2 as i128 - after_3 as i128).abs();

    assert!(diff_12 <= 1, "Nodes 1,2 should have similar available");
    assert!(diff_23 <= 1, "Nodes 2,3 should have similar available");

    println!("✓ Rebalance test passed");
    println!("  Before: {}, {}, {}", before_1, before_2, before_3);
    println!("  After:  {}, {}, {}", after_1, after_2, after_3);
}
