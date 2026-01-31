//! EscalatingKernel: auto-switches from Bloom to precise mode at 40% saturation.

use ctfs::core::kernel::{CausalMode, EscalatingKernel};
use ctfs::core::topology::FactId;
use ctfs::core::StateCell;
use ctfs::invariants::monotonic::{GCounterInvariant, GCounterState};
use zerocopy::IntoBytes;

fn main() {
    // 1. Initialize state
    let initial = GCounterState::new();
    let mut cell = StateCell::new();
    cell.as_slice_mut().copy_from_slice(initial.as_bytes());

    let mut kernel = EscalatingKernel::with_state(GCounterInvariant::new(), cell);

    println!("Initial mode: {:?}", kernel.current_mode()); // Fast

    // 2. Admit facts until saturation triggers escalation
    for i in 0..300u32 {
        let mut fact_id = [0u8; 32];
        fact_id[0..4].copy_from_slice(&i.to_le_bytes());

        let delta = 1u64.to_le_bytes();
        kernel.admit(&fact_id, &[], &delta).expect("admit");

        // Check saturation periodically
        if i % 50 == 49 {
            let sat = kernel.saturation();
            println!(
                "After {} facts: saturation={:.1}%, mode={:?}",
                i + 1,
                sat * 100.0,
                kernel.current_mode()
            );
        }
    }

    // 3. After ~200 facts, saturation exceeds 40% and mode switches to Precise
    assert_eq!(kernel.current_mode(), CausalMode::Precise);

    // 4. Query final state
    let state = kernel.state().cast_ref::<GCounterState>().unwrap();
    println!("Final count: {}", state.count); // 300

    // 5. Manual escalation/reset
    kernel.reset_mode();
    println!("After reset: mode={:?}", kernel.current_mode()); // Fast

    kernel.escalate();
    println!("After escalate: mode={:?}", kernel.current_mode()); // Precise

    println!("EscalatingKernel example complete.");
}
