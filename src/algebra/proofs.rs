//! Proof witnesses. Runtime-verifiable algebraic property verification.

use crate::core::invariant::AlgebraicClass;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CoordinationClass {
    CoordinationFree,
    ScopedCoordination { threshold_percent: u8 },
    GlobalCoordination,
}

impl CoordinationClass {
    pub const fn from_algebraic(class: AlgebraicClass) -> Self {
        match class {
            AlgebraicClass::Commutative
            | AlgebraicClass::CommutativeIdempotent
            | AlgebraicClass::Lattice
            | AlgebraicClass::Group => CoordinationClass::CoordinationFree,

            AlgebraicClass::BoundedCommutative => CoordinationClass::ScopedCoordination {
                threshold_percent: 80,
            },

            AlgebraicClass::Ordered => CoordinationClass::GlobalCoordination,
        }
    }

    pub const fn is_local(&self) -> bool {
        matches!(self, CoordinationClass::CoordinationFree)
    }
}

#[derive(Debug, Clone)]
pub struct CommutativityProof {
    pub initial_state: [u8; 64],
    pub delta_a: [u8; 16],
    pub delta_b: [u8; 16],
    pub result_ab: [u8; 64],
    pub result_ba: [u8; 64],
    pub holds: bool,
}

impl CommutativityProof {
    pub fn verify<F>(initial: &[u8; 64], delta_a: &[u8; 16], delta_b: &[u8; 16], apply: F) -> Self
    where
        F: Fn(&[u8], &mut [u8]) -> Result<(), ()>,
    {
        let mut state_ab = *initial;
        let ok_a1 = apply(delta_a, &mut state_ab).is_ok();
        let ok_b1 = apply(delta_b, &mut state_ab).is_ok();

        let mut state_ba = *initial;
        let ok_b2 = apply(delta_b, &mut state_ba).is_ok();
        let ok_a2 = apply(delta_a, &mut state_ba).is_ok();

        let holds = ok_a1 && ok_b1 && ok_a2 && ok_b2 && state_ab == state_ba;

        Self {
            initial_state: *initial,
            delta_a: *delta_a,
            delta_b: *delta_b,
            result_ab: state_ab,
            result_ba: state_ba,
            holds,
        }
    }

    pub const fn is_valid(&self) -> bool {
        self.holds
    }
}

/// Convergence verification result (no_std compatible, fixed-size).
#[derive(Debug, Clone, Copy)]
pub struct ConvergenceWitness {
    pub initial_state: [u8; 64],
    pub final_state: [u8; 64],
    pub orderings_tested: u32,
    pub converged: bool,
}

impl ConvergenceWitness {
    pub fn verify<F>(initial: &[u8; 64], deltas: &[[u8; 16]], apply: F, _max_orderings: u32) -> Self
    where
        F: Fn(&[u8], &mut [u8]) -> Result<(), ()>,
    {
        if deltas.is_empty() {
            return Self {
                initial_state: *initial,
                final_state: *initial,
                orderings_tested: 1,
                converged: true,
            };
        }

        let mut reference_state = *initial;
        for delta in deltas {
            let _ = apply(delta, &mut reference_state);
        }

        let mut reversed_state = *initial;
        for delta in deltas.iter().rev() {
            let _ = apply(delta, &mut reversed_state);
        }

        let converged = reference_state == reversed_state;

        Self {
            initial_state: *initial,
            final_state: reference_state,
            orderings_tested: 2,
            converged,
        }
    }

    pub const fn is_valid(&self) -> bool {
        self.converged
    }
}

#[derive(Debug, Clone)]
pub struct IdempotenceProof {
    pub initial_state: [u8; 64],
    pub delta: [u8; 16],
    pub state_after_once: [u8; 64],
    pub state_after_twice: [u8; 64],
    pub holds: bool,
}

impl IdempotenceProof {
    pub fn verify<F>(initial: &[u8; 64], delta: &[u8; 16], apply: F) -> Self
    where
        F: Fn(&[u8], &mut [u8]) -> Result<(), ()>,
    {
        let mut state_once = *initial;
        let _ = apply(delta, &mut state_once);

        let mut state_twice = state_once;
        let _ = apply(delta, &mut state_twice);

        let holds = state_once == state_twice;

        Self {
            initial_state: *initial,
            delta: *delta,
            state_after_once: state_once,
            state_after_twice: state_twice,
            holds,
        }
    }

    pub const fn is_valid(&self) -> bool {
        self.holds
    }
}

#[derive(Debug, Clone)]
pub struct AssociativityProof {
    pub a: [u8; 64],
    pub b: [u8; 64],
    pub c: [u8; 64],
    pub ab_c: [u8; 64], // (a ⊔ b) ⊔ c
    pub a_bc: [u8; 64], // a ⊔ (b ⊔ c)
    pub holds: bool,
}

impl AssociativityProof {
    pub fn verify<F>(a: &[u8; 64], b: &[u8; 64], c: &[u8; 64], join: F) -> Self
    where
        F: Fn(&[u8; 64], &[u8; 64]) -> [u8; 64],
    {
        let ab = join(a, b);
        let ab_c = join(&ab, c);

        let bc = join(b, c);
        let a_bc = join(a, &bc);

        let holds = ab_c == a_bc;

        Self {
            a: *a,
            b: *b,
            c: *c,
            ab_c,
            a_bc,
            holds,
        }
    }

    pub const fn is_valid(&self) -> bool {
        self.holds
    }
}

#[derive(Debug, Clone)]
pub struct BoundedLocalityProof {
    pub local_state: [u8; 64],
    pub delta: [u8; 16],
    pub rejected: bool,
    pub rejection_reason: Option<BoundedRejectionReason>,
    pub is_local_decision: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BoundedRejectionReason {
    WouldUnderflow,
    WouldOverflow,
    CapacityExceeded,
}

impl BoundedLocalityProof {
    pub fn verify<F, G>(
        local_state: &[u8; 64],
        delta: &[u8; 16],
        would_reject: F,
        get_reason: G,
    ) -> Self
    where
        F: Fn(&[u8; 64], &[u8; 16]) -> bool,
        G: Fn(&[u8; 64], &[u8; 16]) -> Option<BoundedRejectionReason>,
    {
        let rejected = would_reject(local_state, delta);
        let rejection_reason = if rejected {
            get_reason(local_state, delta)
        } else {
            None
        };

        Self {
            local_state: *local_state,
            delta: *delta,
            rejected,
            rejection_reason,
            is_local_decision: true,
        }
    }
}

/// Composition proof (no_std compatible, fixed-size up to 8 invariants).
#[derive(Debug, Clone, Copy)]
pub struct CompositionProof {
    pub invariant_count: usize,
    pub individual_proofs: [bool; 8],
    pub composition_commutative: bool,
}

impl CompositionProof {
    pub fn verify(individual_commutative: &[bool]) -> Self {
        let all_commutative = individual_commutative.iter().all(|&c| c);
        let mut proofs = [false; 8];
        let count = individual_commutative.len().min(8);
        proofs[..count].copy_from_slice(&individual_commutative[..count]);

        Self {
            invariant_count: count,
            individual_proofs: proofs,
            composition_commutative: all_commutative,
        }
    }

    pub const fn is_valid(&self) -> bool {
        self.composition_commutative
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_coordination_class_derivation() {
        assert_eq!(
            CoordinationClass::from_algebraic(AlgebraicClass::Commutative),
            CoordinationClass::CoordinationFree
        );
        assert_eq!(
            CoordinationClass::from_algebraic(AlgebraicClass::Lattice),
            CoordinationClass::CoordinationFree
        );
        assert!(matches!(
            CoordinationClass::from_algebraic(AlgebraicClass::BoundedCommutative),
            CoordinationClass::ScopedCoordination { .. }
        ));
        assert_eq!(
            CoordinationClass::from_algebraic(AlgebraicClass::Ordered),
            CoordinationClass::GlobalCoordination
        );
    }

    #[test]
    fn test_commutativity_proof_addition() {
        // Test that addition is commutative
        let initial = [0u8; 64];
        let delta_a = 5i128.to_le_bytes();
        let delta_b = 10i128.to_le_bytes();

        let proof = CommutativityProof::verify(&initial, &delta_a, &delta_b, |delta, state| {
            let current = i128::from_le_bytes(state[0..16].try_into().unwrap());
            let d = i128::from_le_bytes(delta.try_into().unwrap());
            let new = current.wrapping_add(d);
            state[0..16].copy_from_slice(&new.to_le_bytes());
            Ok(())
        });

        assert!(proof.is_valid());
    }

    #[test]
    fn test_idempotence_proof_max() {
        // Test that max is idempotent
        let mut initial = [0u8; 64];
        initial[0..8].copy_from_slice(&100u64.to_le_bytes());

        let mut delta = [0u8; 16];
        delta[0..8].copy_from_slice(&50u64.to_le_bytes());

        let proof = IdempotenceProof::verify(&initial, &delta, |delta, state| {
            let current = u64::from_le_bytes(state[0..8].try_into().unwrap());
            let d = u64::from_le_bytes(delta[0..8].try_into().unwrap());
            let new = current.max(d);
            state[0..8].copy_from_slice(&new.to_le_bytes());
            Ok(())
        });

        assert!(proof.is_valid());
    }

    #[test]
    fn test_composition_proof() {
        // All commutative → composition is commutative
        let proof = CompositionProof::verify(&[true, true, true]);
        assert!(proof.is_valid());

        // One non-commutative → composition is not commutative
        let proof = CompositionProof::verify(&[true, false, true]);
        assert!(!proof.is_valid());
    }
}
