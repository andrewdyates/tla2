// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Bridge between tla-check's SCC checking and compiled/optimized acceptance
//! checking for AE constraints.
//!
//! During liveness checking, each PEM's AE constraints (state and action) must
//! be verified against each candidate SCC. The interpreted path uses
//! `CheckMask::contains_all()` on per-SCC aggregate masks. This module provides
//! an optimized alternative using precomputed u64 bitmasks that skip the
//! multi-word `CheckMask` overhead for the common case (< 64 check indices).
//!
//! When all AE indices fit in a single u64 word, the acceptance check reduces
//! to two AND+CMP operations instead of iterating CheckMask word vectors.
//! This is the hot path in the PEM x SCC inner loop.
//!
//! Part of #3992: JIT V2 Phase 10 — Compiled Liveness.

#[cfg(feature = "jit")]
use super::check_mask::CheckMask;

/// Optimized acceptance checker for a PEM's AE constraints using u64 bitmasks.
///
/// When all AE state and action indices fit in the first u64 word (< 64 checks),
/// this replaces `CheckMask::contains_all()` with direct u64 AND+CMP operations.
/// Falls back gracefully when indices exceed u64 capacity.
///
/// Part of #3992.
#[cfg(feature = "jit")]
pub(super) struct CompiledPemAcceptance {
    /// Required AE state mask: bit i set means ae_state_idx contains i.
    ae_state_required: u64,
    /// Required AE action mask: bit i set means ae_action_idx contains i.
    ae_action_required: u64,
}

#[cfg(feature = "jit")]
impl CompiledPemAcceptance {
    /// Try to build an optimized acceptance checker for the given PEM's AE constraints.
    ///
    /// Returns `None` if:
    /// - Both ae_state_idx and ae_action_idx are empty (no constraints to check)
    /// - Any index >= 64 (exceeds u64 bitmask capacity)
    pub(super) fn try_build(ae_state_idx: &[usize], ae_action_idx: &[usize]) -> Option<Self> {
        if ae_state_idx.is_empty() && ae_action_idx.is_empty() {
            return None;
        }

        // All indices must fit in u64 bitmask
        if ae_state_idx.iter().any(|&i| i >= 64) || ae_action_idx.iter().any(|&i| i >= 64) {
            return None;
        }

        let mut ae_state_required = 0u64;
        for &idx in ae_state_idx {
            ae_state_required |= 1u64 << idx;
        }

        let mut ae_action_required = 0u64;
        for &idx in ae_action_idx {
            ae_action_required |= 1u64 << idx;
        }

        Some(Self {
            ae_state_required,
            ae_action_required,
        })
    }

    /// Check whether an SCC's aggregate masks satisfy this PEM's AE constraints.
    ///
    /// Extracts the first u64 word from each aggregate `CheckMask` and checks
    /// that all required bits are present using contains-all semantics:
    /// `(aggregate & required) == required`.
    ///
    /// State and action aggregates are checked independently because they
    /// occupy separate index spaces (state checks and action checks are separate
    /// arrays in `GroupedLivenessPlan`).
    ///
    /// Returns `true` if the SCC satisfies all AE constraints for this PEM.
    #[inline]
    pub(super) fn check_scc_aggregate(
        &self,
        state_agg: &CheckMask,
        action_agg: &CheckMask,
    ) -> bool {
        // Check AE state: aggregate must contain ALL required state bits
        if self.ae_state_required != 0 {
            let state_word = state_agg.as_words().first().copied().unwrap_or(0);
            if (state_word & self.ae_state_required) != self.ae_state_required {
                return false;
            }
        }

        // Check AE action: aggregate must contain ALL required action bits
        if self.ae_action_required != 0 {
            let action_word = action_agg.as_words().first().copied().unwrap_or(0);
            if (action_word & self.ae_action_required) != self.ae_action_required {
                return false;
            }
        }

        true
    }
}

/// Try to build optimized PEM acceptance checkers for a batch of PEMs sharing
/// the same EA signature.
///
/// Returns a Vec with one `Option` per PEM index. `None` entries fall back to
/// the interpreted `CheckMask` path.
///
/// Part of #3992.
#[cfg(feature = "jit")]
pub(super) fn try_build_pem_acceptances(
    pems: &[super::PemPlan],
    pem_indices: &[usize],
) -> Vec<Option<CompiledPemAcceptance>> {
    pem_indices
        .iter()
        .map(|&pem_idx| {
            let pem = &pems[pem_idx];
            CompiledPemAcceptance::try_build(&pem.ae_state_idx, &pem.ae_action_idx)
        })
        .collect()
}

#[cfg(all(test, feature = "jit"))]
mod tests {
    use super::*;

    #[test]
    fn test_empty_constraints_returns_none() {
        assert!(CompiledPemAcceptance::try_build(&[], &[]).is_none());
    }

    #[test]
    fn test_single_ae_state_constraint() {
        let acceptance = CompiledPemAcceptance::try_build(&[3], &[])
            .expect("single state constraint should build");
        assert_ne!(acceptance.ae_state_required, 0);
        assert_eq!(acceptance.ae_action_required, 0);

        // Aggregate with bit 3 set should pass
        let mut state_agg = CheckMask::new();
        state_agg.set(3);
        let action_agg = CheckMask::new();
        assert!(acceptance.check_scc_aggregate(&state_agg, &action_agg));

        // Aggregate without bit 3 should fail
        let mut state_agg2 = CheckMask::new();
        state_agg2.set(4);
        assert!(!acceptance.check_scc_aggregate(&state_agg2, &action_agg));
    }

    #[test]
    fn test_single_ae_action_constraint() {
        let acceptance = CompiledPemAcceptance::try_build(&[], &[5])
            .expect("single action constraint should build");
        assert_eq!(acceptance.ae_state_required, 0);
        assert_ne!(acceptance.ae_action_required, 0);

        // Aggregate with bit 5 in action should pass
        let state_agg = CheckMask::new();
        let mut action_agg = CheckMask::new();
        action_agg.set(5);
        assert!(acceptance.check_scc_aggregate(&state_agg, &action_agg));

        // Aggregate without bit 5 should fail
        let action_agg2 = CheckMask::new();
        assert!(!acceptance.check_scc_aggregate(&state_agg, &action_agg2));
    }

    #[test]
    fn test_combined_state_and_action_constraints() {
        let acceptance = CompiledPemAcceptance::try_build(&[1, 3], &[2, 4])
            .expect("combined constraints should build");

        // All bits present
        let mut state_agg = CheckMask::new();
        state_agg.set(1);
        state_agg.set(3);
        let mut action_agg = CheckMask::new();
        action_agg.set(2);
        action_agg.set(4);
        assert!(acceptance.check_scc_aggregate(&state_agg, &action_agg));

        // Missing state bit 3
        let mut state_agg2 = CheckMask::new();
        state_agg2.set(1);
        assert!(!acceptance.check_scc_aggregate(&state_agg2, &action_agg));

        // Missing action bit 4
        let mut action_agg2 = CheckMask::new();
        action_agg2.set(2);
        assert!(!acceptance.check_scc_aggregate(&state_agg, &action_agg2));
    }

    #[test]
    fn test_overlapping_indices_independent() {
        // State index 2 and action index 2 are independent
        let acceptance = CompiledPemAcceptance::try_build(&[2], &[2])
            .expect("overlapping indices should build");

        // Only state has bit 2 — action check should fail
        let mut state_agg = CheckMask::new();
        state_agg.set(2);
        let action_agg = CheckMask::new(); // bit 2 not set in action
        assert!(!acceptance.check_scc_aggregate(&state_agg, &action_agg));

        // Only action has bit 2 — state check should fail
        let state_agg2 = CheckMask::new();
        let mut action_agg2 = CheckMask::new();
        action_agg2.set(2);
        assert!(!acceptance.check_scc_aggregate(&state_agg2, &action_agg2));

        // Both have bit 2 — should pass
        assert!(acceptance.check_scc_aggregate(&state_agg, &action_agg2));
    }

    #[test]
    fn test_index_over_63_returns_none() {
        assert!(CompiledPemAcceptance::try_build(&[64], &[]).is_none());
        assert!(CompiledPemAcceptance::try_build(&[], &[100]).is_none());
        assert!(CompiledPemAcceptance::try_build(&[0, 64], &[]).is_none());
    }

    #[test]
    fn test_try_build_pem_acceptances_batch() {
        use super::super::PemPlan;

        let pems = vec![
            PemPlan {
                ea_action_idx: vec![],
                ea_state_idx: vec![],
                ae_state_idx: vec![1],
                ae_action_idx: vec![2],
            },
            PemPlan {
                ea_action_idx: vec![],
                ea_state_idx: vec![],
                ae_state_idx: vec![],
                ae_action_idx: vec![],
            },
            PemPlan {
                ea_action_idx: vec![],
                ea_state_idx: vec![],
                ae_state_idx: vec![70], // over 64
                ae_action_idx: vec![],
            },
        ];

        let results = try_build_pem_acceptances(&pems, &[0, 1, 2]);
        assert_eq!(results.len(), 3);
        assert!(results[0].is_some(), "PEM 0 should build");
        assert!(results[1].is_none(), "PEM 1 has no constraints");
        assert!(results[2].is_none(), "PEM 2 has index > 63");
    }

    #[test]
    fn test_all_bits_in_same_word() {
        // All indices 0..10 should work
        let indices: Vec<usize> = (0..10).collect();
        let acceptance = CompiledPemAcceptance::try_build(&indices, &[])
            .expect("indices 0..9 should build");

        let mut state_agg = CheckMask::new();
        for i in 0..10 {
            state_agg.set(i);
        }
        let action_agg = CheckMask::new();
        assert!(acceptance.check_scc_aggregate(&state_agg, &action_agg));

        // Missing one bit should fail (contains_all semantics)
        let mut state_agg2 = CheckMask::new();
        for i in 0..9 {
            state_agg2.set(i);
        }
        assert!(!acceptance.check_scc_aggregate(&state_agg2, &action_agg));
    }

    #[test]
    fn test_extra_bits_in_aggregate_ok() {
        // Aggregate can have MORE bits than required — that's fine
        let acceptance = CompiledPemAcceptance::try_build(&[1, 3], &[])
            .expect("should build");

        let mut state_agg = CheckMask::new();
        state_agg.set(0);
        state_agg.set(1);
        state_agg.set(2);
        state_agg.set(3);
        state_agg.set(4);
        let action_agg = CheckMask::new();
        assert!(acceptance.check_scc_aggregate(&state_agg, &action_agg));
    }
}
