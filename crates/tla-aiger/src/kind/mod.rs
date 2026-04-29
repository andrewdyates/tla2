// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! k-Induction engines for AIGER safety checking.
//!
//! - [`KindEngine`] -- standard k-induction with optional simple-path constraints.
//! - [`KindStrengthenedEngine`] -- strengthened k-induction with invariant discovery.

mod engine;
mod strengthened;

pub use engine::{KindConfig, KindEngine};
pub use strengthened::KindStrengthenedEngine;

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::check_result::CheckResult;
    use crate::parser::parse_aag;
    use crate::sat_types::{Lit, SolverBackend, Var};
    use crate::transys::Transys;
    use std::sync::atomic::AtomicBool;
    use std::sync::Arc;

    #[test]
    fn test_kind_trivially_unsafe() {
        // output=1 => bad at step 0
        let circuit = parse_aag("aag 0 0 0 1 0\n1\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let mut kind = KindEngine::new(ts);
        let result = kind.check(10);
        assert!(matches!(result, CheckResult::Unsafe { depth: 0, .. }));
    }

    #[test]
    fn test_kind_toggle_unsafe() {
        // Toggle: latch toggles, bad = latch. Reachable at step 1.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let mut kind = KindEngine::new(ts);
        let result = kind.check(10);
        assert!(matches!(result, CheckResult::Unsafe { depth: 1, .. }));
    }

    #[test]
    fn test_kind_latch_stays_zero_safe() {
        // Latch with next=0. Bad = latch.
        // Property: latch is always 0. This is 0-inductive (base: init forces 0,
        // step: next=0 means if !bad now, !bad next).
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let mut kind = KindEngine::new(ts);
        let result = kind.check(10);
        assert!(
            matches!(result, CheckResult::Safe),
            "expected Safe, got {result:?}"
        );
    }

    #[test]
    fn test_kind_cancellation() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let mut kind = KindEngine::new(ts);
        let cancel = Arc::new(AtomicBool::new(true));
        kind.set_cancelled(cancel);
        let result = kind.check(100);
        assert!(matches!(result, CheckResult::Unknown { .. }));
    }

    // ----------- Simple-path constraint tests -----------

    #[test]
    fn test_kind_simple_path_trivially_unsafe() {
        // output=1 => bad at step 0
        let circuit = parse_aag("aag 0 0 0 1 0\n1\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let mut kind = KindEngine::new_simple_path(ts);
        let result = kind.check(10);
        assert!(matches!(result, CheckResult::Unsafe { depth: 0, .. }));
    }

    #[test]
    fn test_kind_simple_path_toggle_unsafe() {
        // Toggle: latch toggles, bad = latch. Reachable at step 1.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let mut kind = KindEngine::new_simple_path(ts);
        let result = kind.check(10);
        assert!(matches!(result, CheckResult::Unsafe { depth: 1, .. }));
    }

    #[test]
    fn test_kind_simple_path_latch_stays_zero_returns_unknown() {
        // Latch with next=0. Bad = latch. This property holds, but simple-path
        // k-induction cannot prove it: only 1 reachable state (latch=0) exists,
        // so the vacuity check detects that no simple path of length k+1 exists
        // at any k (state space exhaustion). Standard k-induction (without
        // simple-path) proves this safe at k=1.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let mut kind = KindEngine::new_simple_path(ts);
        let result = kind.check(10);
        assert!(
            matches!(result, CheckResult::Unknown { .. }),
            "expected Unknown (vacuity check), got {result:?}"
        );
    }

    #[test]
    fn test_kind_simple_path_two_step_shift_safe() {
        // 2-stage shift register: l0 toggles, l1 = delayed copy of l0.
        // bad = l0 AND l1 is never reachable (they alternate).
        // Simple-path k-induction proves this safe: at k=2, simple paths
        // of length 3 exist (e.g., 00->10->01) but none reach bad (state 11).
        // The vacuity check confirms non-vacuity, so the step UNSAT is genuine.
        let aag = "aag 3 0 2 0 1 1\n2 3\n4 2\n6\n6 2 4\n";
        let circuit = parse_aag(aag).unwrap();
        let ts = Transys::from_aiger(&circuit);
        let mut kind = KindEngine::new_simple_path(ts);
        let result = kind.check(20);
        assert!(
            matches!(result, CheckResult::Safe),
            "simple-path k-induction should prove shift register Safe, got {result:?}"
        );
    }

    #[test]
    fn test_kind_simple_path_cancellation() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let mut kind = KindEngine::new_simple_path(ts);
        let cancel = Arc::new(AtomicBool::new(true));
        kind.set_cancelled(cancel);
        let result = kind.check(100);
        assert!(matches!(result, CheckResult::Unknown { .. }));
    }

    // ----------- Backend selection tests -----------

    #[test]
    fn test_kind_with_config_and_backend_z4sat() {
        // Verify that explicit z4-sat backend matches the default constructor.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let mut kind =
            KindEngine::with_config_and_backend(ts, KindConfig::default(), SolverBackend::Z4Sat);
        let result = kind.check(10);
        assert!(
            matches!(result, CheckResult::Safe),
            "expected Safe, got {result:?}"
        );
    }

    // ----------- z4-sat variant backend tests -----------

    mod z4_variant_kind_tests {
        use super::*;

        #[test]
        fn test_kind_z4_luby_trivially_unsafe() {
            let circuit = parse_aag("aag 0 0 0 1 0\n1\n").unwrap();
            let ts = Transys::from_aiger(&circuit);
            let mut kind = KindEngine::with_config_and_backend(
                ts,
                KindConfig::default(),
                SolverBackend::Z4Luby,
            );
            let result = kind.check(10);
            assert!(matches!(result, CheckResult::Unsafe { depth: 0, .. }));
        }

        #[test]
        fn test_kind_z4_stable_toggle_unsafe() {
            let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
            let ts = Transys::from_aiger(&circuit);
            let mut kind = KindEngine::with_config_and_backend(
                ts,
                KindConfig::default(),
                SolverBackend::Z4Stable,
            );
            let result = kind.check(10);
            assert!(matches!(result, CheckResult::Unsafe { depth: 1, .. }));
        }

        #[test]
        fn test_kind_z4_vmtf_proves_safe() {
            // Latch with next=0, bad=latch. k-induction proves safe.
            let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
            let ts = Transys::from_aiger(&circuit);
            let mut kind = KindEngine::with_config_and_backend(
                ts,
                KindConfig::default(),
                SolverBackend::Z4Vmtf,
            );
            let result = kind.check(10);
            assert!(
                matches!(result, CheckResult::Safe),
                "z4-sat VMTF k-induction should prove Safe, got {result:?}"
            );
        }

        #[test]
        fn test_kind_z4_luby_skip_bmc() {
            // skip-bmc mode with z4-sat Luby: should prove safe (stuck-at-zero).
            let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
            let ts = Transys::from_aiger(&circuit);
            let mut kind = KindEngine::with_config_and_backend(
                ts,
                KindConfig {
                    simple_path: false,
                    skip_bmc: true,
                },
                SolverBackend::Z4Luby,
            );
            let result = kind.check(10);
            assert!(
                matches!(result, CheckResult::Safe),
                "z4-sat Luby kind-skip-bmc should prove Safe, got {result:?}"
            );
        }

        #[test]
        fn test_kind_z4_chb_cancellation() {
            let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
            let ts = Transys::from_aiger(&circuit);
            let mut kind = KindEngine::with_config_and_backend(
                ts,
                KindConfig::default(),
                SolverBackend::Z4Chb,
            );
            let cancel = Arc::new(AtomicBool::new(true));
            kind.set_cancelled(cancel);
            let result = kind.check(100);
            assert!(matches!(result, CheckResult::Unknown { .. }));
        }

        /// z4-sat variant and default k-induction should agree on results.
        #[test]
        fn test_kind_z4_variant_default_agreement() {
            let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
            let ts = Transys::from_aiger(&circuit);

            let mut default_kind = KindEngine::new(ts.clone());
            let default_result = default_kind.check(10);

            let mut luby_kind = KindEngine::with_config_and_backend(
                ts,
                KindConfig::default(),
                SolverBackend::Z4Luby,
            );
            let luby_result = luby_kind.check(10);

            assert!(
                matches!(default_result, CheckResult::Safe),
                "z4 default result: {default_result:?}"
            );
            assert!(
                matches!(luby_result, CheckResult::Safe),
                "z4 Luby result: {luby_result:?}"
            );
        }
    }

    // ----------- Strengthened k-induction tests -----------

    mod strengthened_kind_tests {
        use super::*;

        #[test]
        fn test_strengthened_trivially_unsafe() {
            let circuit = parse_aag("aag 0 0 0 1 0\n1\n").unwrap();
            let ts = Transys::from_aiger(&circuit);
            let mut engine = KindStrengthenedEngine::new(ts);
            let result = engine.check(10);
            assert!(
                matches!(result, CheckResult::Unsafe { depth: 0, .. }),
                "expected Unsafe at depth 0, got {result:?}"
            );
        }

        #[test]
        fn test_strengthened_toggle_unsafe() {
            let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
            let ts = Transys::from_aiger(&circuit);
            let mut engine = KindStrengthenedEngine::new(ts);
            let result = engine.check(10);
            assert!(
                matches!(result, CheckResult::Unsafe { depth: 1, .. }),
                "expected Unsafe at depth 1, got {result:?}"
            );
        }

        #[test]
        fn test_strengthened_latch_stays_zero_safe() {
            let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
            let ts = Transys::from_aiger(&circuit);
            let mut engine = KindStrengthenedEngine::new(ts);
            let result = engine.check(10);
            assert!(
                matches!(result, CheckResult::Safe),
                "expected Safe, got {result:?}"
            );
        }

        #[test]
        fn test_strengthened_two_step_shift_safe() {
            // 2-stage shift register: l0 toggles, l1 = delayed copy of l0.
            // bad = l0 AND l1. Never reachable: l0 and l1 alternate phases.
            // Standard k-induction can't prove this, but strengthened should.
            let aag = "aag 3 0 2 0 1 1\n2 3\n4 2\n6\n6 2 4\n";
            let circuit = parse_aag(aag).unwrap();
            let ts = Transys::from_aiger(&circuit);
            let mut engine = KindStrengthenedEngine::new(ts);
            let result = engine.check(20);
            assert!(
                matches!(result, CheckResult::Safe),
                "strengthened kind should prove two-step shift Safe, got {result:?}"
            );
        }

        #[test]
        fn test_strengthened_cancellation() {
            let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
            let ts = Transys::from_aiger(&circuit);
            let mut engine = KindStrengthenedEngine::new(ts);
            let cancel = Arc::new(AtomicBool::new(true));
            engine.set_cancelled(cancel);
            let result = engine.check(100);
            assert!(matches!(result, CheckResult::Unknown { .. }));
        }

        #[test]
        fn test_strengthened_discovers_stuck_at_zero_invariant() {
            let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
            let ts = Transys::from_aiger(&circuit);
            let mut engine = KindStrengthenedEngine::new(ts);
            engine.discover_init_invariants();
            assert!(
                !engine.invariant_lits.is_empty(),
                "should discover at least one invariant"
            );
            assert!(
                engine.invariant_lits.contains(&Lit::neg(Var(1))),
                "should discover Var(1)=0 invariant, found: {:?}",
                engine.invariant_lits
            );
        }

        #[test]
        fn test_strengthened_z4_luby_backend() {
            let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
            let ts = Transys::from_aiger(&circuit);
            let mut engine = KindStrengthenedEngine::with_backend(ts, SolverBackend::Z4Luby);
            let result = engine.check(10);
            assert!(
                matches!(result, CheckResult::Safe),
                "z4-luby strengthened kind should prove Safe, got {result:?}"
            );
        }

        /// Verify that the init invariant discovery phase finds stuck-at
        /// invariants and that they are persisted as pair_invariants or
        /// invariant_lits (not lost after assertion).
        #[test]
        fn test_strengthened_invariant_persistence_after_check() {
            // Latch with next=0, bad = latch. The stuck-at-zero invariant
            // is discovered during init analysis and persists through check.
            let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
            let ts = Transys::from_aiger(&circuit);
            let mut engine = KindStrengthenedEngine::new(ts);
            let result = engine.check(10);
            assert!(
                matches!(result, CheckResult::Safe),
                "expected Safe, got {result:?}"
            );
            // Invariants discovered during init phase should still be tracked.
            assert!(
                !engine.invariant_lits.is_empty(),
                "invariant_lits should persist after check()"
            );
        }

        /// Verify pair_invariants field is accessible and initialized empty.
        #[test]
        fn test_strengthened_pair_invariants_initialized_empty() {
            let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
            let ts = Transys::from_aiger(&circuit);
            let engine = KindStrengthenedEngine::new(ts);
            assert!(
                engine.pair_invariants.is_empty(),
                "pair_invariants should be empty before check()"
            );
        }
    }
}
