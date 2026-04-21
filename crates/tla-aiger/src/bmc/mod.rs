// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Bounded Model Checking (BMC) engine with incremental SAT.
//!
//! Unrolls the transition system for k time steps and checks if a bad state
//! is reachable. Uses an incremental SAT solver: each step adds new clauses
//! (the transition relation for one more step) and checks reachability via
//! assumptions.
//!
//! Also provides convenience functions `check_bmc()` and `check_kind()` that
//! apply COI reduction and return a `BmcResult` with raw literal witness traces.
//!
//! Reference: rIC3 `src/bmc.rs` (179 lines), adapted for our SAT types.

pub mod engine;
pub(crate) mod random_sim;
pub mod witness;

pub use engine::{BmcEngine, BmcStepStrategy};
pub(crate) use random_sim::RandomSimEngine;
pub use witness::{check_bmc, check_bmc_dynamic, check_kind, check_kind_simple_path, BmcResult};

#[cfg(test)]
mod tests {
    use std::sync::atomic::AtomicBool;
    use std::sync::Arc;

    use crate::check_result::CheckResult;
    use crate::parser::parse_aag;
    use crate::sat_types::{Lit, Var};
    use crate::transys::Transys;

    use super::*;

    #[test]
    fn test_bmc_trivially_safe() {
        // output=0 (constant FALSE) => never bad
        let circuit = parse_aag("aag 0 0 0 1 0\n0\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let mut bmc = BmcEngine::new(ts, 1);
        let result = bmc.check(10);
        assert!(matches!(result, CheckResult::Unknown { .. }));
    }

    #[test]
    fn test_bmc_trivially_unsafe() {
        // output=1 (constant TRUE) => bad at step 0
        let circuit = parse_aag("aag 0 0 0 1 0\n1\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let mut bmc = BmcEngine::new(ts, 1);
        let result = bmc.check(10);
        assert!(matches!(result, CheckResult::Unsafe { depth: 0, .. }));
    }

    #[test]
    fn test_bmc_toggle_reachable() {
        // Toggle flip-flop: latch starts at 0, toggles each step.
        // Bad = latch. Reachable at step 1.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let mut bmc = BmcEngine::new(ts, 1);
        let result = bmc.check(10);
        match &result {
            CheckResult::Unsafe { depth, trace } => {
                assert_eq!(*depth, 1);
                assert_eq!(trace.len(), 2); // steps 0 and 1
                                            // At step 0, latch should be false (init)
                assert_eq!(trace[0]["l0"], false);
                // At step 1, latch should be true (toggled)
                assert_eq!(trace[1]["l0"], true);
            }
            other => panic!("expected Unsafe, got {other:?}"),
        }
    }

    #[test]
    fn test_bmc_latch_stays_zero() {
        // Latch with next=0. Bad = latch. Never reachable.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let mut bmc = BmcEngine::new(ts, 1);
        let result = bmc.check(10);
        // BMC can't prove safety, only bound it
        assert!(matches!(result, CheckResult::Unknown { .. }));
    }

    #[test]
    fn test_bmc_step_size() {
        // Toggle flip-flop with step=5: unrolls 5 depths, then checks.
        // With the any-depth accumulator, BMC checks ALL depths at once,
        // so it finds the bug at depth 1 (the shallowest reachable bad state),
        // even though it unrolled 5 depths before checking.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let mut bmc = BmcEngine::new(ts, 5);
        let result = bmc.check(20);
        // any-depth accumulator finds the shallowest bug at depth 1
        assert!(
            matches!(result, CheckResult::Unsafe { depth: 1, .. }),
            "expected Unsafe at depth 1 (any-depth accumulator), got {result:?}"
        );
    }

    #[test]
    fn test_bmc_and_gate_unsafe() {
        // Two inputs, AND gate, bad = AND output.
        // Bad is reachable when both inputs are true (step 0).
        let circuit = parse_aag("aag 3 2 0 0 1 1\n2\n4\n6\n6 2 4\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let mut bmc = BmcEngine::new(ts, 1);
        let result = bmc.check(5);
        assert!(matches!(result, CheckResult::Unsafe { depth: 0, .. }));
    }

    #[test]
    fn test_bmc_cancellation() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let mut bmc = BmcEngine::new(ts, 1);
        let cancel = Arc::new(AtomicBool::new(true)); // Already cancelled
        bmc.set_cancelled(cancel);
        let result = bmc.check(100);
        assert!(matches!(result, CheckResult::Unknown { .. }));
    }

    #[test]
    fn test_bmc_dynamic_step_small_circuit() {
        // Small circuit: dynamic step should be large (but capped at 500).
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        // max_var=1, trans_clauses=0 => complexity ~1 => step = min(10M, 500) = 500
        let engine = BmcEngine::new_dynamic(ts);
        assert_eq!(engine.step, 500, "dynamic step should be capped at 500 for tiny circuit");
    }

    #[test]
    fn test_bmc_dynamic_step_finds_trivial_bug() {
        // Trivially unsafe (bad=1 at step 0): dynamic step BMC finds it immediately.
        let circuit = parse_aag("aag 0 0 0 1 0\n1\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let mut bmc = BmcEngine::new_dynamic(ts);
        let result = bmc.check(1000);
        assert!(
            matches!(result, CheckResult::Unsafe { depth: 0, .. }),
            "dynamic BMC should find Unsafe at depth 0, got {result:?}"
        );
    }

    #[test]
    fn test_bmc_dynamic_step_two_step_counter() {
        // 2-step counter: l0 toggles, l1 = delayed l0, bad = !l0 AND l1.
        // Bad reachable at step 2. Dynamic BMC with step=500 unrolls 500 depths,
        // then checks. With the any-depth accumulator, it finds the bug at depth 2
        // (the shallowest bad state), not at depth 500.
        let aag = "aag 3 0 2 0 1 1\n2 3\n4 2\n6\n6 3 4\n";
        let circuit = parse_aag(aag).unwrap();
        let ts = Transys::from_aiger(&circuit);
        let mut bmc = BmcEngine::new_dynamic(ts);
        let result = bmc.check(1000);
        assert!(
            matches!(result, CheckResult::Unsafe { depth: 2, .. }),
            "dynamic BMC should find 2-step counter bug at depth 2, got {result:?}"
        );
    }

    // ----- Tests for convenience functions -----

    #[test]
    fn test_check_bmc_dynamic_trivially_unsafe() {
        // Trivially unsafe: dynamic BMC should find counterexample at depth 0.
        let circuit = parse_aag("aag 0 0 0 1 0\n1\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let result = check_bmc_dynamic(&ts, 100);
        assert_eq!(result.verdict, Some(false));
        assert!(result.witness.is_some());
    }

    #[test]
    fn test_check_kind_simple_path_returns_unknown_for_safe_property() {
        // Latch with next=0, bad=latch. Property holds, but with the #4039
        // soundness guard, simple-path k-induction returns Unknown instead
        // of Safe to prevent false UNSAT on constrained circuits.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let result = check_kind_simple_path(&ts, 10);
        assert_eq!(result.verdict, None, "expected Unknown (soundness guard)");
        assert!(result.witness.is_none());
    }

    #[test]
    fn test_check_kind_simple_path_unsafe() {
        // Toggle: simple-path k-induction should find the counterexample.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let result = check_kind_simple_path(&ts, 10);
        assert_eq!(result.verdict, Some(false));
        assert!(result.witness.is_some());
    }

    #[test]
    fn test_check_bmc_trivially_safe() {
        // output=0 => never bad; BMC returns unknown (can't prove safety)
        let circuit = parse_aag("aag 0 0 0 1 0\n0\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let result = check_bmc(&ts, 10);
        assert_eq!(result.verdict, None);
        assert!(result.witness.is_none());
    }

    #[test]
    fn test_check_bmc_trivially_unsafe() {
        // output=1 => bad at step 0; BMC finds counterexample immediately
        let circuit = parse_aag("aag 0 0 0 1 0\n1\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let result = check_bmc(&ts, 10);
        assert_eq!(result.verdict, Some(false));
        assert_eq!(result.depth, 0);
        assert!(result.witness.is_some());
        let witness = result.witness.unwrap();
        assert_eq!(witness.len(), 1); // 1 step (step 0)
    }

    #[test]
    fn test_check_bmc_toggle() {
        // Toggle: latch starts 0, next=!latch, bad=latch.
        // BMC finds counterexample at depth 1.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let result = check_bmc(&ts, 10);
        assert_eq!(result.verdict, Some(false));
        assert_eq!(result.depth, 1);
        let witness = result.witness.unwrap();
        assert_eq!(witness.len(), 2); // steps 0 and 1
                                      // Step 0: latch (Var(1)) should be negative (false)
        assert!(witness[0].contains(&Lit::neg(Var(1))));
        // Step 1: latch (Var(1)) should be positive (true = bad)
        assert!(witness[1].contains(&Lit::pos(Var(1))));
    }

    #[test]
    fn test_check_kind_latch_stays_zero() {
        // Latch with next=0, bad=latch. k-induction proves safe.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let result = check_kind(&ts, 10);
        assert_eq!(result.verdict, Some(true));
        assert!(result.witness.is_none());
    }

    #[test]
    fn test_check_kind_toggle_unsafe() {
        // Toggle: latch starts 0, next=!latch, bad=latch.
        // k-induction finds counterexample at depth 1 (base case).
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let result = check_kind(&ts, 10);
        assert_eq!(result.verdict, Some(false));
        assert_eq!(result.depth, 1);
        assert!(result.witness.is_some());
    }

    #[test]
    fn test_check_bmc_two_step_shift_register() {
        // 2-stage shift register: l0 toggles, l1 = delayed copy of l0.
        // bad = l0 AND l1 is NEVER reachable (they alternate), so BMC returns unknown.
        //
        // AIGER:
        //   M=3 I=0 L=2 O=0 A=1 B=1
        //   latch: lit 2 (var 1), next = lit 3 (!var 1)  -- l0 toggles
        //   latch: lit 4 (var 2), next = lit 2 (var 1)   -- l1 = l0 delayed
        //   AND: 6 = 2 & 4 (var 3 = l0 AND l1) -- bad
        //   bad: 6
        //
        // Trace: 00 -> 10 -> 01 -> 10 -> ... (l0 AND l1 never true)
        let aag = "aag 3 0 2 0 1 1\n2 3\n4 2\n6\n6 2 4\n";
        let circuit = parse_aag(aag).unwrap();
        let ts = Transys::from_aiger(&circuit);
        let result = check_bmc(&ts, 10);
        // This property holds (l0 and l1 never both 1), but BMC can't prove it.
        assert_eq!(result.verdict, None, "BMC can't prove safety");
        assert!(result.witness.is_none());
    }

    #[test]
    fn test_check_bmc_two_step_counter_precise() {
        // 2-step counter: l0 toggles, l1 = delayed l0, bad = !l0 AND l1.
        // Reaches bad at step 2 (00 -> 10 -> 01, and !0 AND 1 = 1).
        //
        // AIGER (AAG):
        //   aag 3 0 2 0 1 1
        //   latch: 2 next=3 (l0: toggle)
        //   latch: 4 next=2 (l1: delayed copy of l0)
        //   AND: 6 = 3 & 4 (var 3 = !l0 AND l1)
        //   bad: 6
        let aag = "aag 3 0 2 0 1 1\n2 3\n4 2\n6\n6 3 4\n";
        let circuit = parse_aag(aag).unwrap();
        let ts = Transys::from_aiger(&circuit);

        let result = check_bmc(&ts, 10);
        assert_eq!(result.verdict, Some(false), "expected UNSAFE");
        assert_eq!(result.depth, 2, "bad reachable at step 2");
        let witness = result.witness.unwrap();
        assert_eq!(witness.len(), 3); // steps 0, 1, 2

        // Step 0: l0=0, l1=0
        assert!(witness[0].contains(&Lit::neg(Var(1))), "step 0: l0=0");
        assert!(witness[0].contains(&Lit::neg(Var(2))), "step 0: l1=0");
        // Step 1: l0=1, l1=0
        assert!(witness[1].contains(&Lit::pos(Var(1))), "step 1: l0=1");
        assert!(witness[1].contains(&Lit::neg(Var(2))), "step 1: l1=0");
        // Step 2: l0=0, l1=1 (bad: !l0 AND l1 = true)
        assert!(witness[2].contains(&Lit::neg(Var(1))), "step 2: l0=0");
        assert!(witness[2].contains(&Lit::pos(Var(2))), "step 2: l1=1");
    }

    #[test]
    fn test_check_kind_two_step_counter_unsafe() {
        // Same 2-step counter: k-induction should also find this bug.
        let aag = "aag 3 0 2 0 1 1\n2 3\n4 2\n6\n6 3 4\n";
        let circuit = parse_aag(aag).unwrap();
        let ts = Transys::from_aiger(&circuit);

        let result = check_kind(&ts, 10);
        assert_eq!(result.verdict, Some(false), "expected UNSAFE");
        assert!(result.depth >= 2, "needs depth >= 2 to find bug");
    }

    #[test]
    fn test_check_bmc_lit_trace_structure() {
        // Verify the lit trace has the right structure for a simple toggle.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let result = check_bmc(&ts, 5);
        assert_eq!(result.verdict, Some(false));
        let witness = result.witness.unwrap();
        // Each step should have exactly 1 literal (1 latch, 0 inputs)
        for step in &witness {
            assert_eq!(step.len(), 1, "toggle has 1 latch, no inputs");
        }
    }

    #[test]
    fn test_bmc_any_depth_accumulator_finds_intermediate_bug() {
        // Test that the any-depth accumulator catches bugs at intermediate depths
        // even with large step sizes.
        //
        // 2-step counter: bug at depth 2.
        // Step=100 means we unroll depths 1-100 before checking.
        // The accumulator should find the bug at depth 2, not depth 100.
        let aag = "aag 3 0 2 0 1 1\n2 3\n4 2\n6\n6 3 4\n";
        let circuit = parse_aag(aag).unwrap();
        let ts = Transys::from_aiger(&circuit);
        let mut bmc = BmcEngine::new(ts, 100);
        let result = bmc.check(200);
        match &result {
            CheckResult::Unsafe { depth, .. } => {
                assert_eq!(*depth, 2, "accumulator should find shallowest bug at depth 2");
            }
            other => panic!("expected Unsafe, got {other:?}"),
        }
    }

    // ----- z4-sat variant backend BMC tests -----

    mod z4_variant_bmc_tests {
        use super::*;
        use crate::sat_types::SolverBackend;

        #[test]
        fn test_bmc_z4_luby_trivially_unsafe() {
            // output=1 (constant TRUE) => bad at step 0
            let circuit = parse_aag("aag 0 0 0 1 0\n1\n").unwrap();
            let ts = Transys::from_aiger(&circuit);
            let mut bmc = BmcEngine::new_with_backend(ts, 1, SolverBackend::Z4Luby);
            let result = bmc.check(10);
            assert!(matches!(result, CheckResult::Unsafe { depth: 0, .. }));
        }

        #[test]
        fn test_bmc_z4_stable_trivially_safe_bounded() {
            // output=0 (constant FALSE) => never bad
            let circuit = parse_aag("aag 0 0 0 1 0\n0\n").unwrap();
            let ts = Transys::from_aiger(&circuit);
            let mut bmc = BmcEngine::new_with_backend(ts, 1, SolverBackend::Z4Stable);
            let result = bmc.check(10);
            assert!(matches!(result, CheckResult::Unknown { .. }));
        }

        #[test]
        fn test_bmc_z4_vmtf_toggle_reachable() {
            // Toggle flip-flop: latch starts at 0, toggles each step.
            // Bad = latch. Reachable at step 1.
            let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
            let ts = Transys::from_aiger(&circuit);
            let mut bmc = BmcEngine::new_with_backend(ts, 1, SolverBackend::Z4Vmtf);
            let result = bmc.check(10);
            match &result {
                CheckResult::Unsafe { depth, trace } => {
                    assert_eq!(*depth, 1);
                    assert_eq!(trace.len(), 2);
                    assert_eq!(trace[0]["l0"], false);
                    assert_eq!(trace[1]["l0"], true);
                }
                other => panic!("expected Unsafe, got {other:?}"),
            }
        }

        #[test]
        fn test_bmc_z4_geometric_dynamic_step() {
            // Trivially unsafe: dynamic step BMC should find it at depth 0.
            let circuit = parse_aag("aag 0 0 0 1 0\n1\n").unwrap();
            let ts = Transys::from_aiger(&circuit);
            let mut bmc =
                BmcEngine::new_dynamic_with_backend(ts, SolverBackend::Z4Geometric);
            let result = bmc.check(1000);
            assert!(
                matches!(result, CheckResult::Unsafe { depth: 0, .. }),
                "z4-sat Geometric dynamic BMC should find Unsafe at depth 0, got {result:?}"
            );
        }

        #[test]
        fn test_bmc_z4_chb_two_step_counter() {
            // 2-step counter: l0 toggles, l1 = delayed l0, bad = !l0 AND l1.
            // Bad reachable at step 2 (00 -> 10 -> 01, and !0 AND 1 = 1).
            let aag = "aag 3 0 2 0 1 1\n2 3\n4 2\n6\n6 3 4\n";
            let circuit = parse_aag(aag).unwrap();
            let ts = Transys::from_aiger(&circuit);
            let mut bmc = BmcEngine::new_with_backend(ts, 1, SolverBackend::Z4Chb);
            let result = bmc.check(10);
            assert!(
                matches!(result, CheckResult::Unsafe { depth: 2, .. }),
                "z4-sat CHB BMC should find 2-step counter bug at depth 2, got {result:?}"
            );
        }

        #[test]
        fn test_bmc_z4_nopreprocess_cancellation() {
            let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
            let ts = Transys::from_aiger(&circuit);
            let mut bmc =
                BmcEngine::new_with_backend(ts, 1, SolverBackend::Z4NoPreprocess);
            let cancel = Arc::new(AtomicBool::new(true));
            bmc.set_cancelled(cancel);
            let result = bmc.check(100);
            assert!(matches!(result, CheckResult::Unknown { .. }));
        }

        #[test]
        fn test_bmc_z4_luby_step_5_with_accumulator() {
            // Toggle flip-flop with step=5 and z4-sat Luby backend.
            // The any-depth accumulator should find the bug at depth 1.
            let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
            let ts = Transys::from_aiger(&circuit);
            let mut bmc = BmcEngine::new_with_backend(ts, 5, SolverBackend::Z4Luby);
            let result = bmc.check(20);
            assert!(
                matches!(result, CheckResult::Unsafe { depth: 1, .. }),
                "z4-sat Luby BMC with step=5 should find bug at depth 1, got {result:?}"
            );
        }

        /// z4-sat variant and default BMC should produce identical results on the same circuit.
        #[test]
        fn test_bmc_z4_variant_default_agreement() {
            let aag = "aag 3 0 2 0 1 1\n2 3\n4 2\n6\n6 3 4\n";
            let circuit = parse_aag(aag).unwrap();
            let ts = Transys::from_aiger(&circuit);

            let mut default_bmc = BmcEngine::new(ts.clone(), 1);
            let default_result = default_bmc.check(10);

            let mut luby_bmc =
                BmcEngine::new_with_backend(ts, 1, SolverBackend::Z4Luby);
            let luby_result = luby_bmc.check(10);

            // Both should find Unsafe at the same depth.
            match (&default_result, &luby_result) {
                (
                    CheckResult::Unsafe {
                        depth: default_d, ..
                    },
                    CheckResult::Unsafe {
                        depth: luby_d, ..
                    },
                ) => {
                    assert_eq!(
                        default_d, luby_d,
                        "z4-sat default and Luby should find bug at same depth"
                    );
                }
                _ => panic!(
                    "both should be Unsafe: default={default_result:?}, luby={luby_result:?}"
                ),
            }
        }

        /// z4-sat Luby BMC with dynamic step finds intermediate bugs.
        #[test]
        fn test_bmc_z4_luby_dynamic_two_step_counter() {
            let aag = "aag 3 0 2 0 1 1\n2 3\n4 2\n6\n6 3 4\n";
            let circuit = parse_aag(aag).unwrap();
            let ts = Transys::from_aiger(&circuit);
            let mut bmc =
                BmcEngine::new_dynamic_with_backend(ts, SolverBackend::Z4Luby);
            let result = bmc.check(1000);
            assert!(
                matches!(result, CheckResult::Unsafe { depth: 2, .. }),
                "z4-sat Luby dynamic BMC should find 2-step counter bug at depth 2, got {result:?}"
            );
        }
    }

    /// Test that BMC can reach depth 100+ on a shift register chain (#4194).
    ///
    /// Constructs a chain of N latches: l0 toggles, l1 = delayed l0, l2 = delayed l1, etc.
    /// The bad state is the last latch in the chain being true, which is only reachable
    /// at depth N (the toggle propagates through the chain one step at a time).
    /// This verifies that the incremental SAT encoding works correctly for deep
    /// unrolling without excessive memory or solver degradation.
    #[test]
    fn test_bmc_deep_shift_register_chain_depth_128() {
        // Build a chain of 128 latches:
        //   l0: starts 0, next = !l0 (toggle)
        //   l1: starts 0, next = l0
        //   l2: starts 0, next = l1
        //   ...
        //   l127: starts 0, next = l126
        //   bad = l127
        //
        // The toggle at l0 propagates through the chain: l127 becomes true at step 128.
        //
        // AIGER encoding:
        //   M=128 I=0 L=128 O=0 A=0 B=1
        //   Latch 0 (lit 2): next = lit 3 (NOT lit 2, i.e. toggle)
        //   Latch i (lit 2*(i+1)): next = lit 2*i (previous latch)
        //   Bad = lit 2*128 = lit 256 (last latch)
        let n = 128;
        let mut lines = Vec::new();
        lines.push(format!("aag {n} 0 {n} 0 0 1"));
        // Latch 0: toggle
        lines.push(format!("2 3")); // lit 2, next = NOT 2 = 3
        // Latches 1..n-1: delayed copy of previous
        for i in 1..n {
            let lit = 2 * (i + 1);
            let prev_lit = 2 * i;
            lines.push(format!("{lit} {prev_lit}"));
        }
        // Bad = last latch
        let bad_lit = 2 * n;
        lines.push(format!("{bad_lit}"));

        let aag = lines.join("\n") + "\n";
        let circuit = parse_aag(&aag).unwrap();
        let ts = Transys::from_aiger(&circuit);

        // Use geometric backoff for efficiency: step=1 for first 50 depths,
        // then doubles. Should reach depth 128 in ~60 SAT calls.
        let mut bmc = BmcEngine::new_geometric_backoff(ts);
        let result = bmc.check_geometric_backoff(200, 50, 10, 64);

        match &result {
            CheckResult::Unsafe { depth, trace } => {
                assert!(
                    *depth >= 128,
                    "shift register chain should find bug at depth >= 128, got {depth}"
                );
                // Verify the trace has the right length
                assert!(
                    trace.len() > 128,
                    "trace should have > 128 steps, got {}",
                    trace.len()
                );
            }
            other => panic!(
                "expected Unsafe at depth >= 128 for 128-latch shift register, got {other:?}"
            ),
        }
    }

    /// Tests for geometric backoff BMC (#4123).
    mod geometric_backoff_tests {
        use super::*;
        use crate::sat_types::SolverBackend;

        #[test]
        fn test_geometric_backoff_trivially_unsafe() {
            // output=1 (constant TRUE) => bad at step 0
            let circuit = parse_aag("aag 0 0 0 1 0\n1\n").unwrap();
            let ts = Transys::from_aiger(&circuit);
            let mut bmc = BmcEngine::new_geometric_backoff(ts);
            let result = bmc.check_geometric_backoff(1000, 50, 20, 64);
            assert!(
                matches!(result, CheckResult::Unsafe { depth: 0, .. }),
                "geometric backoff BMC should find Unsafe at depth 0, got {result:?}"
            );
        }

        #[test]
        fn test_geometric_backoff_toggle() {
            // Toggle flip-flop: latch starts at 0, toggles each step.
            // Bad = latch. Reachable at step 1 (within initial_depths phase).
            let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
            let ts = Transys::from_aiger(&circuit);
            let mut bmc = BmcEngine::new_geometric_backoff(ts);
            let result = bmc.check_geometric_backoff(1000, 50, 20, 64);
            assert!(
                matches!(result, CheckResult::Unsafe { depth: 1, .. }),
                "geometric backoff BMC should find toggle bug at depth 1, got {result:?}"
            );
        }

        #[test]
        fn test_geometric_backoff_two_step_counter() {
            // 2-step counter: bad at depth 2. Within initial_depths phase.
            let aag = "aag 3 0 2 0 1 1\n2 3\n4 2\n6\n6 3 4\n";
            let circuit = parse_aag(aag).unwrap();
            let ts = Transys::from_aiger(&circuit);
            let mut bmc = BmcEngine::new_geometric_backoff(ts);
            let result = bmc.check_geometric_backoff(1000, 50, 20, 64);
            assert!(
                matches!(result, CheckResult::Unsafe { depth: 2, .. }),
                "geometric backoff BMC should find 2-step counter bug at depth 2, got {result:?}"
            );
        }

        #[test]
        fn test_geometric_backoff_safe_bounded() {
            // output=0 (constant FALSE) => never bad. BMC returns Unknown.
            let circuit = parse_aag("aag 0 0 0 1 0\n0\n").unwrap();
            let ts = Transys::from_aiger(&circuit);
            let mut bmc = BmcEngine::new_geometric_backoff(ts);
            let result = bmc.check_geometric_backoff(100, 50, 20, 64);
            assert!(
                matches!(result, CheckResult::Unknown { .. }),
                "geometric backoff BMC should return Unknown for safe circuit, got {result:?}"
            );
        }

        #[test]
        fn test_geometric_backoff_small_initial_depths() {
            // Test with initial_depths=2 to exercise the transition from
            // phase 1 (step=1) to phase 2 (geometric backoff).
            let aag = "aag 3 0 2 0 1 1\n2 3\n4 2\n6\n6 3 4\n";
            let circuit = parse_aag(aag).unwrap();
            let ts = Transys::from_aiger(&circuit);
            let mut bmc = BmcEngine::new_geometric_backoff(ts);
            // Bug at depth 2. With initial_depths=2, depth 2 is the
            // last depth of phase 1 (step=1), so it should still be caught.
            let result = bmc.check_geometric_backoff(1000, 2, 5, 32);
            assert!(
                matches!(result, CheckResult::Unsafe { depth: 2, .. }),
                "geometric backoff with small initial should find bug at depth 2, got {result:?}"
            );
        }

        #[test]
        fn test_geometric_backoff_cancellation() {
            let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
            let ts = Transys::from_aiger(&circuit);
            let mut bmc = BmcEngine::new_geometric_backoff(ts);
            let cancel = Arc::new(AtomicBool::new(true)); // Already cancelled
            bmc.set_cancelled(cancel);
            let result = bmc.check_geometric_backoff(1000, 50, 20, 64);
            assert!(
                matches!(result, CheckResult::Unknown { .. }),
                "geometric backoff BMC should return Unknown when cancelled, got {result:?}"
            );
        }

        #[test]
        fn test_geometric_backoff_z4_variant() {
            // Geometric backoff with z4-sat Luby backend.
            let aag = "aag 3 0 2 0 1 1\n2 3\n4 2\n6\n6 3 4\n";
            let circuit = parse_aag(aag).unwrap();
            let ts = Transys::from_aiger(&circuit);
            let mut bmc = BmcEngine::new_geometric_backoff_with_backend(
                ts,
                SolverBackend::Z4Luby,
            );
            let result = bmc.check_geometric_backoff(1000, 50, 20, 64);
            assert!(
                matches!(result, CheckResult::Unsafe { depth: 2, .. }),
                "geometric backoff z4-Luby BMC should find bug at depth 2, got {result:?}"
            );
        }
    }

    /// Witness verification tests: verify that BMC witnesses are valid
    /// circuit executions by simulating the circuit.
    mod witness_verification_tests {
        use super::*;

        #[test]
        fn test_bmc_witness_toggle_valid() {
            // Toggle flip-flop: should produce a valid witness at depth 1.
            let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
            let ts = Transys::from_aiger(&circuit);
            let result = check_bmc(&ts, 10);
            assert_eq!(result.verdict, Some(false));

            // Extract the trace from a fresh BMC run to get named trace
            let reduced = ts.coi_reduce().compact_vars();
            let mut engine = BmcEngine::new(reduced.clone(), 1);
            match engine.check(10) {
                CheckResult::Unsafe { depth, trace } => {
                    // Verify the witness against the transition system
                    let verify = reduced.verify_witness(&trace);
                    assert!(
                        verify.is_ok(),
                        "toggle witness should be valid, got: {:?}",
                        verify.err()
                    );
                }
                other => panic!("expected Unsafe, got {other:?}"),
            }
        }

        #[test]
        fn test_bmc_witness_two_step_counter_valid() {
            // 2-step counter: bug at depth 2.
            let aag = "aag 3 0 2 0 1 1\n2 3\n4 2\n6\n6 3 4\n";
            let circuit = parse_aag(aag).unwrap();
            let ts = Transys::from_aiger(&circuit);

            let reduced = ts.coi_reduce().compact_vars();
            let mut engine = BmcEngine::new(reduced.clone(), 1);
            match engine.check(10) {
                CheckResult::Unsafe { depth, trace } => {
                    let verify = reduced.verify_witness(&trace);
                    assert!(
                        verify.is_ok(),
                        "2-step counter witness should be valid, got: {:?}",
                        verify.err()
                    );
                }
                other => panic!("expected Unsafe, got {other:?}"),
            }
        }

        #[test]
        fn test_bmc_witness_preprocessed_valid() {
            // Run BMC on a preprocessed circuit and verify the witness.
            let aag = "aag 3 0 2 0 1 1\n2 3\n4 2\n6\n6 3 4\n";
            let circuit = parse_aag(aag).unwrap();
            let ts = Transys::from_aiger(&circuit);
            let (preprocessed, _) = ts.preprocess();

            let mut engine = BmcEngine::new(preprocessed.clone(), 1);
            match engine.check(10) {
                CheckResult::Unsafe { depth, trace } => {
                    let verify = preprocessed.verify_witness(&trace);
                    assert!(
                        verify.is_ok(),
                        "preprocessed witness should be valid, got: {:?}",
                        verify.err()
                    );
                }
                other => panic!("expected Unsafe, got {other:?}"),
            }
        }

        /// Regression test for #4103: cal76 benchmark spurious SAT.
        ///
        /// All 8 HWMCC competition solvers agree cal76 is SAFE (UNSAT), but
        /// the portfolio path (with full preprocessing + dynamic step BMC)
        /// was finding SAT at depth 210. This test verifies that BMC on the
        /// preprocessed cal76 circuit does NOT find a counterexample.
        ///
        /// Tests both step=1 (no accumulator) and dynamic step (with
        /// any-depth accumulator, matching the portfolio's BMC path).
        #[test]
        fn test_cal76_no_spurious_sat() {
            let bench_path = std::path::PathBuf::from(env!("HOME"))
                .join("hwmcc/benchmarks/bitlevel/safety/2019/goel/industry/cal76/cal76.aig");
            if !bench_path.exists() {
                eprintln!("Skipping cal76 test: benchmark not found at {bench_path:?}");
                return;
            }

            let data = std::fs::read(&bench_path).expect("failed to read cal76");
            let circuit = crate::parser::parse_aig(&data).expect("failed to parse cal76");
            let ts = Transys::from_aiger(&circuit);

            // Preprocess exactly as portfolio does
            let (preprocessed, _stats) = ts.preprocess();
            eprintln!(
                "cal76 preprocessed: max_var={} latches={} inputs={} gates={} clauses={}",
                preprocessed.max_var,
                preprocessed.num_latches,
                preprocessed.num_inputs,
                preprocessed.and_defs.len(),
                preprocessed.trans_clauses.len(),
            );

            // Test with dynamic step (step=500 for this small circuit),
            // which uses the any-depth accumulator -- the exact path
            // that was producing spurious SAT.
            eprintln!("=== Testing with dynamic step (accumulator path) ===");
            let mut engine = BmcEngine::new_dynamic(preprocessed.clone());
            eprintln!("cal76 dynamic step = {}", engine.step);
            let result = engine.check(300);

            match &result {
                CheckResult::Unsafe { depth, trace } => {
                    eprintln!("cal76: dynamic BMC found SAT at depth {depth}");

                    // Verify witness against the preprocessed circuit
                    let verify = preprocessed.verify_witness(trace);
                    if verify.is_err() {
                        eprintln!(
                            "cal76: witness FAILS simulation (spurious SAT): {}",
                            verify.err().unwrap()
                        );
                    } else {
                        eprintln!("cal76: witness PASSES simulation -- preprocessing bug!");
                    }
                    panic!(
                        "cal76: BMC finds SAT at depth {depth}. \
                         Bug #4103 not yet fixed."
                    );
                }
                CheckResult::Unknown { reason } => {
                    eprintln!("cal76 dynamic: BMC bounded -- CORRECT ({reason})");
                }
                CheckResult::Safe => {
                    eprintln!("cal76 dynamic: BMC proved SAFE -- CORRECT");
                }
            }

            // Also test with step=1 (no accumulator) for comparison
            eprintln!("=== Testing with step=1 (no accumulator) ===");
            let mut engine2 = BmcEngine::new(preprocessed.clone(), 1);
            let result2 = engine2.check(300);

            match &result2 {
                CheckResult::Unsafe { depth, .. } => {
                    panic!("cal76: step=1 BMC also found SAT at depth {depth}!");
                }
                CheckResult::Unknown { reason } => {
                    eprintln!("cal76 step=1: BMC bounded -- CORRECT ({reason})");
                }
                CheckResult::Safe => {
                    eprintln!("cal76 step=1: BMC proved SAFE -- CORRECT");
                }
            }

            // Test all z4-sat variant backends used by the portfolio.
            // Use depth 220 (just past the spurious SAT at depth 210) rather
            // than 300 to keep test runtime reasonable. The step=1 and dynamic
            // step tests above already verify depth 300.
            use crate::sat_types::SolverBackend;
            let variants: &[(&str, usize, SolverBackend)] = &[
                ("Z4Luby step=10", 10, SolverBackend::Z4Luby),
                ("Z4Stable step=65", 65, SolverBackend::Z4Stable),
                ("Z4Vmtf step=500", 500, SolverBackend::Z4Vmtf),
                ("Z4Geometric step=1", 1, SolverBackend::Z4Geometric),
                ("Z4Chb step=1", 1, SolverBackend::Z4Chb),
                ("Z4NoPreprocess step=1", 1, SolverBackend::Z4NoPreprocess),
            ];

            for &(name, step, backend) in variants {
                eprintln!("=== Testing {name} ===");
                let mut engine = BmcEngine::new_with_backend(
                    preprocessed.clone(),
                    step,
                    backend,
                );
                let result = engine.check(220);
                match &result {
                    CheckResult::Unsafe { depth, trace } => {
                        eprintln!("cal76 {name}: FOUND SAT at depth {depth}!");
                        let verify = preprocessed.verify_witness(trace);
                        eprintln!(
                            "  witness verification: {}",
                            if verify.is_ok() { "PASSES" } else { "FAILS" }
                        );
                        if let Err(e) = &verify {
                            eprintln!("  reason: {e}");
                        }
                        panic!(
                            "cal76: {name} finds SAT at depth {depth}. \
                             Bug #4103 in z4-sat variant."
                        );
                    }
                    CheckResult::Unknown { reason } => {
                        eprintln!("cal76 {name}: bounded -- CORRECT ({reason})");
                    }
                    CheckResult::Safe => {
                        eprintln!("cal76 {name}: SAFE -- CORRECT");
                    }
                }
            }
        }
    }
}

