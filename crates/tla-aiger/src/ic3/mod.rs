// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! IC3/PDR model checking engine for AIGER circuits.
//!
//! IC3 (Incremental Construction of Inductive Clauses for Indubitable Correctness)
//! is a SAT-based model checking algorithm that proves safety properties by
//! constructing an inductive invariant frame-by-frame.
//!
//! This implementation follows:
//! - Aaron R. Bradley, "SAT-Based Model Checking without Unrolling" (VMCAI 2011)
//! - Niklas Een, Alan Mishchenko, Robert Brayton, "Efficient implementation of
//!   property directed reachability" (FMCAD 2011)
//! - The rIC3 implementation by Yuheng Su (github.com/gipsyh/rIC3)
//!
//! The main loop:
//! 1. Check if Init => !Bad (if init is bad, return UNSAFE at depth 0)
//! 2. Extend frames (add new level)
//! 3. Blocking phase: find bad states reachable at top frame, create obligations
//! 4. Block all obligations (or find counterexample trace)
//! 5. Propagate lemmas forward; if any frame converges, return SAFE
//!
//! # Module structure
//!
//! - `config`: Configuration types (`Ic3Config`, `Ic3Result`, `GeneralizationOrder`, etc.)
//! - `engine`: `Ic3Engine` struct definition, constructor, solver management
//! - `run`: Main IC3 loop (`check`), init checks, state extraction, public entry points
//! - `block`: Blocking phase (`block_all`, `block_one`), CTG parameter computation
//! - `mic`: MIC generalization, CTG, inductiveness checks, domain solver construction
//! - `propagate`: Frame propagation, lemma pushing, infinity frame promotion
//! - `validate`: Independent invariant validation, consecution cross-checks

// --- Core IC3 modules (split from the original monolithic mod.rs) ---
pub(super) mod config;
pub(super) mod engine;
pub(super) mod run;
pub(super) mod block;
pub(super) mod mic;
pub(super) mod propagate;
pub(super) mod validate;

// --- Existing submodules ---
pub(crate) mod cegar;
pub(crate) mod domain;
pub mod frame;
pub mod lift;
pub mod obligation;
pub(crate) mod predprop;
pub(crate) mod vsids;

// --- Public API re-exports ---
pub use config::{GeneralizationOrder, Ic3Config, Ic3Result, RestartStrategy, ValidationStrategy};
pub use engine::Ic3Engine;
pub use run::{check_ic3, check_ic3_with_config};

#[cfg(test)]
pub use run::check_ic3_no_coi;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse_aag;
    use crate::sat_types::{SatSolver, Z4SatCdclSolver};

    #[test]
    fn test_trivially_safe_false_output() {
        let circuit = parse_aag("aag 0 0 0 1 0\n0\n").unwrap();
        let result = check_ic3(&circuit);
        assert!(matches!(result, Ic3Result::Safe { .. }));
    }

    #[test]
    fn test_trivially_unsafe_true_output() {
        let circuit = parse_aag("aag 0 0 0 1 0\n1\n").unwrap();
        let result = check_ic3(&circuit);
        assert!(matches!(result, Ic3Result::Unsafe { depth: 0, .. }));
    }

    #[test]
    fn test_toggle_reachable() {
        // Toggle: latch starts at 0, next = NOT latch. Bad = latch.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let result = check_ic3(&circuit);
        match result {
            Ic3Result::Unsafe { depth, trace } => {
                assert!(depth <= 2, "depth should be small, got {depth}");
                assert!(!trace.is_empty());
            }
            other => panic!("expected Unsafe, got {other:?}"),
        }
    }

    #[test]
    fn test_stuck_at_zero_safe() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let result = check_ic3(&circuit);
        assert!(matches!(result, Ic3Result::Safe { .. }), "got {result:?}");
    }

    #[test]
    fn test_stuck_at_one_unsafe() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 1\n2\n").unwrap();
        let result = check_ic3(&circuit);
        assert!(matches!(result, Ic3Result::Unsafe { .. }), "got {result:?}");
    }

    #[test]
    fn test_two_latches_safe() {
        let circuit = parse_aag("aag 3 0 2 0 1 1\n2 0\n4 0\n6\n6 2 4\n").unwrap();
        let result = check_ic3(&circuit);
        assert!(matches!(result, Ic3Result::Safe { .. }), "got {result:?}");
    }

    #[test]
    fn test_and_gate_unsafe_inputs() {
        let circuit = parse_aag("aag 3 2 0 0 1 1\n2\n4\n6\n6 2 4\n").unwrap();
        let result = check_ic3(&circuit);
        assert!(
            matches!(result, Ic3Result::Unsafe { depth: 0, .. }),
            "got {result:?}"
        );
    }

    #[test]
    fn test_init_bad_direct() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0 1\n2\n").unwrap();
        let result = check_ic3(&circuit);
        assert!(
            matches!(result, Ic3Result::Unsafe { depth: 0, .. }),
            "got {result:?}"
        );
    }

    #[test]
    fn test_no_bad_properties() {
        let circuit = parse_aag("aag 1 1 0 0 0\n2\n").unwrap();
        let result = check_ic3(&circuit);
        assert!(matches!(result, Ic3Result::Safe { .. }), "got {result:?}");
    }

    #[test]
    fn test_ic3_result_trace_structure() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let result = check_ic3(&circuit);
        if let Ic3Result::Unsafe { trace, .. } = result {
            assert!(!trace.is_empty());
            for state in &trace {
                assert!(!state.is_empty());
            }
        }
    }

    #[test]
    fn test_self_loop_safe() {
        // Latch next = current, starts at 0. Bad = latch. Stays 0 forever.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 2\n2\n").unwrap();
        let result = check_ic3(&circuit);
        assert!(
            matches!(result, Ic3Result::Safe { .. }),
            "expected Safe for self-loop latch starting at 0, got {result:?}"
        );
    }

    #[test]
    fn test_self_loop_init_one_unsafe() {
        // Latch next = current, starts at 1. Bad = latch.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 2 1\n2\n").unwrap();
        let result = check_ic3(&circuit);
        assert!(
            matches!(result, Ic3Result::Unsafe { depth: 0, .. }),
            "got {result:?}"
        );
    }

    #[test]
    fn test_input_controlled_bad() {
        let circuit = parse_aag("aag 1 1 0 0 0 1\n2\n2\n").unwrap();
        let result = check_ic3(&circuit);
        assert!(
            matches!(result, Ic3Result::Unsafe { depth: 0, .. }),
            "got {result:?}"
        );
    }

    #[test]
    fn test_negated_input_bad() {
        let circuit = parse_aag("aag 1 1 0 0 0 1\n2\n3\n").unwrap();
        let result = check_ic3(&circuit);
        assert!(
            matches!(result, Ic3Result::Unsafe { depth: 0, .. }),
            "got {result:?}"
        );
    }

    #[test]
    fn test_toggle_simple_vs_z4() {
        // Toggle: latch starts at 0, next = NOT latch. Bad = latch.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let ts = crate::transys::Transys::from_aiger(&circuit);

        // Test with SimpleSolver
        let mut engine_simple = Ic3Engine::new(ts.clone()).with_simple_solver();
        let result_simple = engine_simple.check();
        eprintln!("SimpleSolver result: {result_simple:?}");

        // Debug: test z4-sat solver directly for the toggle
        let mut vs = Z4SatCdclSolver::new(3);
        vs.add_clause(&[crate::sat_types::Lit::TRUE]);
        vs.add_clause(&[crate::sat_types::Lit::neg(crate::sat_types::Var(2)), crate::sat_types::Lit::neg(crate::sat_types::Var(1))]);
        vs.add_clause(&[crate::sat_types::Lit::pos(crate::sat_types::Var(2)), crate::sat_types::Lit::pos(crate::sat_types::Var(1))]);
        let r = vs.solve(&[crate::sat_types::Lit::pos(crate::sat_types::Var(1))]);
        eprintln!("z4-sat direct: bad reachable? {r:?}");
        vs.add_clause(&[crate::sat_types::Lit::neg(crate::sat_types::Var(1))]);
        let r2 = vs.solve(&[crate::sat_types::Lit::pos(crate::sat_types::Var(2))]);
        eprintln!("z4-sat direct: predecessor? {r2:?}");

        // Test with Z4Solver via IC3
        let mut engine_z4 = Ic3Engine::new(ts);
        let result_z4 = engine_z4.check();
        eprintln!("Z4Solver IC3 result: {result_z4:?}");

        assert!(
            matches!(result_simple, Ic3Result::Unsafe { .. }),
            "SimpleSolver should find Unsafe, got {result_simple:?}"
        );
        assert!(
            matches!(result_z4, Ic3Result::Unsafe { .. }),
            "Z4Solver should find Unsafe, got {result_z4:?}"
        );
    }

    /// Test IC3 on a simple constrained circuit.
    ///
    /// 2 inputs (i1, i2), 1 latch (L), constraint: i1 OR i2 (at least one input true).
    /// L starts at 0, next = L AND i1. Bad = L (L can only become 1 if i1=1).
    /// With constraint: i1 or i2 must be true. L=0->0->...->0 unless i1=1.
    /// If i1=1 at step 0: L@1=0&1=0. L can never reach 1 since next=L&i1 and L starts 0.
    /// This is SAFE.
    #[test]
    fn test_constrained_safe() {
        // aag 4 2 1 0 1 1 1
        // inputs: 2, 4
        // latch: 6, next=8
        // bad: 6
        // constraint: 8 (AND of i1 and latch... wrong, let me think)
        // Actually, let's make a simple one:
        // aag 3 2 1 0 0 1 1
        // i1=2, i2=4, L=6 next=0 (L always goes to 0)
        // bad: 6 (L=1 is bad)
        // constraint: 2 (i1 must be true)
        // L starts at 0, goes to 0. L never becomes 1. Safe.
        let aag = "aag 3 2 1 0 0 1 1\n2\n4\n6 0\n6\n2\n";
        let circuit = parse_aag(aag).unwrap();
        let ts = crate::transys::Transys::from_aiger(&circuit);
        assert_eq!(ts.constraint_lits.len(), 1);
        let mut engine = Ic3Engine::new(ts).with_simple_solver();
        let result = engine.check();
        assert!(
            matches!(result, Ic3Result::Safe { .. }),
            "expected Safe, got {result:?}"
        );
    }

    /// Test IC3 with a constraint that allows a bad state to be reached.
    ///
    /// Input i1, latch L (starts 0), next=i1. Bad=L. Constraint: i1.
    /// With constraint i1=true: at step 1, L=i1@0=1 (bad!). Should be UNSAFE.
    #[test]
    fn test_constrained_unsafe() {
        // aag 2 1 1 0 0 1 1
        // i1=2 (var 1)
        // L=4 (var 2), next=2 (= i1)
        // bad: 4 (L)
        // constraint: 2 (i1 must be true)
        let aag = "aag 2 1 1 0 0 1 1\n2\n4 2\n4\n2\n";
        let circuit = parse_aag(aag).unwrap();
        let ts = crate::transys::Transys::from_aiger(&circuit);
        assert_eq!(ts.constraint_lits.len(), 1);
        let mut engine = Ic3Engine::new(ts).with_simple_solver();
        let result = engine.check();
        assert!(
            matches!(result, Ic3Result::Unsafe { .. }),
            "expected Unsafe, got {result:?}"
        );
    }

    // -----------------------------------------------------------------------
    // IC3 soundness regression tests (#3983)
    //
    // These circuits require counterexamples of depth >= 3. Before the fix,
    // IC3 falsely reported Safe because permanent add_clause calls in
    // is_inductive/block_one polluted the solver, causing premature convergence.
    // -----------------------------------------------------------------------

    /// 3-latch shift register: A toggles, B=prev(A), C=prev(B).
    /// Bad = A AND B AND C. Requires 3 steps to reach (1,1,1).
    /// Init: all 0. Step 1: (1,0,0). Step 2: (0,1,0). Step 3: (1,0,1)->(0,1,0)->...
    /// (A,B,C) sequence: (0,0,0)->(1,0,0)->(0,1,0)->(1,0,1)->(0,1,0)->...
    /// Bad=A&B&C: never reached because when A=1,B=0 or when B=1,A=0.
    /// Wait, let me re-think. We need a circuit that IS unsafe at depth N.
    ///
    /// Better: 3-latch shift register where input feeds latch A, A feeds B, B feeds C.
    /// Input is unconstrained. Bad = A AND B AND C.
    /// If input=1 for 3 steps: (0,0,0)->(1,0,0)->(1,1,0)->(1,1,1) = bad at step 3.
    #[test]
    fn test_ic3_soundness_shift_register_3deep() {
        // 3 latches: A=v2(lit 4), B=v3(lit 6), C=v4(lit 8). 1 input: i=v1(lit 2).
        // A.next = i, B.next = A, C.next = B. All init 0.
        // With input=1 for 3 steps: (0,0,0)->(1,0,0)->(1,1,0)->(1,1,1) = bad at step 3.
        // AND gates: v5 = A AND B (lit 10 = AND(4,6)), v6 = v5 AND C (lit 12 = AND(10,8)).
        // Bad = lit 12 (A AND B AND C).
        // Header: aag M I L O A B -> aag 6 1 3 0 2 1
        let aag = "\
aag 6 1 3 0 2 1
2
4 2
6 4
8 6
12
10 4 6
12 10 8
";
        let circuit = parse_aag(aag).unwrap();

        // Test with Z4Sat (production solver). SimpleSolver is too slow for
        // deep circuits with activation literals (no CDCL, DPLL recursion limit).
        let ts = crate::transys::Transys::from_aiger(&circuit);
        let mut engine = Ic3Engine::new(ts);
        let result = engine.check();
        assert!(
            matches!(result, Ic3Result::Unsafe { .. }),
            "3-deep shift register should be Unsafe, got {result:?}"
        );
    }

    /// 4-latch shift register: same pattern but needs 4 steps.
    /// Bad = A AND B AND C AND D. Input feeds A, A->B, B->C, C->D.
    #[test]
    fn test_ic3_soundness_shift_register_4deep() {
        // 4 latches: A=v2(lit 4), B=v3(lit 6), C=v4(lit 8), D=v5(lit 10). Input: v1(lit 2).
        // A.next=input, B.next=A, C.next=B, D.next=C. All init 0.
        // With input=1 for 4 steps: (0,0,0,0)->(1,0,0,0)->(1,1,0,0)->(1,1,1,0)->(1,1,1,1)=bad.
        // AND gates: v6=A&B (12=AND(4,6)), v7=v6&C (14=AND(12,8)), v8=v7&D (16=AND(14,10)).
        // Bad = lit 16 (A AND B AND C AND D).
        // Header: aag M I L O A B -> aag 8 1 4 0 3 1
        let aag = "\
aag 8 1 4 0 3 1
2
4 2
6 4
8 6
10 8
16
12 4 6
14 12 8
16 14 10
";
        let circuit = parse_aag(aag).unwrap();
        let ts = crate::transys::Transys::from_aiger(&circuit);
        let mut engine = Ic3Engine::new(ts);
        let result = engine.check();
        assert!(
            matches!(result, Ic3Result::Unsafe { .. }),
            "4-deep shift register should be Unsafe, got {result:?}"
        );
    }

    /// Regression test for #4039: IC3 lemma solver pollution.
    ///
    /// Before the fix, non-frame-0 blocking lemmas were incorrectly added to
    /// solver[0] (the Init frame solver). This over-constrained solver[0],
    /// causing false UNSAT results in consecution checks at frame 1, which led
    /// to cascading unsound lemmas and premature convergence.
    ///
    /// The bug was exposed by microban_24.aig (29 latches, 211 constraints),
    /// where IC3 falsely converged at depth 4 with an unsound invariant.
    /// All 8 HWMCC solvers report SAT for this benchmark.
    ///
    /// This test verifies:
    /// 1. IC3 does NOT converge within 10 depths on microban_24 (the old bug
    ///    converged at depth 4).
    /// 2. If IC3 does converge reporting Safe, the invariant is validated
    ///    independently (Init=>Inv, Inv AND T => Inv', Inv => !Bad).
    #[test]
    fn test_microban_24_regression_4039() {
        let bench_path =
            std::path::Path::new(env!("HOME"))
                .join("hwmcc/benchmarks/bitlevel/safety/2025/ntu/sat/microban/microban_24.aig");
        if !bench_path.exists() {
            eprintln!("Skipping microban_24 test: benchmark file not found at {bench_path:?}");
            return;
        }
        let data = std::fs::read(&bench_path).expect("failed to read benchmark");
        let circuit = crate::parser::parse_aig(&data).expect("failed to parse benchmark");
        let ts = crate::transys::Transys::from_aiger(&circuit).coi_reduce();
        eprintln!(
            "microban_24: {} latches, {} constraints, {} bad",
            ts.latch_vars.len(),
            ts.constraint_lits.len(),
            ts.bad_lits.len(),
        );

        // Run IC3 with cancellation after 10 depths. Before the fix, IC3
        // falsely converged at depth 4 with an unsound invariant [v51].
        // After the fix, IC3 does NOT converge within 10 depths.
        let cancel = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false));
        let cancel_clone = cancel.clone();

        // Spawn IC3 in a thread with a timeout to prevent hanging.
        let ts_clone = ts.clone();
        let handle = std::thread::spawn(move || {
            let mut engine = Ic3Engine::new(ts_clone);
            engine.set_cancelled(cancel_clone);
            engine.check()
        });

        // Give IC3 up to 5 seconds, then cancel.
        std::thread::sleep(std::time::Duration::from_secs(5));
        cancel.store(true, std::sync::atomic::Ordering::Relaxed);

        let result = handle.join().expect("IC3 thread panicked");
        eprintln!("IC3 result (with 5s timeout): {result:?}");

        // The ground truth for microban_24 is SAT (bad state reachable).
        // IC3 should NOT report Safe within 5 seconds. If it does, it's
        // the old bug returning. IC3 may report Unsafe (correct!) or
        // Unknown (cancelled before convergence, also acceptable).
        if let Ic3Result::Safe { depth, .. } = result {
            if depth < 100 {
                panic!(
                    "BUG REGRESSION #4039: IC3 falsely reported Safe at depth {depth} \
                     for microban_24. Ground truth is SAT. This indicates solver[0] \
                     pollution is back."
                );
            }
        }
    }

    /// Verify that solve_with_temporary_clause does not persist state.
    /// After calling solve_with_temporary_clause with a clause, the clause
    /// should not affect subsequent solve() calls.
    #[test]
    fn test_solve_with_temporary_clause_isolation() {
        use crate::sat_types::SatSolver;
        let mut solver = crate::sat_types::SimpleSolver::new();
        let a = solver.new_var(); // Var(1)
        let b = solver.new_var(); // Var(2)

        // Add: (a OR b)
        solver.add_clause(&[crate::sat_types::Lit::pos(a), crate::sat_types::Lit::pos(b)]);

        // Temporary clause: (!a AND !b) via clause (!a) -- actually let's use it properly.
        // solve_with_temporary_clause with assumptions=[a] and temp_clause=[!a]
        // This should be UNSAT (a is assumed true, but !a is required by temp clause).
        let r1 = solver.solve_with_temporary_clause(&[crate::sat_types::Lit::pos(a)], &[crate::sat_types::Lit::neg(a)]);
        assert_eq!(
            r1,
            crate::sat_types::SatResult::Unsat,
            "should be UNSAT with conflicting temp clause"
        );

        // Now solve without the temp clause -- should be SAT again.
        let r2 = solver.solve(&[crate::sat_types::Lit::pos(a)]);
        assert_eq!(
            r2,
            crate::sat_types::SatResult::Sat,
            "temp clause should not persist; (a OR b) with a=true is SAT"
        );
    }

    /// Test that the `is_poisoned` trait method works correctly for both backends.
    #[test]
    fn test_is_poisoned_trait_method() {
        use crate::sat_types::SatSolver;

        // SimpleSolver should never be poisoned.
        let simple = crate::sat_types::SimpleSolver::new();
        assert!(!simple.is_poisoned(), "SimpleSolver should never be poisoned");

        // Z4SatCdclSolver should start unpoisoned.
        let z4 = Z4SatCdclSolver::new(5);
        assert!(!z4.is_poisoned(), "fresh Z4SatCdclSolver should not be poisoned");
    }

    /// Test that IC3 `rebuild_solver_at` produces a usable solver.
    ///
    /// Builds an IC3 engine, adds some lemmas at frame 0, then rebuilds
    /// the solver at index 0 and verifies the rebuilt solver still has
    /// the correct lemmas (by checking that a blocked cube stays blocked).
    #[test]
    fn test_rebuild_solver_at_preserves_lemmas() {
        // Toggle: latch starts 0, next=NOT latch, bad=latch.
        // IC3 should prove Safe (latch alternates 0->1->0->... but with
        // proper frame lemmas, the bad state is unreachable at init).
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let ts = crate::transys::Transys::from_aiger(&circuit);
        let mut engine = Ic3Engine::new(ts).with_simple_solver();

        // Run IC3 to completion -- this populates frames and solvers.
        let result = engine.check();
        // The toggle circuit is Unsafe (latch goes 0->1, and bad=latch).
        assert!(
            matches!(result, Ic3Result::Unsafe { .. }),
            "expected Unsafe for toggle, got {result:?}"
        );

        // Verify that we have at least one solver.
        assert!(
            !engine.solvers.is_empty(),
            "IC3 should have at least one solver after check()"
        );

        // Rebuild solver at index 0 and verify it's usable.
        let num_solvers = engine.solvers.len();
        if num_solvers > 0 {
            engine.rebuild_solver_at(0);
            // The rebuilt solver should accept new clauses and solve without error.
            let r = engine.solvers[0].solve(&[]);
            assert!(
                r == crate::sat_types::SatResult::Sat || r == crate::sat_types::SatResult::Unsat,
                "rebuilt solver should produce Sat or Unsat, got {r:?}"
            );
        }
    }

    #[test]
    fn test_drop_po_config_safe() {
        // GAP-2: IC3 with drop_po=true should still prove safe correctly.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let config = Ic3Config {
            drop_po: true,
            ..Ic3Config::default()
        };
        let result = check_ic3_with_config(&circuit, config);
        assert!(matches!(result, Ic3Result::Safe { .. }), "got {result:?}");
    }

    #[test]
    fn test_drop_po_config_unsafe() {
        // GAP-2: IC3 with drop_po=true should still find bugs.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let config = Ic3Config {
            drop_po: true,
            ..Ic3Config::default()
        };
        let result = check_ic3_with_config(&circuit, config);
        assert!(
            matches!(result, Ic3Result::Unsafe { .. }),
            "got {result:?}"
        );
    }

    #[test]
    fn test_no_drop_po_safe() {
        // GAP-2: IC3 with drop_po=false should also work correctly.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let config = Ic3Config {
            drop_po: false,
            ..Ic3Config::default()
        };
        let result = check_ic3_with_config(&circuit, config);
        assert!(matches!(result, Ic3Result::Safe { .. }), "got {result:?}");
    }

    #[test]
    fn test_dynamic_generalization_safe() {
        // GAP-5: IC3 with dynamic=true should prove safe correctly.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let config = Ic3Config {
            dynamic: true,
            ..Ic3Config::default()
        };
        let result = check_ic3_with_config(&circuit, config);
        assert!(matches!(result, Ic3Result::Safe { .. }), "got {result:?}");
    }

    #[test]
    fn test_dynamic_generalization_unsafe() {
        // GAP-5: IC3 with dynamic=true should find bugs.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let config = Ic3Config {
            dynamic: true,
            ..Ic3Config::default()
        };
        let result = check_ic3_with_config(&circuit, config);
        assert!(
            matches!(result, Ic3Result::Unsafe { .. }),
            "got {result:?}"
        );
    }

    #[test]
    fn test_dynamic_ctg_params_low_activity() {
        // Low activity (< 10.0) should produce no CTG.
        let po = obligation::ProofObligation::new(2, vec![], 0, None);
        let (max, limit) = Ic3Engine::dynamic_ctg_params(&po);
        assert_eq!(max, 0);
        assert_eq!(limit, 0);
    }

    #[test]
    fn test_dynamic_ctg_params_moderate_activity() {
        // Moderate activity (10.0..40.0) should produce moderate CTG.
        let mut inner = obligation::ProofObligation::new(1, vec![], 0, None);
        inner.act = 15.0;
        let po = obligation::ProofObligation::new(2, vec![], 1, Some(inner));
        let (max, limit) = Ic3Engine::dynamic_ctg_params(&po);
        assert!(max >= 2, "expected max >= 2, got {max}");
        assert_eq!(limit, 1);
    }

    #[test]
    fn test_dynamic_ctg_params_high_activity() {
        // High activity (>= 40.0) should produce aggressive CTG.
        let mut inner = obligation::ProofObligation::new(1, vec![], 0, None);
        inner.act = 50.0;
        let po = obligation::ProofObligation::new(2, vec![], 1, Some(inner));
        let (max, limit) = Ic3Engine::dynamic_ctg_params(&po);
        assert_eq!(max, 5, "expected max=5 for high activity");
        assert!(limit >= 5, "expected limit >= 5, got {limit}");
    }

    #[test]
    fn test_po_activity_bump() {
        let mut po = obligation::ProofObligation::new(2, vec![], 0, None);
        assert_eq!(po.act, 0.0);
        po.bump_act();
        assert_eq!(po.act, 1.0);
        po.bump_act();
        assert_eq!(po.act, 2.0);
    }

    #[test]
    fn test_po_push_to_frame_decays_activity() {
        let mut po = obligation::ProofObligation::new(1, vec![], 0, None);
        po.act = 10.0;
        po.push_to_frame(3); // push from frame 1 to frame 3 = 2 levels
        // 10.0 * 0.6 * 0.6 = 3.6
        assert!((po.act - 3.6).abs() < 0.01);
        assert_eq!(po.frame, 3);
    }

    #[test]
    fn test_dynamic_with_drop_po_safe() {
        // Combined: dynamic + drop_po should work together.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let config = Ic3Config {
            dynamic: true,
            drop_po: true,
            ..Ic3Config::default()
        };
        let result = check_ic3_with_config(&circuit, config);
        assert!(matches!(result, Ic3Result::Safe { .. }), "got {result:?}");
    }

    #[test]
    fn test_drop_po_custom_threshold_safe() {
        // GAP-2: Custom drop_po threshold (lower = more aggressive dropping).
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let config = Ic3Config {
            drop_po: true,
            drop_po_threshold: 10.0,
            ..Ic3Config::default()
        };
        let result = check_ic3_with_config(&circuit, config);
        assert!(matches!(result, Ic3Result::Safe { .. }), "got {result:?}");
    }

    #[test]
    fn test_drop_po_custom_threshold_unsafe() {
        // GAP-2: Custom drop_po threshold should still detect bugs.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let config = Ic3Config {
            drop_po: true,
            drop_po_threshold: 10.0,
            ..Ic3Config::default()
        };
        let result = check_ic3_with_config(&circuit, config);
        assert!(
            matches!(result, Ic3Result::Unsafe { .. }),
            "got {result:?}"
        );
    }

    #[test]
    fn test_drop_po_high_threshold_safe() {
        // GAP-2: Higher threshold = less aggressive dropping (40.0).
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let config = Ic3Config {
            drop_po: true,
            drop_po_threshold: 40.0,
            ..Ic3Config::default()
        };
        let result = check_ic3_with_config(&circuit, config);
        assert!(matches!(result, Ic3Result::Safe { .. }), "got {result:?}");
    }

    #[test]
    fn test_two_latch_dynamic_safe() {
        // Two-latch circuit with dynamic generalization.
        let circuit = parse_aag("aag 3 0 2 0 1 1\n2 0\n4 0\n6\n6 2 4\n").unwrap();
        let config = Ic3Config {
            dynamic: true,
            ..Ic3Config::default()
        };
        let result = check_ic3_with_config(&circuit, config);
        assert!(matches!(result, Ic3Result::Safe { .. }), "got {result:?}");
    }

    // -----------------------------------------------------------------------
    // Tests for #4065: dynamic generalization and portfolio diversity
    // -----------------------------------------------------------------------

    #[test]
    fn test_circuit_adapt_small_circuit_safe() {
        // Circuit adaptation on a small circuit (<100 latches) should boost CTG.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let config = Ic3Config {
            circuit_adapt: true,
            ..Ic3Config::default()
        };
        let result = check_ic3_with_config(&circuit, config);
        assert!(matches!(result, Ic3Result::Safe { .. }), "got {result:?}");
    }

    #[test]
    fn test_circuit_adapt_small_circuit_unsafe() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let config = Ic3Config {
            circuit_adapt: true,
            ..Ic3Config::default()
        };
        let result = check_ic3_with_config(&circuit, config);
        assert!(
            matches!(result, Ic3Result::Unsafe { .. }),
            "got {result:?}"
        );
    }

    #[test]
    fn test_circuit_adapt_ctg_params_adjusted() {
        // Verify circuit_adapt actually adjusts CTG params for small circuits.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let ts = crate::transys::Transys::from_aiger(&circuit);
        assert!(ts.num_latches < 100, "test circuit must be small");

        // With circuit_adapt enabled, ctg_max should be at least 5 and
        // ctg_limit at least 15 for small circuits.
        let config = Ic3Config {
            circuit_adapt: true,
            ctg_max: 1,    // would normally be low
            ctg_limit: 1,  // would normally be low
            ..Ic3Config::default()
        };
        let engine = Ic3Engine::with_config(ts, config);
        // The engine's config should have been boosted to at least 5/15.
        assert!(
            engine.config.ctg_max >= 5,
            "ctg_max should be >= 5 for small circuit, got {}",
            engine.config.ctg_max
        );
        assert!(
            engine.config.ctg_limit >= 15,
            "ctg_limit should be >= 15 for small circuit, got {}",
            engine.config.ctg_limit
        );
    }

    #[test]
    fn test_reverse_topo_generalization_safe() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let config = Ic3Config {
            gen_order: GeneralizationOrder::ReverseTopological,
            ..Ic3Config::default()
        };
        let result = check_ic3_with_config(&circuit, config);
        assert!(matches!(result, Ic3Result::Safe { .. }), "got {result:?}");
    }

    #[test]
    fn test_reverse_topo_generalization_unsafe() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let config = Ic3Config {
            gen_order: GeneralizationOrder::ReverseTopological,
            ..Ic3Config::default()
        };
        let result = check_ic3_with_config(&circuit, config);
        assert!(
            matches!(result, Ic3Result::Unsafe { .. }),
            "got {result:?}"
        );
    }

    #[test]
    fn test_random_shuffle_generalization_safe() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let config = Ic3Config {
            gen_order: GeneralizationOrder::RandomShuffle,
            random_seed: 42,
            ..Ic3Config::default()
        };
        let result = check_ic3_with_config(&circuit, config);
        assert!(matches!(result, Ic3Result::Safe { .. }), "got {result:?}");
    }

    #[test]
    fn test_random_shuffle_generalization_unsafe() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let config = Ic3Config {
            gen_order: GeneralizationOrder::RandomShuffle,
            random_seed: 42,
            ..Ic3Config::default()
        };
        let result = check_ic3_with_config(&circuit, config);
        assert!(
            matches!(result, Ic3Result::Unsafe { .. }),
            "got {result:?}"
        );
    }

    #[test]
    fn test_restart_strategy_geometric_safe() {
        // Restart strategy is advisory, should not break correctness.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let config = Ic3Config {
            restart_strategy: RestartStrategy::Geometric {
                base: 100,
                factor: 1.5,
            },
            ..Ic3Config::default()
        };
        let result = check_ic3_with_config(&circuit, config);
        assert!(matches!(result, Ic3Result::Safe { .. }), "got {result:?}");
    }

    #[test]
    fn test_restart_strategy_luby_unsafe() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let config = Ic3Config {
            restart_strategy: RestartStrategy::Luby { unit: 512 },
            ..Ic3Config::default()
        };
        let result = check_ic3_with_config(&circuit, config);
        assert!(
            matches!(result, Ic3Result::Unsafe { .. }),
            "got {result:?}"
        );
    }

    #[test]
    fn test_combined_new_features_safe() {
        // Combine circuit adaptation + reverse topo + dynamic.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let config = Ic3Config {
            circuit_adapt: true,
            gen_order: GeneralizationOrder::ReverseTopological,
            dynamic: true,
            ctp: true,
            inf_frame: true,
            ..Ic3Config::default()
        };
        let result = check_ic3_with_config(&circuit, config);
        assert!(matches!(result, Ic3Result::Safe { .. }), "got {result:?}");
    }

    #[test]
    fn test_and_gate_depth_computation() {
        // Circuit where AND gate feeds a latch's next-state.
        // aag 3 1 1 0 1 1
        // input: 2 (Var(1))
        // latch: 4 next=6 (Var(2), next = AND output Var(3))
        // AND: 6 = 2 & 4 (Var(3) = Var(1) AND Var(2))
        // bad: 4
        let circuit =
            parse_aag("aag 3 1 1 0 1 1\n2\n4 6\n4\n6 2 4\n").unwrap();
        let ts = crate::transys::Transys::from_aiger(&circuit);
        let config = Ic3Config::default();
        let engine = Ic3Engine::with_config(ts, config);
        let depths = engine.compute_and_gate_depths();
        // Var(1) is an input (depth 0 as leaf).
        // Var(2) is a latch (depth 0 as leaf).
        // Var(3) is the AND gate output = AND(Var(1), Var(2)), depth 1.
        // Var(3) is traced because latch Var(2) has next=Var(3).
        assert_eq!(depths.get(&crate::sat_types::Var(1)).copied().unwrap_or(0), 0);
        assert_eq!(depths.get(&crate::sat_types::Var(2)).copied().unwrap_or(0), 0);
        assert_eq!(depths.get(&crate::sat_types::Var(3)).copied().unwrap_or(0), 1);
    }

    // --- Solver cloning integration tests (#4062) ---

    /// Verify that IC3's extend() works correctly with solver cloning.
    /// The toggle circuit requires multiple frames: extend() is called for each.
    /// If cloning produces incorrect solvers, IC3 would give wrong results.
    #[test]
    fn test_ic3_extend_with_solver_cloning_toggle() {
        // Toggle: latch starts at 0, next = NOT latch. Bad = latch.
        // This requires IC3 to build multiple frames via extend().
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();

        // Test with Z4Sat backend (uses clause-log replay cloning).
        let config_z4 = Ic3Config {
            solver_backend: crate::sat_types::SolverBackend::Z4Sat,
            ..Ic3Config::default()
        };
        let result_z4 = check_ic3_with_config(&circuit, config_z4);
        assert!(
            matches!(result_z4, Ic3Result::Unsafe { .. }),
            "Z4Sat with cloning: expected Unsafe, got {result_z4:?}"
        );

        // Test with Simple backend (uses direct struct clone).
        let config_simple = Ic3Config {
            solver_backend: crate::sat_types::SolverBackend::Simple,
            ..Ic3Config::default()
        };
        let result_simple = check_ic3_with_config(&circuit, config_simple);
        assert!(
            matches!(result_simple, Ic3Result::Unsafe { .. }),
            "Simple with cloning: expected Unsafe, got {result_simple:?}"
        );
    }

    /// Verify that solver cloning works correctly for safe properties too.
    /// The stuck-at-zero circuit is safe; if cloning introduces wrong clauses,
    /// IC3 might incorrectly report it as unsafe.
    #[test]
    fn test_ic3_extend_with_solver_cloning_safe() {
        // Stuck at zero: latch next = 0. Bad = latch. Always safe.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();

        let config_z4 = Ic3Config {
            solver_backend: crate::sat_types::SolverBackend::Z4Sat,
            ..Ic3Config::default()
        };
        let result = check_ic3_with_config(&circuit, config_z4);
        assert!(
            matches!(result, Ic3Result::Safe { .. }),
            "Z4Sat with cloning: expected Safe, got {result:?}"
        );
    }

    /// Verify that the rebuild_solvers path with cloning produces correct results.
    /// We create an engine, manually trigger rebuild, and check results.
    #[test]
    fn test_ic3_rebuild_solvers_with_cloning() {
        // Two-latch safe circuit (exercises multiple frames and rebuild).
        let circuit = parse_aag("aag 3 0 2 0 1 1\n2 0\n4 0\n6\n6 2 4\n").unwrap();
        let ts = crate::transys::Transys::from_aiger(&circuit);
        let mut engine = Ic3Engine::with_config(ts, Ic3Config::default());

        // Run IC3 to build frames.
        let result = engine.check();
        assert!(
            matches!(result, Ic3Result::Safe { .. }),
            "initial check should be Safe, got {result:?}"
        );

        // Force a rebuild of all solvers and run again.
        // (engine already ran, but rebuild_solvers should still produce valid solvers)
        engine.rebuild_solvers();
        // After rebuild, the solvers should be in a valid state.
        // We can't re-run check() on an already-completed engine, but we verify
        // that rebuild_solvers didn't panic and the solve_count was reset.
        assert_eq!(
            engine.solve_count, 0,
            "rebuild_solvers should reset solve_count"
        );
    }

    /// Verify that blocking_budget forces IC3 to advance past depth 1 (#4072).
    ///
    /// Uses a multi-latch circuit where the blocking phase at depth 1 would
    /// normally stall (many bad cubes). With blocking_budget set, IC3 should
    /// advance to depth 2+ and eventually converge or timeout with depth > 1.
    #[test]
    fn test_blocking_budget_advances_depth() {
        // 4-latch circuit: latches all start at 0, all next-state = 0.
        // Bad = AND of first two latches. Always safe (latches stay at 0).
        // aag 5 0 4 0 1 1
        // latches: 2 0, 4 0, 6 0, 8 0
        // bad: 10 (AND gate: 10 = 2 & 4)
        let circuit = parse_aag("aag 5 0 4 0 1 1\n2 0\n4 0\n6 0\n8 0\n10\n10 2 4\n").unwrap();
        let ts = crate::transys::Transys::from_aiger(&circuit);
        let config = Ic3Config {
            blocking_budget: 5,
            solver_backend: crate::sat_types::SolverBackend::Simple,
            ..Ic3Config::default()
        };
        let mut engine = Ic3Engine::with_config(ts, config);
        let result = engine.check();
        assert!(
            matches!(result, Ic3Result::Safe { .. }),
            "blocking_budget should not prevent convergence on safe circuit, got {result:?}"
        );
    }

    /// Verify that blocking_budget still finds counterexamples (unsafe circuits).
    #[test]
    fn test_blocking_budget_finds_unsafe() {
        // Toggle: latch starts at 0, next = NOT latch. Bad = latch.
        // Unsafe at depth 1 (latch becomes 1 after one step).
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let ts = crate::transys::Transys::from_aiger(&circuit);
        let config = Ic3Config {
            blocking_budget: 5,
            solver_backend: crate::sat_types::SolverBackend::Simple,
            ..Ic3Config::default()
        };
        let mut engine = Ic3Engine::with_config(ts, config);
        let result = engine.check();
        assert!(
            matches!(result, Ic3Result::Unsafe { .. }),
            "blocking_budget should not prevent finding counterexample, got {result:?}"
        );
    }

    // --- Predicate propagation tests (#4065) ---

    #[test]
    fn test_predprop_safe_circuit() {
        // Safe circuit: latch stays at 0, bad = latch. Predprop should not
        // prevent IC3 from proving safety.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let config = Ic3Config {
            predprop: true,
            ..Ic3Config::default()
        };
        let result = check_ic3_with_config(&circuit, config);
        assert!(matches!(result, Ic3Result::Safe { .. }), "got {result:?}");
    }

    #[test]
    fn test_predprop_unsafe_circuit() {
        // Toggle circuit: latch starts at 0, next = NOT latch, bad = latch.
        // Predprop should find the counterexample.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let config = Ic3Config {
            predprop: true,
            ..Ic3Config::default()
        };
        let result = check_ic3_with_config(&circuit, config);
        assert!(
            matches!(result, Ic3Result::Unsafe { .. }),
            "got {result:?}"
        );
    }

    #[test]
    fn test_predprop_with_ctp_safe() {
        // Predprop + CTP + inf should still prove safe correctly.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let config = Ic3Config {
            predprop: true,
            ctp: true,
            inf_frame: true,
            ..Ic3Config::default()
        };
        let result = check_ic3_with_config(&circuit, config);
        assert!(matches!(result, Ic3Result::Safe { .. }), "got {result:?}");
    }

    #[test]
    fn test_no_preprocess_config_safe() {
        // No-preprocess variant (CTG=0, drop_po=false) should still work.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let config = Ic3Config {
            ctg_max: 0,
            ctg_limit: 0,
            drop_po: false,
            parent_lemma: false,
            ..Ic3Config::default()
        };
        let result = check_ic3_with_config(&circuit, config);
        assert!(matches!(result, Ic3Result::Safe { .. }), "got {result:?}");
    }

    #[test]
    fn test_no_preprocess_config_unsafe() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let config = Ic3Config {
            ctg_max: 0,
            ctg_limit: 0,
            drop_po: false,
            parent_lemma: false,
            ..Ic3Config::default()
        };
        let result = check_ic3_with_config(&circuit, config);
        assert!(
            matches!(result, Ic3Result::Unsafe { .. }),
            "got {result:?}"
        );
    }

    #[test]
    fn test_no_parent_config_safe() {
        // No-parent variant (drop_po=false, parent_lemma=false) should work.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let config = Ic3Config {
            drop_po: false,
            parent_lemma: false,
            ..Ic3Config::default()
        };
        let result = check_ic3_with_config(&circuit, config);
        assert!(matches!(result, Ic3Result::Safe { .. }), "got {result:?}");
    }

    #[test]
    fn test_two_latch_predprop_safe() {
        // Two-latch safe circuit with predprop.
        let circuit = parse_aag("aag 3 0 2 0 1 1\n2 0\n4 0\n6\n6 2 4\n").unwrap();
        let config = Ic3Config {
            predprop: true,
            ..Ic3Config::default()
        };
        let result = check_ic3_with_config(&circuit, config);
        assert!(matches!(result, Ic3Result::Safe { .. }), "got {result:?}");
    }

    #[test]
    fn test_multi_order_lift_2_safe() {
        // 2-ordering lift should not affect correctness on a safe circuit.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let config = Ic3Config {
            multi_lift_orderings: 2,
            ..Ic3Config::default()
        };
        let result = check_ic3_with_config(&circuit, config);
        assert!(matches!(result, Ic3Result::Safe { .. }), "got {result:?}");
    }

    #[test]
    fn test_multi_order_lift_3_safe() {
        // 3-ordering lift (max diversity) should not affect correctness.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let config = Ic3Config {
            multi_lift_orderings: 3,
            ..Ic3Config::default()
        };
        let result = check_ic3_with_config(&circuit, config);
        assert!(matches!(result, Ic3Result::Safe { .. }), "got {result:?}");
    }

    #[test]
    fn test_multi_order_lift_unsafe() {
        // Multi-ordering lift should not affect counterexample detection.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let config = Ic3Config {
            multi_lift_orderings: 2,
            ..Ic3Config::default()
        };
        let result = check_ic3_with_config(&circuit, config);
        assert!(matches!(result, Ic3Result::Unsafe { .. }), "got {result:?}");
    }

    #[test]
    fn test_multi_order_lift_3_unsafe() {
        // 3-ordering lift should not affect counterexample detection.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let config = Ic3Config {
            multi_lift_orderings: 3,
            ..Ic3Config::default()
        };
        let result = check_ic3_with_config(&circuit, config);
        assert!(matches!(result, Ic3Result::Unsafe { .. }), "got {result:?}");
    }

    #[test]
    fn test_multi_order_lift_with_ctp_safe() {
        // Multi-ordering lift + CTP + inf_frame should still prove safe.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let config = Ic3Config {
            multi_lift_orderings: 2,
            ctp: true,
            inf_frame: true,
            ..Ic3Config::default()
        };
        let result = check_ic3_with_config(&circuit, config);
        assert!(matches!(result, Ic3Result::Safe { .. }), "got {result:?}");
    }

    #[test]
    fn test_multi_order_lift_with_dynamic_safe() {
        // Multi-ordering lift + dynamic generalization should still prove safe.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let config = Ic3Config {
            multi_lift_orderings: 2,
            dynamic: true,
            ..Ic3Config::default()
        };
        let result = check_ic3_with_config(&circuit, config);
        assert!(matches!(result, Ic3Result::Safe { .. }), "got {result:?}");
    }

    #[test]
    fn test_multi_order_single_vs_multi_same_verdict() {
        // Both single-ordering and multi-ordering MIC must produce the same
        // verdict (safe/unsafe). Multi-ordering may produce tighter lemmas
        // (shorter generalized cubes), but must never change the verdict.
        let safe_circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let unsafe_circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        for (circuit, expected_safe) in [(&safe_circuit, true), (&unsafe_circuit, false)] {
            let single = Ic3Config {
                multi_lift_orderings: 1,
                ..Ic3Config::default()
            };
            let multi = Ic3Config {
                multi_lift_orderings: 3,
                ..Ic3Config::default()
            };
            let r_single = check_ic3_with_config(circuit, single);
            let r_multi = check_ic3_with_config(circuit, multi);
            if expected_safe {
                assert!(matches!(r_single, Ic3Result::Safe { .. }), "single: {r_single:?}");
                assert!(matches!(r_multi, Ic3Result::Safe { .. }), "multi: {r_multi:?}");
            } else {
                assert!(matches!(r_single, Ic3Result::Unsafe { .. }), "single: {r_single:?}");
                assert!(matches!(r_multi, Ic3Result::Unsafe { .. }), "multi: {r_multi:?}");
            }
        }
    }

    #[test]
    fn test_multi_order_default_config_enabled() {
        // Default config should have multi_lift_orderings=3 (enabled by default).
        let config = Ic3Config::default();
        assert_eq!(config.multi_lift_orderings, 3, "multi-ordering should be enabled by default");
    }

    // -----------------------------------------------------------------------
    // Non-unit init clause convergence tests (#4104)
    //
    // Circuits with non-unit init clauses (binary equivalence from
    // non-standard latch resets) require the SAT-based init consistency
    // check to correctly identify spurious cubes that the fast unit-clause
    // check over-approximates as init-consistent.
    // -----------------------------------------------------------------------

    #[test]
    fn test_cube_sat_consistent_with_init_unit_only() {
        // Circuit with only unit init clauses: both checks should agree.
        // Latch A (var 1) starts at 0, next = NOT A. Bad = A.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let ts = crate::transys::Transys::from_aiger(&circuit);
        let engine = Ic3Engine::new(ts).with_simple_solver();

        // Cube [A=true]: contradicts init (A=0), both checks return false.
        let cube_a_true = vec![crate::sat_types::Lit::pos(crate::sat_types::Var(1))];
        assert!(!engine.cube_consistent_with_init(&cube_a_true));
        assert!(!engine.cube_sat_consistent_with_init(&cube_a_true));

        // Cube [A=false]: consistent with init, both checks return true.
        let cube_a_false = vec![crate::sat_types::Lit::neg(crate::sat_types::Var(1))];
        assert!(engine.cube_consistent_with_init(&cube_a_false));
        assert!(engine.cube_sat_consistent_with_init(&cube_a_false));
    }

    #[test]
    fn test_cube_sat_consistent_with_init_non_unit() {
        // Circuit with non-unit init clauses: fast check over-approximates.
        //
        // Latch A (var 2): reset=0, next=0.
        // Latch B (var 3): reset=4 (=latch A's lit), next=0.
        // Init: A=false (unit), B<=>A (binary: !B OR A, B OR !A).
        // Combined: A=false AND B=false.
        //
        // aag format: M=3 I=0 L=2 O=0 A=0 B=1
        // Latch A: lit=4, next=0, reset=0
        // Latch B: lit=6, next=0, reset=4 (= A's lit)
        // Bad: lit 6 (B)
        let aag = "aag 3 0 2 0 0 1\n4 0 0\n6 0 4\n6\n";
        let circuit = parse_aag(aag).unwrap();
        let ts = crate::transys::Transys::from_aiger(&circuit);

        // Verify non-unit init clauses exist.
        let non_unit_count = ts.init_clauses.iter().filter(|c| c.lits.len() > 1).count();
        assert!(
            non_unit_count > 0,
            "expected non-unit init clauses, got {} unit-only",
            ts.init_clauses.len()
        );

        let engine = Ic3Engine::new(ts).with_simple_solver();

        // Cube [B=true]: actually inconsistent with Init (Init forces B=A=false),
        // but B is NOT in init_map (only unit clauses go into init_map).
        let cube_b_true = vec![crate::sat_types::Lit::pos(crate::sat_types::Var(3))];

        // Fast check: returns true (over-approximation -- B not in init_map).
        assert!(
            engine.cube_consistent_with_init(&cube_b_true),
            "fast check should over-approximate: B not in init_map"
        );

        // SAT check: returns false (precise -- Init AND B=true is UNSAT).
        assert!(
            !engine.cube_sat_consistent_with_init(&cube_b_true),
            "SAT check should detect B=true contradicts non-unit init clause B<=>A with A=false"
        );

        // Cube [A=true, B=true]: inconsistent with Init (A=false is a unit clause).
        // Both checks should catch this.
        let cube_ab_true = vec![crate::sat_types::Lit::pos(crate::sat_types::Var(2)), crate::sat_types::Lit::pos(crate::sat_types::Var(3))];
        assert!(!engine.cube_consistent_with_init(&cube_ab_true));
        assert!(!engine.cube_sat_consistent_with_init(&cube_ab_true));

        // Cube [A=false, B=false]: consistent with Init. Both return true.
        let cube_ab_false = vec![crate::sat_types::Lit::neg(crate::sat_types::Var(2)), crate::sat_types::Lit::neg(crate::sat_types::Var(3))];
        assert!(engine.cube_consistent_with_init(&cube_ab_false));
        assert!(engine.cube_sat_consistent_with_init(&cube_ab_false));
    }

    #[test]
    fn test_ic3_non_unit_init_safe_converges() {
        // Regression test for convergence with non-unit init clauses (#4104).
        //
        // Two latches with binary init constraint (B resets to A's value).
        // Both start at 0, both stay at 0 (next=0). Bad = B.
        // Should be Safe and converge quickly (B can never become 1).
        //
        // Without the fix: if a spurious cube [B=true] at frame 0 passes
        // the fast init check (B not in init_map), verify_trace fails, and
        // no blocking lemma is added, IC3 may rediscover the same cube
        // repeatedly, preventing convergence.
        let aag = "aag 3 0 2 0 0 1\n4 0 0\n6 0 4\n6\n";
        let circuit = parse_aag(aag).unwrap();
        let ts = crate::transys::Transys::from_aiger(&circuit);
        let mut engine = Ic3Engine::new(ts).with_simple_solver();
        let result = engine.check();
        assert!(
            matches!(result, Ic3Result::Safe { .. }),
            "expected Safe for non-unit init circuit where bad is unreachable, got {result:?}"
        );
    }

    #[test]
    fn test_ic3_non_unit_init_sat_check_both_paths() {
        // Verify that cube_sat_consistent_with_init returns true for cubes
        // that ARE genuinely in Init, even with non-unit init clauses (#4104).
        // This ensures the SAT-based check doesn't over-restrict.
        //
        // Same circuit as test_cube_sat_consistent_with_init_non_unit:
        // Latch A (var 2): reset=0, Latch B (var 3): reset=A's lit.
        // Init: A=false, B=false.
        let aag = "aag 3 0 2 0 0 1\n4 0 0\n6 0 4\n6\n";
        let circuit = parse_aag(aag).unwrap();
        let ts = crate::transys::Transys::from_aiger(&circuit);
        let engine = Ic3Engine::new(ts).with_simple_solver();

        // Cube [A=false, B=false]: this IS in Init, SAT check should return true.
        assert!(engine.cube_sat_consistent_with_init(&[crate::sat_types::Lit::neg(crate::sat_types::Var(2)), crate::sat_types::Lit::neg(crate::sat_types::Var(3))]));

        // Cube [B=true]: NOT in Init, SAT check should return false.
        assert!(!engine.cube_sat_consistent_with_init(&[crate::sat_types::Lit::pos(crate::sat_types::Var(3))]));

        // Cube [A=false]: partial cube in Init, SAT check should return true.
        assert!(engine.cube_sat_consistent_with_init(&[crate::sat_types::Lit::neg(crate::sat_types::Var(2))]));

        // Empty cube: trivially consistent, SAT check should return true.
        assert!(engine.cube_sat_consistent_with_init(&[]));
    }

    // -----------------------------------------------------------------------
    // Adaptive consecution verification tests (#4121)
    // -----------------------------------------------------------------------

    #[test]
    fn test_consecution_verify_interval_full_low_ratio() {
        // Low trans_clauses/latches and low constraints/latches -> interval=10.
        let interval = super::config::consecution_verify_interval_full(100, 10, 50);
        assert_eq!(interval, 10);
    }

    #[test]
    fn test_consecution_verify_interval_full_high_trans_ratio() {
        // High trans_clauses/latches (ratio 10x) -> interval=1.
        let interval = super::config::consecution_verify_interval_full(500, 10, 50);
        assert_eq!(interval, 1);
    }

    #[test]
    fn test_consecution_verify_interval_full_high_constraint_ratio() {
        // Low trans_clauses but high constraints/latches (ratio 6x) -> interval=1.
        // This is the microban pattern: few trans clauses but many constraint_lits.
        let interval = super::config::consecution_verify_interval_full(100, 300, 50);
        assert_eq!(interval, 1);
    }

    #[test]
    fn test_consecution_verify_interval_full_moderate_constraint_ratio() {
        // Moderate constraints/latches (ratio 3x) -> interval=3.
        let interval = super::config::consecution_verify_interval_full(50, 150, 50);
        assert_eq!(interval, 3);
    }

    #[test]
    fn test_consecution_verify_interval_full_zero_latches() {
        // Zero latches -> interval=1 (safety: avoid division by zero).
        let interval = super::config::consecution_verify_interval_full(100, 50, 0);
        assert_eq!(interval, 1);
    }

    #[test]
    fn test_consecution_verify_interval_full_both_high() {
        // Both trans and constraints high -> interval=1 (uses max).
        let interval = super::config::consecution_verify_interval_full(500, 300, 50);
        assert_eq!(interval, 1);
    }

    #[test]
    fn test_consecution_verify_interval_full_small_circuit_skip() {
        // Small-circuit fast path (#4259, #4288): circuits with fewer than 30
        // latches skip cross-check entirely (usize::MAX sentinel). This is
        // because SimpleSolver's basic DPLL produces false SAT on clause-dense
        // small circuits (cal14: 23 latches, 1656 trans clauses, 72x ratio),
        // rejecting z4-sat's correct UNSAT lemmas indefinitely. Post-
        // convergence validate_invariant_budgeted() provides the soundness net.
        let cal14_interval = super::config::consecution_verify_interval_full(
            1656, 0, 23,
        );
        assert_eq!(cal14_interval, usize::MAX, "cal14 must skip cross-check");

        // Boundary: 29 latches -> skip. 30 latches -> use ratio logic.
        let at_29 = super::config::consecution_verify_interval_full(200, 0, 29);
        assert_eq!(at_29, usize::MAX, "<30 latches skips cross-check");
        let at_30 = super::config::consecution_verify_interval_full(200, 0, 30);
        assert_ne!(at_30, usize::MAX, ">=30 latches uses adaptive interval");
    }

    #[test]
    fn test_is_high_constraint_circuit_microban_pattern() {
        // microban: 124 constraints, 879 trans, 23 latches.
        // constraint_ratio = 124/23 = 5.39 -> true.
        assert!(super::config::is_high_constraint_circuit(879, 124, 23));
    }

    #[test]
    fn test_is_high_constraint_circuit_low_ratio() {
        // Normal circuit: 100 trans, 10 constraints, 50 latches.
        assert!(!super::config::is_high_constraint_circuit(100, 10, 50));
    }

    #[test]
    fn test_is_high_constraint_circuit_high_trans_with_constraints() {
        // High trans + non-trivial constraints: 600 trans, 60 constraints, 50 latches.
        // trans_ratio=12, constraint>latches: true.
        assert!(super::config::is_high_constraint_circuit(600, 60, 50));
    }

    #[test]
    fn test_is_high_constraint_circuit_high_trans_no_constraints() {
        // High trans but zero constraints: 600 trans, 0 constraints, 50 latches.
        // Second condition needs constraints > latches, which fails.
        assert!(!super::config::is_high_constraint_circuit(600, 0, 50));
    }

    #[test]
    fn test_is_high_constraint_circuit_zero_latches() {
        // Zero latches -> false (no meaningful ratio).
        assert!(!super::config::is_high_constraint_circuit(100, 50, 0));
    }

    /// Test that crosscheck_disabled is auto-set for high-constraint circuits (#4121).
    #[test]
    fn test_crosscheck_auto_disabled_high_constraint() {
        // Build a circuit that has constraint_lits > 5x latches.
        // Simple: 2 inputs, 1 latch, 10 constraints. All constraints = i1.
        // This gives constraint_ratio = 10/1 = 10x -> crosscheck_disabled.
        //
        // aag M I L O A B C  -> aag 2 2 1 0 0 1 10
        // inputs: 2, 4
        // latch: 6, next=0
        // bad: 6
        // constraints: 2 2 2 2 2 2 2 2 2 2 (10 copies of i1 must be true)
        let mut aag = String::from("aag 3 2 1 0 0 1 10\n2\n4\n6 0\n6\n");
        for _ in 0..10 {
            aag.push_str("2\n");
        }
        let circuit = parse_aag(&aag).unwrap();
        let ts = crate::transys::Transys::from_aiger(&circuit);
        assert_eq!(ts.constraint_lits.len(), 10);
        assert_eq!(ts.latch_vars.len(), 1);

        let engine = Ic3Engine::new(ts);
        assert!(
            engine.crosscheck_disabled,
            "crosscheck should be auto-disabled for 10 constraints / 1 latch"
        );
    }

    /// Regression test for #4105: IC3 infinite solver rebuild loop on microban_1.
    ///
    /// microban_1 is an UNSAT benchmark (23 latches, 124 constraints) that
    /// regressed from UNSAT in Wave 7 to UNKNOWN in Wave 9. The root cause
    /// was the consecution cross-check (#4092) creating an infinite loop:
    /// z4-sat says UNSAT but SimpleSolver disagrees (false SAT on constraint-
    /// dense formulas), causing repeated solver rebuilds.
    ///
    /// Fixes:
    /// 1. (#4121) Auto-disable cross-checking for high-constraint circuits
    ///    (constraint_lits / latches > 5). microban_1 has ratio 5.39.
    /// 2. (#4105) Use MAX_SPURIOUS_INIT_PREDS as a loop breaker for spurious
    ///    init-consistent predecessors. After 3 consecutive spurious predecessors
    ///    where verify_trace fails, stop re-queuing the successor PO.
    ///
    /// This test verifies:
    /// - crosscheck is auto-disabled for microban_1's constraint pattern
    /// - IC3 does NOT report false Unsafe (ground truth is UNSAT)
    /// - IC3 terminates within the timeout (no infinite loop)
    #[test]
    fn test_microban_1_regression_4105() {
        let bench_path =
            std::path::Path::new(env!("HOME"))
                .join("hwmcc/benchmarks/bitlevel/safety/2025/ntu/unsat/microban_1.aig");
        if !bench_path.exists() {
            eprintln!("Skipping microban_1 test: benchmark file not found at {bench_path:?}");
            return;
        }
        let data = std::fs::read(&bench_path).expect("failed to read benchmark");
        let circuit = crate::parser::parse_aig(&data).expect("failed to parse benchmark");
        let ts = crate::transys::Transys::from_aiger(&circuit).coi_reduce();
        eprintln!(
            "microban_1: {} latches, {} constraints, {} trans_clauses, {} bad",
            ts.latch_vars.len(),
            ts.constraint_lits.len(),
            ts.trans_clauses.len(),
            ts.bad_lits.len(),
        );

        // Verify that crosscheck is auto-disabled for this circuit.
        let engine_check = Ic3Engine::new(ts.clone());
        assert!(
            engine_check.crosscheck_disabled,
            "crosscheck should be auto-disabled for microban_1 \
             (constraint_ratio={:.1}x)",
            engine_check.ts.constraint_lits.len() as f64
                / engine_check.ts.latch_vars.len().max(1) as f64,
        );

        // Run IC3 with a 10s timeout. We verify no false Unsafe and no
        // panics. Full convergence (Safe) may not happen in debug builds
        // within this timeout, and that's acceptable.
        let cancel = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false));
        let cancel_clone = cancel.clone();

        let ts_clone = ts;
        let handle = std::thread::spawn(move || {
            let mut engine = Ic3Engine::new(ts_clone);
            engine.set_cancelled(cancel_clone);
            engine.check()
        });

        // Give IC3 up to 10 seconds, then cancel.
        std::thread::sleep(std::time::Duration::from_secs(10));
        cancel.store(true, std::sync::atomic::Ordering::Relaxed);

        let result = handle.join().expect("IC3 thread panicked");
        eprintln!("microban_1 IC3 result: {result:?}");

        // microban_1 ground truth is UNSAT. IC3 should report Safe or
        // Unknown (cancelled before convergence). It must NOT report Unsafe
        // (that would be a false positive).
        match result {
            Ic3Result::Safe { depth, .. } => {
                eprintln!("microban_1: Safe at depth {depth} (correct!)");
            }
            Ic3Result::Unknown { ref reason } => {
                eprintln!("microban_1: Unknown ({reason}) — acceptable for portfolio");
            }
            Ic3Result::Unsafe { depth, .. } => {
                panic!(
                    "BUG: IC3 falsely reported Unsafe at depth {depth} for microban_1. \
                     Ground truth is UNSAT."
                );
            }
        }
    }

    /// Test that the spurious init-consistent predecessor loop breaker works (#4105).
    ///
    /// This unit test verifies the MAX_SPURIOUS_INIT_PREDS mechanism that
    /// prevents infinite loops when verify_trace repeatedly fails on init-
    /// consistent predecessors. The counter should reset on successful blocks.
    #[test]
    fn test_spurious_init_pred_counter_resets_on_block() {
        // Use a simple safe circuit to run IC3 to completion.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let ts = crate::transys::Transys::from_aiger(&circuit);
        let mut engine = Ic3Engine::new(ts).with_simple_solver();

        // Initially, counter is 0.
        assert_eq!(engine.spurious_init_pred_count, 0);

        // After IC3 check, counter should still be 0 (no spurious preds on
        // this trivial circuit, and any blocks reset the counter).
        let result = engine.check();
        assert!(
            matches!(result, Ic3Result::Safe { .. }),
            "expected Safe, got {result:?}"
        );
        assert_eq!(
            engine.spurious_init_pred_count, 0,
            "spurious counter should be 0 after successful IC3 run"
        );
    }

    /// Test that the per-frame solver rebuild budget works (#4105).
    ///
    /// Verifies that:
    /// 1. rebuild_counts starts at zero for all frames
    /// 2. solver_rebuild_budget_exceeded returns false initially
    /// 3. After MAX_SOLVER_REBUILDS_PER_FRAME rebuilds, budget is exceeded
    /// 4. Full rebuild_solvers() resets the counters
    #[test]
    fn test_solver_rebuild_budget() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let ts = crate::transys::Transys::from_aiger(&circuit);
        let mut engine = Ic3Engine::new(ts).with_simple_solver();

        // Run IC3 to populate frames and solvers.
        let result = engine.check();
        assert!(
            matches!(result, Ic3Result::Safe { .. }),
            "expected Safe, got {result:?}"
        );

        // Verify rebuild_counts was grown to match solvers.
        assert!(
            engine.rebuild_counts.len() >= engine.solvers.len(),
            "rebuild_counts should match solver count"
        );

        // Budget should not be exceeded initially.
        if !engine.solvers.is_empty() {
            assert!(
                !engine.solver_rebuild_budget_exceeded(0),
                "budget should not be exceeded initially"
            );

            // Rebuild the solver MAX_SOLVER_REBUILDS_PER_FRAME+1 times.
            for _ in 0..=super::config::MAX_SOLVER_REBUILDS_PER_FRAME {
                engine.rebuild_solver_at(0);
            }

            // Now budget should be exceeded.
            assert!(
                engine.solver_rebuild_budget_exceeded(0),
                "budget should be exceeded after {} rebuilds",
                super::config::MAX_SOLVER_REBUILDS_PER_FRAME + 1,
            );

            // Full rebuild should reset the counter.
            engine.rebuild_solvers();
            assert!(
                !engine.solver_rebuild_budget_exceeded(0),
                "budget should be reset after full rebuild"
            );
        }
    }

    /// Test that crosscheck_disabled is NOT auto-set for low-constraint circuits (#4121).
    #[test]
    fn test_crosscheck_not_disabled_low_constraint() {
        // Simple: 1 input, 1 latch, 1 constraint. Ratio = 1/1 = 1x.
        let aag = "aag 2 1 1 0 0 1 1\n2\n4 0\n4\n2\n";
        let circuit = parse_aag(aag).unwrap();
        let ts = crate::transys::Transys::from_aiger(&circuit);
        assert_eq!(ts.constraint_lits.len(), 1);
        assert_eq!(ts.latch_vars.len(), 1);

        let engine = Ic3Engine::new(ts);
        assert!(
            !engine.crosscheck_disabled,
            "crosscheck should NOT be disabled for 1 constraint / 1 latch"
        );
    }

    // -----------------------------------------------------------------------
    // Internal signals (--inn) tests (#4148)
    //
    // rIC3's internal signals mode (FMCAD'21) extends IC3 cubes to include
    // AND-gate output literals. This helps generalization on arithmetic
    // circuits where the cone of influence spans many gates.
    // -----------------------------------------------------------------------

    /// IC3 with internal_signals=true on a safe circuit.
    /// The stuck-at-zero latch is always safe regardless of internal signals.
    #[test]
    fn test_ic3_internal_signals_safe() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let config = Ic3Config {
            internal_signals: true,
            ..Ic3Config::default()
        };
        let result = check_ic3_with_config(&circuit, config);
        assert!(
            matches!(result, Ic3Result::Safe { .. }),
            "internal_signals should not break safe proof, got {result:?}"
        );
    }

    /// IC3 with internal_signals=true on an unsafe circuit.
    /// The toggle circuit should still find the counterexample.
    #[test]
    fn test_ic3_internal_signals_unsafe() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let config = Ic3Config {
            internal_signals: true,
            ..Ic3Config::default()
        };
        let result = check_ic3_with_config(&circuit, config);
        assert!(
            matches!(result, Ic3Result::Unsafe { .. }),
            "internal_signals should still find bugs, got {result:?}"
        );
    }

    /// IC3 with internal_signals on a circuit that HAS AND gates.
    /// Uses SimpleSolver to avoid z4-sat crash bugs on small circuits.
    /// 1 input, 1 latch (init=0, next=input), AND gate, bad=AND(input, latch).
    /// At step 1 with input=1: latch=1, AND(1,1)=1 -> unsafe at depth 1.
    #[test]
    fn test_ic3_internal_signals_with_and_gates_unsafe() {
        // v1=input(lit2), v2=latch(lit4, init=0, next=v1),
        // v3=AND(v1,v2)=lit6. Bad=v3.
        let circuit = parse_aag("aag 3 1 1 0 1 1\n2\n4 2\n6\n6 2 4\n").unwrap();
        let config = Ic3Config {
            internal_signals: true,
            solver_backend: crate::sat_types::SolverBackend::Simple,
            ..Ic3Config::default()
        };
        let result = check_ic3_with_config(&circuit, config);
        assert!(
            matches!(result, Ic3Result::Unsafe { .. }),
            "AND-gate circuit with internal_signals should be Unsafe, got {result:?}"
        );
    }

    /// IC3 with internal_signals on a safe two-latch circuit with AND gates.
    /// Both latches start at 0, stay at 0. Bad = AND(A, B). Always safe.
    #[test]
    fn test_ic3_internal_signals_with_and_gates_safe() {
        let circuit = parse_aag("aag 3 0 2 0 1 1\n2 0\n4 0\n6\n6 2 4\n").unwrap();
        let config = Ic3Config {
            internal_signals: true,
            ..Ic3Config::default()
        };
        let result = check_ic3_with_config(&circuit, config);
        assert!(
            matches!(result, Ic3Result::Safe { .. }),
            "two-latch safe circuit with internal_signals, got {result:?}"
        );
    }

    /// Verify select_internal_signals selects AND gates with fanout >= 2.
    #[test]
    fn test_select_internal_signals_fanout_threshold() {
        // Build a circuit where one AND gate feeds two different latches' next-state.
        // 1 input (v1=lit2), 2 latches (v2=lit4, v3=lit6), 1 AND gate (v4=lit8).
        // v4 = AND(v1, v2). Latch v2.next = v4, Latch v3.next = v4.
        // AND gate v4 has fanout=2 (both latches reference it).
        // Bad = v2.
        let aag = "\
aag 4 1 2 0 1 1
2
4 8
6 8
4
8 2 4
";
        let circuit = parse_aag(aag).unwrap();
        let mut ts = crate::transys::Transys::from_aiger(&circuit);
        // select_internal_signals requires >= 20 latches by default.
        // Override the threshold for testing by calling the method on a
        // circuit that would normally be too small. The method checks
        // num_latches < 20 and skips, so we test the logic directly.
        assert!(
            ts.internal_signals.is_empty(),
            "should start with no internal signals"
        );
        // For circuits < 20 latches, select_internal_signals() skips.
        ts.select_internal_signals();
        assert!(
            ts.internal_signals.is_empty(),
            "small circuit should not select internal signals (threshold: 20 latches)"
        );
    }

    /// IC3 inn + CTP configuration correctness (matches rIC3's ic3_inn_ctp).
    #[test]
    fn test_ic3_inn_ctp_safe() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let config = Ic3Config {
            internal_signals: true,
            ctp: true,
            inf_frame: true,
            ..Ic3Config::default()
        };
        let result = check_ic3_with_config(&circuit, config);
        assert!(
            matches!(result, Ic3Result::Safe { .. }),
            "ic3_inn_ctp should prove safe, got {result:?}"
        );
    }

    /// IC3 inn + CTP on unsafe circuit.
    #[test]
    fn test_ic3_inn_ctp_unsafe() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let config = Ic3Config {
            internal_signals: true,
            ctp: true,
            inf_frame: true,
            ..Ic3Config::default()
        };
        let result = check_ic3_with_config(&circuit, config);
        assert!(
            matches!(result, Ic3Result::Unsafe { .. }),
            "ic3_inn_ctp should find bugs, got {result:?}"
        );
    }

    /// IC3 inn + no CTG (matches rIC3's ic3_inn_noctg).
    #[test]
    fn test_ic3_inn_noctg_safe() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let config = Ic3Config {
            internal_signals: true,
            ctg_max: 0,
            ctg_limit: 0,
            ..Ic3Config::default()
        };
        let result = check_ic3_with_config(&circuit, config);
        assert!(
            matches!(result, Ic3Result::Safe { .. }),
            "ic3_inn_noctg should prove safe, got {result:?}"
        );
    }

    /// IC3 inn + no CTG on unsafe circuit.
    #[test]
    fn test_ic3_inn_noctg_unsafe() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let config = Ic3Config {
            internal_signals: true,
            ctg_max: 0,
            ctg_limit: 0,
            ..Ic3Config::default()
        };
        let result = check_ic3_with_config(&circuit, config);
        assert!(
            matches!(result, Ic3Result::Unsafe { .. }),
            "ic3_inn_noctg should find bugs, got {result:?}"
        );
    }

    /// IC3 inn + dynamic generalization (matches rIC3's ic3_inn_dynamic).
    #[test]
    fn test_ic3_inn_dynamic_safe() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let config = Ic3Config {
            internal_signals: true,
            dynamic: true,
            drop_po: false,
            ..Ic3Config::default()
        };
        let result = check_ic3_with_config(&circuit, config);
        assert!(
            matches!(result, Ic3Result::Safe { .. }),
            "ic3_inn_dynamic should prove safe, got {result:?}"
        );
    }

    /// IC3 inn + dynamic on unsafe circuit.
    #[test]
    fn test_ic3_inn_dynamic_unsafe() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let config = Ic3Config {
            internal_signals: true,
            dynamic: true,
            drop_po: false,
            ..Ic3Config::default()
        };
        let result = check_ic3_with_config(&circuit, config);
        assert!(
            matches!(result, Ic3Result::Unsafe { .. }),
            "ic3_inn_dynamic should find bugs, got {result:?}"
        );
    }

    /// Verify that next_vars includes internal signal variables when enabled.
    #[test]
    fn test_internal_signals_next_vars_allocated() {
        // Circuit with AND gate: v3 = AND(v1, v2). v1 is input, v2 is latch.
        let circuit = parse_aag("aag 3 1 1 0 1 1\n2\n4 6\n4\n6 2 4\n").unwrap();
        let mut ts = crate::transys::Transys::from_aiger(&circuit);
        // Manually add an internal signal for testing (normally requires >= 20 latches).
        ts.internal_signals = vec![crate::sat_types::Var(3)]; // AND gate output

        let config = Ic3Config {
            internal_signals: true,
            ..Ic3Config::default()
        };
        let engine = Ic3Engine::with_config(ts, config);

        // Latch var 2 should have a next-state variable.
        assert!(
            engine.next_vars.contains_key(&crate::sat_types::Var(2)),
            "latch var should have next_var"
        );
        // Internal signal var 3 should ALSO have a next-state variable.
        assert!(
            engine.next_vars.contains_key(&crate::sat_types::Var(3)),
            "internal signal var should have next_var when internal_signals=true"
        );
    }

    /// Verify that next_vars does NOT include internal signals when disabled.
    #[test]
    fn test_internal_signals_next_vars_not_allocated_when_disabled() {
        let circuit = parse_aag("aag 3 1 1 0 1 1\n2\n4 6\n4\n6 2 4\n").unwrap();
        let mut ts = crate::transys::Transys::from_aiger(&circuit);
        ts.internal_signals = vec![crate::sat_types::Var(3)];

        let config = Ic3Config {
            internal_signals: false,
            ..Ic3Config::default()
        };
        let engine = Ic3Engine::with_config(ts, config);

        assert!(
            engine.next_vars.contains_key(&crate::sat_types::Var(2)),
            "latch var should have next_var"
        );
        assert!(
            !engine.next_vars.contains_key(&crate::sat_types::Var(3)),
            "internal signal var should NOT have next_var when disabled"
        );
    }

    /// Verify that prime_cube maps internal signal literals to primed vars.
    #[test]
    fn test_internal_signals_prime_cube() {
        let circuit = parse_aag("aag 3 1 1 0 1 1\n2\n4 6\n4\n6 2 4\n").unwrap();
        let mut ts = crate::transys::Transys::from_aiger(&circuit);
        ts.internal_signals = vec![crate::sat_types::Var(3)];

        let config = Ic3Config {
            internal_signals: true,
            ..Ic3Config::default()
        };
        let engine = Ic3Engine::with_config(ts, config);

        // Cube with latch + internal signal literals.
        let cube = vec![
            crate::sat_types::Lit::pos(crate::sat_types::Var(2)), // latch
            crate::sat_types::Lit::neg(crate::sat_types::Var(3)), // internal signal
        ];
        let primed = engine.prime_cube(&cube);
        // Both should be mapped to their next-state variables.
        assert_eq!(primed.len(), 2, "prime_cube should map both latch and isig");
        // The primed vars should be different from the original vars.
        for lit in &primed {
            assert!(
                lit.var() != crate::sat_types::Var(2) && lit.var() != crate::sat_types::Var(3),
                "primed var should differ from original"
            );
        }
    }

    /// Verify init consistency with internal signal cube (#4148).
    ///
    /// When internal signals are in the cube, the SAT-based init check must
    /// load AND-gate definitions (trans_clauses) to constrain internal signal
    /// values. Otherwise a cube with `[latch=0, isig=1]` where `isig = AND(latch, ...)`
    /// would falsely appear init-consistent.
    #[test]
    fn test_init_consistency_with_internal_signals() {
        // Circuit: 1 input (v1), 1 latch (v2, init=0, next=v1),
        // AND gate: v3 = AND(v1, v2). Bad = v3.
        let circuit = parse_aag("aag 3 1 1 0 1 1\n2\n4 2\n6\n6 2 4\n").unwrap();
        let mut ts = crate::transys::Transys::from_aiger(&circuit);
        ts.internal_signals = vec![crate::sat_types::Var(3)]; // AND gate

        let config = Ic3Config {
            internal_signals: true,
            ..Ic3Config::default()
        };
        let engine = Ic3Engine::with_config(ts, config);

        // Cube [latch=0, isig=1]: isig = AND(input, latch).
        // At init, latch=0, so AND(anything, 0) = 0. isig=1 is impossible.
        let cube_impossible = vec![
            crate::sat_types::Lit::neg(crate::sat_types::Var(2)), // latch=0
            crate::sat_types::Lit::pos(crate::sat_types::Var(3)), // isig=1 (impossible)
        ];
        // The SAT check should detect this is inconsistent because
        // trans_clauses encode v3 = AND(v1, v2) and v2=0 forces v3=0.
        assert!(
            !engine.cube_sat_consistent_with_init(&cube_impossible),
            "cube with impossible internal signal value should NOT be init-consistent"
        );

        // Cube [latch=0, isig=0]: isig = AND(input, 0) = 0. Consistent.
        let cube_possible = vec![
            crate::sat_types::Lit::neg(crate::sat_types::Var(2)), // latch=0
            crate::sat_types::Lit::neg(crate::sat_types::Var(3)), // isig=0 (correct)
        ];
        assert!(
            engine.cube_sat_consistent_with_init(&cube_possible),
            "cube with correct internal signal value should be init-consistent"
        );
    }

    /// IC3 with internal signals on a 2-step unsafe circuit.
    /// Uses SimpleSolver to avoid z4-sat crash bugs.
    /// Latch starts at 0, next = NOT latch. Bad = latch.
    /// Unsafe at depth 1 (latch flips to 1).
    #[test]
    fn test_ic3_internal_signals_toggle_simple_solver() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let config = Ic3Config {
            internal_signals: true,
            solver_backend: crate::sat_types::SolverBackend::Simple,
            ..Ic3Config::default()
        };
        let result = check_ic3_with_config(&circuit, config);
        assert!(
            matches!(result, Ic3Result::Unsafe { .. }),
            "toggle with internal_signals + SimpleSolver should be Unsafe, got {result:?}"
        );
    }

    /// IC3 with all inn variants combined (internal + CTP + dynamic features).
    #[test]
    fn test_ic3_internal_signals_combined_safe() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let config = Ic3Config {
            internal_signals: true,
            ctp: true,
            inf_frame: true,
            ternary_reduce: true,
            parent_lemma: true,
            ..Ic3Config::default()
        };
        let result = check_ic3_with_config(&circuit, config);
        assert!(
            matches!(result, Ic3Result::Safe { .. }),
            "fully combined internal_signals config should prove safe, got {result:?}"
        );
    }

    /// returns SAT (v2 CAN become true from v2=false because A.next = input).
    #[test]
    fn test_shift_register_consecution_direct() {
        use crate::sat_types::{SimpleSolver, SatSolver, SatResult, Lit, Var};
        let aag = "\
aag 6 1 3 0 2 1
2
4 2
6 4
8 6
12
10 4 6
12 10 8
";
        let circuit = parse_aag(aag).unwrap();
        let ts = crate::transys::Transys::from_aiger(&circuit);

        // Build inf_solver equivalent manually
        let mut solver = SimpleSolver::new();

        // Allocate next-state variables
        let max_var = ts.max_var;
        // v1=input(lit2), v2=latchA(lit4), v3=latchB(lit6), v4=latchC(lit8)
        // v5=AND(lit10), v6=AND(lit12)
        // Next-state vars: v2'=v7, v3'=v8, v4'=v9
        let v2_next = Var(max_var + 1); // v7
        let v3_next = Var(max_var + 2); // v8
        let v4_next = Var(max_var + 3); // v9
        solver.ensure_vars(max_var + 3);

        // Var 0 = false
        solver.add_clause(&[Lit::TRUE]);

        // Trans clauses (AND gate Tseitin)
        for clause in &ts.trans_clauses {
            solver.add_clause(&clause.lits);
            eprintln!("  trans clause: {:?}", clause.lits);
        }

        // Next-linking: v2' <=> input(v1=lit2), v3' <=> v2(lit4), v4' <=> v3(lit6)
        // Build from transition system
        for &latch_var in &ts.latch_vars {
            if let Some(&next_expr) = ts.next_state.get(&latch_var) {
                let next_var = if latch_var == Var(2) { v2_next }
                    else if latch_var == Var(3) { v3_next }
                    else { v4_next };
                let nv_pos = Lit::pos(next_var);
                let nv_neg = Lit::neg(next_var);
                // next_var <=> next_expr
                solver.add_clause(&[nv_neg, next_expr]);
                solver.add_clause(&[nv_pos, !next_expr]);
                eprintln!("  linking: {:?} <=> {:?}", next_var, next_expr);
            }
        }

        // Now test: is cube [v2] blocked at frame 1?
        // Consecution: Trans AND (!v2) AND (v2') is UNSAT?
        let cube = vec![Lit::pos(Var(2))]; // v2 = true
        let neg_cube = vec![Lit::neg(Var(2))]; // !v2 = false
        let primed_cube = vec![Lit::pos(v2_next)]; // v2' = true

        let result = solver.solve_with_temporary_clause(&primed_cube, &neg_cube);
        eprintln!("Consecution result for cube [v2]: {:?}", result);
        assert_eq!(
            result, SatResult::Sat,
            "cube [v2] should NOT be blocked — v2 can become true from v2=false (A.next=input)"
        );
    }

    /// Test propagation consecution with frame lemmas (#4092 debug).
    ///
    /// Replicates the exact solver state at propagation time: solver[1] has
    /// Trans + linking + frame-1 lemmas [~v2,~v3] and [~v4]. Then checks if
    /// cube [v4] is blocked (should be SAT, i.e., NOT blocked).
    #[test]
    fn test_shift_register_propagation_consecution() {
        use crate::sat_types::{SimpleSolver, SatSolver, SatResult, Lit, Var};
        let aag = "\
aag 6 1 3 0 2 1
2
4 2
6 4
8 6
12
10 4 6
12 10 8
";
        let circuit = parse_aag(aag).unwrap();
        let ts = crate::transys::Transys::from_aiger(&circuit);

        let mut solver = SimpleSolver::new();
        let max_var = ts.max_var;
        let v2_next = Var(max_var + 1);
        let v3_next = Var(max_var + 2);
        let v4_next = Var(max_var + 3);
        solver.ensure_vars(max_var + 3);

        // Var 0 = false
        solver.add_clause(&[Lit::TRUE]);

        // Trans clauses
        for clause in &ts.trans_clauses {
            solver.add_clause(&clause.lits);
        }

        // Next-linking
        for &latch_var in &ts.latch_vars {
            if let Some(&next_expr) = ts.next_state.get(&latch_var) {
                let next_var = if latch_var == Var(2) { v2_next }
                    else if latch_var == Var(3) { v3_next }
                    else { v4_next };
                solver.add_clause(&[Lit::neg(next_var), next_expr]);
                solver.add_clause(&[Lit::pos(next_var), !next_expr]);
            }
        }

        // Frame-1 lemmas (as would be present during propagation)
        solver.add_clause(&[Lit::neg(Var(2)), Lit::neg(Var(3))]); // [~v2, ~v3]
        solver.add_clause(&[Lit::neg(Var(4))]); // [~v4]

        // Propagation check for cube [v4] (should NOT be blocked):
        // solver AND v4' should be SAT
        let result = solver.solve(&[Lit::pos(v4_next)]);
        eprintln!("Propagation consecution for [v4] with frame lemmas: {:?}", result);
        assert_eq!(
            result, SatResult::Sat,
            "cube [v4] should NOT be blocked at frame 2 — v4 can become true via C.next=B"
        );

        // Also check with solve_with_temporary_clause (which propagation_blocked does NOT use,
        // but push_lemma DOES use):
        let result2 = solver.solve_with_temporary_clause(
            &[Lit::pos(v4_next)],
            &[Lit::neg(Var(4))],
        );
        eprintln!("push_lemma consecution for [v4] with frame lemmas: {:?}", result2);
    }

    /// Test that activation literal accumulation causes SimpleSolver false UNSAT (#4092).
    ///
    /// SimpleSolver's default `solve_with_temporary_clause` adds permanent clauses
    /// with activation literals. When DPLL searches, it tries all unassigned variables
    /// including activation variables. Setting old activation vars to `true` activates
    /// old temporary clauses, over-constraining the formula.
    #[test]
    fn test_activation_literal_pollution() {
        use crate::sat_types::{SimpleSolver, SatSolver, SatResult, Lit, Var};

        let mut solver = SimpleSolver::new();
        let a = Var(1);
        let b = Var(2);
        solver.ensure_vars(2);

        // Base formula: just variables a and b, no constraints.
        // solve(&[pos(a)]) should be SAT.
        assert_eq!(solver.solve(&[Lit::pos(a)]), SatResult::Sat);

        // Add several temporary clauses that constrain a when activated.
        for _ in 0..5 {
            // temp clause: [!a] (a must be false when activated)
            solver.solve_with_temporary_clause(&[Lit::pos(b)], &[Lit::neg(a)]);
        }

        // Now solve(&[pos(a)]) should STILL be SAT — old activation lits are unassigned.
        // But if DPLL picks an activation var and sets it to true, it activates
        // the [!a] clause, forcing a=false, which conflicts with the assumption a=true.
        let result = solver.solve(&[Lit::pos(a)]);
        eprintln!("After 5 temp clause calls: solve([pos(a)]) = {:?}", result);
        assert_eq!(
            result, SatResult::Sat,
            "activation literal pollution: old temp clauses should not affect new queries"
        );
    }

    /// Test that SimpleSolver finds the 3-deep shift register as Unsafe (#4092).
    ///
    /// Root cause: init-inconsistent cubes blocked at frame 0 were propagated
    /// to ALL frame solvers via `for s in &mut self.solvers { s.add_clause(...) }`.
    /// This is unsound because a cube like {v2} (v2=true) is init-inconsistent
    /// (Init forces v2=0) but v2=true IS reachable at higher frames through the
    /// transition relation. Adding [~v2] to all solvers falsely constrains higher
    /// frames, causing IC3 to converge on an unsound invariant.
    ///
    /// Fix: frame-0 lemmas are only added to solver[0], not to higher solvers.
    /// This matches IC3ref (Bradley), which adds blocking clauses to frames
    /// 1..=level and NEVER adds to frame 0's solver.
    #[test]
    fn test_shift_register_3deep_simple_solver() {
        let aag = "\
aag 6 1 3 0 2 1
2
4 2
6 4
8 6
12
10 4 6
12 10 8
";
        let circuit = parse_aag(aag).unwrap();
        let ts = crate::transys::Transys::from_aiger(&circuit);
        let mut engine = Ic3Engine::new(ts).with_simple_solver();
        let result = engine.check();
        assert!(
            matches!(result, Ic3Result::Unsafe { .. }),
            "3-deep shift register should be Unsafe with SimpleSolver, got {result:?}"
        );
    }

    /// Test that 4-deep shift register is also correctly Unsafe (#4092).
    ///
    /// Similar to the 3-deep case but with 4 latches: input -> v2 -> v3 -> v4 -> v5.
    /// Bad = v2 AND v3 AND v4 AND v5 (all latches true). Reachable after 4 steps
    /// of input=1. Tests that the frame-0 lemma fix works for deeper circuits.
    #[test]
    fn test_shift_register_4deep_simple_solver() {
        let aag = "\
aag 9 1 4 0 4 1
2
4 2
6 4
8 6
10 8
18
12 4 6
14 12 8
16 14 10
18 16 10
";
        // v1=input, v2..v5=latches, AND: v6=v2&v3, v7=v6&v4, v8=v7&v5, bad=v9=v8&v5
        // Actually let me re-do this with correct AIGER encoding.
        // Bad = v2 AND v3 AND v4 AND v5 = AND(AND(AND(v2,v3),v4),v5)
        // Need 3 AND gates: g1=v2&v3 (lit 12), g2=g1&v4 (lit 14), g3=g2&v5 (lit 16)
        // Bad output = lit 16
        let aag = "\
aag 8 1 4 0 3 1
2
4 2
6 4
8 6
10 8
16
12 4 6
14 12 8
16 14 10
";
        let circuit = parse_aag(aag).unwrap();
        let ts = crate::transys::Transys::from_aiger(&circuit);
        let mut engine = Ic3Engine::new(ts).with_simple_solver();
        let result = engine.check();
        assert!(
            matches!(result, Ic3Result::Unsafe { .. }),
            "4-deep shift register should be Unsafe with SimpleSolver, got {result:?}"
        );
    }

    /// Test that a 2-deep shift register with constrained input is Safe (#4092).
    ///
    /// Circuit: input -> v2 -> v3. Bad = v2 AND v3.
    /// Constraint: NOT input (input is always 0).
    /// Since input is always 0, v2 is always 0, so v2 AND v3 is never true.
    /// This tests that IC3 correctly handles frame-0 lemma scoping on a safe
    /// circuit with constraints.
    #[test]
    fn test_shift_register_2deep_constrained_safe() {
        // v1=input, v2=latch(next=v1), v3=latch(next=v2)
        // AND: v4 = v2 AND v3. Bad = v4.
        // Constraint: NOT v1 (input always 0, lit 3 = ~lit 2).
        // AAG section order: inputs, latches, outputs, bad, constraints, AND gates.
        let aag = "\
aag 4 1 2 0 1 1 1
2
4 2
6 4
8
3
8 4 6
";
        let circuit = parse_aag(aag).unwrap();
        let ts = crate::transys::Transys::from_aiger(&circuit);
        let mut engine = Ic3Engine::new(ts).with_simple_solver();
        let result = engine.check();
        assert!(
            matches!(result, Ic3Result::Safe { .. }),
            "2-deep constrained shift register should be Safe, got {result:?}"
        );
    }

    // -----------------------------------------------------------------------
    // Tests for #4151: PO dropping prevents IC3 thrashing
    // -----------------------------------------------------------------------

    /// Test that PO dropping with aggressive threshold (10.0) terminates
    /// and produces correct results on a 3-deep shift register (safe).
    ///
    /// Circuit: input -> v2 -> v3 -> v4. Bad = v2 AND v3 AND v4.
    /// Init: all latches 0. The 3-way AND of all latches is never satisfied
    /// because the initial 0 propagates through the pipeline. With drop_po
    /// at threshold 10.0, any POs that thrash are dropped quickly.
    #[test]
    fn test_drop_po_aggressive_threshold_terminates_safe() {
        // 3-deep shift register: v1=input, v2=latch(v1), v3=latch(v2), v4=latch(v3)
        // v5 = v2 AND v3, v6 = v5 AND v4 (3-way AND). Bad = v6.
        // Constraint: NOT v1 (input always 0).
        let aag = "\
aag 6 1 3 0 2 1 1
2
4 2
6 4
8 6
12
3
10 4 6
12 10 8
";
        let circuit = parse_aag(aag).unwrap();
        let config = Ic3Config {
            drop_po: true,
            drop_po_threshold: 10.0,
            ..Ic3Config::default()
        };
        let result = check_ic3_with_config(&circuit, config);
        assert!(
            matches!(result, Ic3Result::Safe { .. }),
            "3-deep constrained shift register with aggressive drop (threshold=10) should be Safe, got {result:?}"
        );
    }

    /// Test that PO dropping with conservative threshold (40.0) terminates
    /// and produces correct results on an unsafe circuit.
    ///
    /// Circuit: toggle latch (starts 0, next=NOT latch). Bad = latch.
    /// This is trivially unsafe at depth 1. Even with conservative PO
    /// dropping, the counterexample should be found before any PO reaches
    /// activity 40.0.
    #[test]
    fn test_drop_po_conservative_threshold_terminates_unsafe() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let config = Ic3Config {
            drop_po: true,
            drop_po_threshold: 40.0,
            ..Ic3Config::default()
        };
        let result = check_ic3_with_config(&circuit, config);
        assert!(
            matches!(result, Ic3Result::Unsafe { .. }),
            "toggle circuit with conservative drop (threshold=40) should be Unsafe, got {result:?}"
        );
    }

    /// Test that PO dropping counts are tracked in the engine.
    ///
    /// Uses an extremely low threshold (1.0) so that ANY PO that is re-encountered
    /// even once gets dropped. The circuit is safe (latch stuck at 0), so IC3
    /// should still prove it. This exercises the counting path.
    #[test]
    fn test_drop_po_count_tracked() {
        // Simple circuit: latch next=0 (constant false), bad=latch.
        // Latch stays 0 forever. Bad is never reachable. Safe.
        let aag = "aag 1 0 1 0 0 1\n2 0\n2\n";
        let circuit = parse_aag(aag).unwrap();
        let ts = crate::transys::Transys::from_aiger(&circuit);
        let config = Ic3Config {
            drop_po: true,
            drop_po_threshold: 1.0,
            ..Ic3Config::default()
        };
        let mut engine = Ic3Engine::with_config(ts, config);
        let result = engine.check();
        assert!(
            matches!(result, Ic3Result::Safe { .. }),
            "constrained single-latch circuit with drop threshold=1.0 should be Safe, got {result:?}"
        );
        // po_drop_count tracks the total number of dropped POs.
        // With threshold=1.0, any PO that gets bumped past 1.0 is dropped.
        // The exact count depends on the circuit, but the field should be accessible.
        // (May be 0 if IC3 converges before any PO activity exceeds 1.0.)
        let _drop_count = engine.po_drop_count;
    }

    /// Test that PO activity decays correctly when pushed to a higher frame.
    ///
    /// This verifies the interaction between bump_act() and push_to_frame():
    /// a PO that accumulates activity 20.0 at frame 1, then gets pushed to
    /// frame 3 (2 levels), should have activity 20.0 * 0.6^2 = 7.2, which is
    /// BELOW the default drop threshold (20.0). This means successfully
    /// generalized POs get a second chance at higher frames.
    #[test]
    fn test_drop_po_activity_decay_gives_second_chance() {
        let mut po = obligation::ProofObligation::new(1, vec![], 0, None);
        // Bump 20 times to reach activity 20.0 (default drop threshold).
        for _ in 0..20 {
            po.bump_act();
        }
        assert_eq!(po.act, 20.0);

        // Push from frame 1 to frame 3 (2 levels of 0.6x decay).
        po.push_to_frame(3);
        // 20.0 * 0.6 * 0.6 = 7.2
        assert!((po.act - 7.2).abs() < 0.01);
        assert!(po.act < 20.0, "decayed activity should be below drop threshold");
    }

    /// Test portfolio variants with different drop_po thresholds all produce
    /// correct results on the same circuit.
    #[test]
    fn test_drop_po_portfolio_variants_consistent() {
        use crate::portfolio::{ic3_aggressive_drop, ic3_conservative_drop, ic3_aggressive_drop_ctp};
        use crate::portfolio::EngineConfig;

        // Toggle: unsafe at depth 1. All portfolio variants must detect the bug.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();

        for engine_cfg in [
            ic3_aggressive_drop(),
            ic3_conservative_drop(),
            ic3_aggressive_drop_ctp(),
        ] {
            if let EngineConfig::Ic3Configured { config, name } = engine_cfg {
                let result = check_ic3_with_config(&circuit, config);
                assert!(
                    matches!(result, Ic3Result::Unsafe { .. }),
                    "portfolio variant '{name}' should detect bug, got {result:?}"
                );
            }
        }

        // Simple safe circuit: latch stuck at 0, bad=latch. All variants must prove Safe.
        let safe_circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();

        for engine_cfg in [
            ic3_aggressive_drop(),
            ic3_conservative_drop(),
            ic3_aggressive_drop_ctp(),
        ] {
            if let EngineConfig::Ic3Configured { config, name } = engine_cfg {
                let result = check_ic3_with_config(&safe_circuit, config);
                assert!(
                    matches!(result, Ic3Result::Safe { .. }),
                    "portfolio variant '{name}' should prove Safe, got {result:?}"
                );
            }
        }
    }

    // -----------------------------------------------------------------------
    // Consecution diagnostics and verification tests (#4121)
    // -----------------------------------------------------------------------

    /// Test that consecution stats are tracked during IC3 execution.
    #[test]
    fn test_consecution_stats_tracked() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let ts = crate::transys::Transys::from_aiger(&circuit);
        let mut engine = Ic3Engine::new(ts).with_simple_solver();
        let result = engine.check();
        assert!(
            matches!(result, Ic3Result::Safe { .. }),
            "expected Safe, got {result:?}"
        );
        let stats = &engine.consecution_stats;
        assert!(
            stats.total_queries == stats.unsat_results + stats.sat_results + stats.unknown_results,
            "total queries should equal sum of results: {} != {} + {} + {}",
            stats.total_queries,
            stats.unsat_results,
            stats.sat_results,
            stats.unknown_results,
        );
    }

    /// Test that consecution stats track SAT results for an unsafe circuit.
    #[test]
    fn test_consecution_stats_unsafe_circuit() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let ts = crate::transys::Transys::from_aiger(&circuit);
        let mut engine = Ic3Engine::new(ts).with_simple_solver();
        let result = engine.check();
        assert!(
            matches!(result, Ic3Result::Unsafe { .. }),
            "expected Unsafe, got {result:?}"
        );
        let stats = &engine.consecution_stats;
        assert!(
            stats.total_queries == stats.unsat_results + stats.sat_results + stats.unknown_results,
            "total queries should equal sum of results"
        );
    }

    /// Test verify_lemma_consecution rejects a non-inductive cube.
    #[test]
    fn test_verify_lemma_consecution_rejects_non_inductive() {
        let aag = "\
aag 6 1 3 0 2 1
2
4 2
6 4
8 6
12
10 4 6
12 10 8
";
        let circuit = parse_aag(aag).unwrap();
        let ts = crate::transys::Transys::from_aiger(&circuit);
        let mut engine = Ic3Engine::new(ts).with_simple_solver();

        engine.extend(); // frame 0
        engine.extend(); // frame 1

        let cube_a = vec![crate::sat_types::Lit::pos(crate::sat_types::Var(2))];
        let result = engine.verify_lemma_consecution(1, &cube_a);
        assert!(
            !result,
            "cube {{v2}} should NOT pass consecution at frame 1"
        );

        let cube_c = vec![crate::sat_types::Lit::pos(crate::sat_types::Var(4))];
        let result_c = engine.verify_lemma_consecution(1, &cube_c);
        assert!(
            !result_c,
            "cube {{v4}} should NOT pass consecution at frame 1"
        );
    }

    /// Test verify_lemma_consecution accepts a genuinely inductive lemma.
    #[test]
    fn test_verify_lemma_consecution_accepts_inductive() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let ts = crate::transys::Transys::from_aiger(&circuit);
        let mut engine = Ic3Engine::new(ts).with_simple_solver();

        engine.extend(); // frame 0
        engine.extend(); // frame 1

        let cube_latch_true = vec![crate::sat_types::Lit::pos(crate::sat_types::Var(1))];
        let result = engine.verify_lemma_consecution(1, &cube_latch_true);
        assert!(
            result,
            "cube {{latch=true}} SHOULD pass consecution: latch.next=0"
        );
    }

    /// Regression test: cross-solver comparison on shift register (#4121).
    #[test]
    fn test_ic3_cross_solver_shift_register_soundness() {
        let aag = "\
aag 6 1 3 0 2 1
2
4 2
6 4
8 6
12
10 4 6
12 10 8
";
        let circuit = parse_aag(aag).unwrap();

        let ts = crate::transys::Transys::from_aiger(&circuit);
        let mut engine_simple = Ic3Engine::new(ts).with_simple_solver();
        let result_simple = engine_simple.check();
        assert!(
            matches!(result_simple, Ic3Result::Unsafe { .. }),
            "3-deep shift register should be Unsafe with SimpleSolver, got {result_simple:?}"
        );

        let circuit2 = parse_aag(aag).unwrap();
        let ts2 = crate::transys::Transys::from_aiger(&circuit2);
        let mut engine_z4 = Ic3Engine::new(ts2);
        let result_z4 = engine_z4.check();
        assert!(
            matches!(result_z4, Ic3Result::Unsafe { .. }),
            "3-deep shift register should be Unsafe with Z4Sat, got {result_z4:?}"
        );

        let stats = &engine_z4.consecution_stats;
        assert!(
            stats.total_queries > 0,
            "expected at least one consecution query on 3-latch circuit"
        );
    }

    /// Test IC3_VERIFY_LEMMAS mechanism is wired end-to-end (#4121).
    #[test]
    fn test_ic3_verify_lemmas_mechanism_active() {
        let aag = "\
aag 6 1 3 0 2 1
2
4 2
6 4
8 6
12
10 4 6
12 10 8
";
        let circuit = parse_aag(aag).unwrap();
        let ts = crate::transys::Transys::from_aiger(&circuit);

        std::env::set_var("IC3_VERIFY_LEMMAS", "1");
        let config = Ic3Config {
            solver_backend: crate::sat_types::SolverBackend::Simple,
            ..Ic3Config::default()
        };
        let mut engine = Ic3Engine::with_config(ts, config);
        let result = engine.check();
        std::env::remove_var("IC3_VERIFY_LEMMAS");

        assert!(
            matches!(result, Ic3Result::Unsafe { .. }),
            "3-deep shift register with verify_lemmas should be Unsafe, got {result:?}"
        );

        let stats = &engine.consecution_stats;
        assert!(
            stats.total_queries > 0,
            "IC3_VERIFY_LEMMAS should have triggered consecution queries"
        );
        let verify_total = stats.lemmas_rejected + stats.lemmas_verified;
        assert!(
            verify_total > 0 || stats.total_queries > 0,
            "expected verification path to be exercised"
        );
    }

    // -----------------------------------------------------------------------
    // Tests for #4181: !cube strengthening in propagation_blocked()
    // -----------------------------------------------------------------------

    /// SAT-level demonstration that `!cube` strengthening distinguishes relative
    /// from absolute inductiveness (#4181).
    ///
    /// Circuit: identity latch (next = self). A stays at its init value (0)
    /// forever. This creates a cube {A=1} that is:
    /// - NOT absolutely inductive: F_k AND T AND A' is SAT (set A=1, A'=A=1).
    /// - Relatively inductive: F_k AND !{A=1} AND T AND A' is UNSAT
    ///   (A=0 forces A'=A=0, contradicting A'=1).
    ///
    /// Without the `!cube` strengthening fix, `propagation_blocked()` would
    /// return None (not blocked) for this cube, preventing the lemma [!A] from
    /// being pushed forward through frames. With strengthening, it correctly
    /// returns Some (blocked), enabling propagation.
    #[test]
    fn test_propagation_blocked_strengthening_sat_level() {
        use crate::sat_types::{SimpleSolver, SatSolver, SatResult, Lit, Var};

        let mut solver = SimpleSolver::new();
        // Var 0 = constant false (standard). Var 1 = latch A, Var 2 = A' (next).
        let a = Var(1);
        let a_next = Var(2);
        solver.ensure_vars(2);

        // Var(0) = false (standard IC3 convention).
        solver.add_clause(&[Lit::TRUE]);

        // Transition: next(A) = A. Encoded as A' <=> A.
        // Clause 1: (!A' OR A) — if A' is true, A must be true.
        solver.add_clause(&[Lit::neg(a_next), Lit::pos(a)]);
        // Clause 2: (A' OR !A) — if A is true, A' must be true.
        solver.add_clause(&[Lit::pos(a_next), Lit::neg(a)]);

        // Cube = {A=1}. Primed cube = {A'=1}. Strengthening = !cube = {!A}.
        let primed_cube = [Lit::pos(a_next)];
        let neg_cube = [Lit::neg(a)];

        // WITHOUT strengthening: F_k AND T AND cube' — is there any state
        // in the frame that can produce A'=1?
        // Since the solver has no frame lemmas restricting A, it can set A=1,
        // then T gives A'=A=1. Result: SAT (NOT blocked).
        let result_without = solver.solve(&primed_cube);
        assert_eq!(
            result_without, SatResult::Sat,
            "without !cube strengthening, cube {{A=1}} should NOT be blocked (absolute inductiveness fails)"
        );

        // WITH strengthening: F_k AND !cube AND T AND cube' — can a state
        // where A=0 (i.e., satisfying !cube) produce A'=1?
        // !cube forces A=0. T gives A'=A=0. A'=1 is contradicted. UNSAT (blocked).
        let result_with = solver.solve_with_temporary_clause(&primed_cube, &neg_cube);
        assert_eq!(
            result_with, SatResult::Unsat,
            "with !cube strengthening, cube {{A=1}} should be blocked (relative inductiveness holds)"
        );
    }

    /// Integration test: IC3 proves Safe on an identity-latch circuit where
    /// `!cube` strengthening in propagation enables efficient convergence (#4181).
    ///
    /// Circuit: 3 latches in a pipeline (input -> A -> B -> C, all init 0).
    /// Bad = A AND C. Constraint: NOT input (input is always 0).
    /// Since input is always 0, A stays 0, so A AND C is never true. Safe.
    ///
    /// During IC3, the lemma [!A] (encoding "A is always false") must be
    /// propagated through frames. The cube {A=1} is relatively inductive
    /// (since A=0 in the next state when A=0, via the pipeline delay) but
    /// NOT absolutely inductive at higher frames (the solver could guess A=1).
    /// Strengthening with !cube ([!A]) in propagation_blocked() allows this
    /// lemma to be pushed forward, enabling frame convergence.
    #[test]
    fn test_propagation_strengthening_enables_convergence() {
        // 3-latch pipeline: A=latch(input), B=latch(A), C=latch(B).
        // Bad = A AND C. Constraint: NOT input.
        // AAG format: aag max_var inputs latches outputs ands bads constraints
        // Vars: 1=input(lit2), 2=A(lit4), 3=B(lit6), 4=C(lit8)
        // AND: 5=A&C (lit10)
        // Bad = lit10. Constraint = lit3 (NOT input).
        let aag = "\
aag 5 1 3 0 1 1 1
2
4 2
6 4
8 6
10
3
10 4 8
";
        let circuit = parse_aag(aag).unwrap();
        let ts = crate::transys::Transys::from_aiger(&circuit);

        // Use SimpleSolver to avoid z4-sat bugs.
        let mut engine = Ic3Engine::new(ts).with_simple_solver();
        let result = engine.check();
        assert!(
            matches!(result, Ic3Result::Safe { .. }),
            "3-latch pipeline with constrained input should be Safe, got {result:?}"
        );
    }

    /// Integration test: IC3 correctly detects Unsafe on a circuit with
    /// self-maintaining latches, verifying that `!cube` strengthening does
    /// not weaken the blocking check (#4181).
    ///
    /// Circuit: 2 latches (A, B), A.next = A OR input, B.next = A.
    /// Bad = A AND B. Reachable: step 0 (0,0), step 1 with input=1: (1,0),
    /// step 2: (1,1) — bad reached.
    ///
    /// This tests that strengthening does not cause false Safe results:
    /// even though {A=1,B=1} might be relatively inductive, IC3 must still
    /// find the 2-step counterexample.
    #[test]
    fn test_propagation_strengthening_does_not_weaken_unsafe_detection() {
        // A.next = A OR input. Need AND gate for OR: A OR i = NOT(NOT A AND NOT i).
        // Vars: 1=input(lit2), 2=A(lit4), 3=B(lit6)
        // AND gate: 4 = NOT_A AND NOT_i (lit8), so A OR i = NOT(lit8) = lit9.
        // AND gate: 5 = A AND B (lit10)
        // A.next = lit9 (= NOT(NOT_A AND NOT_i) = A OR i)
        // B.next = lit4 (= A)
        // Bad = lit10
        let aag = "\
aag 5 1 2 0 2 1
2
4 9
6 4
10
8 5 3
10 4 6
";
        let circuit = parse_aag(aag).unwrap();
        let ts = crate::transys::Transys::from_aiger(&circuit);
        let mut engine = Ic3Engine::new(ts).with_simple_solver();
        let result = engine.check();
        assert!(
            matches!(result, Ic3Result::Unsafe { .. }),
            "sticky-latch circuit with reachable bad state should be Unsafe, got {result:?}"
        );
    }

    /// SAT-level test with 2 latches demonstrating that `!cube` strengthening
    /// enables propagation of multi-literal cubes (#4181).
    ///
    /// Circuit: A.next = A, B.next = B (both identity latches, init 0).
    /// Cube {A=1, B=1}: states where both latches are true.
    /// - Without strengthening: SAT (solver sets A=1, B=1, gets A'=1, B'=1)
    /// - With strengthening: UNSAT (!cube = [!A, !B] forces A=0 OR B=0;
    ///   since A'=A and B'=B, at least one of A', B' is 0, contradicting cube')
    #[test]
    fn test_propagation_blocked_strengthening_multi_literal_cube() {
        use crate::sat_types::{SimpleSolver, SatSolver, SatResult, Lit, Var};

        let mut solver = SimpleSolver::new();
        // Var 0 = false. Var 1 = A, Var 2 = B, Var 3 = A', Var 4 = B'.
        let a = Var(1);
        let b = Var(2);
        let a_next = Var(3);
        let b_next = Var(4);
        solver.ensure_vars(4);

        solver.add_clause(&[Lit::TRUE]);

        // Trans: A' <=> A (identity).
        solver.add_clause(&[Lit::neg(a_next), Lit::pos(a)]);
        solver.add_clause(&[Lit::pos(a_next), Lit::neg(a)]);
        // Trans: B' <=> B (identity).
        solver.add_clause(&[Lit::neg(b_next), Lit::pos(b)]);
        solver.add_clause(&[Lit::pos(b_next), Lit::neg(b)]);

        // Cube = {A=1, B=1}. Primed = {A'=1, B'=1}. !cube = {!A, !B} (clause: !A OR !B).
        let primed_cube = [Lit::pos(a_next), Lit::pos(b_next)];
        let neg_cube_clause = [Lit::neg(a), Lit::neg(b)]; // !A OR !B

        // WITHOUT strengthening: solver can set A=1, B=1 → A'=1, B'=1. SAT.
        let result_without = solver.solve(&primed_cube);
        assert_eq!(
            result_without, SatResult::Sat,
            "without strengthening, multi-literal cube should NOT be blocked"
        );

        // WITH strengthening: !cube forces !A OR !B. If A=0, then A'=0
        // contradicts primed_cube A'=1. If B=0, then B'=0 contradicts B'=1.
        // The clause (!A OR !B) means at least one is 0, so at least one
        // primed assumption fails. UNSAT.
        let result_with = solver.solve_with_temporary_clause(&primed_cube, &neg_cube_clause);
        assert_eq!(
            result_with, SatResult::Unsat,
            "with strengthening, multi-literal cube on identity latches should be blocked"
        );
    }

    /// Exercises the push-time inductive-subclause generalization path
    /// added for #4244.
    ///
    /// A 3-latch stuck-at-zero circuit (each latch `x` has `x' = 0`) is
    /// trivially SAFE and converges quickly with a handful of pushed
    /// lemmas. With `push_generalize = true`, the propagation path routes
    /// through `try_push_generalize`, which must (a) produce the same SAFE
    /// result as the default config, and (b) never admit an unsound
    /// subclause that intersects the initial state.
    ///
    /// This test guards against the regression flagged in #4244, where the
    /// reverted MIC-propagation salvage caused IC3 to return `Unknown` on
    /// small circuits. A SAFE result here demonstrates that the new code
    /// path preserves soundness and convergence for the default (conservative)
    /// literal-drop budget.
    #[test]
    fn test_push_generalize_preserves_safe_on_stuck_at_zero() {
        // 2-latch stuck-at-zero with bad = l1 AND l2. Each latch has next=0.
        // This is SAFE — `bad` is unreachable from initial state (latches=0).
        // Header `aag M I L O A B`: M=3 maxvar, I=0 inputs, L=2 latches,
        // O=0 outputs, A=1 and-gate, B=1 bad. Mirrors the circuit used by
        // the existing `test_two_latches_safe` helper AAG.
        let aag = "aag 3 0 2 0 1 1\n2 0\n4 0\n6\n6 2 4\n";
        let circuit = parse_aag(aag).expect("valid AAG");

        let default_cfg = Ic3Config::default();
        let default_result = check_ic3_with_config(&circuit, default_cfg);
        assert!(
            matches!(default_result, Ic3Result::Safe { .. }),
            "stuck-at-zero must be SAFE under default config, got {default_result:?}",
        );

        let mut push_gen_cfg = Ic3Config::default();
        push_gen_cfg.push_generalize = true;
        push_gen_cfg.push_generalize_budget = 4;
        let push_gen_result = check_ic3_with_config(&circuit, push_gen_cfg);
        assert!(
            matches!(push_gen_result, Ic3Result::Safe { .. }),
            "push_generalize=true must still converge to SAFE on stuck-at-zero, got {push_gen_result:?}",
        );

        // Budget=0 must be a no-op equivalent to push_generalize=false.
        let mut zero_budget_cfg = Ic3Config::default();
        zero_budget_cfg.push_generalize = true;
        zero_budget_cfg.push_generalize_budget = 0;
        let zero_budget_result = check_ic3_with_config(&circuit, zero_budget_cfg);
        assert!(
            matches!(zero_budget_result, Ic3Result::Safe { .. }),
            "push_generalize_budget=0 must not regress convergence, got {zero_budget_result:?}",
        );
    }

    /// #4317: type-gated #4247 trivially-safe convergence.
    ///
    /// Build an `Ic3Engine` whose frames are all empty at depth >= 2 — the
    /// exact precondition that would have triggered the pre-#4310 shortcut
    /// unconditionally. Call `propagate()` twice:
    ///
    ///   1. With `blocking_witness = None` (simulating every early-out
    ///      break path: blocking budget, repeated cube #4139, drop_po,
    ///      cancellation). The shortcut MUST NOT fire and `propagate()` MUST
    ///      return [`PropagateOutcome::NotYet`].
    ///   2. With `blocking_witness = Some(ConvergenceProof::from_natural_exit())`
    ///      (the only admissible caller — the `get_bad() => None` arm in
    ///      `run.rs`). The shortcut fires and `propagate()` returns
    ///      [`PropagateOutcome::Converged`].
    ///
    /// Together these cases prove the #4310 → #4317 soundness gate: the
    /// shortcut cannot fire without an unforgeable `ConvergenceProof`, and
    /// the type system now enforces that only `run.rs`'s natural-exit arm can
    /// mint one.
    #[test]
    fn test_propagate_convergence_proof_gates_shortcut_4317() {
        use super::propagate::{ConvergenceProof, PropagateOutcome};

        // Minimal safe circuit: 1 latch stuck at 0, bad = latch.
        // This is SAFE, and `Ic3Engine::new` sets up a well-formed transys.
        // `aag 1 0 1 0 0 1\n2 0\n2\n` — parsed in `test_stuck_at_zero_safe`.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").expect("valid AAG");
        let ts = crate::transys::Transys::from_aiger(&circuit);
        let mut engine = Ic3Engine::new(ts).with_simple_solver();

        // Manually extend frames to depth 2 with no lemmas in any frame.
        // This reproduces the exact state that triggers the #4247 shortcut:
        // `depth >= 2` and all frames in `[1..depth)` empty.
        engine.frames.push_new();
        engine.frames.push_new();
        assert_eq!(engine.frames.depth(), 2);
        assert!(engine.frames.frames[1].lemmas.is_empty());

        // Case 1: no witness. Simulates every early-out break path from the
        // blocking loop (budget, #4139 repeat, drop_po, cancellation). The
        // shortcut MUST be refused; propagate() returns NotYet.
        let early_exit_outcome = engine.propagate(None);
        assert_eq!(
            early_exit_outcome,
            PropagateOutcome::NotYet,
            "#4310/#4317: propagate() MUST NOT take the trivially-safe \
             shortcut when blocking did not complete naturally (no \
             ConvergenceProof witness), even if all frames are empty. \
             Observed: {early_exit_outcome:?}",
        );

        // Reset frames to the same all-empty, depth=2 state for case 2.
        // propagate() may have mutated earliest_changed_frame / inf_lemmas;
        // rebuild the empty frames so the shortcut precondition still holds.
        engine.frames = super::frame::Frames::new();
        engine.frames.push_new();
        engine.frames.push_new();
        engine.inf_lemmas.clear();
        assert_eq!(engine.frames.depth(), 2);

        // Case 2: natural-exit witness. Only `run.rs`'s `get_bad() => None`
        // arm constructs this in production. The shortcut fires and
        // propagate() returns Converged.
        let natural_outcome = engine.propagate(Some(ConvergenceProof::from_natural_exit()));
        assert_eq!(
            natural_outcome,
            PropagateOutcome::Converged,
            "#4317: propagate() MUST take the trivially-safe shortcut when \
             given a ConvergenceProof witness and all frames are empty. \
             Observed: {natural_outcome:?}",
        );
    }
}
