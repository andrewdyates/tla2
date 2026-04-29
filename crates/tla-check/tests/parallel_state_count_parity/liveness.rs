// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Liveness parity tests for parallel vs sequential checking (#2740, #3327).

use super::*;

/// Helper: run both sequential and parallel checkers with liveness properties
/// and assert result-kind + state-count parity.
fn assert_liveness_parity(
    case_name: &str,
    src: &str,
    spec_name: &str,
    properties: Vec<String>,
    workers: usize,
    expected_states: usize,
    expect_violation: bool,
) {
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.expect("failed to parse module");

    // Resolve SPECIFICATION to extract Init/Next/fairness
    let spec_config = Config {
        specification: Some(spec_name.to_string()),
        ..Default::default()
    };
    let resolved = resolve_spec_from_config(&spec_config, &tree)
        .unwrap_or_else(|e| panic!("{case_name}: failed to resolve spec: {e:?}"));

    let config = Config {
        init: Some(resolved.init.clone()),
        next: Some(resolved.next.clone()),
        properties,
        check_deadlock: false,
        ..Default::default()
    };

    // Sequential — liveness checking requires full state storage
    let mut seq_checker = ModelChecker::new(&module, &config);
    seq_checker.set_deadlock_check(false);
    seq_checker.set_store_states(true);
    seq_checker.set_fairness(resolved.fairness.clone());
    let seq_result = seq_checker.check();
    let seq_stats = stats(&seq_result);

    assert_eq!(
        seq_stats.states_found, expected_states,
        "{case_name}: sequential states_found mismatch"
    );

    // Verify the sequential result matches the expected outcome kind.
    // This prevents false negatives where both checkers silently return Success
    // for specs that should produce LivenessViolation (see #3327).
    if expect_violation {
        assert!(
            matches!(seq_result, CheckResult::LivenessViolation { .. }),
            "{case_name}: expected LivenessViolation from sequential checker, got: {seq_result:?}"
        );
    } else {
        assert!(
            matches!(seq_result, CheckResult::Success(_)),
            "{case_name}: expected Success from sequential checker, got: {seq_result:?}"
        );
    }

    // Parallel (test with both handle_state modes)
    for use_handle_state in [false, true] {
        let _guard = set_use_handle_state_override(use_handle_state);

        let mut par_checker = ParallelChecker::new(&module, &config, workers);
        par_checker.set_deadlock_check(false);
        par_checker.set_store_states(true);
        par_checker.set_fairness(resolved.fairness.clone());
        let par_result = par_checker.check();
        let par_stats = stats(&par_result);

        assert_result_kind_parity(case_name, use_handle_state, &seq_result, &par_result);
        assert_eq!(
            seq_stats.states_found, par_stats.states_found,
            "{case_name}: states_found mismatch (handle_state={use_handle_state})"
        );
        assert_eq!(
            seq_stats.initial_states, par_stats.initial_states,
            "{case_name}: initial_states mismatch (handle_state={use_handle_state})"
        );
    }
}

/// Part of #2740: End-to-end parity test for liveness checking between
/// sequential and parallel modes.
///
/// SystemLoop spec (Manna & Pnueli): x cycles 0→1→2→3→0 with 4 states.
/// - Without fairness (`Spec`): stuttering allowed, `[]<>(x=3)` FAILS
/// - With weak fairness (`SpecWeakFair`): stuttering prevented, `[]<>(x=3)` PASSES
///
/// This is the acceptance criterion for #2740: at least one spec with temporal
/// properties verified in parallel mode matches single-threaded results.
#[cfg_attr(test, ntest::timeout(60000))]
#[test]
fn test_parallel_sequential_liveness_parity() {
    let _scope = ParityTestScope::begin();
    let src = r#"
---- MODULE SystemLoopParity ----
VARIABLES x
vars == <<x>>

Init == x = 0

One == x = 0 /\ x' = 1
Two == x = 1 /\ x' = 2
Three == x = 2 /\ x' = 3
Back == x = 3 /\ x' = 0

Next == One \/ Two \/ Three \/ Back

(* Without fairness - allows stuttering, liveness should FAIL *)
Spec == Init /\ [][Next]_vars

(* With weak fairness - prevents stuttering, liveness should PASS *)
SpecWeakFair == Spec /\ WF_vars(Next)

(* Liveness property: x will infinitely often be 3 *)
Liveness == []<>(x=3)

====
"#;

    // Case 1: No fairness → liveness violation in both modes
    for workers in [2, 4] {
        assert_liveness_parity(
            &format!("system_loop_no_fair_{workers}w"),
            src,
            "Spec",
            vec!["Liveness".to_string()],
            workers,
            4,    // x ∈ {0,1,2,3}
            true, // expect LivenessViolation
        );
    }

    // Case 2: Weak fairness → liveness satisfied in both modes
    for workers in [2, 4] {
        assert_liveness_parity(
            &format!("system_loop_fair_{workers}w"),
            src,
            "SpecWeakFair",
            vec!["Liveness".to_string()],
            workers,
            4,     // x ∈ {0,1,2,3}
            false, // expect Success
        );
    }
}

/// Part of #2740: Parity test with eventually-always pattern `<>[](x=2)`.
/// The spec has x going 0→1→2→stuck, so `<>[](x=2)` is satisfied (x=2 is
/// an absorbing state). Both sequential and parallel should report Success.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_parallel_sequential_eventually_always_parity() {
    let _scope = ParityTestScope::begin();
    let src = r#"
---- MODULE EventuallyAlwaysParity ----
EXTENDS Integers
VARIABLE x
vars == <<x>>

Init == x = 0
Next == IF x < 2 THEN x' = x + 1 ELSE UNCHANGED x

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Prop == <>[](x = 2)

====
"#;

    for workers in [2, 4] {
        assert_liveness_parity(
            &format!("eventually_always_{workers}w"),
            src,
            "Spec",
            vec!["Prop".to_string()],
            workers,
            3,     // x ∈ {0,1,2}
            false, // expect Success
        );
    }
}

/// Part of #3327: Verify the fp-only liveness path (store_full_states=false)
/// produces the same results as the full-state path. This exercises the
/// `build_fp_only_liveness_cache` code path in the parallel checker, which
/// replays BFS from cached fingerprint data rather than using stored ArrayStates.
///
/// The #3327 fix ensures the `successors` DashMap is keyed by value-based FPs
/// (from ArrayState::fingerprint), not handle-based FPs. Both store_full_states
/// and fp-only liveness depend on this: the successors map must use FPs
/// consistent with the state cache. Without the fix, fp-only liveness would
/// silently produce disconnected graphs and miss violations.
#[cfg_attr(test, ntest::timeout(60000))]
#[test]
fn test_parallel_liveness_fp_only_parity() {
    let _scope = ParityTestScope::begin();
    let src = r#"
---- MODULE FpOnlyLivenessParity ----
VARIABLES x
vars == <<x>>

Init == x = 0

One == x = 0 /\ x' = 1
Two == x = 1 /\ x' = 2
Three == x = 2 /\ x' = 3
Back == x = 3 /\ x' = 0

Next == One \/ Two \/ Three \/ Back

(* Without fairness - stuttering allowed, liveness should FAIL *)
Spec == Init /\ [][Next]_vars

(* Liveness property: x will infinitely often be 3 *)
Liveness == []<>(x=3)

====
"#;

    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.expect("failed to parse module");

    let spec_config = Config {
        specification: Some("Spec".to_string()),
        ..Default::default()
    };
    let resolved = resolve_spec_from_config(&spec_config, &tree)
        .unwrap_or_else(|e| panic!("failed to resolve spec: {e:?}"));

    let config = Config {
        init: Some(resolved.init.clone()),
        next: Some(resolved.next.clone()),
        properties: vec!["Liveness".to_string()],
        check_deadlock: false,
        ..Default::default()
    };

    // Sequential baseline with full state storage
    let mut seq_checker = ModelChecker::new(&module, &config);
    seq_checker.set_deadlock_check(false);
    seq_checker.set_store_states(true);
    seq_checker.set_fairness(resolved.fairness.clone());
    let seq_result = seq_checker.check();
    assert!(
        matches!(seq_result, CheckResult::LivenessViolation { .. }),
        "sequential should detect liveness violation, got: {seq_result:?}"
    );

    // Parallel WITHOUT store_full_states — exercises fp-only liveness path
    for use_handle_state in [false, true] {
        let _guard = set_use_handle_state_override(use_handle_state);

        let mut par_checker = ParallelChecker::new(&module, &config, 2);
        par_checker.set_deadlock_check(false);
        // Deliberately NOT calling set_store_states(true) to exercise fp-only path
        par_checker.set_fairness(resolved.fairness.clone());
        let par_result = par_checker.check();

        assert!(
            matches!(par_result, CheckResult::LivenessViolation { .. }),
            "fp-only parallel (handle_state={use_handle_state}) should detect liveness violation, got: {par_result:?}"
        );
    }
}
