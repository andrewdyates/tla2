// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for the adaptive model checker.
//! Extracted from adaptive.rs for file size compliance (Part of #3389).

use super::*;
use crate::error::EvalError;
use crate::test_support::parse_module;
use crate::EvalCheckError;
use crate::LivenessCheckError;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_adaptive_pilot_applies_cfg_module_assignments() {
    let _serial = crate::test_utils::acquire_interner_lock();
    // Regression test for #806: adaptive pilot must apply cfg-scoped module assignments
    // consistently with the sequential/parallel checkers.
    let inst_src = r#"
---- MODULE Inst ----
NoHash == CHOOSE h : TRUE
====
"#;
    let main_src = r#"
---- MODULE Main ----
VARIABLE x
I == INSTANCE Inst
Init == x = I!NoHash
Next == FALSE
Valid == x = h1
====
"#;

    let inst_module = parse_module(inst_src);
    let main_module = parse_module(main_src);

    let mut module_assignments = std::collections::HashMap::new();
    module_assignments.insert(
        "Inst".to_string(),
        std::collections::HashMap::from([("NoHash".to_string(), "h1".to_string())]),
    );

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Valid".to_string()],
        module_assignments,
        ..Default::default()
    };

    let mut checker = AdaptiveChecker::new_with_extends(&main_module, &[&inst_module], &config);
    checker.set_deadlock_check(false);

    let (result, _analysis) = checker.check();
    assert!(matches!(result, CheckResult::Success(_)), "{:?}", result);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_adaptive_small_spec_uses_sequential() {
    let _serial = crate::test_utils::acquire_interner_lock();
    // Part of #617: A spec with low branching factor (b ≈ 1) now conservatively
    // estimates large state space to handle deep counters. To trigger Sequential,
    // we need a spec with very low branching factor (b < 0.5), i.e., mostly
    // terminal states or UNCHANGED behavior.
    //
    // This test uses a "one-shot" spec: many initial states, no transitions.
    // branching_factor ≈ 0, so estimate = initial * 10 = 1000 < PARALLEL_THRESHOLD.
    let src = r#"
---- MODULE OneShot ----
VARIABLE x
Init == x \in 1..100
Next == FALSE
InRange == x >= 1 /\ x <= 100
====
"#;
    let module = parse_module(src);

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["InRange".to_string()],
        ..Default::default()
    };

    let mut checker = AdaptiveChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    let (result, analysis) = checker.check();

    assert!(matches!(result, CheckResult::Success(_)));

    let analysis = analysis.unwrap();
    assert_eq!(analysis.initial_states, 100);
    // Very low branching (b < 0.5) should choose sequential
    // estimate = 100 * 10 = 1000 < PARALLEL_THRESHOLD
    assert!(
        matches!(analysis.strategy, Strategy::Sequential),
        "Expected Sequential for one-shot spec with no transitions, got {:?}",
        analysis.strategy
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_adaptive_larger_spec_uses_parallel() {
    let _serial = crate::test_utils::acquire_interner_lock();
    // Spec with many initial states should use parallel
    let src = r#"
---- MODULE LargerSpec ----
VARIABLE x, y, z
Init == x \in {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}
     /\ y \in {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}
     /\ z \in {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}
Next == x' \in {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}
     /\ y' \in {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}
     /\ z' \in {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}
Valid == TRUE
====
"#;
    let module = parse_module(src);

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Valid".to_string()],
        ..Default::default()
    };

    let mut checker = AdaptiveChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    checker.set_max_states(100); // Limit to avoid long test

    let (_result, analysis) = checker.check();

    let analysis = analysis.unwrap();
    // 10 * 10 * 10 = 1000 initial states
    assert_eq!(analysis.initial_states, 1000);
    // Large initial state count with high branching should use parallel
    assert!(
        matches!(analysis.strategy, Strategy::Parallel(_)),
        "Expected Parallel for large spec, got {:?}",
        analysis.strategy
    );
}

/// Part of #3706: Verify POR is accepted in adaptive mode.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_adaptive_por_is_accepted() {
    let _serial = crate::test_utils::acquire_interner_lock();
    let src = r#"
---- MODULE AdaptivePor ----
VARIABLE x, y, z
Init == x \in {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}
     /\ y \in {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}
     /\ z \in {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}
Next == x' \in {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}
     /\ y' \in {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}
     /\ z' \in {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}
Valid == TRUE
====
"#;
    let module = parse_module(src);

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Valid".to_string()],
        por_enabled: true,
        ..Default::default()
    };

    let mut checker = AdaptiveChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    checker.set_max_states(100);

    let (result, _analysis) = checker.check();
    match &result {
        CheckResult::Success { .. } | CheckResult::LimitReached { .. } => {
            // POR is accepted — adaptive checker proceeds normally
        }
        other => panic!("AdaptiveChecker should accept POR (Part of #3706), got: {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_adaptive_liveness_properties_force_sequential_path() {
    let _serial = crate::test_utils::acquire_interner_lock();
    let src = r#"
---- MODULE AdaptiveLiveness ----
VARIABLE x
Init == x = 0
Next == x' = x
Prop == <>TRUE
====
"#;
    let module = parse_module(src);

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["Prop".to_string()],
        ..Default::default()
    };

    let mut checker = AdaptiveChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    let (result, analysis) = checker.check();
    let analysis = analysis.expect("adaptive check should return pilot analysis");
    // Part of #3175: ParallelChecker now supports liveness checking in both
    // full-state and fp-only modes. Liveness no longer forces sequential.
    assert!(
        matches!(
            analysis.strategy,
            Strategy::Parallel(_) | Strategy::Sequential
        ),
        "Liveness with small spec can use either strategy, got {:?}",
        analysis.strategy
    );

    match result {
        CheckResult::Error {
            error: CheckError::Liveness(LivenessCheckError::FormulaTautology { .. }),
            ..
        } => {}
        other => panic!("Expected liveness tautology error, got: {:?}", other),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_adaptive_no_trace_propagates_to_parallel_checker() {
    let _serial = crate::test_utils::acquire_interner_lock();
    // Ensure store_full_states=false is passed through when strategy selects Parallel.
    let src = r#"
---- MODULE NoTraceParallel ----
VARIABLE x
Init == x \in 0 .. 999
Next == x' \in 0 .. 1000
Safe == x < 1000
====
"#;
    let module = parse_module(src);

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Safe".to_string()],
        ..Default::default()
    };

    let mut checker = AdaptiveChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    checker.set_store_states(false);
    checker.set_max_depth(1);

    let (result, analysis) = checker.check();

    let analysis = analysis.unwrap();
    assert!(
        matches!(analysis.strategy, Strategy::Parallel(_)),
        "Expected Parallel for no-trace propagation test, got {:?}",
        analysis.strategy
    );

    match result {
        CheckResult::InvariantViolation { trace, .. } => {
            assert!(trace.is_empty(), "Trace should be empty in no-trace mode");
        }
        other => panic!("Expected invariant violation, got: {:?}", other),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_adaptive_parallel_preserves_invariant_eval_error() {
    let _serial = crate::test_utils::acquire_interner_lock();
    // Regression coverage for parallel invariant evaluation errors when using
    // adaptive (auto) strategy selection.
    //
    // TLC errors when attempting to enumerate a non-enumerable function set.
    //
    // NOTE: This is a b≈1 spec (stuttering Next). The adaptive heuristic treats b<1.5 as
    // potentially very deep (linear growth), so it should select parallel mode even though
    // the reachable state space here is tiny.
    let src = r#"
---- MODULE FuncSetEmptyEquality ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = x
Inv == [Nat -> Nat] = {}
====
"#;
    let module = parse_module(src);

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Inv".to_string()],
        ..Default::default()
    };

    let mut checker = AdaptiveChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    checker.set_max_depth(0);

    let (result, analysis) = checker.check();
    let analysis = analysis.expect("expected PilotAnalysis for adaptive check");

    assert!(
        matches!(analysis.strategy, Strategy::Parallel(_)),
        "Expected Parallel strategy for b≈1 spec, got {:?} (estimate={}, b={:.3}, sampled={})",
        analysis.strategy,
        analysis.estimated_states,
        analysis.avg_branching_factor,
        analysis.states_sampled
    );

    match result {
        CheckResult::Error { error, .. } => match error {
            CheckError::Eval(EvalCheckError::Eval(EvalError::SetTooLarge { .. })) => {}
            other => panic!("expected SetTooLarge EvalError, got: {other:?}"),
        },
        other => panic!("expected Error, got: {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pilot_analysis_branching_factor() {
    // Test branching factor calculation
    let src = r#"
---- MODULE Branching ----
VARIABLE x
Init == x = 0
Next == x' \in {x + 1, x + 2, x + 3}
Valid == TRUE
====
"#;
    let module = parse_module(src);

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Valid".to_string()],
        ..Default::default()
    };

    let mut checker = AdaptiveChecker::new(&module, &config);
    let analysis = checker.run_pilot().unwrap();

    // Each state has 3 successors
    assert!(
        analysis.avg_branching_factor >= 2.5,
        "Expected branching factor >= 2.5, got {}",
        analysis.avg_branching_factor
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pilot_does_not_hang_on_operator_call_in_guard() {
    let _serial = crate::test_utils::acquire_interner_lock();
    // Regression for #409: auto mode pilot phase used state-based enumeration and could hang.
    // This spec is tiny (4 states) and must be sampled quickly.
    //
    // Part of #409: Run in a thread with larger stack (8MB) to handle recursive operator
    // compilation in debug builds where stack frames are larger.
    std::thread::Builder::new()
        .stack_size(8 * 1024 * 1024)
        .spawn(|| {
            let src = r#"
---- MODULE Test409Pilot ----
EXTENDS Integers

RECURSIVE And(_, _, _, _)
And(x, y, n, m) ==
    LET exp == 2^n
    IN IF m = 0 THEN 0
       ELSE exp * ((x \div exp) % 2) * ((y \div exp) % 2)
            + And(x, y, n+1, m \div 2)

x & y == And(x, y, 0, x)

HasBit(val, bit) == (val & bit) = bit

VARIABLE x
Init == x = 0
Next == \E v \in {1, 2, 3}:
          /\ HasBit(7, v)
          /\ x' = v
====
"#;
            let module = parse_module(src);
            let config = Config {
                init: Some("Init".to_string()),
                next: Some("Next".to_string()),
                ..Default::default()
            };
            let mut checker = AdaptiveChecker::new(&module, &config);
            checker.set_deadlock_check(false);

            let analysis = checker.run_pilot().unwrap();
            assert_eq!(analysis.initial_states, 1);
            assert!(
                analysis.avg_branching_factor >= 2.5,
                "Expected branching factor >= 2.5, got {}",
                analysis.avg_branching_factor
            );
        })
        .unwrap()
        .join()
        .unwrap();
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_adaptive_consistency_with_direct_checkers() {
    let _serial = crate::test_utils::acquire_interner_lock();
    // Adaptive should produce same results as direct checkers
    let src = r#"
---- MODULE Consistency ----
VARIABLE x, y
Init == x \in {0, 1} /\ y \in {0, 1}
Next == x' \in {0, 1} /\ y' \in {0, 1}
Valid == x + y < 3
====
"#;
    let module = parse_module(src);

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Valid".to_string()],
        ..Default::default()
    };

    // Run sequential
    let mut seq_checker = ModelChecker::new(&module, &config);
    seq_checker.set_deadlock_check(false);
    let seq_result = seq_checker.check();

    // Run adaptive
    let mut adaptive_checker = AdaptiveChecker::new(&module, &config);
    adaptive_checker.set_deadlock_check(false);
    let (adaptive_result, _) = adaptive_checker.check();

    // Both should succeed with same state count
    match (seq_result, adaptive_result) {
        (CheckResult::Success(seq_stats), CheckResult::Success(adaptive_stats)) => {
            assert_eq!(seq_stats.states_found, adaptive_stats.states_found);
            assert_eq!(seq_stats.initial_states, adaptive_stats.initial_states);
        }
        (seq, adaptive) => panic!("Results differ: seq={:?}, adaptive={:?}", seq, adaptive),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_adaptive_typeok_fallback() {
    let _serial = crate::test_utils::acquire_interner_lock();
    // Test that adaptive mode falls back to TypeOK when Init uses unsupported expressions.
    // This pattern occurs in specs where Init = Inv = TypeOK /\ IInv.
    let src = r#"
---- MODULE TypeOKFallback ----
VARIABLES x, y

TypeOK == x \in {0, 1, 2} /\ y \in {0, 1}

(* IInv has a nested IF expression that cannot be directly extracted *)
IInv == IF x = 0 THEN y = 0 ELSE TRUE

(* Init uses conjunction with unsupported expression *)
Inv == TypeOK /\ IInv

Init == Inv

Next == x' \in {0, 1, 2} /\ y' \in {0, 1}
====
"#;
    let module = parse_module(src);

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TypeOK".to_string()],
        ..Default::default()
    };

    let mut checker = AdaptiveChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    // This should succeed by falling back to TypeOK enumeration + filtering
    let (result, analysis) = checker.check();

    assert!(
        matches!(result, CheckResult::Success(_)),
        "Expected success with TypeOK fallback, got {:?}",
        result
    );

    let analysis = analysis.unwrap();
    // TypeOK gives 3*2=6 states, but IInv filters when x=0 to require y=0
    // When x=0: only y=0 is valid (1 state)
    // When x=1,2: y can be 0 or 1 (4 states)
    // Total: 5 initial states
    assert_eq!(
        analysis.initial_states, 5,
        "Expected 5 initial states after filtering by IInv"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_adaptive_allows_assume_only_models_without_init_next() {
    let _serial = crate::test_utils::acquire_interner_lock();
    let src = r#"
---- MODULE AssumeOnly ----
ASSUME TRUE
====
"#;
    let module = parse_module(src);
    let config = Config::default();

    let mut checker = AdaptiveChecker::new(&module, &config);
    let (result, analysis) = checker.check();

    match &result {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 0,
                "ASSUME-only model with no Init/Next should have 0 states"
            );
        }
        other => panic!("expected Success for ASSUME-only model, got: {other:?}"),
    }
    assert!(analysis.is_some());
    assert!(matches!(analysis.unwrap().strategy, Strategy::Sequential));
}
