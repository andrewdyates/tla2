// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Fairness conjunction tests — WF/SF constraint handling in parallel liveness checking

use super::*;

/// Part of #2740: Verify that the parallel checker detects a liveness violation
/// when there is NO fairness constraint and stuttering is allowed. This is the
/// control case for `test_parallel_liveness_fairness_conjunction_passes`.
///
/// Spec: x cycles 0→1→2→3→0..., but `[Next]_vars` allows stuttering.
/// Without WF_vars(Next), the system can stutter forever, violating `[]<>(x=3)`.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_parallel_liveness_no_fairness_detects_violation() {
    let _serial = super::acquire_interner_lock();
    let src = r#"
---- MODULE ParallelNoFair ----

VARIABLE x
vars == <<x>>

Init == x = 0

One == x = 0 /\ x' = 1
Two == x = 1 /\ x' = 2
Three == x = 2 /\ x' = 3
Back == x = 3 /\ x' = 0

Next == One \/ Two \/ Three \/ Back

Spec == Init /\ [][Next]_vars

Liveness == []<>(x = 3)

===="#;
    let tree = tla_core::parse_to_syntax_tree(src);
    let lower_result = tla_core::lower(tla_core::FileId(0), &tree);
    let module = lower_result.module.unwrap();

    // Resolve SPECIFICATION to get stuttering_allowed (no fairness)
    let spec_config = Config {
        specification: Some("Spec".to_string()),
        ..Default::default()
    };
    let resolved = crate::check::resolve_spec_from_config(&spec_config, &tree).unwrap();
    assert!(resolved.stuttering_allowed);
    assert!(resolved.fairness.is_empty(), "No fairness for Spec");

    let config = Config {
        init: Some(resolved.init.clone()),
        next: Some(resolved.next.clone()),
        properties: vec!["Liveness".to_string()],
        ..Default::default()
    };

    let checker = ParallelChecker::new(&module, &config, 2);
    let result = checker.check();

    match result {
        CheckResult::LivenessViolation { property, .. } => {
            assert_eq!(property, "Liveness");
        }
        other => panic!(
            "Expected LivenessViolation without fairness, got: {:?}",
            other
        ),
    }
}

/// Part of #2740: Verify that the parallel checker correctly conjoins fairness
/// constraints with the negated property during post-BFS liveness checking.
///
/// Same spec as `test_parallel_liveness_no_fairness_detects_violation`, but with
/// `WF_vars(Next)` added to the SPECIFICATION. Weak fairness prevents infinite
/// stuttering, so `[]<>(x=3)` is satisfied because the system always eventually
/// makes progress through the 0→1→2→3→0 cycle.
///
/// This test exercises the `fairness_to_live_expr` → conjunction → `push_negation`
/// pipeline in the parallel checker's `check_single_property()`.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_parallel_liveness_fairness_conjunction_passes() {
    let _serial = super::acquire_interner_lock();
    let src = r#"
---- MODULE ParallelFair ----

VARIABLE x
vars == <<x>>

Init == x = 0

One == x = 0 /\ x' = 1
Two == x = 1 /\ x' = 2
Three == x = 2 /\ x' = 3
Back == x = 3 /\ x' = 0

Next == One \/ Two \/ Three \/ Back

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Liveness == []<>(x = 3)

===="#;
    let tree = tla_core::parse_to_syntax_tree(src);
    let lower_result = tla_core::lower(tla_core::FileId(0), &tree);
    let module = lower_result.module.unwrap();

    // Resolve SPECIFICATION to get stuttering_allowed + fairness
    let spec_config = Config {
        specification: Some("Spec".to_string()),
        ..Default::default()
    };
    let resolved = crate::check::resolve_spec_from_config(&spec_config, &tree).unwrap();
    assert!(resolved.stuttering_allowed);
    assert_eq!(resolved.fairness.len(), 1, "Should have WF_vars(Next)");

    let config = Config {
        init: Some(resolved.init.clone()),
        next: Some(resolved.next.clone()),
        properties: vec!["Liveness".to_string()],
        ..Default::default()
    };

    let mut checker = ParallelChecker::new(&module, &config, 2);
    checker.set_fairness(resolved.fairness);
    let result = checker.check();

    match result {
        CheckResult::Success(stats) => {
            assert_eq!(stats.states_found, 4, "4 states: x=0, x=1, x=2, x=3");
        }
        CheckResult::LivenessViolation { .. } => {
            panic!(
                "Liveness should be satisfied with WF_vars(Next) — \
                 fairness conjunction not working in parallel checker"
            );
        }
        other => panic!("Unexpected result: {:?}", other),
    }
}

/// Part of #2762: Verify that `<<Next>>_vars` (angle-bracket subscript) correctly
/// sets `stuttering_allowed=false` in the parallel checker.
///
/// With `<<Next>>_vars`, no stuttering self-loops should be injected into the
/// behavior graph. The spec cycles 0->1->2->3->0->..., so `[]<>(x=3)` is
/// satisfied because every infinite behavior visits x=3 infinitely often.
///
/// If stuttering_allowed were hardcoded to true (the bug), self-loops would be
/// injected and infinite stuttering at x=0 would violate `[]<>(x=3)`.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_parallel_liveness_angle_bracket_no_stuttering() {
    let _serial = super::acquire_interner_lock();
    let src = r#"
---- MODULE ParallelAngleBracket ----

VARIABLE x
vars == <<x>>

Init == x = 0

One == x = 0 /\ x' = 1
Two == x = 1 /\ x' = 2
Three == x = 2 /\ x' = 3
Back == x = 3 /\ x' = 0

Next == One \/ Two \/ Three \/ Back

Spec == Init /\ []<<Next>>_vars

Liveness == []<>(x = 3)

===="#;
    let tree = tla_core::parse_to_syntax_tree(src);
    let lower_result = tla_core::lower(tla_core::FileId(0), &tree);
    let module = lower_result.module.unwrap();

    // Resolve SPECIFICATION to get stuttering_allowed flag
    let spec_config = Config {
        specification: Some("Spec".to_string()),
        ..Default::default()
    };
    let resolved = crate::check::resolve_spec_from_config(&spec_config, &tree).unwrap();
    assert!(
        !resolved.stuttering_allowed,
        "<<Next>>_vars should set stuttering_allowed=false"
    );

    let config = Config {
        init: Some(resolved.init.clone()),
        next: Some(resolved.next.clone()),
        properties: vec!["Liveness".to_string()],
        ..Default::default()
    };

    let mut checker = ParallelChecker::new(&module, &config, 2);
    checker.set_stuttering_allowed(resolved.stuttering_allowed);
    checker.set_deadlock_check(false);
    let result = checker.check();

    match result {
        CheckResult::Success(stats) => {
            assert_eq!(stats.states_found, 4, "4 states: x=0, x=1, x=2, x=3");
        }
        CheckResult::LivenessViolation { .. } => {
            panic!(
                "<<Next>>_vars forbids stuttering — no self-loops should be injected. \
                 Liveness []<>(x=3) should pass because the only infinite behavior is the \
                 cycle 0->1->2->3->0->... which visits x=3 infinitely often."
            );
        }
        other => panic!("Unexpected result: {:?}", other),
    }
}
