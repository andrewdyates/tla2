// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Part of #2291: `[Next]_vars` stuttering flag must be consumed by liveness checker.
///
/// Without fairness, `[Next]_vars` allows infinite stuttering. The liveness property
/// `[]<>(x=3)` is violated because the system can stutter forever at any state.
/// TLC detects this via a stuttering counterexample. TLA2 must match.
///
/// Prior to the fix, `stuttering_allowed` was parsed but never consumed — the liveness
/// checker only injected stuttering self-loops when `config.specification.is_none()`,
/// missing the dominant SPECIFICATION-based `[Next]_vars` case.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_liveness_stuttering_no_fairness_detects_violation() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // SystemLoop without fairness: stuttering is allowed, liveness MUST fail
    let src = r#"
---- MODULE StutterNoFair ----

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
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    // Resolve SPECIFICATION to get stuttering_allowed flag
    let spec_config = Config {
        specification: Some("Spec".to_string()),
        ..Default::default()
    };
    let resolved = resolve_spec_from_config(&spec_config, &tree).unwrap();
    assert!(
        resolved.stuttering_allowed,
        "[Next]_vars should set stuttering_allowed=true"
    );
    assert!(
        resolved.fairness.is_empty(),
        "No fairness for Spec (no WF/SF)"
    );

    // Create checker with explicit init/next and set stuttering_allowed from resolved spec
    let config = Config {
        init: Some(resolved.init.clone()),
        next: Some(resolved.next.clone()),
        properties: vec!["Liveness".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    checker.set_stuttering_allowed(resolved.stuttering_allowed);
    // Liveness checking requires full state storage (not fingerprint-only mode)
    checker.set_store_states(true);

    let result = checker.check();

    match result {
        CheckResult::LivenessViolation { .. } => {
            // Correct: liveness violation detected via stuttering
        }
        CheckResult::Success(stats) => {
            panic!(
                "Expected LivenessViolation (stuttering allows infinite stall), \
                 but got Success with {} states. The stuttering_allowed flag is \
                 not being consumed by the liveness checker.",
                stats.states_found
            );
        }
        other => panic!("Unexpected result: {:?}", other),
    }
}

/// Part of #2291: `[Next]_vars` with WF_vars(Next) should still pass liveness.
///
/// This is the control case for `test_liveness_stuttering_no_fairness_detects_violation`.
/// With weak fairness, stuttering is prevented and `[]<>(x=3)` is satisfied.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_liveness_stuttering_with_fairness_passes() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    let src = r#"
---- MODULE StutterFair ----

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
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    // Resolve SPECIFICATION to get stuttering_allowed + fairness
    let spec_config = Config {
        specification: Some("Spec".to_string()),
        ..Default::default()
    };
    let resolved = resolve_spec_from_config(&spec_config, &tree).unwrap();
    assert!(resolved.stuttering_allowed);
    assert_eq!(resolved.fairness.len(), 1, "Should have WF_vars(Next)");

    let config = Config {
        init: Some(resolved.init.clone()),
        next: Some(resolved.next.clone()),
        properties: vec!["Liveness".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    checker.set_stuttering_allowed(resolved.stuttering_allowed);
    checker.set_fairness(resolved.fairness);
    // Liveness checking requires full state storage (not fingerprint-only mode)
    checker.set_store_states(true);

    let result = checker.check();

    match result {
        CheckResult::Success(stats) => {
            assert_eq!(stats.states_found, 4, "4 states: x=0, x=1, x=2, x=3");
        }
        CheckResult::LivenessViolation { .. } => {
            panic!("Liveness should be satisfied with weak fairness (no stuttering)");
        }
        other => panic!("Unexpected result: {:?}", other),
    }
}

/// Part of #2291: `<<Next>>_vars` (stuttering forbidden) should NOT inject self-loops.
///
/// When stuttering is forbidden (angle-bracket form), the liveness checker must NOT
/// inject self-loop edges. This is the opposite polarity of
/// `test_liveness_stuttering_no_fairness_detects_violation`. With `<<Next>>_vars`,
/// the system MUST make progress at every step, so infinite stuttering is impossible.
/// Liveness `[]<>(x = 3)` should PASS even without fairness because the cycle
/// (0->1->2->3->0->...) is the only infinite behavior.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_liveness_stuttering_forbidden_no_self_loops() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Same cycle spec as the stuttering tests, but using <<Next>>_vars.
    // Without self-loops, the only infinite behavior is the cycle 0->1->2->3->0->...
    // which visits x=3 infinitely often, satisfying []<>(x=3).
    let src = r#"
---- MODULE StutterForbidden ----

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
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    // Resolve SPECIFICATION to get stuttering_allowed flag
    let spec_config = Config {
        specification: Some("Spec".to_string()),
        ..Default::default()
    };
    let resolved = resolve_spec_from_config(&spec_config, &tree).unwrap();
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

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    checker.set_stuttering_allowed(resolved.stuttering_allowed);
    checker.set_store_states(true);

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
