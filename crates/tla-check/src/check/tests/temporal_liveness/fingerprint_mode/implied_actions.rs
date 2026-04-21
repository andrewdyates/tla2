// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Part of #2670: `[][Bad]_vars` violations still surface in fingerprint-only mode.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_implied_action_violation_detected_in_fingerprint_only_mode() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Next increments x, but the property requires [][UNCHANGED x]_vars.
    // The transition x=0 -> x=1 violates the implied action.
    let src = r#"
---- MODULE ImpliedActionFpOnly ----
EXTENDS Integers

VARIABLE x
vars == <<x>>

Init == x = 0

Next == IF x < 2 THEN x' = x + 1 ELSE UNCHANGED x

Bad == UNCHANGED x
SpecProp == [][Bad]_vars
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec![],
        properties: vec!["SpecProp".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    // Do NOT call set_store_states(true) — stay in fingerprint-only mode (default).
    // Before #2670, this would return Success. After #2670, InvariantViolation.

    let result = checker.check();
    match result {
        // Part of #2834: implied action violations from PROPERTIES are correctly
        // reported as PropertyViolation.
        CheckResult::PropertyViolation {
            property,
            trace: _,
            stats: _,
            kind: _,
        } => {
            assert_eq!(property, "SpecProp");
        }
        CheckResult::Success(_) => {
            panic!(
                "Implied action violation should be detected in fingerprint-only mode. \
                 Got Success, meaning the [][Bad]_vars check was silently skipped."
            );
        }
        other => panic!(
            "Expected PropertyViolation for implied action, got: {:?}",
            other
        ),
    }
}

/// Part of #2670: implied actions are checked even on transitions to seen states.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_implied_action_checked_for_seen_state_transitions() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // x toggles between 0 and 1. The property forbids x changing (UNCHANGED x).
    // The first transition (x=0->x=1) is to a new state and should be caught.
    let src = r#"
---- MODULE ImpliedActionSeen ----
EXTENDS Integers

VARIABLE x
vars == <<x>>

Init == x \in {0, 1}

Next == x' = 1 - x

Bad == UNCHANGED x
NeverChange == [][Bad]_vars
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec![],
        properties: vec!["NeverChange".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    let result = checker.check();
    match result {
        // Part of #2834: implied action violations from PROPERTIES are correctly
        // reported as PropertyViolation.
        CheckResult::PropertyViolation { property, .. } => {
            assert_eq!(property, "NeverChange");
        }
        other => panic!("Expected PropertyViolation, got: {:?}", other),
    }
}

/// Part of #2670: fully promoted action properties are omitted from the warning.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_fingerprint_warning_excludes_promoted_action_properties() {
    let config = Config {
        properties: vec!["ActionProp".to_string(), "TemporalProp".to_string()],
        ..Default::default()
    };

    // ActionProp is promoted (appears in promoted_names).
    // TemporalProp is not promoted (remains in warning).
    let promoted = vec!["ActionProp".to_string()];
    let warning = config
        .fingerprint_liveness_warning(false, &promoted)
        .expect("warning should exist for non-promoted temporal property");
    assert!(
        !warning.contains("ActionProp"),
        "Warning should not mention promoted action property: {warning}"
    );
    assert!(
        warning.contains("TemporalProp"),
        "Warning should mention non-promoted temporal property: {warning}"
    );
}

/// Part of #2670: No warning when all properties are fully promoted.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_fingerprint_warning_absent_when_all_promoted() {
    let config = Config {
        properties: vec!["ActionProp".to_string()],
        ..Default::default()
    };

    let promoted = vec!["ActionProp".to_string()];
    assert!(
        config
            .fingerprint_liveness_warning(false, &promoted)
            .is_none(),
        "No warning when all properties are fully promoted to BFS-phase checking"
    );
}

/// Part of #2670, Step 7 test case 4: mixed properties still BFS-check their action term.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_mixed_property_splitting_action_part_checked_in_bfs() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Next increments x, but the property says [][UNCHANGED x]_vars (Bad).
    // The property ALSO has WF_vars(Next) — a liveness/fairness constraint.
    // The action violation should be caught during BFS despite the liveness parts.
    let src = r#"
---- MODULE MixedPropertySplit ----
EXTENDS Integers

VARIABLE x
vars == <<x>>

Init == x = 0

Next == IF x < 2 THEN x' = x + 1 ELSE UNCHANGED x

Bad == UNCHANGED x

\* Mixed property: init + implied action + fairness
\* - Init is a state predicate (checked on initial states)
\* - [][Bad]_vars is an action property (checked during BFS on ALL transitions)
\* - WF_vars(Next) is a fairness constraint (requires liveness/SCC analysis)
MixedSpec == Init /\ [][Bad]_vars /\ WF_vars(Next)
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec![],
        properties: vec!["MixedSpec".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    // Fingerprint-only mode (default): the implied action part ([][Bad]_vars)
    // must still be checked during BFS before the liveness phase matters.

    let result = checker.check();
    match result {
        // Part of #2834: implied action violations from PROPERTIES are correctly
        // reported as PropertyViolation.
        CheckResult::PropertyViolation {
            property,
            trace: _,
            stats: _,
            kind: _,
        } => {
            assert_eq!(property, "MixedSpec");
        }
        CheckResult::Success(_) => {
            panic!(
                "Mixed property implied action violation should be detected during BFS. \
                 Got Success — the [][Bad]_vars part was not extracted for BFS checking \
                 when mixed with WF_vars(Next)."
            );
        }
        other => panic!(
            "Expected PropertyViolation for mixed property implied action, got: {:?}",
            other
        ),
    }
}

/// Part of #2670, Step 7 test case 4b: a satisfied mixed action term still succeeds.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_mixed_property_splitting_action_part_satisfied() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Next is the same action used in [][Next]_vars, so the implied action is satisfied.
    // The property also has WF_vars(Next), which is satisfied on this path.
    let src = r#"
---- MODULE MixedPropertySatSplit ----
EXTENDS Integers

VARIABLE x
vars == <<x>>

Init == x = 0

Next == IF x < 2 THEN x' = x + 1 ELSE UNCHANGED x

\* Mixed property where the action part matches Next (always satisfied)
MixedSpec == Init /\ [][Next]_vars /\ WF_vars(Next)
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec![],
        properties: vec!["MixedSpec".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    // Disable stuttering so the only behavior is 0→1→2→2→... which satisfies
    // WF_vars(Next). With stuttering_allowed=true (default), infinite stuttering
    // at x=0 or x=1 would violate WF_vars(Next) since <<Next>>_vars is enabled
    // but never taken on a pure stutter cycle.
    checker.set_stuttering_allowed(false);

    let result = checker.check();
    match result {
        CheckResult::Success(stats) => {
            // x takes values 0, 1, 2
            assert_eq!(stats.states_found, 3);
        }
        other => panic!(
            "Expected Success for satisfied mixed property in fp-only mode, \
             got: {:?}",
            other
        ),
    }
}
