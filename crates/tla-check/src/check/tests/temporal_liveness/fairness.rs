// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_fairness_extraction_from_spec() {
    use tla_core::parse_to_syntax_tree;

    // Test that fairness is extracted from SPECIFICATION formula
    let src = r#"
---- MODULE FairnessTest ----
VARIABLE x
vars == <<x>>
Init == x = 0
Next == x' = x + 1
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
===="#;
    let tree = parse_to_syntax_tree(src);

    let config = Config {
        specification: Some("Spec".to_string()),
        ..Default::default()
    };

    let resolved = super::resolve_spec_from_config(&config, &tree).unwrap();
    assert_eq!(resolved.init, "Init");
    assert_eq!(resolved.next, "Next");
    assert_eq!(resolved.fairness.len(), 1);

    match &resolved.fairness[0] {
        FairnessConstraint::Weak { vars, action, .. } => {
            assert_eq!(vars, "vars");
            assert_eq!(action, "Next");
        }
        _ => panic!("Expected weak fairness"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_fairness_set_and_get() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    let src = r#"
---- MODULE SetFairnessTest ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x' = x + 1
===="#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);

    // Initially no fairness
    assert!(checker.test_fairness().is_empty());

    // Set fairness
    let fairness = vec![FairnessConstraint::Weak {
        vars: "vars".to_string(),
        action: "Next".to_string(),
        action_node: None,
    }];
    checker.set_fairness(fairness);

    assert_eq!(checker.test_fairness().len(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_fairness_extraction_from_nested_spec() {
    use tla_core::parse_to_syntax_tree;

    // Test that fairness is extracted from nested SPECIFICATION formula
    // SpecWeakFair == Spec /\ WF_vars(Next) where Spec contains Init/Next
    let src = r#"
---- MODULE NestedFairnessTest ----
VARIABLE x
vars == <<x>>
Init == x = 0
Next == x' = x + 1
Spec == Init /\ [][Next]_vars
SpecWeakFair == Spec /\ WF_vars(Next)
===="#;
    let tree = parse_to_syntax_tree(src);

    let config = Config {
        specification: Some("SpecWeakFair".to_string()),
        ..Default::default()
    };

    let resolved = super::resolve_spec_from_config(&config, &tree).unwrap();
    assert_eq!(resolved.init, "Init");
    assert_eq!(resolved.next, "Next");
    assert_eq!(
        resolved.fairness.len(),
        1,
        "Should have extracted fairness from nested spec"
    );

    match &resolved.fairness[0] {
        FairnessConstraint::Weak { vars, action, .. } => {
            assert_eq!(vars, "vars");
            assert_eq!(action, "Next");
        }
        _ => panic!("Expected weak fairness"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_liveness_with_disjunctive_action_and_fairness() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // SystemLoop test case: disjunctive Next action with weak fairness
    // This is the Manna & Pneuli LOOP example
    let src = r#"
---- MODULE SystemLoopTest ----

VARIABLE x
vars == <<x>>

Init == x = 0

One == x = 0 /\ x' = 1
Two == x = 1 /\ x' = 2
Three == x = 2 /\ x' = 3
Back == x = 3 /\ x' = 0

Next == One \/ Two \/ Three \/ Back

\* Spec with weak fairness
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Liveness: x will infinitely often be 3
Liveness == []<>(x = 3)

===="#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    // Resolve spec to get init/next/fairness
    let spec_config = Config {
        specification: Some("Spec".to_string()),
        ..Default::default()
    };
    let resolved = resolve_spec_from_config(&spec_config, &tree).unwrap();

    // Check fairness was extracted
    assert_eq!(
        resolved.fairness.len(),
        1,
        "Should have weak fairness extracted"
    );

    // Create checker with explicit init/next and fairness
    let config = Config {
        init: Some(resolved.init.clone()),
        next: Some(resolved.next.clone()),
        invariants: vec![],
        properties: vec!["Liveness".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    checker.set_fairness(resolved.fairness);

    let result = checker.check();

    match result {
        CheckResult::Success(stats) => {
            // 4 states: x=0, x=1, x=2, x=3
            assert_eq!(stats.states_found, 4);
        }
        CheckResult::LivenessViolation { .. } => {
            panic!("Liveness should be satisfied with weak fairness (no stuttering)");
        }
        CheckResult::Error { error, .. } => {
            panic!("Unexpected error: {:?}", error);
        }
        other => panic!("Unexpected result: {:?}", other),
    }
}
