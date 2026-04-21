// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// ============================
// SPECIFICATION directive tests
// ============================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_resolve_spec_explicit_init_next() {
    use tla_core::parse_to_syntax_tree;

    let src = r#"
---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
===="#;
    let tree = parse_to_syntax_tree(src);

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };

    let resolved = super::resolve_spec_from_config(&config, &tree).unwrap();
    assert_eq!(resolved.init, "Init");
    assert_eq!(resolved.next, "Next");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_resolve_spec_from_specification() {
    use tla_core::parse_to_syntax_tree;

    let src = r#"
---- MODULE Test ----
VARIABLE x
vars == <<x>>
Init == x = 0
Next == x' = x + 1
Spec == Init /\ [][Next]_vars
===="#;
    let tree = parse_to_syntax_tree(src);

    let config = Config {
        specification: Some("Spec".to_string()),
        ..Default::default()
    };

    let resolved = super::resolve_spec_from_config(&config, &tree).unwrap();
    assert_eq!(resolved.init, "Init");
    assert_eq!(resolved.next, "Next");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_resolve_spec_from_specification_with_wrapper_operator_in_extends() {
    use tla_core::parse_to_syntax_tree;

    let base = r#"
---- MODULE Base ----
VARIABLE x
vars == <<x>>
Init == x = 0
Next == x' = x + 1
Spec == Init /\ [][Next]_vars
===="#;
    let base_tree = parse_to_syntax_tree(base);

    let main = r#"
---- MODULE Main ----
EXTENDS Base
Foo == TRUE
TestSpec == Foo /\ Spec
===="#;
    let main_tree = parse_to_syntax_tree(main);

    let config = Config {
        specification: Some("TestSpec".to_string()),
        ..Default::default()
    };

    let resolved =
        super::resolve_spec_from_config_with_extends(&config, &main_tree, &[&base_tree]).unwrap();
    assert_eq!(resolved.init, "Init");
    assert_eq!(resolved.next, "Next");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_resolve_spec_missing_specification() {
    use tla_core::parse_to_syntax_tree;

    let src = r#"
---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
===="#;
    let tree = parse_to_syntax_tree(src);

    let config = Config {
        specification: Some("NonExistent".to_string()),
        ..Default::default()
    };

    let result = super::resolve_spec_from_config(&config, &tree);
    assert!(result.is_err());
    if let Err(CheckError::Config(ConfigCheckError::Specification(msg))) = result {
        assert!(msg.contains("NonExistent"));
    } else {
        panic!("Expected SpecificationError");
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_resolve_spec_missing_init_next() {
    use tla_core::parse_to_syntax_tree;

    let src = r#"
---- MODULE Test ----
VARIABLE x
Init == x = 0
===="#;
    let tree = parse_to_syntax_tree(src);

    let config = Config::default();

    let result = super::resolve_spec_from_config(&config, &tree);
    assert!(result.is_err());
    assert!(matches!(
        result,
        Err(CheckError::Config(ConfigCheckError::MissingInit))
    ));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_resolve_spec_inline_next_expression() {
    use tla_core::parse_to_syntax_tree;

    // Test case: Spec with inline existential quantifier in NEXT
    let src = r#"
---- MODULE Test ----
CONSTANT Node
VARIABLE x
vars == x
Init == x = 0
Next(n) == x' = n
Spec == Init /\ [][\E n \in Node: Next(n)]_vars
===="#;
    let tree = parse_to_syntax_tree(src);

    let config = Config {
        specification: Some("Spec".to_string()),
        ..Default::default()
    };

    let resolved = super::resolve_spec_from_config(&config, &tree).unwrap();
    assert_eq!(resolved.init, "Init");
    // When there's an inline NEXT, we use the synthetic name
    assert_eq!(resolved.next, super::INLINE_NEXT_NAME);
    // The next_node should be present
    assert!(resolved.next_node.is_some());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_model_checker_with_inline_next() {
    use crate::config::ConstantValue;
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // A simple spec using inline existential in NEXT
    let src = r#"
---- MODULE InlineNextTest ----
EXTENDS Integers
CONSTANT Node
VARIABLE x
vars == <<x>>
Init == x = 0
Step(n) == x < 3 /\ x' = x + 1
Spec == Init /\ [][\E n \in Node: Step(n)]_vars
===="#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let spec_config = Config {
        specification: Some("Spec".to_string()),
        ..Default::default()
    };
    let resolved = super::resolve_spec_from_config(&spec_config, &tree).unwrap();

    // Create checker config with the resolved NEXT name
    let mut constants = std::collections::HashMap::new();
    constants.insert("Node".to_string(), ConstantValue::Value("{1}".to_string()));

    let config = Config {
        init: Some(resolved.init.clone()),
        next: Some(resolved.next.clone()),
        constants,
        invariants: vec![],
        ..Default::default()
    };

    let mut checker = super::ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    // Register the inline NEXT expression
    checker
        .register_inline_next(&resolved)
        .expect("Failed to register inline next");

    let result = checker.check();

    // Should succeed and find states: x=0, x=1, x=2, x=3
    match result {
        super::CheckResult::Success(stats) => {
            assert_eq!(stats.states_found, 4, "Expected 4 states (x=0,1,2,3)");
        }
        other => panic!("Expected success, got: {:?}", other),
    }
}

/// Regression test for #1278: `[Next \/ UNCHANGED vars]_vars` inline disjunctive action.
///
/// The spec formula `[][Next \/ UNCHANGED vars]_vars` must produce successors from both
/// the `Next` action (incrementing x) AND the `UNCHANGED vars` stuttering step. Without
/// the #1278 fix, only `Next` was extracted and the `UNCHANGED vars` disjunct was silently
/// dropped, causing trace validation specs to get stuck.
///
/// With stuttering, deadlock is never possible since every state has at least one successor
/// (itself via UNCHANGED vars). The state space is x=0..3 = 4 states.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_model_checker_with_inline_disjunctive_next() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    let src = r#"
---- MODULE DisjunctiveNextTest ----
EXTENDS Integers
VARIABLE x
vars == <<x>>
Init == x = 0
Next == x < 3 /\ x' = x + 1
TraceSpec == Init /\ [][Next \/ UNCHANGED vars]_vars
===="#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let spec_config = Config {
        specification: Some("TraceSpec".to_string()),
        ..Default::default()
    };
    let resolved = super::resolve_spec_from_config(&spec_config, &tree).unwrap();

    // Verify the inline next was detected
    assert!(
        resolved.next_node.is_some(),
        "Disjunctive action should produce an inline next node"
    );

    let config = Config {
        init: Some(resolved.init.clone()),
        next: Some(resolved.next.clone()),
        invariants: vec![],
        ..Default::default()
    };

    let mut checker = super::ModelChecker::new(&module, &config);
    // Stuttering is allowed, so deadlock check should not trigger
    checker.set_deadlock_check(true);

    checker
        .register_inline_next(&resolved)
        .expect("Failed to register inline next");

    let result = checker.check();

    // Should succeed: x=0, x=1, x=2, x=3 (4 states)
    // With UNCHANGED vars, every state has a stuttering successor,
    // so no deadlock even though x=3 has no Next-successor.
    match result {
        super::CheckResult::Success(stats) => {
            assert_eq!(stats.states_found, 4, "Expected 4 states (x=0,1,2,3)");
        }
        other => panic!("Expected success, got: {:?}", other),
    }
}

// ==========================================================================
// Resolve: cyclic reference detection (#1230)
// ==========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_resolve_spec_cyclic_specification_reference() {
    use tla_core::parse_to_syntax_tree;

    // A == B, B == A — cyclic SPECIFICATION reference should be detected
    let src = r#"
---- MODULE CyclicTest ----
VARIABLE x
A == B
B == A
===="#;
    let tree = parse_to_syntax_tree(src);

    let config = Config {
        specification: Some("A".to_string()),
        ..Default::default()
    };

    let result = super::resolve_spec_from_config(&config, &tree);
    assert!(result.is_err());
    if let Err(CheckError::Config(ConfigCheckError::Specification(msg))) = result {
        assert!(
            msg.contains("cyclic") || msg.contains("unsupported"),
            "Expected cyclic or unsupported error, got: {}",
            msg
        );
    } else {
        panic!("Expected SpecificationError for cyclic reference");
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_resolve_spec_strong_fairness_extraction() {
    use tla_core::parse_to_syntax_tree;

    // SF_vars(Next) — strong fairness should be extracted
    let src = r#"
---- MODULE StrongFairnessTest ----
VARIABLE x
vars == <<x>>
Init == x = 0
Next == x' = x + 1
Spec == Init /\ [][Next]_vars /\ SF_vars(Next)
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
        FairnessConstraint::Strong { vars, action, .. } => {
            assert_eq!(vars, "vars");
            assert_eq!(action, "Next");
        }
        other => panic!("Expected strong fairness, got: {:?}", other),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_resolve_spec_multiple_combined_fairness() {
    use tla_core::parse_to_syntax_tree;

    // Both WF and SF on same spec
    let src = r#"
---- MODULE MultiFairnessTest ----
VARIABLE x
vars == <<x>>
Init == x = 0
Next == x' = x + 1
ActionA == x' = x + 2
Spec == Init /\ [][Next]_vars /\ WF_vars(Next) /\ SF_vars(ActionA)
===="#;
    let tree = parse_to_syntax_tree(src);

    let config = Config {
        specification: Some("Spec".to_string()),
        ..Default::default()
    };

    let resolved = super::resolve_spec_from_config(&config, &tree).unwrap();
    assert_eq!(resolved.init, "Init");
    assert_eq!(resolved.next, "Next");
    assert!(
        resolved.fairness.len() >= 2,
        "Expected at least 2 fairness constraints, got {}",
        resolved.fairness.len()
    );

    let has_weak = resolved
        .fairness
        .iter()
        .any(|f| matches!(f, FairnessConstraint::Weak { action, .. } if action == "Next"));
    let has_strong = resolved
        .fairness
        .iter()
        .any(|f| matches!(f, FairnessConstraint::Strong { action, .. } if action == "ActionA"));
    assert!(has_weak, "Should have WF_vars(Next)");
    assert!(has_strong, "Should have SF_vars(ActionA)");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_resolve_spec_operator_aliasing_chain() {
    use tla_core::parse_to_syntax_tree;

    // MySpec == LSpec, LSpec == Spec, Spec == Init /\ [][Next]_vars
    let src = r#"
---- MODULE AliasingTest ----
VARIABLE x
vars == <<x>>
Init == x = 0
Next == x' = x + 1
Spec == Init /\ [][Next]_vars
LSpec == Spec
MySpec == LSpec
===="#;
    let tree = parse_to_syntax_tree(src);

    let config = Config {
        specification: Some("MySpec".to_string()),
        ..Default::default()
    };

    let resolved = super::resolve_spec_from_config(&config, &tree).unwrap();
    assert_eq!(resolved.init, "Init");
    assert_eq!(resolved.next, "Next");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_resolve_spec_stuttering_allowed() {
    use tla_core::parse_to_syntax_tree;

    // Standard stuttering-allowed form: [][Next]_vars
    let src = r#"
---- MODULE StutterAllowedTest ----
VARIABLE x
vars == <<x>>
Init == x = 0
Next == x' = x + 1
Spec == Init /\ [][Next]_vars
===="#;
    let tree = parse_to_syntax_tree(src);

    let config = Config {
        specification: Some("Spec".to_string()),
        ..Default::default()
    };

    let resolved = super::resolve_spec_from_config(&config, &tree).unwrap();
    assert!(
        resolved.stuttering_allowed,
        "[][Next]_vars should allow stuttering"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_resolve_spec_nested_fairness_from_wrapper_operator() {
    use tla_core::parse_to_syntax_tree;

    // Fairness in a separate operator referenced by wrapper:
    // Liveness == WF_vars(Next)
    // FairSpec == Spec /\ Liveness
    let src = r#"
---- MODULE NestedFairnessOp ----
VARIABLE x
vars == <<x>>
Init == x = 0
Next == x' = x + 1
Spec == Init /\ [][Next]_vars
Liveness == WF_vars(Next)
FairSpec == Spec /\ Liveness
===="#;
    let tree = parse_to_syntax_tree(src);

    let config = Config {
        specification: Some("FairSpec".to_string()),
        ..Default::default()
    };

    let resolved = super::resolve_spec_from_config(&config, &tree).unwrap();
    assert_eq!(resolved.init, "Init");
    assert_eq!(resolved.next, "Next");
    // Should extract fairness from the Liveness operator
    let has_weak = resolved
        .fairness
        .iter()
        .any(|f| matches!(f, FairnessConstraint::Weak { action, .. } if action == "Next"));
    assert!(
        has_weak,
        "Should extract WF_vars(Next) from Liveness operator, got: {:?}",
        resolved.fairness
    );
}
