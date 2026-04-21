// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression tests for adaptive (auto) strategy selection and setup parity.

mod common;

use tla_check::{resolve_spec_from_config, AdaptiveChecker, CheckResult, Config};
use tla_core::{lower, parse_to_syntax_tree, FileId};

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_adaptive_registers_inline_next_on_selected_checker() {
    let src = r#"
---- MODULE InlineNextAdaptive ----
VARIABLE x
vars == <<x>>
Init == x = 0
Spec == Init /\ [][\E n \in {0} : x' = x]_vars
===="#;
    let tree = parse_to_syntax_tree(src);
    let lowered = lower(FileId(0), &tree);
    let module = lowered.module.expect("Failed to parse module");

    let mut config = Config {
        specification: Some("Spec".to_string()),
        ..Default::default()
    };
    let resolved = resolve_spec_from_config(&config, &tree).expect("resolve SPECIFICATION");
    assert!(
        resolved.next_node.is_some(),
        "expected inline NEXT next_node to be present"
    );
    config.init = Some(resolved.init.clone());
    config.next = Some(resolved.next.clone());

    let mut checker = AdaptiveChecker::new(&module, &config);
    checker
        .register_inline_next(&resolved)
        .expect("register inline NEXT");
    checker.set_deadlock_check(false);

    let (result, _analysis) = checker.check();
    match &result {
        CheckResult::Success(stats) => {
            // Spec: Init == x = 0, Next == \E n \in {0} : x' = x (stuttering).
            // Exactly 1 initial state, 1 total state.
            assert_eq!(stats.initial_states, 1, "expected 1 initial state");
            assert_eq!(stats.states_found, 1, "expected 1 total state");
        }
        _ => panic!("expected Success, got: {result:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_adaptive_pilot_supports_instance_module_extends_chain() {
    let b_src = r#"
---- MODULE B ----
BVal == 1
===="#;
    let a_src = r#"
---- MODULE A ----
EXTENDS B
====
"#;
    let main_src = r#"
---- MODULE Main ----
VARIABLE x
I == INSTANCE A
Init == x = I!BVal
Next == FALSE
Inv == x = 1
===="#;

    let b = common::parse_module(b_src);
    let a = common::parse_module(a_src);
    let main = common::parse_module(main_src);

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Inv".to_string()],
        ..Default::default()
    };

    let mut checker = AdaptiveChecker::new_with_extends(&main, &[&a, &b], &config);
    checker.set_deadlock_check(false);

    let (result, _analysis) = checker.check();
    match &result {
        CheckResult::Success(stats) => {
            // Spec: Init == x = I!BVal (= 1), Next == FALSE, Inv == x = 1.
            // 1 initial state, 1 total state.
            assert_eq!(stats.initial_states, 1, "expected 1 initial state");
            assert_eq!(stats.states_found, 1, "expected 1 total state");
        }
        _ => panic!("expected Success, got: {result:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_adaptive_pilot_applies_cfg_scoped_assignment() {
    // Regression for #806: adaptive pilot must apply cfg-scoped module assignments
    // before enumerating Init.
    let src = r#"
---- MODULE Main ----
VARIABLE x
Foo == FALSE
Init == Foo /\ x = 0
Next == FALSE
Inv == x = 0
===="#;
    let module = common::parse_module(src);

    let module_assignments = std::collections::HashMap::from([(
        "Main".to_string(),
        std::collections::HashMap::from([("Foo".to_string(), "TRUE".to_string())]),
    )]);

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Inv".to_string()],
        module_assignments,
        ..Default::default()
    };

    let mut checker = AdaptiveChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    let (result, _analysis) = checker.check();
    match &result {
        CheckResult::Success(stats) => {
            // Spec: Init == TRUE /\ x = 0 (Foo overridden to TRUE), Next == FALSE.
            // 1 initial state, 1 total state.
            assert_eq!(stats.initial_states, 1, "expected 1 initial state");
            assert_eq!(stats.states_found, 1, "expected 1 total state");
        }
        _ => panic!("expected Success, got: {result:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_adaptive_pilot_applies_cfg_scoped_assignment_on_instanced_module_choose() {
    // Regression for #806: adaptive pilot must apply cfg-scoped module assignments
    // before enumerating Init, even when the underlying operator body is not evaluable.
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
Inv == x = h1
====
"#;
    let inst = common::parse_module(inst_src);
    let main = common::parse_module(main_src);

    let module_assignments = std::collections::HashMap::from([(
        "Inst".to_string(),
        std::collections::HashMap::from([("NoHash".to_string(), "h1".to_string())]),
    )]);

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Inv".to_string()],
        module_assignments,
        ..Default::default()
    };

    let mut checker = AdaptiveChecker::new_with_extends(&main, &[&inst], &config);
    checker.set_deadlock_check(false);

    let (result, _analysis) = checker.check();
    match &result {
        CheckResult::Success(stats) => {
            // Spec: Init == x = I!NoHash (overridden to "h1"), Next == FALSE.
            // 1 initial state, 1 total state.
            assert_eq!(stats.initial_states, 1, "expected 1 initial state");
            assert_eq!(stats.states_found, 1, "expected 1 total state");
        }
        _ => panic!("expected Success, got: {result:?}"),
    }
}
