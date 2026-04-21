// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for #1653: named-INSTANCE invariants must not be classified
//! as action-level solely because they cross a module boundary.
//!
//! `compute_contains_prime` now treats `ModuleRef` as opaque. These tests lock
//! the intended checker behavior:
//! - a state-level imported invariant must pass end-to-end
//! - an imported action-level operator must still fail at evaluation time

mod common;

use tla_check::{
    CheckError, CheckResult, Config, ConfigCheckError, EvalCheckError, EvalError, ModelChecker,
};
use tla_core::FileId;
use tla_eval::clear_for_test_reset;

fn assert_success_states(result: CheckResult, expected_states: usize, label: &str) {
    match result {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, expected_states,
                "Bug #1653 regression ({label}): expected {expected_states} states, got {}",
                stats.states_found
            );
        }
        other => panic!("Bug #1653 regression ({label}): expected Success, got {other:?}"),
    }
}

fn assert_primed_var_error(result: CheckResult, label: &str) {
    match result {
        CheckResult::Error { error, .. } => match error {
            CheckError::Eval(EvalCheckError::Eval(EvalError::PrimedVariableNotBound {
                ..
            })) => {}
            other => panic!(
                "Bug #1653 regression ({label}): expected PrimedVariableNotBound, got {other:?}"
            ),
        },
        other => panic!("Bug #1653 regression ({label}): expected Error, got {other:?}"),
    }
}

fn assert_invariant_not_state_level(result: CheckResult, name: &str, label: &str) {
    match result {
        CheckResult::Error { error, .. } => match error {
            CheckError::Config(ConfigCheckError::InvariantNotStateLevel {
                name: actual_name,
                has_prime,
                has_temporal,
            }) => {
                assert_eq!(
                    actual_name, name,
                    "Bug #1653 regression ({label}): unexpected invariant name"
                );
                assert!(
                    has_prime,
                    "Bug #1653 regression ({label}): expected has_prime=true"
                );
                assert!(
                    !has_temporal,
                    "Bug #1653 regression ({label}): expected has_temporal=false"
                );
            }
            other => panic!(
                "Bug #1653 regression ({label}): expected InvariantNotStateLevel, got {other:?}"
            ),
        },
        other => panic!("Bug #1653 regression ({label}): expected Error, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn bug_1653_instance_state_invariant_is_accepted() {
    clear_for_test_reset();
    let inner = common::parse_module_strict_with_id(
        r#"
---- MODULE Inner ----
VARIABLE x
TypeInv == x \in {0, 1}
====
"#,
        FileId(1),
    );

    let outer = common::parse_module_strict_with_id(
        r#"
---- MODULE Outer ----
EXTENDS Integers
VARIABLE y
Init == y = 0
Next == y' = 1 - y
I == INSTANCE Inner WITH x <- y
OuterInv == I!TypeInv
====
"#,
        FileId(0),
    );

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["OuterInv".to_string()],
        check_deadlock: false,
        ..Default::default()
    };

    let mut checker = ModelChecker::new_with_extends(&outer, &[&inner], &config);
    assert_success_states(checker.check(), 2, "state-level INSTANCE invariant");
}

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn bug_1653_instance_action_invariant_still_errors() {
    clear_for_test_reset();
    let inner = common::parse_module_strict_with_id(
        r#"
---- MODULE InnerAction ----
EXTENDS Integers
VARIABLE x
BadInv == x' = x + 1
====
"#,
        FileId(1),
    );

    let outer = common::parse_module_strict_with_id(
        r#"
---- MODULE OuterAction ----
EXTENDS Integers
VARIABLE y
Init == y = 0
Next == y' = y
I == INSTANCE InnerAction WITH x <- y
OuterInv == I!BadInv
====
"#,
        FileId(0),
    );

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["OuterInv".to_string()],
        check_deadlock: false,
        ..Default::default()
    };

    let mut checker = ModelChecker::new_with_extends(&outer, &[&inner], &config);
    assert_primed_var_error(checker.check(), "action-level INSTANCE invariant");
}

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn bug_1653_parameterized_instance_target_prime_is_rejected_at_validation() {
    clear_for_test_reset();
    let inner = common::parse_module_strict_with_id(
        r#"
---- MODULE Inner ----
VARIABLE x
TypeInv == x \in {0, 1}
====
"#,
        FileId(1),
    );

    let outer = common::parse_module_strict_with_id(
        r#"
---- MODULE OuterParameterized ----
EXTENDS Integers
VARIABLE y
Init == y = 0
Next == y' = 1 - y
P(value) == INSTANCE Inner WITH x <- value
OuterInv == P(y')!TypeInv
====
"#,
        FileId(0),
    );

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["OuterInv".to_string()],
        check_deadlock: false,
        ..Default::default()
    };

    let mut checker = ModelChecker::new_with_extends(&outer, &[&inner], &config);
    assert_invariant_not_state_level(
        checker.check(),
        "OuterInv",
        "parameterized INSTANCE target prime",
    );
}

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn bug_1653_chained_instance_target_prime_is_rejected_at_validation() {
    clear_for_test_reset();
    let inner = common::parse_module_strict_with_id(
        r#"
---- MODULE Inner ----
VARIABLE x
TypeInv == P0:: (x \in {0, 1})
====
"#,
        FileId(1),
    );

    let outer = common::parse_module_strict_with_id(
        r#"
---- MODULE OuterChained ----
EXTENDS Integers
VARIABLE y
Init == y = 0
Next == y' = 1 - y
P(value) == INSTANCE Inner WITH x <- value
OuterInv == P(y')!TypeInv!P0
====
"#,
        FileId(0),
    );

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["OuterInv".to_string()],
        check_deadlock: false,
        ..Default::default()
    };

    let mut checker = ModelChecker::new_with_extends(&outer, &[&inner], &config);
    assert_invariant_not_state_level(checker.check(), "OuterInv", "chained INSTANCE target prime");
}
