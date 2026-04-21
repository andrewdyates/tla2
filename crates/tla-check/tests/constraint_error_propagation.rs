// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

mod common;

use tla_check::CheckResult;
use tla_check::ParallelChecker;
use tla_check::{check_module, CheckError, Config, EvalCheckError};

fn assert_constraint_not_boolean(result: CheckResult, expected_name: &str) {
    match result {
        CheckResult::Error { error, .. } => match error {
            CheckError::Eval(EvalCheckError::ConstraintNotBoolean(name)) => {
                assert_eq!(name, expected_name);
            }
            other => panic!("expected ConstraintNotBoolean({expected_name}), got: {other:?}"),
        },
        other => panic!("expected Error, got: {other:?}"),
    }
}

fn assert_eval_error(result: CheckResult) {
    match result {
        CheckResult::Error {
            error: CheckError::Eval(EvalCheckError::Eval(_)),
            ..
        } => {}
        other => panic!("expected CheckError::Eval(EvalCheckError::Eval), got: {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_constraint_non_boolean_is_error_in_sequential_and_parallel() {
    let src = r#"
---- MODULE ConstraintNonBoolean ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x < 2 /\ x' = x + 1
BadConstraint == 1
====
"#;
    let module = common::parse_module(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        constraints: vec!["BadConstraint".to_string()],
        ..Default::default()
    };

    let seq = check_module(&module, &config);
    assert_constraint_not_boolean(seq, "BadConstraint");

    let mut par = ParallelChecker::new(&module, &config, 2);
    par.set_deadlock_check(false);
    let par_result = par.check();
    assert_constraint_not_boolean(par_result, "BadConstraint");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_action_constraint_eval_error_is_error_in_sequential_and_parallel() {
    let src = r#"
---- MODULE ActionConstraintEvalError ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x < 2 /\ x' = x + 1
BadAction == (1 \div 0) = 0
====
"#;
    let module = common::parse_module(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        action_constraints: vec!["BadAction".to_string()],
        ..Default::default()
    };

    let seq = check_module(&module, &config);
    assert_eval_error(seq);

    let mut par = ParallelChecker::new(&module, &config, 2);
    par.set_deadlock_check(false);
    let par_result = par.check();
    assert_eval_error(par_result);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_terminal_operator_non_boolean_is_error_during_deadlock_check() {
    let src = r#"
---- MODULE TerminalNonBoolean ----
VARIABLE x
Init == x = 0
Next == FALSE
BadTerminal == 1
====
"#;
    let module = common::parse_module(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        terminal: Some(tla_check::TerminalSpec::Operator("BadTerminal".to_string())),
        ..Default::default()
    };

    let seq = check_module(&module, &config);
    assert_constraint_not_boolean(seq, "BadTerminal");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_terminal_operator_eval_error_is_error_during_deadlock_check() {
    let src = r#"
---- MODULE TerminalEvalError ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == FALSE
BadTerminal == (1 \div 0) = 0
====
"#;
    let module = common::parse_module(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        terminal: Some(tla_check::TerminalSpec::Operator("BadTerminal".to_string())),
        ..Default::default()
    };

    let seq = check_module(&module, &config);
    assert_eval_error(seq);
}
