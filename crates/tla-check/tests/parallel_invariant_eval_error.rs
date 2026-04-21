// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

mod common;

use tla_check::Config;
use tla_check::EvalCheckError;
use tla_check::EvalError;
use tla_check::ParallelChecker;
use tla_check::{CheckError, CheckResult};

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parallel_invariant_eval_error_is_error_not_violation() {
    // TLC errors when attempting to enumerate a non-enumerable function set.
    let src = r#"
---- MODULE FuncSetEmptyEquality ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = x
Inv == [Nat -> Nat] = {}
====
"#;
    let module = common::parse_module(src);

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Inv".to_string()],
        ..Default::default()
    };

    // Sequential checker should also treat this as an eval error (not an invariant violation).
    let seq = tla_check::check_module(&module, &config);
    match seq {
        CheckResult::Error { error, .. } => match error {
            CheckError::Eval(EvalCheckError::Eval(EvalError::SetTooLarge { .. })) => {}
            other => panic!("expected SetTooLarge EvalError (sequential), got: {other:?}"),
        },
        other => panic!("expected Error (sequential), got: {other:?}"),
    }

    let mut checker = ParallelChecker::new(&module, &config, 2);
    checker.set_deadlock_check(false);

    let result = checker.check();
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
fn test_parallel_invariant_eval_error_is_error_not_violation_after_successor() {
    // Force the EvalError to occur at depth 1, not on the initial state.
    // This exercises error propagation from invariant evaluation on successor states.
    let src = r#"
---- MODULE FuncSetEmptyEqualityAfterSuccessor ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = 1
Inv == IF x = 0 THEN TRUE ELSE [Nat -> Nat] = {}
====
"#;
    let module = common::parse_module(src);

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Inv".to_string()],
        ..Default::default()
    };

    let mut init_only = ParallelChecker::new(&module, &config, 2);
    init_only.set_deadlock_check(false);
    init_only.set_max_depth(0);
    match init_only.check() {
        CheckResult::Success(_) => {}
        CheckResult::LimitReached {
            limit_type: tla_check::LimitType::Depth,
            ..
        } => {}
        other => panic!("expected Success or Depth limit at depth 0, got: {other:?}"),
    }

    let mut with_successor = ParallelChecker::new(&module, &config, 2);
    with_successor.set_deadlock_check(false);
    with_successor.set_max_depth(1);
    match with_successor.check() {
        CheckResult::Error { error, .. } => match error {
            CheckError::Eval(EvalCheckError::Eval(EvalError::SetTooLarge { .. })) => {}
            other => panic!("expected SetTooLarge EvalError, got: {other:?}"),
        },
        other => panic!("expected Error at depth 1, got: {other:?}"),
    }
}
