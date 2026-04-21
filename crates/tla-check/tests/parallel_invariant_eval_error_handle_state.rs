// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

mod common;

use tla_check::Config;
use tla_check::EvalCheckError;
use tla_check::ParallelChecker;
use tla_check::{CheckError, CheckResult};

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parallel_invariant_eval_error_is_error_not_violation_handle_state() {
    // Part of #3318: HandleState is now the default parallel mode, no env var needed.

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

    let mut checker = ParallelChecker::new(&module, &config, 2);
    checker.set_deadlock_check(false);

    let result = checker.check();
    match result {
        CheckResult::Error { error, .. } => match error {
            CheckError::Eval(EvalCheckError::Eval(_)) => {}
            other => panic!("expected EvalError, got: {other:?}"),
        },
        other => panic!("expected Error, got: {other:?}"),
    }
}
