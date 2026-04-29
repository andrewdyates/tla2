// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

mod common;

use tla_check::Config;
use tla_check::EvalCheckError;
use tla_check::EvalError;
use tla_check::ParallelChecker;
use tla_check::{CheckError, CheckResult};

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parallel_continue_on_error_does_not_mask_eval_error() {
    // Construct a run where:
    // - x=1 violates BadInv (recorded, but continue)
    // - x=2 triggers ErrInv eval error (must take precedence in final result)
    let src = r#"
---- MODULE ContinueViolationThenError ----
EXTENDS Naturals
VARIABLE x

Init == x = 0
Next == x < 2 /\ x' = x + 1

ErrInv == IF x = 2 THEN SUBSET Nat = {} ELSE TRUE
BadInv == x # 1

====
"#;
    let module = common::parse_module(src);

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["ErrInv".to_string(), "BadInv".to_string()],
        ..Default::default()
    };

    let mut checker = ParallelChecker::new(&module, &config, 2);
    checker.set_deadlock_check(false);
    checker.set_continue_on_error(true);

    let result = checker.check();
    match result {
        CheckResult::Error { error, .. } => match error {
            CheckError::Eval(EvalCheckError::Eval(EvalError::SetTooLarge { .. })) => {}
            other => panic!("expected SetTooLarge EvalError, got: {other:?}"),
        },
        other => panic!("expected Error, got: {other:?}"),
    }
}
