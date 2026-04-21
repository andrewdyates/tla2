// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

mod common;

use tla_check::Config;
use tla_check::EvalCheckError;
use tla_check::EvalError;
use tla_check::ParallelChecker;
use tla_check::{CheckError, CheckResult};

fn assert_invariant_not_boolean_error(result: CheckResult) {
    match result {
        CheckResult::Error { error, .. } => match error {
            CheckError::Eval(EvalCheckError::Eval(EvalError::TypeError { expected, .. })) => {
                assert_eq!(expected, "BOOLEAN");
            }
            other => panic!("expected EvalError(TypeError expected BOOLEAN), got: {other:?}"),
        },
        other => panic!("expected Error, got: {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parallel_non_boolean_invariant_matches_sequential_error_type() {
    // TLC errors when an invariant does not evaluate to BOOLEAN.
    let src = r#"
---- MODULE InvNotBool ----
VARIABLE x
Init == x = 0
Next == x' = x
Inv == 1
====
"#;
    let module = common::parse_module(src);

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Inv".to_string()],
        ..Default::default()
    };

    let seq = tla_check::check_module(&module, &config);
    assert_invariant_not_boolean_error(seq);

    let mut par = ParallelChecker::new(&module, &config, 2);
    par.set_deadlock_check(false);
    let result = par.check();
    assert_invariant_not_boolean_error(result);
}
