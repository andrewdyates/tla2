// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

mod common;

use tla_check::Config;
use tla_check::EvalCheckError;
use tla_check::EvalError;
use tla_check::ParallelChecker;
use tla_check::{CheckError, CheckResult};

#[derive(Debug, PartialEq, Eq)]
enum NonBooleanInvariantErrorKind {
    InvariantNotBoolean(String),
    TypeErrorBoolean,
}

fn non_boolean_invariant_error_kind(result: CheckResult) -> NonBooleanInvariantErrorKind {
    match result {
        CheckResult::Error { error, .. } => match error {
            CheckError::Eval(EvalCheckError::Eval(EvalError::TypeError { expected, .. })) => {
                assert_eq!(expected, "BOOLEAN");
                NonBooleanInvariantErrorKind::TypeErrorBoolean
            }
            CheckError::Eval(EvalCheckError::InvariantNotBoolean(name)) => {
                NonBooleanInvariantErrorKind::InvariantNotBoolean(name)
            }
            other => panic!("expected non-boolean invariant error, got: {other:?}"),
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
    let seq_error = non_boolean_invariant_error_kind(seq);

    let mut par = ParallelChecker::new(&module, &config, 2);
    par.set_deadlock_check(false);
    let result = par.check();
    let par_error = non_boolean_invariant_error_kind(result);
    assert_eq!(par_error, seq_error);
}
