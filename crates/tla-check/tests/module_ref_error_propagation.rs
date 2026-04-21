// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for #1724: INSTANCE module reference error propagation.
//!
//! When an operator referenced via `I!Op` is not found (typo, missing definition),
//! the model checker must report an error — not silently produce zero successors.

mod common;

use tla_check::EvalCheckError;
use tla_check::{CheckError, CheckResult};
use tla_check::{Config, EvalError, ModelChecker};
use tla_core::FileId;

/// #1724: A typo in the operator name referenced through an INSTANCE
/// must produce an error, not silently yield zero successors.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_1724_instance_undefined_op_errors() {
    let inner_src = r#"
---- MODULE Inner ----
VARIABLE x
Op == x' = x + 1
====
"#;
    let main_src = r#"
---- MODULE Main ----
EXTENDS Integers
VARIABLE x
I == INSTANCE Inner
Init == x = 0
Next == I!Nonexistent
====
"#;

    let inner_module = common::parse_module_strict_with_id(inner_src, FileId(1));
    let main_module = common::parse_module_strict_with_id(main_src, FileId(0));
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        check_deadlock: false,
        ..Default::default()
    };

    let mut checker = ModelChecker::new_with_extends(&main_module, &[&inner_module], &config);
    let result = checker.check();

    assert!(
        matches!(
            result,
            CheckResult::Error {
                error: CheckError::Eval(EvalCheckError::Eval(EvalError::UndefinedOp { .. })),
                ..
            }
        ),
        "#1724 regression: undefined operator in INSTANCE must error, got: {result:?}"
    );
}

/// #1724: A reference to a non-existent INSTANCE (not just a missing operator)
/// must also produce an error rather than silently succeeding.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_1724_nonexistent_instance_errors() {
    // This spec references I!Op but the Inner module is never loaded as an
    // extended module, so the INSTANCE "I" cannot be resolved.
    let main_src = r#"
---- MODULE Main ----
EXTENDS Integers
VARIABLE x
I == INSTANCE Inner
Init == x = 0
Next == I!Op
====
"#;

    let main_module = common::parse_module_strict_with_id(main_src, FileId(0));
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        check_deadlock: false,
        ..Default::default()
    };

    // No extended modules provided — Inner is not loaded
    let mut checker = ModelChecker::new_with_extends(&main_module, &[], &config);
    let result = checker.check();

    // Should error, not silently produce zero successors
    assert!(
        matches!(result, CheckResult::Error { .. }),
        "#1724 regression: missing INSTANCE module must error, got: {result:?}"
    );
}
