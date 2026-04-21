// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// =========================================================================
// Unit tests for helper functions
// =========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_is_action_level_error_primed_variable() {
    // Part of #1891: uses typed variant instead of string-matched Internal
    let err = EvalError::PrimedVariableNotBound { span: None };
    assert!(is_action_level_error(&err));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_is_action_level_error_unchanged() {
    // Part of #1891: uses typed variant instead of string-matched Internal
    let err = EvalError::UnchangedNotEvaluable { span: None };
    assert!(is_action_level_error(&err));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_is_action_level_error_other_internal() {
    let err = EvalError::Internal {
        message: "Some other error".to_string(),
        span: None,
    };
    assert!(!is_action_level_error(&err));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_is_action_level_error_rejects_internal_with_primed_string() {
    // Part of #1891: Internal errors with "Primed variable" in message are NO
    // LONGER classified as action-level — only the typed variant counts.
    // This is the whole point of the fix: string matching was fragile.
    let err = EvalError::Internal {
        message: "Primed variable x' has no value".to_string(),
        span: None,
    };
    assert!(
        !is_action_level_error(&err),
        "Internal errors should not be classified by string matching"
    );
}

// =========================================================================
// Unit tests for is_let_lazy_safe_error
// =========================================================================

#[test]
fn test_is_let_lazy_safe_catches_internal_io_error() {
    // IO errors (e.g., JsonDeserialize file not found) in unused LET bodies
    // must be caught — TLC would skip them lazily.
    let err = EvalError::Internal {
        message: "JsonDeserialize: failed to read file 'missing.json': No such file".to_string(),
        span: None,
    };
    assert!(
        is_let_lazy_safe_error(&err),
        "Internal IO errors should be caught in LET lazy binding"
    );
}

#[test]
fn test_is_let_lazy_safe_catches_action_level_primed() {
    // Part of #1891: use typed variant instead of Internal with string
    let err = EvalError::PrimedVariableNotBound { span: None };
    assert!(
        is_let_lazy_safe_error(&err),
        "Action-level PrimedVariableNotBound errors should be caught in LET lazy binding"
    );
}

#[test]
fn test_is_let_lazy_safe_rejects_exit_requested() {
    let err = EvalError::ExitRequested { span: None };
    assert!(
        !is_let_lazy_safe_error(&err),
        "ExitRequested must propagate — it's a control flow signal"
    );
}

#[test]
fn test_is_let_lazy_safe_defers_type_error() {
    // TLC never evaluates unused LET bindings, so TypeError in an unused
    // binding is invisible. TLA2 must defer it to match TLC semantics.
    let err = EvalError::TypeError {
        expected: "Set",
        got: "Int",
        span: None,
    };
    assert!(
        is_let_lazy_safe_error(&err),
        "TypeError in unused LET binding should be deferred — TLC evaluates lazily"
    );
}

#[test]
fn test_is_let_lazy_safe_catches_unchanged_not_evaluable() {
    let err = EvalError::UnchangedNotEvaluable { span: None };
    assert!(
        is_let_lazy_safe_error(&err),
        "Action-level UnchangedNotEvaluable errors should be caught in LET lazy binding"
    );
}

#[test]
fn test_is_let_lazy_safe_catches_undefined_var() {
    let err = EvalError::UndefinedVar {
        name: "x".to_string(),
        span: None,
    };
    assert!(
        is_let_lazy_safe_error(&err),
        "UndefinedVar should be caught — binding may reference not-yet-bound variables"
    );
}

#[test]
fn test_is_let_lazy_safe_catches_undefined_op() {
    let err = EvalError::UndefinedOp {
        name: "Foo".to_string(),
        span: None,
    };
    assert!(
        is_let_lazy_safe_error(&err),
        "UndefinedOp should be caught — binding may reference not-yet-bound operators"
    );
}

#[test]
fn test_is_let_lazy_safe_defers_assertion_failed() {
    // TLC never evaluates unused LET bindings, so AssertionFailed in an
    // unused binding is invisible. TLA2 must defer it.
    let err = EvalError::AssertionFailed {
        message: "test".to_string(),
        span: None,
    };
    assert!(
        is_let_lazy_safe_error(&err),
        "AssertionFailed in unused LET binding should be deferred — TLC evaluates lazily"
    );
}

#[test]
fn test_is_let_lazy_safe_defers_division_by_zero() {
    // TLC never evaluates unused LET bindings, so DivisionByZero in an
    // unused binding is invisible. TLA2 must defer it.
    let err = EvalError::DivisionByZero { span: None };
    assert!(
        is_let_lazy_safe_error(&err),
        "DivisionByZero in unused LET binding should be deferred — TLC evaluates lazily"
    );
}

#[test]
fn test_is_let_lazy_safe_defers_arity_mismatch() {
    // TLC never evaluates unused LET bindings, so ArityMismatch in an
    // unused binding is invisible. TLA2 must defer it.
    let err = EvalError::ArityMismatch {
        op: "Foo".to_string(),
        expected: 2,
        got: 1,
        span: None,
    };
    assert!(
        is_let_lazy_safe_error(&err),
        "ArityMismatch in unused LET binding should be deferred — TLC evaluates lazily"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_is_disabled_action_error_not_in_domain() {
    let err = EvalError::NotInDomain {
        arg: "42".to_string(),
        func_display: None,
        span: None,
    };
    assert!(is_disabled_action_error(&err));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_is_disabled_action_error_index_out_of_bounds() {
    let err = EvalError::IndexOutOfBounds {
        index: 10,
        len: 5,
        value_display: None,
        span: None,
    };
    assert!(is_disabled_action_error(&err));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_is_disabled_action_error_no_such_field() {
    let err = EvalError::NoSuchField {
        field: "foo".to_string(),
        record_display: None,
        span: None,
    };
    assert!(is_disabled_action_error(&err));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_is_disabled_action_error_choose_failed() {
    let err = EvalError::ChooseFailed { span: None };
    assert!(is_disabled_action_error(&err));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_is_disabled_action_error_division_by_zero() {
    let err = EvalError::DivisionByZero { span: None };
    assert!(is_disabled_action_error(&err));
}

// FIX #353, #1326, #1479: TypeError is NOT a disabled action error,
// and is also NOT disabled in Or-branch contexts. TLC propagates
// TypeErrors (including non-boolean predicate errors) as fatal errors
// from all contexts, including Or branches.
// See: reports/prover/2026-01-27-p196-type-error-analysis.md
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_is_disabled_action_error_false_for_type_error() {
    let err = EvalError::TypeError {
        expected: "integer",
        got: "string",
        span: None,
    };
    assert!(!is_disabled_action_error(&err));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_is_disabled_action_error_false_for_other() {
    let err = EvalError::Internal {
        message: "unexpected error".to_string(),
        span: None,
    };
    assert!(!is_disabled_action_error(&err));
}
