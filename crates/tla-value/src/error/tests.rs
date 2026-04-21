// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Snapshot tests for `EvalError` message format stability.
//!
//! These tests ensure error messages don't change unexpectedly.

use super::*;
use insta::assert_snapshot;
use tla_core::{FileId, Span};

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn snapshot_type_error() {
    let err = EvalError::TypeError {
        expected: "integer",
        got: "set",
        span: Some(Span::new(FileId(0), 10, 20)),
    };
    assert_snapshot!("snapshot_type_error", err.to_string());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn snapshot_division_by_zero() {
    let err = EvalError::DivisionByZero {
        span: Some(Span::new(FileId(0), 15, 20)),
    };
    assert_snapshot!("snapshot_division_by_zero", err.to_string());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn snapshot_modulus_not_positive() {
    let err = EvalError::ModulusNotPositive {
        value: "-5".to_string(),
        span: Some(Span::new(FileId(0), 15, 20)),
    };
    assert_snapshot!("snapshot_modulus_not_positive", err.to_string());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn snapshot_modulus_not_positive_zero() {
    let err = EvalError::ModulusNotPositive {
        value: "0".to_string(),
        span: Some(Span::new(FileId(0), 15, 20)),
    };
    assert_snapshot!("snapshot_modulus_not_positive_zero", err.to_string());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn snapshot_undefined_var() {
    let err = EvalError::UndefinedVar {
        name: "myVar".to_string(),
        span: Some(Span::new(FileId(0), 5, 10)),
    };
    assert_snapshot!("snapshot_undefined_var", err.to_string());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn snapshot_undefined_op() {
    let err = EvalError::UndefinedOp {
        name: "MyOperator".to_string(),
        span: Some(Span::new(FileId(0), 25, 35)),
    };
    assert_snapshot!("snapshot_undefined_op", err.to_string());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn snapshot_not_in_domain() {
    let err = EvalError::NotInDomain {
        arg: "42".to_string(),
        func_display: None,
        span: Some(Span::new(FileId(0), 30, 35)),
    };
    assert_snapshot!("snapshot_not_in_domain", err.to_string());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn snapshot_no_such_field() {
    let err = EvalError::NoSuchField {
        field: "missingField".to_string(),
        record_display: None,
        span: Some(Span::new(FileId(0), 40, 52)),
    };
    assert_snapshot!("snapshot_no_such_field", err.to_string());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn snapshot_no_such_field_tlc() {
    let err = EvalError::NoSuchField {
        field: "missingField".to_string(),
        record_display: Some("[a |-> 1, b |-> 2]".to_string()),
        span: Some(Span::new(FileId(0), 40, 52)),
    };
    assert_snapshot!("snapshot_no_such_field_tlc", err.to_string());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn snapshot_index_out_of_bounds() {
    let err = EvalError::IndexOutOfBounds {
        index: 10,
        len: 5,
        value_display: None,
        span: Some(Span::new(FileId(0), 50, 55)),
    };
    assert_snapshot!("snapshot_index_out_of_bounds", err.to_string());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn snapshot_index_out_of_bounds_tlc() {
    let err = EvalError::IndexOutOfBounds {
        index: 10,
        len: 3,
        value_display: Some("<<1, 2, 3>>".to_string()),
        span: Some(Span::new(FileId(0), 50, 55)),
    };
    assert_snapshot!("snapshot_index_out_of_bounds_tlc", err.to_string());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn snapshot_choose_failed() {
    let err = EvalError::ChooseFailed {
        span: Some(Span::new(FileId(0), 60, 75)),
    };
    assert_snapshot!("snapshot_choose_failed", err.to_string());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn snapshot_arity_mismatch() {
    let err = EvalError::ArityMismatch {
        op: "Add".to_string(),
        expected: 2,
        got: 1,
        span: Some(Span::new(FileId(0), 80, 85)),
    };
    assert_snapshot!("snapshot_arity_mismatch", err.to_string());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn snapshot_set_too_large() {
    let err = EvalError::SetTooLarge {
        span: Some(Span::new(FileId(0), 90, 100)),
    };
    assert_snapshot!("snapshot_set_too_large", err.to_string());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn snapshot_argument_error() {
    let err = EvalError::ArgumentError {
        position: "first",
        op: "+".to_string(),
        expected_type: "integer",
        value_display: "TRUE".to_string(),
        span: Some(Span::new(FileId(0), 85, 90)),
    };
    assert_snapshot!("snapshot_argument_error", err.to_string());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn snapshot_argument_error_an() {
    // Test "an" article for expected types starting with vowel
    let err = EvalError::ArgumentError {
        position: "second",
        op: "+".to_string(),
        expected_type: "integer",
        value_display: "\"hello\"".to_string(),
        span: Some(Span::new(FileId(0), 85, 90)),
    };
    assert_snapshot!("snapshot_argument_error_an", err.to_string());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn snapshot_internal_error() {
    let err = EvalError::Internal {
        message: "unexpected state in evaluator".to_string(),
        span: Some(Span::new(FileId(0), 100, 110)),
    };
    assert_snapshot!("snapshot_internal_error", err.to_string());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn snapshot_one_argument_error() {
    let err = EvalError::OneArgumentError {
        op: "Len",
        expected_type: "sequence",
        value_display: "TRUE".to_string(),
        span: Some(Span::new(FileId(0), 50, 55)),
    };
    assert_snapshot!("snapshot_one_argument_error", err.to_string());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn snapshot_apply_empty_seq() {
    let err = EvalError::ApplyEmptySeq {
        op: "Head",
        span: Some(Span::new(FileId(0), 50, 55)),
    };
    assert_snapshot!("snapshot_apply_empty_seq", err.to_string());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn snapshot_evaluating_error() {
    let err = EvalError::EvaluatingError {
        form: "Append(s, v)",
        expected_type: "sequence",
        value_display: "TRUE".to_string(),
        span: Some(Span::new(FileId(0), 50, 55)),
    };
    assert_snapshot!("snapshot_evaluating_error", err.to_string());
}
