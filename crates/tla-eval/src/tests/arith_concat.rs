// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::error::EvalError;
use crate::eval_arith::apply_builtin_binary_op;
use crate::value::Value;

#[test]
fn test_eval_arith_concat_string_string() {
    // Prover Finding 1: apply_builtin_binary_op \o must handle string
    // concatenation matching the parallel path in builtin_sequences.rs
    // (Sequences.java:147-158).
    let result =
        apply_builtin_binary_op("\\o", Value::string("abc"), Value::string("def"), None).unwrap();
    assert_eq!(result, Value::string("abcdef"));
}

#[test]
fn test_eval_arith_concat_string_empty() {
    let result =
        apply_builtin_binary_op("\\o", Value::string("abc"), Value::string(""), None).unwrap();
    assert_eq!(result, Value::string("abc"));
}

#[test]
fn test_eval_arith_concat_empty_string() {
    let result =
        apply_builtin_binary_op("\\o", Value::string(""), Value::string("abc"), None).unwrap();
    assert_eq!(result, Value::string("abc"));
}

#[test]
fn test_eval_arith_concat_string_seq_type_mismatch() {
    let err = apply_builtin_binary_op(
        "\\o",
        Value::string("abc"),
        Value::seq([Value::int(1)]),
        None,
    )
    .unwrap_err();
    assert!(
        matches!(
            err,
            EvalError::EvaluatingError {
                expected_type: "string",
                ..
            }
        ),
        "Expected EvaluatingError with expected_type 'string', got {:?}",
        err
    );
}

#[test]
fn test_eval_arith_concat_seq_seq() {
    let result = apply_builtin_binary_op(
        "\\o",
        Value::seq([Value::int(1), Value::int(2)]),
        Value::seq([Value::int(3)]),
        None,
    )
    .unwrap();
    assert_eq!(
        result,
        Value::seq([Value::int(1), Value::int(2), Value::int(3)])
    );
}
