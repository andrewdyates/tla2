// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! STRING module tests (membership, \notin, equality, \subseteq).
//!
//! Split from property_tests.rs lines 2505-2582. Part of #1371.

use tla_check::Value;
use tla_core::{lower, parse_to_syntax_tree, FileId};

// ============================================================================
// STRING module tests
// ============================================================================

fn eval_strings_str(src: &str) -> Result<Value, String> {
    let module_src = format!(
        "---- MODULE Test ----\nEXTENDS Strings\n\nOp == {}\n\n====",
        src
    );
    let tree = parse_to_syntax_tree(&module_src);
    let lower_result = lower(FileId(0), &tree);
    let module = match lower_result.module {
        Some(m) => m,
        None => return Err(format!("Parse error: {:?}", lower_result.errors)),
    };

    let mut ctx = tla_check::EvalCtx::new();
    ctx.load_module(&module);
    ctx.eval_op("Op").map_err(|e| format!("{:?}", e))
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_string_membership() {
    // A string is a member of STRING
    let result = eval_strings_str(r#""hello" \in STRING"#).unwrap();
    assert_eq!(result, Value::Bool(true));

    // An integer is not a member of STRING
    let result = eval_strings_str(r#"42 \in STRING"#).unwrap();
    assert_eq!(result, Value::Bool(false));

    // TRUE is not a member of STRING
    let result = eval_strings_str(r#"TRUE \in STRING"#).unwrap();
    assert_eq!(result, Value::Bool(false));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_string_not_in() {
    // An integer is not in STRING
    let result = eval_strings_str(r#"42 \notin STRING"#).unwrap();
    assert_eq!(result, Value::Bool(true));

    // A string is in STRING
    let result = eval_strings_str(r#""test" \notin STRING"#).unwrap();
    assert_eq!(result, Value::Bool(false));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_string_set_equality() {
    // Ensure STRING comparisons don't panic (STRING is non-enumerable).
    let err = eval_strings_str("STRING = {}").unwrap_err();
    assert!(
        err.contains("SetTooLarge"),
        "expected SetTooLarge, got: {err}"
    );

    let err = eval_strings_str("{} = STRING").unwrap_err();
    assert!(
        err.contains("SetTooLarge"),
        "expected SetTooLarge, got: {err}"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_string_set_subseteq() {
    let result = eval_strings_str(r#"{"a", "b"} \subseteq STRING"#).unwrap();
    assert_eq!(result, Value::Bool(true));

    let result = eval_strings_str(r#"{"a", 1} \subseteq STRING"#).unwrap();
    assert_eq!(result, Value::Bool(false));

    // Non-enumerable left side should be an error.
    assert!(eval_strings_str("STRING \\subseteq STRING").is_err());
}
