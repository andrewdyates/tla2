// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! TLCExt module operator tests (AssertEq, TLCDefer, PickSuccessor, TLCNoOp,
//! TLCCache, TLCGetOrDefault, TLCGetAndSet, TLCFP, AssertError,
//! TLCEvalDefinition, Trace, CounterExample, ToTrace).
//!
//! Consolidated from property_tests.rs lines 1816-1980, 2211-2503, 3883-3958.
//! Part of #1371.

use tla_check::Value;
use tla_core::{lower, parse_to_syntax_tree, FileId};

use super::helpers::int_set;

// ============================================================================
// TLCExt operator tests
// ============================================================================

fn eval_tlcext_str(src: &str) -> Result<Value, String> {
    let ctx = tla_check::EvalCtx::new();
    eval_tlcext_str_with_ctx(&ctx, src)
}

fn eval_tlcext_str_with_ctx(ctx: &tla_check::EvalCtx, src: &str) -> Result<Value, String> {
    let module_src = format!(
        "---- MODULE Test ----\nEXTENDS TLC, TLCExt\n\nOp == {}\n\n====",
        src
    );
    let tree = parse_to_syntax_tree(&module_src);
    let lower_result = lower(FileId(0), &tree);
    let module = match lower_result.module {
        Some(m) => m,
        None => return Err(format!("Parse error: {:?}", lower_result.errors)),
    };

    for unit in &module.units {
        if let tla_core::ast::Unit::Operator(def) = &unit.node {
            if def.name.node == "Op" {
                return tla_check::eval(ctx, &def.body).map_err(|e| format!("{:?}", e));
            }
        }
    }
    Err("Op not found".to_string())
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_assert_eq_equal() {
    // AssertEq returns TRUE when values are equal
    let result = eval_tlcext_str("AssertEq(1, 1)").unwrap();
    assert_eq!(result, Value::Bool(true));

    let result = eval_tlcext_str("AssertEq({1, 2}, {2, 1})").unwrap();
    assert_eq!(result, Value::Bool(true));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_assert_eq_unequal() {
    // AssertEq returns FALSE when values are not equal
    let result = eval_tlcext_str("AssertEq(1, 2)").unwrap();
    assert_eq!(result, Value::Bool(false));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tlc_defer() {
    // TLCDefer evaluates and returns the expression
    let result = eval_tlcext_str("TLCDefer(1 + 2)").unwrap();
    assert_eq!(result, Value::int(3));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pick_successor() {
    // PickSuccessor returns TRUE (stub behavior)
    let result = eval_tlcext_str("PickSuccessor(TRUE)").unwrap();
    assert_eq!(result, Value::Bool(true));

    let result = eval_tlcext_str("PickSuccessor(FALSE)").unwrap();
    assert_eq!(result, Value::Bool(true));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tlc_noop() {
    // TLCNoOp returns its argument unchanged
    let result = eval_tlcext_str("TLCNoOp(42)").unwrap();
    assert_eq!(result, Value::int(42));

    let result = eval_tlcext_str("TLCNoOp({1, 2, 3})").unwrap();
    assert_eq!(result, int_set(&[1, 2, 3]));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tlc_cache() {
    // TLCCache returns the expression (stub behavior)
    let result = eval_tlcext_str("TLCCache(1 + 2, 3)").unwrap();
    assert_eq!(result, Value::int(3));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tlc_get_or_default() {
    // TLCGetOrDefault returns default value when key not set
    let result = eval_tlcext_str("TLCGetOrDefault(1, 42)").unwrap();
    assert_eq!(result, Value::int(42));

    // Works with different types
    let result = eval_tlcext_str("TLCGetOrDefault(0, TRUE)").unwrap();
    assert_eq!(result, Value::Bool(true));

    let result = eval_tlcext_str("TLCGetOrDefault(99, {1, 2, 3})").unwrap();
    assert_eq!(result, int_set(&[1, 2, 3]));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tlc_get_and_set() {
    // TLCGetAndSet returns the default value (old value) since no registers are set
    // TLCGetAndSet(key, Op, val, defaultVal) - returns oldVal before setting
    let module_src = r#"---- MODULE Test ----
EXTENDS TLC, TLCExt

Add(a, b) == a + b
Op == TLCGetAndSet(1, Add, 5, 10)

===="#;
    let tree = parse_to_syntax_tree(module_src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let mut ctx = tla_check::EvalCtx::new();
    ctx.load_module(&module);
    let result = ctx.eval_op("Op").unwrap();
    // Returns the default value (since no register was set)
    assert_eq!(result, Value::int(10));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tlcfp_integer() {
    // TLCFP returns a fingerprint for an integer
    let result = eval_tlcext_str("TLCFP(42)").unwrap();
    // Should be an integer (lower 32 bits of fingerprint)
    // Use is_int() to handle both SmallInt and Int variants
    assert!(result.is_int());

    // Same value should produce same fingerprint
    let result1 = eval_tlcext_str("TLCFP(42)").unwrap();
    let result2 = eval_tlcext_str("TLCFP(42)").unwrap();
    assert_eq!(result1, result2);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tlcfp_different_values() {
    // Different values should (very likely) produce different fingerprints
    let result1 = eval_tlcext_str("TLCFP(1)").unwrap();
    let result2 = eval_tlcext_str("TLCFP(2)").unwrap();
    assert_ne!(result1, result2);

    // Different types should produce different fingerprints
    let result_int = eval_tlcext_str("TLCFP(1)").unwrap();
    let result_str = eval_tlcext_str(r#"TLCFP("1")"#).unwrap();
    assert_ne!(result_int, result_str);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tlcfp_set() {
    // TLCFP works with sets
    let result = eval_tlcext_str("TLCFP({1, 2, 3})").unwrap();
    // Use is_int() to handle both SmallInt and Int variants
    assert!(result.is_int());

    // Same set (different order) should produce same fingerprint
    let result1 = eval_tlcext_str("TLCFP({1, 2, 3})").unwrap();
    let result2 = eval_tlcext_str("TLCFP({3, 2, 1})").unwrap();
    assert_eq!(result1, result2);
}

// ============================================================================
// AssertError tests - TLC semantics: catches evaluation errors
// ============================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_assert_error_no_error_returns_false() {
    // When expr evaluates successfully (no error), AssertError returns FALSE
    let result = eval_tlcext_str(r#"AssertError("irrelevant", TRUE)"#).unwrap();
    assert_eq!(result, Value::Bool(false));

    let result = eval_tlcext_str(r#"AssertError("irrelevant", 42)"#).unwrap();
    assert_eq!(result, Value::Bool(false));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_assert_error_catches_error() {
    // When expr throws an error, AssertError catches it and returns FALSE
    // (because message doesn't match). This proves error-catching works -
    // if errors weren't caught, eval_tlcext_str would return Err.
    let result =
        eval_tlcext_str(r#"AssertError("wrong message", Assert(FALSE, "actual error"))"#).unwrap();
    assert_eq!(result, Value::Bool(false));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_assert_error_assert_message_passthrough_tlc_parity() {
    // TLC semantics: Assert(FALSE, msg) throws the message string directly.
    // AssertError(msg, Assert(FALSE, msg)) returns TRUE because the thrown
    // error message is exactly the raw string, not wrapped.
    // Ref: TLC Assert.java — EvalException carries the raw message.
    let result =
        eval_tlcext_str(r#"AssertError("my custom error", Assert(FALSE, "my custom error"))"#)
            .unwrap();
    assert_eq!(result, Value::Bool(true));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_assert_error_domain_error_format_tlc_parity() {
    // Verify NotInDomain error message matches TLC format (FcnRcdValue.java:354-356).
    // TLC: "Attempted to apply function:\n<func>\nto argument <arg>, which is
    //       not in the domain of the function."
    // Test via direct EvalError construction to avoid value-display fragility.
    use tla_check::EvalError;

    // With func_display (TLC FcnRcdValue format)
    let err = EvalError::NotInDomain {
        arg: "3".to_string(),
        func_display: Some("(1 :> \"a\" @@ 2 :> \"b\")".to_string()),
        span: None,
    };
    assert_eq!(
        err.to_string(),
        "Attempted to apply function:\n(1 :> \"a\" @@ 2 :> \"b\")\nto argument 3, which is not in the domain of the function."
    );

    // Without func_display (compact variant)
    let err = EvalError::NotInDomain {
        arg: "42".to_string(),
        func_display: None,
        span: None,
    };
    assert_eq!(
        err.to_string(),
        "Attempted to apply function to argument 42, which is not in the domain of the function."
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_assert_error_type_error_catches() {
    // Verify that type errors thrown during evaluation are caught by AssertError.
    // TLC-compatible format (EC.TLC_MODULE_ARGUMENT_ERROR):
    //   "The second argument of + should be an integer, but instead it is:\nTRUE"
    let module_src =
        "---- MODULE Test ----\nEXTENDS TLC, TLCExt, Integers\n\nOp == AssertError(\"The second argument of + should be an integer, but instead it is:\\nTRUE\", 1 + TRUE)\n\n====";
    let tree = parse_to_syntax_tree(module_src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.expect("parse should succeed");
    for unit in &module.units {
        if let tla_core::ast::Unit::Operator(def) = &unit.node {
            if def.name.node == "Op" {
                let ctx = tla_check::EvalCtx::new();
                let result = tla_check::eval(&ctx, &def.body).unwrap();
                assert_eq!(result, Value::Bool(true));
                return;
            }
        }
    }
    panic!("Op not found");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_assert_error_argument_error_first_arg_tlc_parity() {
    // TLC EC.TLC_MODULE_ARGUMENT_ERROR parity for first argument type error.
    // TLC: "The first argument of + should be an integer, but instead it is:\nTRUE"
    let module_src =
        "---- MODULE Test ----\nEXTENDS TLC, TLCExt, Integers\n\nOp == AssertError(\"The first argument of + should be an integer, but instead it is:\\nTRUE\", TRUE + 1)\n\n====";
    let tree = parse_to_syntax_tree(module_src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.expect("parse should succeed");
    for unit in &module.units {
        if let tla_core::ast::Unit::Operator(def) = &unit.node {
            if def.name.node == "Op" {
                let ctx = tla_check::EvalCtx::new();
                let result = tla_check::eval(&ctx, &def.body).unwrap();
                assert_eq!(result, Value::Bool(true));
                return;
            }
        }
    }
    panic!("Op not found");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_assert_error_argument_error_wrong_msg_returns_false() {
    // Using the OLD format (which no longer matches) should return FALSE.
    // This verifies exact-match semantics.
    let module_src =
        "---- MODULE Test ----\nEXTENDS TLC, TLCExt, Integers\n\nOp == AssertError(\"Type error: expected Int, got BOOLEAN\", 1 + TRUE)\n\n====";
    let tree = parse_to_syntax_tree(module_src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.expect("parse should succeed");
    for unit in &module.units {
        if let tla_core::ast::Unit::Operator(def) = &unit.node {
            if def.name.node == "Op" {
                let ctx = tla_check::EvalCtx::new();
                let result = tla_check::eval(&ctx, &def.body).unwrap();
                // Old format no longer matches, so AssertError returns FALSE
                assert_eq!(result, Value::Bool(false));
                return;
            }
        }
    }
    panic!("Op not found");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_assert_error_matching_message() {
    // Test exact message matching via direct eval to avoid TLA+ string escaping issues.
    // Build AssertError("The second argument of \\div is 0.", <expr that divides by zero>)
    // The Integers module provides \div, but we need EXTENDS Integers.
    // Message matches TLC's EC.TLC_MODULE_DIVISION_BY_ZERO exactly.
    let module_src =
        "---- MODULE Test ----\nEXTENDS TLC, TLCExt, Integers\n\nOp == AssertError(\"The second argument of \\\\div is 0.\", 1 \\div 0)\n\n====";
    let tree = parse_to_syntax_tree(module_src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.expect("parse should succeed");
    for unit in &module.units {
        if let tla_core::ast::Unit::Operator(def) = &unit.node {
            if def.name.node == "Op" {
                let ctx = tla_check::EvalCtx::new();
                let result = tla_check::eval(&ctx, &def.body).unwrap();
                assert_eq!(result, Value::Bool(true));
                return;
            }
        }
    }
    panic!("Op not found");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_assert_error_division_message_mismatch() {
    // Verify that a WRONG message returns FALSE (TLC parity: exact match required)
    let module_src =
        "---- MODULE Test ----\nEXTENDS TLC, TLCExt, Integers\n\nOp == AssertError(\"Division by zero\", 1 \\div 0)\n\n====";
    let tree = parse_to_syntax_tree(module_src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.expect("parse should succeed");
    for unit in &module.units {
        if let tla_core::ast::Unit::Operator(def) = &unit.node {
            if def.name.node == "Op" {
                let ctx = tla_check::EvalCtx::new();
                let result = tla_check::eval(&ctx, &def.body).unwrap();
                // "Division by zero" is NOT the TLC message, so this returns FALSE
                assert_eq!(result, Value::Bool(false));
                return;
            }
        }
    }
    panic!("Op not found");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_assert_error_modulus_message_tlc_parity() {
    // TLC message for modulus with non-positive arg:
    // "The second argument of % should be a positive number, but instead it is:\n<value>"
    let module_src =
        "---- MODULE Test ----\nEXTENDS TLC, TLCExt, Integers\n\nOp == AssertError(\"The second argument of % should be a positive number, but instead it is:\\n0\", 1 % 0)\n\n====";
    let tree = parse_to_syntax_tree(module_src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.expect("parse should succeed");
    for unit in &module.units {
        if let tla_core::ast::Unit::Operator(def) = &unit.node {
            if def.name.node == "Op" {
                let ctx = tla_check::EvalCtx::new();
                let result = tla_check::eval(&ctx, &def.body).unwrap();
                assert_eq!(result, Value::Bool(true));
                return;
            }
        }
    }
    panic!("Op not found");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_assert_error_no_such_field_tlc_parity() {
    // TLC RecordValue.java:484-485 format:
    // "Attempted to access nonexistent field '<field>' of record\n<record>"
    // Test that AssertError catches record field errors with TLC-format messages.
    use tla_check::EvalError;

    // First verify the error message format directly
    let err = EvalError::NoSuchField {
        field: "b".to_string(),
        record_display: Some("[a |-> 1]".to_string()),
        span: None,
    };
    let expected_msg = "Attempted to access nonexistent field 'b' of record\n[a |-> 1]";
    assert_eq!(err.to_string(), expected_msg);

    // Now test via AssertError end-to-end: evaluate [a |-> 1].b which should throw
    // a NoSuchField error with record_display, and verify AssertError catches it
    // with the correct TLC-format message.
    let result = eval_tlcext_str(
        r#"AssertError("Attempted to access nonexistent field 'b' of record\n[a |-> 1]", [a |-> 1].b)"#,
    );
    match result {
        Ok(v) => assert_eq!(
            v,
            Value::Bool(true),
            "AssertError should return TRUE for matching NoSuchField message"
        ),
        Err(e) => panic!("Expected Ok(Bool(true)), got Err: {}", e),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_assert_error_index_out_of_bounds_tlc_parity() {
    // TLC TupleValue.java:144 format for sequence/tuple index out of bounds:
    // "Attempted to access index <N> of tuple\n<tuple>\nwhich is out of bounds."
    // Sequences/tuples in TLC are TupleValue, not FcnRcdValue, so they report
    // "out of bounds" rather than "not in the domain".
    use tla_check::EvalError;

    // First verify the error message format directly
    let err = EvalError::IndexOutOfBounds {
        index: 5,
        len: 3,
        value_display: Some("<<1, 2, 3>>".to_string()),
        span: None,
    };
    let expected_msg = "Attempted to access index 5 of tuple\n<<1, 2, 3>>\nwhich is out of bounds.";
    assert_eq!(err.to_string(), expected_msg);

    // Now test via AssertError end-to-end: evaluate <<1, 2, 3>>[5] which should throw
    // an IndexOutOfBounds error, and verify AssertError catches it with the TLC-format message.
    let result = eval_tlcext_str(
        r#"AssertError("Attempted to access index 5 of tuple\n<<1, 2, 3>>\nwhich is out of bounds.", <<1, 2, 3>>[5])"#,
    );
    match result {
        Ok(v) => assert_eq!(
            v,
            Value::Bool(true),
            "AssertError should return TRUE for matching IndexOutOfBounds message"
        ),
        Err(e) => panic!("Expected Ok(Bool(true)), got Err: {}", e),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_assert_error_no_such_field_wrong_msg_returns_false() {
    // Verify that old-format message does NOT match (exact-match semantics)
    let result = eval_tlcext_str(r#"AssertError("Record has no field: b", [a |-> 1].b)"#);
    match result {
        Ok(v) => assert_eq!(
            v,
            Value::Bool(false),
            "Old-format message should NOT match TLC format"
        ),
        Err(e) => panic!("Expected Ok(Bool(false)), got Err: {}", e),
    }
}

// ============================================================================
// TLCExt operator tests - TLCEvalDefinition, Trace, CounterExample, ToTrace
// ============================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tlc_eval_definition() {
    // TLCEvalDefinition evaluates a zero-arity definition by name
    let module_src = r#"---- MODULE Test ----
EXTENDS TLC, TLCExt

MyConst == 42
Op == TLCEvalDefinition("MyConst")

===="#;
    let tree = parse_to_syntax_tree(module_src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let mut ctx = tla_check::EvalCtx::new();
    ctx.load_module(&module);
    let result = ctx.eval_op("Op").unwrap();
    assert_eq!(result, Value::int(42));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tlc_eval_definition_complex() {
    // TLCEvalDefinition with a more complex expression
    let module_src = r#"---- MODULE Test ----
EXTENDS TLC, TLCExt

MySet == {1, 2, 3}
Op == TLCEvalDefinition("MySet")

===="#;
    let tree = parse_to_syntax_tree(module_src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let mut ctx = tla_check::EvalCtx::new();
    ctx.load_module(&module);
    let result = ctx.eval_op("Op").unwrap();
    assert_eq!(result, int_set(&[1, 2, 3]));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_trace_without_context() {
    // Part of #1117: Trace returns error when called without trace context
    // (i.e., outside model checking where trace is reconstructed and set)
    let result = eval_tlcext_str("Trace");
    assert!(result.is_err(), "Trace should error without trace context");
    let err_msg = result.unwrap_err().clone();
    assert!(
        err_msg.contains("trace context not available"),
        "Expected trace context error, got: {}",
        err_msg
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_counter_example_without_context_returns_empty_graph() {
    let result = eval_tlcext_str("CounterExample").unwrap();
    assert_eq!(
        result,
        Value::record([
            ("action", Value::empty_set()),
            ("state", Value::empty_set()),
        ])
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_counter_example_with_trace_context_builds_state_graph() {
    let mut ctx = tla_check::EvalCtx::new();
    ctx.set_tlc_trace_value(Some(Value::tuple([
        Value::record([("x", Value::int(1))]),
        Value::record([("x", Value::int(2))]),
    ])));

    let result = eval_tlcext_str_with_ctx(&ctx, "CounterExample").unwrap();
    assert_eq!(
        result,
        Value::record([
            (
                "action",
                Value::set([Value::tuple([
                    Value::tuple([Value::int(1), Value::record([("x", Value::int(1))]),]),
                    Value::record([("name", Value::string("<Action>"))]),
                    Value::tuple([Value::int(2), Value::record([("x", Value::int(2))]),]),
                ])]),
            ),
            (
                "state",
                Value::set([
                    Value::tuple([Value::int(1), Value::record([("x", Value::int(1))]),]),
                    Value::tuple([Value::int(2), Value::record([("x", Value::int(2))]),]),
                ]),
            ),
        ])
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_to_trace_round_trips_counter_example() {
    let expected_trace = Value::tuple([
        Value::record([("x", Value::int(1))]),
        Value::record([("x", Value::int(2))]),
    ]);
    let mut ctx = tla_check::EvalCtx::new();
    ctx.set_tlc_trace_value(Some(expected_trace.clone()));

    let result = eval_tlcext_str_with_ctx(&ctx, "ToTrace(CounterExample)").unwrap();
    assert_eq!(result, expected_trace);
}
