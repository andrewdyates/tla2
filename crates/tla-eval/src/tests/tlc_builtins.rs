// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for `builtin_tlc` and `builtin_tlcext` module operators.

use super::eval_str;
use crate::error::EvalError;
use crate::Value;
use std::sync::Arc;
use tla_core::{lower, parse_to_syntax_tree, FileId};

fn eval_op_with_ctx(module_src: &str, ctx: &crate::EvalCtx, op_name: &str) -> Value {
    let tree = parse_to_syntax_tree(module_src);
    let lower_result = lower(FileId(0), &tree);
    let module = match lower_result.module {
        Some(module) => module,
        None => panic!("failed to lower module: {:?}", lower_result.errors),
    };
    let mut eval_ctx = ctx.clone();
    eval_ctx.load_module(&module);
    eval_ctx
        .eval_op(op_name)
        .unwrap_or_else(|err| panic!("failed to evaluate {op_name}: {err:?}"))
}

// --- ToString ---

#[test]
fn test_to_string_integer() {
    let v = eval_str("ToString(42)").unwrap();
    assert_eq!(v.as_string().unwrap(), "42");
}

#[test]
fn test_to_string_boolean() {
    let v = eval_str("ToString(TRUE)").unwrap();
    assert_eq!(v.as_string().unwrap(), "TRUE");
}

#[test]
fn test_to_string_string() {
    let v = eval_str("ToString(\"hello\")").unwrap();
    assert_eq!(v.as_string().unwrap(), "\"hello\"");
}

// --- Assert ---

#[test]
fn test_assert_true_returns_true() {
    let v = eval_str("Assert(TRUE, \"should not fail\")").unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_assert_false_errors() {
    let result = eval_str("Assert(FALSE, \"assertion failed\")");
    assert!(result.is_err());
    let err_msg = format!("{}", result.unwrap_err());
    assert!(
        err_msg.contains("assertion failed"),
        "Expected assertion message, got: {}",
        err_msg
    );
}

// --- :> (single-element function) ---

#[test]
fn test_colon_greater_creates_function() {
    // "a" :> 1 creates [a |-> 1]
    let v = eval_str("(\"a\" :> 1)[\"a\"]").unwrap();
    assert_eq!(v, Value::SmallInt(1));
}

// --- @@ (function merge) ---

#[test]
fn test_at_at_merge_disjoint() {
    // Merge two disjoint functions
    let v = eval_str("((\"a\" :> 1) @@ (\"b\" :> 2))[\"b\"]").unwrap();
    assert_eq!(v, Value::SmallInt(2));
}

#[test]
fn test_at_at_merge_overlapping_left_priority() {
    // f @@ g: f takes priority for overlapping keys
    let v = eval_str("((\"a\" :> 1) @@ (\"a\" :> 2))[\"a\"]").unwrap();
    assert_eq!(v, Value::SmallInt(1));
}

#[test]
fn test_at_at_merge_records() {
    // Record merge preserves record type
    let v = eval_str("([a |-> 1] @@ [b |-> 2]).b").unwrap();
    assert_eq!(v, Value::SmallInt(2));
}

#[test]
fn test_at_at_record_override() {
    // Left record overrides right for overlapping fields
    let v = eval_str("([a |-> 10] @@ [a |-> 20]).a").unwrap();
    assert_eq!(v, Value::SmallInt(10));
}

#[test]
fn test_at_at_incompatible_types_errors() {
    // TLC raises a type error for @@ on incompatible types (e.g., int @@ set).
    // This tests the builtin_tlc.rs @@ operator path (via to_func_coerced).
    let result = eval_str("3 @@ {1, 2}");
    assert!(
        matches!(result, Err(EvalError::TypeError { .. })),
        "Expected TypeError for incompatible @@ operands, got: {:?}",
        result
    );
}

#[test]
fn test_at_at_string_and_integer_errors() {
    // Strings and integers are not records or functions
    // This tests the builtin_tlc.rs @@ operator path (via to_func_coerced).
    let result = eval_str("\"hello\" @@ 42");
    assert!(
        matches!(result, Err(EvalError::TypeError { .. })),
        "Expected TypeError for string @@ int, got: {:?}",
        result
    );
}

// --- merge_values (convert.rs helper, used by SVG module) ---

#[test]
fn test_merge_values_incompatible_types_errors() {
    // Directly test convert.rs::merge_values catch-all.
    // Regression: previously returned Ok(left.clone()) silently (#1877).
    use crate::merge_values;
    let left = Value::SmallInt(3);
    let right = Value::Set(Default::default());
    let result = merge_values(&left, &right);
    assert!(
        matches!(result, Err(EvalError::TypeError { .. })),
        "Expected TypeError from merge_values for int vs set, got: {:?}",
        result
    );
}

#[test]
fn test_merge_values_records_succeed() {
    // Verify merge_values still works for valid record merge.
    use crate::merge_values;
    let left = Value::record([("a", Value::SmallInt(1))]);
    let right = Value::record([("b", Value::SmallInt(2))]);
    let merged = merge_values(&left, &right).expect("record merge should succeed");
    // Merged record should have both fields
    if let Value::Record(r) = &merged {
        assert_eq!(r.len(), 2);
    } else {
        panic!("Expected Record, got: {:?}", merged);
    }
}

// --- TLCSet / TLCGet ---

#[test]
fn test_tlc_set_and_get_register() {
    // TLCSet stores a value, TLCGet retrieves it
    // Use sequence: TLCSet returns TRUE, then TLCGet retrieves
    // We test this by asserting the set succeeded
    let v = eval_str("TLCSet(0, 42)").unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_tlc_get_unset_register_errors() {
    // Getting an unset register should error with NotInDomain
    let err = eval_str("TLCGet(99999)").unwrap_err();
    let msg = format!("{}", err);
    assert!(
        msg.contains("TLCGet")
            || matches!(
                err,
                EvalError::NotInDomain { .. } | EvalError::Internal { .. }
            ),
        "Expected TLCGet-related error, got: {}",
        msg
    );
}

#[test]
fn test_tlc_set_exit_true() {
    // TLCSet("exit", TRUE) triggers ExitRequested
    let err = eval_str("TLCSet(\"exit\", TRUE)").unwrap_err();
    assert!(
        matches!(err, EvalError::ExitRequested { .. }),
        "Expected ExitRequested, got: {:?}",
        err
    );
}

#[test]
fn test_tlc_set_exit_non_true_ignored() {
    // TLCSet("exit", FALSE) is silently ignored per TLC semantics
    let v = eval_str("TLCSet(\"exit\", FALSE)").unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_random_element_simulation_mode_bypasses_zero_arg_cache() {
    // When simulation RNG is seeded, RandomElement should use the RNG path
    // instead of the deterministic fingerprint-based selection. Two calls with
    // the same set should return different elements (with high probability)
    // because the RNG advances between calls.
    let ctx = crate::EvalCtx::new();
    ctx.set_simulation_random_seed(Some(42));

    let v1 = super::eval_str_with_ctx("RandomElement({1,2,3,4,5,6,7,8,9,10})", &ctx).unwrap();
    let v2 = super::eval_str_with_ctx("RandomElement({1,2,3,4,5,6,7,8,9,10})", &ctx).unwrap();

    // Both must be valid set members
    let v1_int = v1.as_i64().expect("v1 should be an integer");
    let v2_int = v2.as_i64().expect("v2 should be an integer");
    assert!((1..=10).contains(&v1_int), "v1={v1_int} out of range");
    assert!((1..=10).contains(&v2_int), "v2={v2_int} out of range");

    // With a 10-element set, the probability of two consecutive RNG draws hitting
    // the same index is 1/10. Over the test suite this is acceptable — the key
    // property is that the simulation RNG path is used at all.
    assert_ne!(
        v1_int, v2_int,
        "simulation RNG should produce different selections"
    );
}

#[test]
fn test_tlc_get_runtime_stats_override_level_stats() {
    // When runtime stats are set, TLCGet("stats") should return them instead
    // of the default BFS level-based stats.
    let ctx = crate::EvalCtx::new();
    ctx.set_tlc_runtime_stats(Some(crate::core::TlcRuntimeStats::new(100, 50, 10, 3, 3)));

    let v = super::eval_str_with_ctx("TLCGet(\"stats\").generated", &ctx).unwrap();
    assert_eq!(v, Value::SmallInt(100));

    let v = super::eval_str_with_ctx("TLCGet(\"stats\").distinct", &ctx).unwrap();
    assert_eq!(v, Value::SmallInt(50));

    let v = super::eval_str_with_ctx("TLCGet(\"stats\").traces", &ctx).unwrap();
    assert_eq!(v, Value::SmallInt(3));
}

#[test]
fn test_tlc_get_action_without_action_scope_returns_dummy_name() {
    let v = eval_str("TLCGet(\"action\").name").unwrap();
    assert_eq!(v, Value::String("".into()));
}

#[test]
fn test_tlc_get_action_zero_arg_operator_uses_action_name() {
    let ctx = crate::EvalCtx::new().with_next_state(Default::default());
    let v = eval_op_with_ctx(
        r#"---- MODULE Test ----
EXTENDS TLC

Action == TLCGet("action").name
Op == Action

===="#,
        &ctx,
        "Op",
    );
    assert_eq!(v, Value::String("Action".into()));
}

#[test]
fn test_tlc_get_action_nested_zero_arg_helper_keeps_outer_action_name() {
    let ctx = crate::EvalCtx::new().with_next_state(Default::default());
    let v = eval_op_with_ctx(
        r#"---- MODULE Test ----
EXTENDS TLC

Helper == TLCGet("action").name
Action == Helper
Op == Action

===="#,
        &ctx,
        "Op",
    );
    assert_eq!(v, Value::String("Action".into()));
}

#[test]
fn test_tlc_get_action_applied_operator_exposes_parameter_context() {
    let ctx = crate::EvalCtx::new().with_next_state(Default::default());
    let v = eval_op_with_ctx(
        r#"---- MODULE Test ----
EXTENDS TLC

Action(p) == TLCGet("action").context.p
Op == Action(42)

===="#,
        &ctx,
        "Op",
    );
    assert_eq!(v, Value::SmallInt(42));
}

// --- TLCEval ---

#[test]
fn test_tlc_eval_passthrough() {
    // TLCEval just evaluates its argument (TLA2 is already eager)
    let v = eval_str("TLCEval(1 + 2)").unwrap();
    assert_eq!(v, Value::SmallInt(3));
}

// --- Permutations ---

#[test]
fn test_permutations_two_elements() {
    // Permutations({1,2}) = 2 bijections
    let v = eval_str("Cardinality(Permutations({1, 2}))").unwrap();
    assert_eq!(v, Value::SmallInt(2));
}

#[test]
fn test_permutations_three_elements() {
    // 3! = 6
    let v = eval_str("Cardinality(Permutations({1, 2, 3}))").unwrap();
    assert_eq!(v, Value::SmallInt(6));
}

#[test]
fn test_permutations_single_element() {
    // Only one permutation of a single element
    let v = eval_str("Cardinality(Permutations({1}))").unwrap();
    assert_eq!(v, Value::SmallInt(1));
}

// --- AssertEq ---

#[test]
fn test_assert_eq_equal() {
    let v = eval_str("AssertEq(1 + 1, 2)").unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_assert_eq_not_equal() {
    let v = eval_str("AssertEq(1, 2)").unwrap();
    assert_eq!(v, Value::Bool(false));
}

// Regression test for #2894: AssertEq must use values_equal for set comparison.
// Without values_equal, SetPred({x \in {1,2,3} : x < 3}) and Set({1,2}) compare
// as structurally different via PartialEq, making AssertEq return FALSE when
// these sets are extensionally equal.
#[test]
fn test_assert_eq_setpred_vs_explicit_set() {
    let v = eval_str("AssertEq({x \\in {1,2,3} : x < 3}, {1, 2})").unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_assert_eq_setpred_not_equal() {
    let v = eval_str("AssertEq({x \\in {1,2,3} : x < 3}, {1, 3})").unwrap();
    assert_eq!(v, Value::Bool(false));
}

// --- AssertError ---

#[test]
fn test_assert_error_catches_division_by_zero() {
    // AssertError(msg, expr) returns TRUE if expr throws with matching message
    // Use the actual TLC-compatible error message for DivisionByZero
    let v = eval_str("AssertError(\"The second argument of \\\\div is 0.\", 1 \\div 0)").unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_assert_error_wrong_message_returns_false() {
    // AssertError with non-matching message should return FALSE
    let v = eval_str("AssertError(\"dummy\", 1 \\div 0)").unwrap();
    assert_eq!(v, Value::Bool(false));
}

// --- TLCModelValue ---

#[test]
fn test_tlc_model_value() {
    let v = eval_str("TLCModelValue(\"m1\") = TLCModelValue(\"m1\")").unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_tlc_model_value_different() {
    let v = eval_str("TLCModelValue(\"m1\") = TLCModelValue(\"m2\")").unwrap();
    assert_eq!(v, Value::Bool(false));
}

// --- TLCDefer / TLCNoOp ---

#[test]
fn test_tlc_defer_passthrough() {
    let v = eval_str("TLCDefer(42)").unwrap();
    assert_eq!(v, Value::SmallInt(42));
}

#[test]
fn test_tlc_no_op_passthrough() {
    let v = eval_str("TLCNoOp(\"hello\")").unwrap();
    assert_eq!(v.as_string().unwrap(), "hello");
}

// --- atoi (IOUtils community module) ---

#[test]
fn test_atoi_numeric_string() {
    let v = eval_str("atoi(\"42\")").unwrap();
    assert_eq!(v, Value::Int(Arc::new(42.into())));
}

#[test]
fn test_atoi_negative_string() {
    let v = eval_str("atoi(\"-7\")").unwrap();
    assert_eq!(v, Value::Int(Arc::new((-7).into())));
}

#[test]
fn test_atoi_trimmed_whitespace() {
    let v = eval_str("atoi(\" 42 \")").unwrap();
    assert_eq!(v, Value::Int(Arc::new(42.into())));
}

#[test]
fn test_atoi_non_numeric_string_errors() {
    // Regression test for #2284: TLC throws EvalException for non-numeric strings,
    // TLA2 previously returned 0 silently via .unwrap_or(0).
    let result = eval_str("atoi(\"hello\")");
    assert!(
        matches!(result, Err(EvalError::ArgumentError { .. })),
        "atoi(\"hello\") should return ArgumentError, got: {:?}",
        result
    );
}

#[test]
fn test_atoi_empty_string_errors() {
    // Empty string is also non-numeric — TLC throws.
    let result = eval_str("atoi(\"\")");
    assert!(
        matches!(result, Err(EvalError::ArgumentError { .. })),
        "atoi(\"\") should return ArgumentError, got: {:?}",
        result
    );
}

// --- zeroPadN (IOUtils community module) ---

#[test]
fn test_zero_pad_n_basic() {
    let v = eval_str("zeroPadN(42, 6)").unwrap();
    assert_eq!(v.as_string().unwrap(), "000042");
}

#[test]
fn test_zero_pad_n_no_padding_needed() {
    let v = eval_str("zeroPadN(12345, 3)").unwrap();
    assert_eq!(v.as_string().unwrap(), "12345");
}

#[test]
fn test_zero_pad_n_bigint_not_truncated() {
    // Regression: #2299 - BigInt was truncated to i64 via to_i64().unwrap_or(0),
    // producing "0000000000" instead of the correct string representation.
    let v = eval_str("zeroPadN(2^128, 10)").unwrap();
    let s = v.as_string().unwrap();
    assert!(
        !s.chars().all(|c| c == '0'),
        "zeroPadN(2^128, 10) should not produce all zeros, got: {}",
        s
    );
    assert!(
        s.contains("340282366920938463463374607431768211456"),
        "zeroPadN(2^128, 10) should contain the full BigInt representation, got: {}",
        s
    );
}

// =============================================================================
// Part of #3287: TLC string token eager assignment regressions
// =============================================================================

/// Verify that TLCGet("action").name returns a string with an eagerly assigned
/// TLC token (non-zero), confirming builtin_tlc_get.rs routes through
/// Value::string() → intern_string().
#[test]
fn test_tlc_get_action_name_assigns_token_at_construction() {
    use tla_value::tlc_string_token;

    let v = eval_str("TLCGet(\"action\").name").unwrap();
    let Value::String(arc) = &v else {
        panic!("Expected Value::String from TLCGet(\"action\").name, got {v:?}");
    };
    let tok = tlc_string_token(arc);
    assert_ne!(
        tok, 0,
        "TLCGet(\"action\").name should have eager TLC token, got 0"
    );
}

/// Verify that SVG Line element coordinate strings have eagerly assigned
/// TLC tokens, confirming builtin_svg.rs routes through Value::string() →
/// intern_string().
#[test]
fn test_svg_line_coordinate_strings_assign_tokens_at_construction() {
    use tla_value::tlc_string_token;

    let v = eval_str("Line(0, 0, 1, 1, [stroke |-> \"black\"]).name").unwrap();
    let Value::String(arc) = &v else {
        panic!("Expected Value::String from Line().name, got {v:?}");
    };
    let tok = tlc_string_token(arc);
    assert_ne!(
        tok, 0,
        "SVG element name should have eager TLC token, got 0"
    );
}
