// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::unwrap_used)]

use super::*;
use crate::expr::eval_array_select;
use crate::{ChcDtConstructor, ChcDtSelector, ChcSort, ChcVar};
use std::sync::Arc;

/// Test helper: call term_body_to_smt_value with empty DT ctor set.
fn tv(term: &z4_frontend::Term) -> Option<SmtValue> {
    term_body_to_smt_value(term, &FxHashSet::default())
}

/// Test helper: call parse_model_into with empty DT ctor set.
fn pm(model: &mut FxHashMap<String, SmtValue>, s: &str) {
    parse_model_into(model, s, &FxHashSet::default());
}

/// Verify that `quote_symbol` (now delegating to `z4_core::quote_symbol`)
/// correctly quotes reserved words like "true", "false", "let", "assert".
#[test]
fn test_quote_symbol_matches_z4_core_on_reserved_words() {
    let reserved = ["true", "false", "let", "forall", "exists", "assert"];
    for name in &reserved {
        let local = quote_symbol(name);
        let core = z4_core::quote_symbol(name);
        assert_eq!(
            local, core,
            "quote_symbol should match z4_core for reserved word '{name}'"
        );
        // Reserved words must be pipe-quoted.
        assert!(
            local.starts_with('|') && local.ends_with('|'),
            "reserved word '{name}' should be pipe-quoted: got {local:?}"
        );
    }
}

/// Verify that `quote_symbol` (now delegating to `z4_core::quote_symbol`)
/// correctly sanitizes pipe characters inside names.
#[test]
fn test_quote_symbol_matches_z4_core_on_pipe_chars() {
    let name = "a|b";
    let local = quote_symbol(name);
    let core = z4_core::quote_symbol(name);
    assert_eq!(
        local, core,
        "quote_symbol should match z4_core for pipe-containing name"
    );
    // Pipe chars should be sanitized to underscores inside pipe-quoted name.
    assert_eq!(
        local, "|a_b|",
        "pipe char should be sanitized: got {local:?}"
    );
}

/// Verify BV operations produce correct SMT-LIB names.
/// Previously (#6047 W3:1873), the wildcard arm used `{op:?}` which
/// produced Rust enum variant names (BvAdd) instead of SMT-LIB (bvadd).
#[test]
fn test_bv_op_serialization_produces_correct_smtlib() {
    let x = ChcVar::new("x", ChcSort::BitVec(8));
    let y = ChcVar::new("y", ChcSort::BitVec(8));
    let bvadd = ChcExpr::Op(
        crate::ChcOp::BvAdd,
        vec![ChcExpr::var(x).into(), ChcExpr::var(y).into()],
    );
    let smtlib = InvariantModel::expr_to_smtlib(&bvadd);
    assert_eq!(smtlib, "(bvadd x y)");
}

/// Verify indexed BV operations produce correct `(_ op params)` syntax.
/// Previously used Debug format producing `(BvExtract(7, 0) x)`.
#[test]
fn test_bv_indexed_op_serialization_produces_correct_smtlib() {
    let x = ChcVar::new("x", ChcSort::BitVec(16));
    let extract = ChcExpr::Op(crate::ChcOp::BvExtract(7, 0), vec![ChcExpr::var(x).into()]);
    let smtlib = InvariantModel::expr_to_smtlib(&extract);
    assert_eq!(smtlib, "((_ extract 7 0) x)");
}

// ========================================================================
// detect_logic tests — covers all 7 match arms
// ========================================================================

#[test]
fn test_detect_logic_array_bv() {
    let vars = vec![
        ChcVar::new(
            "a",
            ChcSort::Array(Box::new(ChcSort::BitVec(32)), Box::new(ChcSort::BitVec(8))),
        ),
        ChcVar::new("x", ChcSort::BitVec(32)),
    ];
    let expr = ChcExpr::Bool(true);
    assert_eq!(detect_logic(&vars, &expr), "QF_AUFBV");
}

#[test]
fn test_detect_logic_array_int_real() {
    let vars = vec![
        ChcVar::new(
            "a",
            ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
        ),
        ChcVar::new("x", ChcSort::Int),
        ChcVar::new("r", ChcSort::Real),
    ];
    let expr = ChcExpr::Bool(true);
    assert_eq!(detect_logic(&vars, &expr), "QF_AUFLIRA");
}

#[test]
fn test_detect_logic_array_real_only() {
    let vars = vec![
        ChcVar::new(
            "a",
            ChcSort::Array(Box::new(ChcSort::Real), Box::new(ChcSort::Real)),
        ),
        ChcVar::new("r", ChcSort::Real),
    ];
    let expr = ChcExpr::Bool(true);
    assert_eq!(detect_logic(&vars, &expr), "QF_AUFLRA");
}

#[test]
fn test_detect_logic_array_int_only() {
    let vars = vec![
        ChcVar::new(
            "a",
            ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
        ),
        ChcVar::new("x", ChcSort::Int),
    ];
    let expr = ChcExpr::Bool(true);
    assert_eq!(detect_logic(&vars, &expr), "QF_AUFLIA");
}

#[test]
fn test_detect_logic_array_only_bool() {
    // Array with Bool indices and values — no Int, Real, or BV vars.
    let vars = vec![ChcVar::new(
        "a",
        ChcSort::Array(Box::new(ChcSort::Bool), Box::new(ChcSort::Bool)),
    )];
    let expr = ChcExpr::Bool(true);
    assert_eq!(detect_logic(&vars, &expr), "QF_AX");
}

#[test]
fn test_detect_logic_bv_no_array() {
    let vars = vec![
        ChcVar::new("x", ChcSort::BitVec(32)),
        ChcVar::new("y", ChcSort::BitVec(32)),
    ];
    let expr = ChcExpr::Bool(true);
    assert_eq!(detect_logic(&vars, &expr), "QF_UFBV");
}

#[test]
fn test_detect_logic_default_int_only() {
    // Int without arrays — falls through to default QF_AUFLIA.
    let vars = vec![ChcVar::new("x", ChcSort::Int)];
    let expr = ChcExpr::Bool(true);
    assert_eq!(detect_logic(&vars, &expr), "QF_AUFLIA");
}

#[test]
fn test_detect_logic_array_from_expr_ops() {
    // No array-sorted variables, but the expression contains array ops.
    let vars = vec![ChcVar::new("x", ChcSort::Int)];
    let store_expr = ChcExpr::Op(
        crate::ChcOp::Store,
        vec![
            ChcExpr::var(ChcVar::new(
                "arr",
                ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
            ))
            .into(),
            ChcExpr::Bool(true).into(),
            ChcExpr::Int(42).into(),
        ],
    );
    // Should detect array from expr ops even without array-sorted vars.
    let logic = detect_logic(&vars, &store_expr);
    assert!(
        logic.contains("AU") || logic == "QF_AX",
        "should detect array logic from expr ops: got {logic}"
    );
}

#[test]
fn test_detect_logic_nested_datatype_selector_bv() {
    let inner = ChcSort::Datatype {
        name: "Inner".to_string(),
        constructors: Arc::new(vec![ChcDtConstructor {
            name: "mk-inner".to_string(),
            selectors: vec![ChcDtSelector {
                name: "payload".to_string(),
                sort: ChcSort::BitVec(32),
            }],
        }]),
    };
    let wrapper = ChcSort::Datatype {
        name: "Wrapper".to_string(),
        constructors: Arc::new(vec![ChcDtConstructor {
            name: "mk-wrapper".to_string(),
            selectors: vec![ChcDtSelector {
                name: "inner".to_string(),
                sort: inner,
            }],
        }]),
    };

    let vars = vec![ChcVar::new("w", wrapper)];
    let expr = ChcExpr::Bool(true);
    assert_eq!(detect_logic(&vars, &expr), "_DT_AUFBV");
}

#[test]
fn test_detect_logic_array_of_datatype_activates_dt_logic() {
    let pair = ChcSort::Datatype {
        name: "Pair".to_string(),
        constructors: Arc::new(vec![ChcDtConstructor {
            name: "mk-pair".to_string(),
            selectors: vec![ChcDtSelector {
                name: "fst".to_string(),
                sort: ChcSort::Int,
            }],
        }]),
    };

    let vars = vec![ChcVar::new(
        "arr",
        ChcSort::Array(Box::new(pair), Box::new(ChcSort::Int)),
    )];
    let expr = ChcExpr::Bool(true);
    assert_eq!(detect_logic(&vars, &expr), "_DT_AUFLIA");
}

// ========================================================================
// sort_to_smtlib tests
// ========================================================================

#[test]
fn test_sort_to_smtlib_basic() {
    assert_eq!(sort_to_smtlib(&ChcSort::Bool), "Bool");
    assert_eq!(sort_to_smtlib(&ChcSort::Int), "Int");
    assert_eq!(sort_to_smtlib(&ChcSort::Real), "Real");
    assert_eq!(sort_to_smtlib(&ChcSort::BitVec(32)), "(_ BitVec 32)");
}

#[test]
fn test_sort_to_smtlib_array() {
    let sort = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int));
    assert_eq!(sort_to_smtlib(&sort), "(Array Int Int)");
}

#[test]
fn test_sort_to_smtlib_nested_array() {
    // Array(Int, Array(Int, Bool))
    let inner = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Bool));
    let outer = ChcSort::Array(Box::new(ChcSort::Int), Box::new(inner));
    assert_eq!(sort_to_smtlib(&outer), "(Array Int (Array Int Bool))");
}

// ========================================================================
// term_body_to_smt_value tests
// ========================================================================

#[test]
fn test_term_body_to_smt_value_bool_true() {
    let term = z4_frontend::Term::Const(z4_frontend::Constant::True);
    assert_eq!(tv(&term), Some(SmtValue::Bool(true)));
}

#[test]
fn test_term_body_to_smt_value_bool_false() {
    let term = z4_frontend::Term::Const(z4_frontend::Constant::False);
    assert_eq!(tv(&term), Some(SmtValue::Bool(false)));
}

#[test]
fn test_term_body_to_smt_value_numeral() {
    let term = z4_frontend::Term::Const(z4_frontend::Constant::Numeral("42".to_string()));
    assert_eq!(tv(&term), Some(SmtValue::Int(42)));
}

/// #6180: Numeral exceeding i64 range returns None (not silent drop).
#[test]
fn test_term_body_to_smt_value_numeral_overflow_returns_none() {
    // 2^63 = 9223372036854775808, which exceeds i64::MAX (2^63 - 1)
    let term = z4_frontend::Term::Const(z4_frontend::Constant::Numeral(
        "9223372036854775808".to_string(),
    ));
    assert_eq!(
        tv(&term),
        None,
        "numeral exceeding i64 range should return None"
    );
}

/// #6180: Negation of an overflowing numeral returns None.
#[test]
fn test_term_body_to_smt_value_neg_overflow_returns_none() {
    // -(2^63) = -9223372036854775808 = i64::MIN, which is representable.
    // But -(2^63 + 1) is not.
    let inner = z4_frontend::Term::Const(z4_frontend::Constant::Numeral(
        "9223372036854775809".to_string(),
    ));
    let term = z4_frontend::Term::App("-".to_string(), vec![inner]);
    assert_eq!(
        tv(&term),
        None,
        "negation of overflowing numeral should return None"
    );
}

#[test]
fn test_term_body_to_smt_value_negation() {
    let inner = z4_frontend::Term::Const(z4_frontend::Constant::Numeral("7".to_string()));
    let term = z4_frontend::Term::App("-".to_string(), vec![inner]);
    assert_eq!(tv(&term), Some(SmtValue::Int(-7)));
}

#[test]
fn test_term_body_to_smt_value_hex_bv() {
    let term = z4_frontend::Term::Const(z4_frontend::Constant::Hexadecimal("FF".to_string()));
    assert_eq!(tv(&term), Some(SmtValue::BitVec(255, 8)));
}

#[test]
fn test_term_body_to_smt_value_wide_hex_bv_truncation_7040() {
    // 192-bit hex (48 hex digits): truncates to low 128 bits
    let term = z4_frontend::Term::Const(z4_frontend::Constant::Hexadecimal(
        "000000000000000100000000000000020000000000000003".to_string(),
    ));
    assert_eq!(
        tv(&term),
        Some(SmtValue::BitVec(0x00000000000000020000000000000003, 192))
    );
}

#[test]
fn test_term_body_to_smt_value_wide_bin_bv_truncation_7040() {
    // 192-bit binary: truncates to low 128 bits (all ones)
    let term = z4_frontend::Term::Const(z4_frontend::Constant::Binary("1".repeat(192)));
    assert_eq!(tv(&term), Some(SmtValue::BitVec(u128::MAX, 192)));
}

#[test]
fn test_term_body_to_smt_value_binary_bv() {
    let term = z4_frontend::Term::Const(z4_frontend::Constant::Binary("1010".to_string()));
    assert_eq!(tv(&term), Some(SmtValue::BitVec(10, 4)));
}

#[test]
fn test_term_body_to_smt_value_decimal() {
    use num_rational::BigRational;
    let term = z4_frontend::Term::Const(z4_frontend::Constant::Decimal("1.5".to_string()));
    let result = tv(&term);
    let expected = BigRational::new(3.into(), 2.into());
    assert_eq!(result, Some(SmtValue::Real(expected)));
}

#[test]
fn test_term_body_to_smt_value_decimal_zero() {
    use num_rational::BigRational;
    let term = z4_frontend::Term::Const(z4_frontend::Constant::Decimal("0.0".to_string()));
    let result = tv(&term);
    let expected = BigRational::new(0.into(), 1.into());
    assert_eq!(result, Some(SmtValue::Real(expected)));
}

#[test]
fn test_term_body_to_smt_value_negation_real() {
    use num_rational::BigRational;
    // (- 1.5) should produce Real(-3/2)
    let inner = z4_frontend::Term::Const(z4_frontend::Constant::Decimal("1.5".to_string()));
    let term = z4_frontend::Term::App("-".to_string(), vec![inner]);
    let result = tv(&term);
    let expected = BigRational::new((-3).into(), 2.into());
    assert_eq!(result, Some(SmtValue::Real(expected)));
}

#[test]
fn test_term_body_to_smt_value_rational_division() {
    use num_rational::BigRational;
    // (/ 3 2) should produce Real(3/2)
    let num = z4_frontend::Term::Const(z4_frontend::Constant::Numeral("3".to_string()));
    let den = z4_frontend::Term::Const(z4_frontend::Constant::Numeral("2".to_string()));
    let term = z4_frontend::Term::App("/".to_string(), vec![num, den]);
    let result = tv(&term);
    let expected = BigRational::new(3.into(), 2.into());
    assert_eq!(result, Some(SmtValue::Real(expected)));
}

#[test]
fn test_term_body_to_smt_value_div_by_zero_returns_none() {
    let num = z4_frontend::Term::Const(z4_frontend::Constant::Numeral("5".to_string()));
    let den = z4_frontend::Term::Const(z4_frontend::Constant::Numeral("0".to_string()));
    let term = z4_frontend::Term::App("/".to_string(), vec![num, den]);
    assert_eq!(tv(&term), None);
}

// ========================================================================
// parse_model_into tests
// ========================================================================

#[test]
fn test_parse_model_into_empty_string() {
    let mut model = FxHashMap::default();
    pm(&mut model, "");
    assert!(model.is_empty());
}

#[test]
fn test_parse_model_into_define_fun_int() {
    let mut model = FxHashMap::default();
    let model_str = "(model\n  (define-fun x () Int 42)\n)";
    pm(&mut model, model_str);
    assert_eq!(model.get("x"), Some(&SmtValue::Int(42)));
}

#[test]
fn test_parse_model_into_define_fun_bool() {
    let mut model = FxHashMap::default();
    let model_str = "(model\n  (define-fun b () Bool true)\n)";
    pm(&mut model, model_str);
    assert_eq!(model.get("b"), Some(&SmtValue::Bool(true)));
}

#[test]
fn test_parse_model_into_define_fun_negint() {
    let mut model = FxHashMap::default();
    let model_str = "(model\n  (define-fun x () Int (- 5))\n)";
    pm(&mut model, model_str);
    assert_eq!(model.get("x"), Some(&SmtValue::Int(-5)));
}

#[test]
fn test_parse_model_into_multiple_entries() {
    let mut model = FxHashMap::default();
    let model_str = "(model\n  (define-fun x () Int 1)\n  (define-fun y () Int 2)\n  (define-fun b () Bool false)\n)";
    pm(&mut model, model_str);
    assert_eq!(model.get("x"), Some(&SmtValue::Int(1)));
    assert_eq!(model.get("y"), Some(&SmtValue::Int(2)));
    assert_eq!(model.get("b"), Some(&SmtValue::Bool(false)));
}

#[test]
fn test_parse_model_into_skips_parameterized_funs() {
    let mut model = FxHashMap::default();
    // define-fun with parameters should be skipped (not a 0-arity constant).
    let model_str = "(model\n  (define-fun f ((x Int)) Int x)\n  (define-fun c () Int 7)\n)";
    pm(&mut model, model_str);
    assert!(
        !model.contains_key("f"),
        "parameterized fun should be skipped"
    );
    assert_eq!(model.get("c"), Some(&SmtValue::Int(7)));
}

#[test]
fn test_parse_model_into_preserves_existing_entries() {
    let mut model = FxHashMap::default();
    model.insert("existing".to_string(), SmtValue::Int(99));
    let model_str = "(model\n  (define-fun x () Int 1)\n)";
    pm(&mut model, model_str);
    assert_eq!(model.get("existing"), Some(&SmtValue::Int(99)));
    assert_eq!(model.get("x"), Some(&SmtValue::Int(1)));
}

/// #6180: Model with i64-overflowing numeral drops that entry (not panic/UB).
#[test]
fn test_parse_model_into_large_int_dropped() {
    let mut model = FxHashMap::default();
    // 2^63 exceeds i64 max — the variable should be silently dropped from model.
    let model_str =
        "(model\n  (define-fun big () Int 9223372036854775808)\n  (define-fun ok () Int 1)\n)";
    pm(&mut model, model_str);
    assert!(
        !model.contains_key("big"),
        "overflowing numeral should be dropped from model"
    );
    assert_eq!(
        model.get("ok"),
        Some(&SmtValue::Int(1)),
        "non-overflowing entry should be preserved"
    );
}

// ========================================================================
// parse_decimal_to_rational tests
// ========================================================================

#[test]
fn test_parse_decimal_to_rational_simple() {
    use num_rational::BigRational;
    let r = parse_decimal_to_rational("1.5").unwrap();
    assert_eq!(r, BigRational::new(3.into(), 2.into()));
}

#[test]
fn test_parse_decimal_to_rational_integer() {
    use num_rational::BigRational;
    let r = parse_decimal_to_rational("42").unwrap();
    assert_eq!(r, BigRational::from_integer(42.into()));
}

#[test]
fn test_parse_decimal_to_rational_trailing_zeros() {
    use num_rational::BigRational;
    // "3.0" -> 30/10 = 3/1
    let r = parse_decimal_to_rational("3.0").unwrap();
    assert_eq!(r, BigRational::from_integer(3.into()));
}

#[test]
fn test_parse_decimal_to_rational_precise() {
    use num_rational::BigRational;
    // "0.125" -> 125/1000 = 1/8
    let r = parse_decimal_to_rational("0.125").unwrap();
    assert_eq!(r, BigRational::new(1.into(), 8.into()));
}

// ========================================================================
// #6047: Array model parsing tests
// ========================================================================

#[test]
fn test_term_body_to_smt_value_const_array() {
    // ((as const (Array Int Int)) 0) -> ConstArray(Int(0))
    let inner = z4_frontend::Term::Const(z4_frontend::Constant::Numeral("0".to_string()));
    let sort = z4_frontend::command::Sort::Parameterized(
        "Array".to_string(),
        vec![
            z4_frontend::command::Sort::Simple("Int".to_string()),
            z4_frontend::command::Sort::Simple("Int".to_string()),
        ],
    );
    let term = z4_frontend::Term::QualifiedApp("const".to_string(), sort, vec![inner]);
    let result = tv(&term);
    assert_eq!(
        result,
        Some(SmtValue::ConstArray(Box::new(SmtValue::Int(0))))
    );
}

#[test]
fn test_term_body_to_smt_value_const_array_bv() {
    // ((as const (Array (_ BitVec 32) (_ BitVec 8))) #x42) -> ConstArray(BitVec(0x42, 8))
    let inner = z4_frontend::Term::Const(z4_frontend::Constant::Hexadecimal("42".to_string()));
    let sort = z4_frontend::command::Sort::Parameterized(
        "Array".to_string(),
        vec![
            z4_frontend::command::Sort::Indexed("BitVec".to_string(), vec!["32".to_string()]),
            z4_frontend::command::Sort::Indexed("BitVec".to_string(), vec!["8".to_string()]),
        ],
    );
    let term = z4_frontend::Term::QualifiedApp("const".to_string(), sort, vec![inner]);
    let result = tv(&term);
    assert_eq!(
        result,
        Some(SmtValue::ConstArray(Box::new(SmtValue::BitVec(0x42, 8))))
    );
}

#[test]
fn test_term_body_to_smt_value_store_on_const_array() {
    // (store ((as const (Array Int Int)) 0) 1 42)
    // -> ArrayMap { default: Int(0), entries: [(Int(1), Int(42))] }
    let sort = z4_frontend::command::Sort::Parameterized(
        "Array".to_string(),
        vec![
            z4_frontend::command::Sort::Simple("Int".to_string()),
            z4_frontend::command::Sort::Simple("Int".to_string()),
        ],
    );
    let const_arr = z4_frontend::Term::QualifiedApp(
        "const".to_string(),
        sort,
        vec![z4_frontend::Term::Const(z4_frontend::Constant::Numeral(
            "0".to_string(),
        ))],
    );
    let term = z4_frontend::Term::App(
        "store".to_string(),
        vec![
            const_arr,
            z4_frontend::Term::Const(z4_frontend::Constant::Numeral("1".to_string())),
            z4_frontend::Term::Const(z4_frontend::Constant::Numeral("42".to_string())),
        ],
    );
    let result = tv(&term);
    assert_eq!(
        result,
        Some(SmtValue::ArrayMap {
            default: Box::new(SmtValue::Int(0)),
            entries: vec![(SmtValue::Int(1), SmtValue::Int(42))],
        })
    );
}

#[test]
fn test_term_body_to_smt_value_nested_store() {
    // (store (store ((as const (Array Int Int)) 0) 1 10) 2 20)
    // -> ArrayMap { default: Int(0), entries: [(1,10), (2,20)] }
    let sort = z4_frontend::command::Sort::Parameterized(
        "Array".to_string(),
        vec![
            z4_frontend::command::Sort::Simple("Int".to_string()),
            z4_frontend::command::Sort::Simple("Int".to_string()),
        ],
    );
    let const_arr = z4_frontend::Term::QualifiedApp(
        "const".to_string(),
        sort,
        vec![z4_frontend::Term::Const(z4_frontend::Constant::Numeral(
            "0".to_string(),
        ))],
    );
    let inner_store = z4_frontend::Term::App(
        "store".to_string(),
        vec![
            const_arr,
            z4_frontend::Term::Const(z4_frontend::Constant::Numeral("1".to_string())),
            z4_frontend::Term::Const(z4_frontend::Constant::Numeral("10".to_string())),
        ],
    );
    let term = z4_frontend::Term::App(
        "store".to_string(),
        vec![
            inner_store,
            z4_frontend::Term::Const(z4_frontend::Constant::Numeral("2".to_string())),
            z4_frontend::Term::Const(z4_frontend::Constant::Numeral("20".to_string())),
        ],
    );
    let result = tv(&term);
    assert_eq!(
        result,
        Some(SmtValue::ArrayMap {
            default: Box::new(SmtValue::Int(0)),
            entries: vec![
                (SmtValue::Int(1), SmtValue::Int(10)),
                (SmtValue::Int(2), SmtValue::Int(20)),
            ],
        })
    );
}

#[test]
fn test_parse_model_into_const_array() {
    // Full round-trip: parse model output with constant array.
    let mut model = FxHashMap::default();
    let model_str =
        "(model\n  (define-fun arr () (Array Int Int)\n    ((as const (Array Int Int)) 0))\n)";
    pm(&mut model, model_str);
    assert_eq!(
        model.get("arr"),
        Some(&SmtValue::ConstArray(Box::new(SmtValue::Int(0))))
    );
}

#[test]
fn test_parse_model_into_store_array() {
    // Full round-trip: parse model output with store chain.
    let mut model = FxHashMap::default();
    let model_str = "(model\n  (define-fun arr () (Array Int Int)\n    (store ((as const (Array Int Int)) 0) 5 99))\n)";
    pm(&mut model, model_str);
    assert_eq!(
        model.get("arr"),
        Some(&SmtValue::ArrayMap {
            default: Box::new(SmtValue::Int(0)),
            entries: vec![(SmtValue::Int(5), SmtValue::Int(99))],
        })
    );
}

#[test]
fn test_term_body_store_array_preserves_symbolic_base_as_opaque_1753() {
    let term = z4_frontend::Term::App(
        "store".to_string(),
        vec![
            z4_frontend::Term::Symbol("A!0".to_string()),
            z4_frontend::Term::Const(z4_frontend::Constant::Numeral("5".to_string())),
            z4_frontend::Term::Const(z4_frontend::Constant::Numeral("99".to_string())),
        ],
    );
    let result = tv(&term).expect("store over symbolic base should still parse");

    assert_eq!(
        eval_array_select(&result, &SmtValue::Int(5)),
        Some(SmtValue::Int(99))
    );
    assert!(
        matches!(
            eval_array_select(&result, &SmtValue::Int(6)),
            Some(SmtValue::Opaque(_))
        ),
        "unstored indices should fall back to an opaque base: {result:?}"
    );
}

#[test]
fn test_parse_model_into_store_array_with_symbolic_base_1753() {
    let mut model = FxHashMap::default();
    let model_str = "(model\n  (define-fun arr () (Array Int Int)\n    (store A!0 5 99))\n)";
    pm(&mut model, model_str);
    let arr = model
        .get("arr")
        .expect("store over symbolic base should not be dropped");

    assert_eq!(
        eval_array_select(arr, &SmtValue::Int(5)),
        Some(SmtValue::Int(99))
    );
    assert!(
        matches!(
            eval_array_select(arr, &SmtValue::Int(6)),
            Some(SmtValue::Opaque(_))
        ),
        "unstored indices should keep an opaque symbolic default: {arr:?}"
    );
}

// ========================================================================
// SmtValue::Datatype model parsing tests
// ========================================================================

#[test]
fn test_parse_model_dt_nullary_constructor() {
    let mut model = FxHashMap::default();
    let dt_ctors: FxHashSet<String> = ["Green", "Red", "Yellow"]
        .iter()
        .map(ToString::to_string)
        .collect();
    let model_str = "(model\n  (define-fun color () Color Green)\n)";
    parse_model_into(&mut model, model_str, &dt_ctors);
    assert_eq!(
        model.get("color"),
        Some(&SmtValue::Datatype("Green".to_string(), vec![]))
    );
}

#[test]
fn test_parse_model_dt_constructor_with_fields() {
    let mut model = FxHashMap::default();
    let dt_ctors: FxHashSet<String> = ["mkpair"].iter().map(ToString::to_string).collect();
    let model_str = "(model\n  (define-fun p () Pair (mkpair 42 7))\n)";
    parse_model_into(&mut model, model_str, &dt_ctors);
    assert_eq!(
        model.get("p"),
        Some(&SmtValue::Datatype(
            "mkpair".to_string(),
            vec![SmtValue::Int(42), SmtValue::Int(7)]
        ))
    );
}

#[test]
fn test_term_body_dt_nullary_app() {
    let dt_ctors: FxHashSet<String> = ["None_"].iter().map(ToString::to_string).collect();
    let term = z4_frontend::Term::App("None_".to_string(), vec![]);
    assert_eq!(
        term_body_to_smt_value(&term, &dt_ctors),
        Some(SmtValue::Datatype("None_".to_string(), vec![]))
    );
}

#[test]
fn test_term_body_dt_constructor_app() {
    let dt_ctors: FxHashSet<String> = ["Some_"].iter().map(ToString::to_string).collect();
    let arg = z4_frontend::Term::Const(z4_frontend::Constant::Numeral("99".to_string()));
    let term = z4_frontend::Term::App("Some_".to_string(), vec![arg]);
    assert_eq!(
        term_body_to_smt_value(&term, &dt_ctors),
        Some(SmtValue::Datatype(
            "Some_".to_string(),
            vec![SmtValue::Int(99)]
        ))
    );
}

#[test]
fn test_term_body_unknown_app_returns_none_without_dt_ctors() {
    // Without DT constructor names, unknown App returns None.
    let term = z4_frontend::Term::App(
        "mkpair".to_string(),
        vec![z4_frontend::Term::Const(z4_frontend::Constant::Numeral(
            "1".to_string(),
        ))],
    );
    assert_eq!(tv(&term), None);
}

// ========================================================================
// parse_simple_value tests (fallback parser)
// ========================================================================

#[test]
fn test_parse_simple_value_int_positive() {
    assert_eq!(parse_simple_value("Int 42)"), Some(SmtValue::Int(42)));
}

#[test]
fn test_parse_simple_value_int_negative() {
    assert_eq!(parse_simple_value("Int (- 7))"), Some(SmtValue::Int(-7)));
}

#[test]
fn test_parse_simple_value_bool_true() {
    assert_eq!(parse_simple_value("Bool true)"), Some(SmtValue::Bool(true)));
}

#[test]
fn test_parse_simple_value_bool_false() {
    assert_eq!(
        parse_simple_value("Bool false)"),
        Some(SmtValue::Bool(false))
    );
}

#[test]
fn test_parse_simple_value_unknown_sort() {
    assert_eq!(parse_simple_value("Real 1.5)"), None);
}

/// #6180: parse_simple_value returns None for i64-overflowing integers.
#[test]
fn test_parse_simple_value_int_overflow_returns_none() {
    assert_eq!(
        parse_simple_value("Int 9223372036854775808)"),
        None,
        "positive overflow should return None"
    );
}

/// #6180: parse_simple_value returns None for negative i64-overflowing integers.
#[test]
fn test_parse_simple_value_neg_int_overflow_returns_none() {
    assert_eq!(
        parse_simple_value("Int (- 9223372036854775809))"),
        None,
        "negative overflow should return None"
    );
}

// ========================================================================
// parse_model_simple tests (fallback parser)
// ========================================================================

#[test]
fn test_parse_model_simple_basic() {
    let mut model = FxHashMap::default();
    let model_str = "(define-fun x () Int 42)\n(define-fun b () Bool true)";
    parse_model_simple(&mut model, model_str);
    assert_eq!(model.get("x"), Some(&SmtValue::Int(42)));
    assert_eq!(model.get("b"), Some(&SmtValue::Bool(true)));
}

#[test]
fn test_parse_model_simple_negative_int() {
    let mut model = FxHashMap::default();
    let model_str = "(define-fun x () Int (- 3))";
    parse_model_simple(&mut model, model_str);
    assert_eq!(model.get("x"), Some(&SmtValue::Int(-3)));
}

#[test]
fn test_parse_model_simple_skips_non_define_fun() {
    let mut model = FxHashMap::default();
    let model_str = "(model\n  some garbage\n  (define-fun x () Int 1)\n)";
    parse_model_simple(&mut model, model_str);
    assert_eq!(model.get("x"), Some(&SmtValue::Int(1)));
}

#[test]
fn test_parse_model_simple_skips_parameterized() {
    let mut model = FxHashMap::default();
    // Has params "(x Int)" instead of "()" — should be skipped.
    let model_str = "(define-fun f (x Int) Int x)";
    parse_model_simple(&mut model, model_str);
    assert!(model.is_empty());
}

#[test]
fn test_parse_model_simple_pipe_quoted_name_no_spaces() {
    // Pipe-quoted names without internal spaces parse correctly.
    // Names with spaces (e.g., |my var|) are split incorrectly by the
    // space-based heuristic — this is a known limitation of the fallback
    // parser. The primary parser (parse_model_into via z4-frontend) handles
    // pipe-quoted names correctly.
    let mut model = FxHashMap::default();
    let model_str = "(define-fun |my_var| () Int 99)";
    parse_model_simple(&mut model, model_str);
    assert_eq!(model.get("my_var"), Some(&SmtValue::Int(99)));
}

// ========================================================================
// check_sat_via_executor integration tests
// ========================================================================

#[test]
fn test_check_sat_via_executor_sat_simple() {
    // (x > 0) with x:Int — trivially SAT.
    let x = ChcVar::new("x", ChcSort::Int);
    let expr = ChcExpr::Op(
        crate::ChcOp::Gt,
        vec![ChcExpr::var(x).into(), ChcExpr::Int(0).into()],
    );
    let smt = SmtContext::new();
    let propagated = FxHashMap::default();
    let result = smt.check_sat_via_executor(&expr, &propagated, std::time::Duration::from_secs(5));
    assert!(
        matches!(result, SmtResult::Sat(_)),
        "x > 0 should be SAT via executor: got {result:?}"
    );
}

#[test]
fn test_check_sat_via_executor_unsat_contradiction() {
    // (x > 0 AND x < 0) — UNSAT.
    let x = ChcVar::new("x", ChcSort::Int);
    let gt = ChcExpr::Op(
        crate::ChcOp::Gt,
        vec![ChcExpr::var(x.clone()).into(), ChcExpr::Int(0).into()],
    );
    let lt = ChcExpr::Op(
        crate::ChcOp::Lt,
        vec![ChcExpr::var(x).into(), ChcExpr::Int(0).into()],
    );
    let expr = ChcExpr::Op(crate::ChcOp::And, vec![gt.into(), lt.into()]);
    let smt = SmtContext::new();
    let propagated = FxHashMap::default();
    let result = smt.check_sat_via_executor(&expr, &propagated, std::time::Duration::from_secs(5));
    assert!(
        matches!(result, SmtResult::Unsat),
        "(x > 0 AND x < 0) should be UNSAT via executor: got {result:?}"
    );
}

#[test]
fn test_check_sat_via_executor_propagated_model_merged() {
    // SAT formula with propagated model entries — propagated values appear in result.
    let x = ChcVar::new("x", ChcSort::Int);
    let expr = ChcExpr::Op(
        crate::ChcOp::Gt,
        vec![ChcExpr::var(x).into(), ChcExpr::Int(0).into()],
    );
    let smt = SmtContext::new();
    let mut propagated = FxHashMap::default();
    propagated.insert("y".to_string(), SmtValue::Int(42));
    let result = smt.check_sat_via_executor(&expr, &propagated, std::time::Duration::from_secs(5));
    if let SmtResult::Sat(model) = result {
        assert_eq!(
            model.get("y"),
            Some(&SmtValue::Int(42)),
            "propagated model entry should be preserved in SAT model"
        );
    } else {
        panic!("expected SAT, got {result:?}");
    }
}

#[test]
fn test_check_sat_via_executor_empty_vars_returns_unknown() {
    // Expression with no free variables returns Unknown (line 38-41).
    let expr = ChcExpr::Bool(true);
    let smt = SmtContext::new();
    let propagated = FxHashMap::default();
    let result = smt.check_sat_via_executor(&expr, &propagated, std::time::Duration::from_secs(5));
    assert!(
        matches!(result, SmtResult::Unknown),
        "no-variable expression should return Unknown: got {result:?}"
    );
}

#[test]
fn test_accept_reparsed_sat_model_rejects_indeterminate_array_query_4993() {
    let arr = ChcVar::new(
        "A",
        ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
    );
    let expr = ChcExpr::eq(
        ChcExpr::select(ChcExpr::var(arr), ChcExpr::Int(0)),
        ChcExpr::Int(42),
    );

    assert!(
        accept_reparsed_sat_model(&[&expr], FxHashMap::default(), "executor_adapter test",)
            .is_none(),
        "array fallback SAT models must validate definitively before acceptance"
    );
}

// debug-only: the mk_le sort check is a debug_assert! (z4-core arithmetic.rs:1080).
// In release, the assert is compiled out and Le(Bool, true) is processed normally.
#[test]
#[cfg(debug_assertions)]
fn test_check_sat_via_executor_z4_panic_returns_unknown_issue_6781() {
    // #6781: malformed arithmetic comparisons can still reach the executor
    // through higher-level CHC discovery. The executor boundary must convert
    // z4-internal sort panics into Unknown instead of aborting the solve.
    let b = ChcVar::new("b", ChcSort::Bool);
    let expr = ChcExpr::Op(
        crate::ChcOp::Le,
        vec![ChcExpr::var(b).into(), ChcExpr::Bool(true).into()],
    );
    let smt = SmtContext::new();
    let propagated = FxHashMap::default();
    let result = smt.check_sat_via_executor(&expr, &propagated, std::time::Duration::from_secs(5));
    assert!(
        matches!(result, SmtResult::Unknown),
        "z4-internal sort panic should degrade to Unknown: got {result:?}"
    );
}

// ========================================================================
// check_sat_conjunction_via_executor integration tests
// ========================================================================

#[test]
fn test_check_sat_conjunction_via_executor_sat() {
    use super::super::incremental::IncrementalCheckResult;
    let x = ChcVar::new("x", ChcSort::Int);
    let gt = ChcExpr::Op(
        crate::ChcOp::Gt,
        vec![ChcExpr::var(x.clone()).into(), ChcExpr::Int(0).into()],
    );
    let lt = ChcExpr::Op(
        crate::ChcOp::Lt,
        vec![ChcExpr::var(x).into(), ChcExpr::Int(100).into()],
    );
    let propagated = FxHashMap::default();
    let result = check_sat_conjunction_via_executor(
        &[gt, lt],
        &propagated,
        std::time::Duration::from_secs(5),
    );
    assert!(
        matches!(result, IncrementalCheckResult::Sat(_)),
        "(x > 0) AND (x < 100) conjunction should be SAT: got {result:?}"
    );
}

#[test]
fn test_check_sat_conjunction_via_executor_unsat() {
    use super::super::incremental::IncrementalCheckResult;
    let x = ChcVar::new("x", ChcSort::Int);
    let gt = ChcExpr::Op(
        crate::ChcOp::Gt,
        vec![ChcExpr::var(x.clone()).into(), ChcExpr::Int(10).into()],
    );
    let lt = ChcExpr::Op(
        crate::ChcOp::Lt,
        vec![ChcExpr::var(x).into(), ChcExpr::Int(5).into()],
    );
    let propagated = FxHashMap::default();
    let result = check_sat_conjunction_via_executor(
        &[gt, lt],
        &propagated,
        std::time::Duration::from_secs(5),
    );
    assert!(
        matches!(result, IncrementalCheckResult::Unsat),
        "(x > 10) AND (x < 5) conjunction should be UNSAT: got {result:?}"
    );
}

#[test]
fn test_check_sat_conjunction_via_executor_empty_returns_unknown() {
    use super::super::incremental::IncrementalCheckResult;
    // No expressions with variables -> Unknown.
    let result = check_sat_conjunction_via_executor(
        &[ChcExpr::Bool(true)],
        &FxHashMap::default(),
        std::time::Duration::from_secs(5),
    );
    assert!(
        matches!(result, IncrementalCheckResult::Unknown),
        "no-variable conjunction should return Unknown: got {result:?}"
    );
}

#[test]
fn test_check_sat_conjunction_via_executor_merges_propagated() {
    use super::super::incremental::IncrementalCheckResult;
    let x = ChcVar::new("x", ChcSort::Int);
    let gt = ChcExpr::Op(
        crate::ChcOp::Gt,
        vec![ChcExpr::var(x).into(), ChcExpr::Int(0).into()],
    );
    let mut propagated = FxHashMap::default();
    propagated.insert("y".to_string(), 99);
    let result =
        check_sat_conjunction_via_executor(&[gt], &propagated, std::time::Duration::from_secs(5));
    if let IncrementalCheckResult::Sat(model) = result {
        assert_eq!(
            model.get("y"),
            Some(&SmtValue::Int(99)),
            "propagated equality should be in SAT model"
        );
    } else {
        panic!("expected SAT, got {result:?}");
    }
}

#[test]
fn test_emit_declare_datatype_roundtrip_enum() {
    // Nullary constructors (enum): Color = Red | Green | Blue
    let ctors = vec![
        ChcDtConstructor {
            name: "Red".to_string(),
            selectors: vec![],
        },
        ChcDtConstructor {
            name: "Green".to_string(),
            selectors: vec![],
        },
        ChcDtConstructor {
            name: "Blue".to_string(),
            selectors: vec![],
        },
    ];
    let emitted = emit_declare_datatype("Color", &ctors);
    let sexp = z4_frontend::sexp::parse_sexp(&emitted).unwrap();
    let cmd = z4_frontend::Command::from_sexp(&sexp).unwrap();
    match &cmd {
        z4_frontend::Command::DeclareDatatype(name, dt_dec) => {
            assert_eq!(name, "Color");
            assert_eq!(dt_dec.constructors.len(), 3);
            assert_eq!(dt_dec.constructors[0].name, "Red");
            assert_eq!(dt_dec.constructors[1].name, "Green");
            assert_eq!(dt_dec.constructors[2].name, "Blue");
            for c in &dt_dec.constructors {
                assert!(c.selectors.is_empty(), "enum ctors have no selectors");
            }
        }
        other => panic!("expected DeclareDatatype, got {other:?}"),
    }
}

#[test]
fn test_emit_declare_datatype_roundtrip_record() {
    // Record with selectors: Point = mk-point(x: Int, y: Int)
    let ctors = vec![ChcDtConstructor {
        name: "mk-point".to_string(),
        selectors: vec![
            ChcDtSelector {
                name: "x".to_string(),
                sort: ChcSort::Int,
            },
            ChcDtSelector {
                name: "y".to_string(),
                sort: ChcSort::Int,
            },
        ],
    }];
    let emitted = emit_declare_datatype("Point", &ctors);
    let sexp = z4_frontend::sexp::parse_sexp(&emitted).unwrap();
    let cmd = z4_frontend::Command::from_sexp(&sexp).unwrap();
    match &cmd {
        z4_frontend::Command::DeclareDatatype(name, dt_dec) => {
            assert_eq!(name, "Point");
            assert_eq!(dt_dec.constructors.len(), 1);
            let ctor = &dt_dec.constructors[0];
            assert_eq!(ctor.name, "mk-point");
            assert_eq!(ctor.selectors.len(), 2);
            assert_eq!(ctor.selectors[0].name, "x");
            assert_eq!(ctor.selectors[1].name, "y");
        }
        other => panic!("expected DeclareDatatype, got {other:?}"),
    }
}

#[test]
fn test_emit_declare_datatype_roundtrip_zani_tuple() {
    // zani-style tuple: Tuple_bv32_bool = mk-Tuple_bv32_bool(fst: BitVec(32), snd: Bool)
    let ctors = vec![ChcDtConstructor {
        name: "mk-Tuple_bv32_bool".to_string(),
        selectors: vec![
            ChcDtSelector {
                name: "fst".to_string(),
                sort: ChcSort::BitVec(32),
            },
            ChcDtSelector {
                name: "snd".to_string(),
                sort: ChcSort::Bool,
            },
        ],
    }];
    let emitted = emit_declare_datatype("Tuple_bv32_bool", &ctors);
    let sexp = z4_frontend::sexp::parse_sexp(&emitted).unwrap();
    let cmd = z4_frontend::Command::from_sexp(&sexp).unwrap();
    match &cmd {
        z4_frontend::Command::DeclareDatatype(name, dt_dec) => {
            assert_eq!(name, "Tuple_bv32_bool");
            assert_eq!(dt_dec.constructors.len(), 1);
            let ctor = &dt_dec.constructors[0];
            assert_eq!(ctor.name, "mk-Tuple_bv32_bool");
            assert_eq!(ctor.selectors.len(), 2);
            assert_eq!(ctor.selectors[0].name, "fst");
            assert_eq!(ctor.selectors[1].name, "snd");
        }
        other => panic!("expected DeclareDatatype, got {other:?}"),
    }
}

#[test]
fn test_emit_declare_datatype_roundtrip_nested_array_sort() {
    // DT with Array-sorted selector: Wrapper = wrap(data: Array(Int, Int))
    let ctors = vec![ChcDtConstructor {
        name: "wrap".to_string(),
        selectors: vec![ChcDtSelector {
            name: "data".to_string(),
            sort: ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
        }],
    }];
    let emitted = emit_declare_datatype("Wrapper", &ctors);
    let sexp = z4_frontend::sexp::parse_sexp(&emitted).unwrap();
    let cmd = z4_frontend::Command::from_sexp(&sexp).unwrap();
    match &cmd {
        z4_frontend::Command::DeclareDatatype(name, dt_dec) => {
            assert_eq!(name, "Wrapper");
            assert_eq!(dt_dec.constructors.len(), 1);
            let sel = &dt_dec.constructors[0].selectors[0];
            assert_eq!(sel.name, "data");
            // Sort should be (Array Int Int)
            match &sel.sort {
                z4_frontend::Sort::Parameterized(sort_name, params) => {
                    assert_eq!(sort_name, "Array");
                    assert_eq!(params.len(), 2);
                }
                other => panic!("expected Parameterized Array sort, got {other:?}"),
            }
        }
        other => panic!("expected DeclareDatatype, got {other:?}"),
    }
}
