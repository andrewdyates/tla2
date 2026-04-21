// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::{ChcDtConstructor, ChcDtSelector};
// --- eval_array_select ---

#[test]
fn test_eval_array_select_const_array() {
    // ConstArray(42) → select at any index returns 42
    let arr = SmtValue::ConstArray(Box::new(SmtValue::Int(42)));
    let idx = SmtValue::Int(0);
    assert_eq!(eval_array_select(&arr, &idx), Some(SmtValue::Int(42)));
    let idx2 = SmtValue::Int(999);
    assert_eq!(eval_array_select(&arr, &idx2), Some(SmtValue::Int(42)));
}

#[test]
fn test_eval_array_select_basic() {
    // store(const(0), 5, 100) → select at 5 returns 100
    let arr = SmtValue::ArrayMap {
        default: Box::new(SmtValue::Int(0)),
        entries: vec![(SmtValue::Int(5), SmtValue::Int(100))],
    };
    assert_eq!(
        eval_array_select(&arr, &SmtValue::Int(5)),
        Some(SmtValue::Int(100))
    );
}

#[test]
fn test_eval_array_select_different_index() {
    // store(const(0), 5, 100) → select at 3 returns default 0
    let arr = SmtValue::ArrayMap {
        default: Box::new(SmtValue::Int(0)),
        entries: vec![(SmtValue::Int(5), SmtValue::Int(100))],
    };
    assert_eq!(
        eval_array_select(&arr, &SmtValue::Int(3)),
        Some(SmtValue::Int(0))
    );
}

#[test]
fn test_eval_array_select_nested_store() {
    // store(store(const(0), 1, 10), 2, 20) → select at 1 returns 10, at 2 returns 20
    let arr = SmtValue::ArrayMap {
        default: Box::new(SmtValue::Int(0)),
        entries: vec![
            (SmtValue::Int(1), SmtValue::Int(10)),
            (SmtValue::Int(2), SmtValue::Int(20)),
        ],
    };
    assert_eq!(
        eval_array_select(&arr, &SmtValue::Int(1)),
        Some(SmtValue::Int(10))
    );
    assert_eq!(
        eval_array_select(&arr, &SmtValue::Int(2)),
        Some(SmtValue::Int(20))
    );
    assert_eq!(
        eval_array_select(&arr, &SmtValue::Int(3)),
        Some(SmtValue::Int(0))
    );
}

#[test]
fn test_eval_array_select_last_store_wins() {
    // store(store(const(0), 1, 10), 1, 20) → last store at idx 1 wins
    // After dedup in eval_array_store, there should be only one entry.
    // But if entries are manually constructed with duplicates, reverse order wins.
    let arr = SmtValue::ArrayMap {
        default: Box::new(SmtValue::Int(0)),
        entries: vec![
            (SmtValue::Int(1), SmtValue::Int(10)),
            (SmtValue::Int(1), SmtValue::Int(20)),
        ],
    };
    // Reverse order scan: (1, 20) is found first → returns 20
    assert_eq!(
        eval_array_select(&arr, &SmtValue::Int(1)),
        Some(SmtValue::Int(20))
    );
}

#[test]
fn test_eval_array_select_bv_index() {
    // Array(BV32, Bool) with BV-indexed entries
    let arr = SmtValue::ArrayMap {
        default: Box::new(SmtValue::Bool(false)),
        entries: vec![(SmtValue::BitVec(0, 32), SmtValue::Bool(true))],
    };
    assert_eq!(
        eval_array_select(&arr, &SmtValue::BitVec(0, 32)),
        Some(SmtValue::Bool(true))
    );
    assert_eq!(
        eval_array_select(&arr, &SmtValue::BitVec(1, 32)),
        Some(SmtValue::Bool(false))
    );
}

#[test]
fn test_eval_array_select_non_array_returns_none() {
    // Selecting from a non-array value returns None
    let not_arr = SmtValue::Int(42);
    assert_eq!(eval_array_select(&not_arr, &SmtValue::Int(0)), None);
}

#[test]
fn test_eval_array_select_opaque_key_returns_none_6289() {
    let arr = SmtValue::ArrayMap {
        default: Box::new(SmtValue::Bool(false)),
        entries: vec![(
            SmtValue::Opaque("__au_k0".to_string()),
            SmtValue::Bool(true),
        )],
    };
    assert_eq!(eval_array_select(&arr, &SmtValue::BitVec(0, 32)), None);
}

// --- eval_array_store ---

#[test]
fn test_eval_array_store_into_const_array() {
    // store(const(false), bv0, true) → ArrayMap with one entry
    let arr = SmtValue::ConstArray(Box::new(SmtValue::Bool(false)));
    let result = eval_array_store(arr, SmtValue::BitVec(0, 32), SmtValue::Bool(true));
    match &result {
        SmtValue::ArrayMap { default, entries } => {
            assert_eq!(**default, SmtValue::Bool(false));
            assert_eq!(entries.len(), 1);
            assert_eq!(entries[0], (SmtValue::BitVec(0, 32), SmtValue::Bool(true)));
        }
        _ => panic!("Expected ArrayMap, got {result:?}"),
    }
}

#[test]
fn test_eval_array_store_overwrite() {
    // store(store(const(0), 5, 10), 5, 20) → entry at 5 is overwritten to 20
    let arr = SmtValue::ArrayMap {
        default: Box::new(SmtValue::Int(0)),
        entries: vec![(SmtValue::Int(5), SmtValue::Int(10))],
    };
    let result = eval_array_store(arr, SmtValue::Int(5), SmtValue::Int(20));
    match &result {
        SmtValue::ArrayMap { entries, .. } => {
            assert_eq!(entries.len(), 1, "Overwrite should dedup: {entries:?}");
            assert_eq!(entries[0], (SmtValue::Int(5), SmtValue::Int(20)));
        }
        _ => panic!("Expected ArrayMap, got {result:?}"),
    }
}

#[test]
fn test_eval_array_store_multiple() {
    // store(store(const(0), 1, 10), 2, 20) → two entries
    let arr = SmtValue::ConstArray(Box::new(SmtValue::Int(0)));
    let arr = eval_array_store(arr, SmtValue::Int(1), SmtValue::Int(10));
    let arr = eval_array_store(arr, SmtValue::Int(2), SmtValue::Int(20));
    // Verify both entries via select
    assert_eq!(
        eval_array_select(&arr, &SmtValue::Int(1)),
        Some(SmtValue::Int(10))
    );
    assert_eq!(
        eval_array_select(&arr, &SmtValue::Int(2)),
        Some(SmtValue::Int(20))
    );
    assert_eq!(
        eval_array_select(&arr, &SmtValue::Int(3)),
        Some(SmtValue::Int(0))
    );
}

#[test]
fn test_eval_array_store_preserves_opaque_default_6289() {
    let arr = SmtValue::Opaque("@arr33".to_string());
    let stored = eval_array_store(arr, SmtValue::BitVec(0, 32), SmtValue::Bool(true));
    assert_eq!(
        eval_array_select(&stored, &SmtValue::BitVec(1, 32)),
        Some(SmtValue::Opaque("@arr33".to_string()))
    );
}

// --- evaluate_expr integration with arrays ---

use crate::expr::ChcVar;
use crate::ChcSort;
use std::sync::Arc;

/// Helper: wrap expr in Arc for Op arguments.
fn a(e: ChcExpr) -> Arc<ChcExpr> {
    Arc::new(e)
}

/// Helper: create a ChcVar with the given name and Int sort.
fn int_var(name: &str) -> ChcVar {
    ChcVar::new(name.to_string(), ChcSort::Int)
}

#[test]
fn test_evaluate_expr_const_array() {
    let model = FxHashMap::default();
    let expr = ChcExpr::ConstArray(ChcSort::Int, a(ChcExpr::Int(42)));
    let result = evaluate_expr(&expr, &model);
    assert_eq!(
        result,
        Some(SmtValue::ConstArray(Box::new(SmtValue::Int(42))))
    );
}

#[test]
fn test_evaluate_expr_store_then_select() {
    let model = FxHashMap::default();
    // select(store(const(0), 5, 100), 5) → 100
    let const_arr = ChcExpr::ConstArray(ChcSort::Int, a(ChcExpr::Int(0)));
    let stored = ChcExpr::Op(
        ChcOp::Store,
        vec![a(const_arr), a(ChcExpr::Int(5)), a(ChcExpr::Int(100))],
    );
    let selected = ChcExpr::Op(ChcOp::Select, vec![a(stored), a(ChcExpr::Int(5))]);
    assert_eq!(evaluate_expr(&selected, &model), Some(SmtValue::Int(100)));
}

#[test]
fn test_evaluate_expr_select_miss() {
    let model = FxHashMap::default();
    // select(store(const(0), 5, 100), 3) → 0 (default)
    let const_arr = ChcExpr::ConstArray(ChcSort::Int, a(ChcExpr::Int(0)));
    let stored = ChcExpr::Op(
        ChcOp::Store,
        vec![a(const_arr), a(ChcExpr::Int(5)), a(ChcExpr::Int(100))],
    );
    let selected = ChcExpr::Op(ChcOp::Select, vec![a(stored), a(ChcExpr::Int(3))]);
    assert_eq!(evaluate_expr(&selected, &model), Some(SmtValue::Int(0)));
}

#[test]
fn test_evaluate_expr_eq_with_opaque_value_returns_none_6289() {
    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Opaque("__au_k0".to_string()));

    let expr = ChcExpr::eq(
        ChcExpr::var(ChcVar::new("x", ChcSort::BitVec(32))),
        ChcExpr::BitVec(0, 32),
    );

    assert_eq!(evaluate_expr(&expr, &model), None);
}

#[test]
fn test_evaluate_expr_eq_array_overwrite_uses_last_store_wins_1753() {
    let lhs = ChcVar::new(
        "lhs",
        ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
    );
    let rhs = ChcVar::new(
        "rhs",
        ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
    );
    let expr = ChcExpr::eq(ChcExpr::var(lhs.clone()), ChcExpr::var(rhs.clone()));

    let mut model = FxHashMap::default();
    model.insert(
        lhs.name,
        SmtValue::ArrayMap {
            default: Box::new(SmtValue::Int(0)),
            entries: vec![
                (SmtValue::Int(1), SmtValue::Int(10)),
                (SmtValue::Int(1), SmtValue::Int(20)),
            ],
        },
    );
    model.insert(
        rhs.name,
        SmtValue::ArrayMap {
            default: Box::new(SmtValue::Int(0)),
            entries: vec![(SmtValue::Int(1), SmtValue::Int(20))],
        },
    );

    assert_eq!(evaluate_expr(&expr, &model), Some(SmtValue::Bool(true)));
}

#[test]
fn test_evaluate_expr_nested_store_select() {
    let model = FxHashMap::default();
    // store(store(const(false), bv0, true), bv1, true)
    // then select at bv0 → true, select at bv2 → false (default)
    let const_arr = ChcExpr::ConstArray(ChcSort::BitVec(32), a(ChcExpr::Bool(false)));
    let s1 = ChcExpr::Op(
        ChcOp::Store,
        vec![
            a(const_arr),
            a(ChcExpr::BitVec(0, 32)),
            a(ChcExpr::Bool(true)),
        ],
    );
    let s2 = ChcExpr::Op(
        ChcOp::Store,
        vec![a(s1), a(ChcExpr::BitVec(1, 32)), a(ChcExpr::Bool(true))],
    );
    let sel0 = ChcExpr::Op(
        ChcOp::Select,
        vec![a(s2.clone()), a(ChcExpr::BitVec(0, 32))],
    );
    let sel2 = ChcExpr::Op(ChcOp::Select, vec![a(s2), a(ChcExpr::BitVec(2, 32))]);
    assert_eq!(evaluate_expr(&sel0, &model), Some(SmtValue::Bool(true)));
    assert_eq!(evaluate_expr(&sel2, &model), Some(SmtValue::Bool(false)));
}

#[test]
fn test_evaluate_expr_select_with_model_var() {
    let mut model = FxHashMap::default();
    // Model: arr = store(const(0), 3, 99)
    model.insert(
        "arr".to_string(),
        SmtValue::ArrayMap {
            default: Box::new(SmtValue::Int(0)),
            entries: vec![(SmtValue::Int(3), SmtValue::Int(99))],
        },
    );
    let arr_var = ChcExpr::Var(int_var("arr"));
    // select(arr, 3) → 99
    let sel = ChcExpr::Op(ChcOp::Select, vec![a(arr_var.clone()), a(ChcExpr::Int(3))]);
    assert_eq!(evaluate_expr(&sel, &model), Some(SmtValue::Int(99)));
    // select(arr, 0) → 0 (default)
    let sel0 = ChcExpr::Op(ChcOp::Select, vec![a(arr_var), a(ChcExpr::Int(0))]);
    assert_eq!(evaluate_expr(&sel0, &model), Some(SmtValue::Int(0)));
}

#[test]
fn test_evaluate_expr_datatype_selector_and_tester() {
    let pair_sort = ChcSort::Datatype {
        name: "Pair".to_string(),
        constructors: Arc::new(vec![ChcDtConstructor {
            name: "mk".to_string(),
            selectors: vec![
                ChcDtSelector {
                    name: "fst".to_string(),
                    sort: ChcSort::Int,
                },
                ChcDtSelector {
                    name: "snd".to_string(),
                    sort: ChcSort::Int,
                },
            ],
        }]),
    };
    let constructor = ChcExpr::FuncApp(
        "mk".to_string(),
        pair_sort.clone(),
        vec![a(ChcExpr::Int(10)), a(ChcExpr::Int(42))],
    );
    let expected_value =
        SmtValue::Datatype("mk".to_string(), vec![SmtValue::Int(10), SmtValue::Int(42)]);
    let mut model = FxHashMap::default();
    model.insert("p".to_string(), expected_value.clone());

    assert_eq!(
        evaluate_expr(&constructor, &model),
        Some(expected_value.clone())
    );

    let p_var = ChcExpr::Var(ChcVar::new("p", pair_sort));
    let selector = ChcExpr::FuncApp("fst".to_string(), ChcSort::Int, vec![a(p_var.clone())]);
    let tester = ChcExpr::FuncApp("is-mk".to_string(), ChcSort::Bool, vec![a(p_var.clone())]);
    let equality = ChcExpr::eq(p_var, constructor);

    assert_eq!(evaluate_expr(&selector, &model), Some(SmtValue::Int(10)));
    assert_eq!(evaluate_expr(&tester, &model), Some(SmtValue::Bool(true)));
    assert_eq!(evaluate_expr(&equality, &model), Some(SmtValue::Bool(true)));
}
