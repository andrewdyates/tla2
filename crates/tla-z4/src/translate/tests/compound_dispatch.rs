// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Integration tests for compound type dispatch wiring (Part of #3778).
//!
//! Tests that `translate_bool_extended` and `translate_int_extended` correctly
//! route compound type expressions to the appropriate encoder methods:
//! - `Expr::NotIn` -> membership negation
//! - `Expr::Record` -> `RecordEncoder` via `translate_record_construct_bool`
//! - `Expr::FuncDef` -> `FunctionEncoder` via `translate_func_def_bool`
//! - `Expr::Except` -> record/function EXCEPT via `translate_except_bool`
//! - `Expr::RecordAccess` -> `RecordEncoder` field access
//! - `Expr::Subseteq` -> `FiniteSetEncoder` via `translate_subseteq_bool`
//! - `Expr::Apply("Cardinality", _)` -> `FiniteSetEncoder` cardinality

use super::*;
use tla_core::ast::{ExceptPathElement, ExceptSpec, RecordFieldName};

// =========================================================================
// NotIn dispatch: x \notin S => ~(x \in S)
// =========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_notin_dispatch() {
    let mut trans = Z4Translator::new();
    trans.declare_var("x", TlaSort::Int).unwrap();

    // x \notin {1, 2, 3}  with x = 2 should be UNSAT
    let notin = spanned(Expr::NotIn(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::SetEnum(vec![
            spanned(Expr::Int(BigInt::from(1))),
            spanned(Expr::Int(BigInt::from(2))),
            spanned(Expr::Int(BigInt::from(3))),
        ]))),
    ));

    let notin_term = trans.translate_bool(&notin).unwrap();
    trans.assert(notin_term);

    // Also assert x = 2
    let x_eq_2 = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(2)))),
    ));
    let eq_term = trans.translate_bool(&x_eq_2).unwrap();
    trans.assert(eq_term);

    // x = 2 AND x \notin {1,2,3} is UNSAT
    assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_notin_dispatch_sat() {
    let mut trans = Z4Translator::new();
    trans.declare_var("x", TlaSort::Int).unwrap();

    // x \notin {1, 2, 3}  with x = 5 should be SAT
    let notin = spanned(Expr::NotIn(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::SetEnum(vec![
            spanned(Expr::Int(BigInt::from(1))),
            spanned(Expr::Int(BigInt::from(2))),
            spanned(Expr::Int(BigInt::from(3))),
        ]))),
    ));

    let notin_term = trans.translate_bool(&notin).unwrap();
    trans.assert(notin_term);

    // Also assert x = 5
    let x_eq_5 = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(5)))),
    ));
    let eq_term = trans.translate_bool(&x_eq_5).unwrap();
    trans.assert(eq_term);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

// =========================================================================
// Record construction dispatch: [a |-> 1, b |-> 2]
// =========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_record_construct_dispatch() {
    let mut trans = Z4Translator::new();

    // Translate [a |-> 1, b |-> 2] as a Bool constraint
    let record = spanned(Expr::Record(vec![
        (
            spanned("a".to_string()),
            spanned(Expr::Int(BigInt::from(1))),
        ),
        (
            spanned("b".to_string()),
            spanned(Expr::Int(BigInt::from(2))),
        ),
    ]));

    let term = trans.translate_bool(&record).unwrap();
    trans.assert(term);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

// =========================================================================
// Record field access dispatch: r.field
// =========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_record_access_int_dispatch() {
    let mut trans = Z4Translator::new();

    // Declare record r with fields a: Int, b: Int
    trans
        .declare_record_var(
            "r",
            vec![
                ("a".to_string(), TlaSort::Int),
                ("b".to_string(), TlaSort::Int),
            ],
        )
        .unwrap();

    // Assert r.a = 42
    let field_name = RecordFieldName::new(spanned("a".to_string()));
    let access = spanned(Expr::RecordAccess(
        Box::new(spanned(Expr::Ident(
            "r".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        field_name,
    ));

    let eq = spanned(Expr::Eq(
        Box::new(access),
        Box::new(spanned(Expr::Int(BigInt::from(42)))),
    ));

    let term = trans.translate_bool(&eq).unwrap();
    trans.assert(term);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans.get_model().unwrap();
    assert_eq!(model.int_val("r__a").cloned(), Some(bi(42)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_record_access_bool_dispatch() {
    let mut trans = Z4Translator::new();

    // Declare record r with fields flag: Bool, count: Int
    trans
        .declare_record_var(
            "r",
            vec![
                ("flag".to_string(), TlaSort::Bool),
                ("count".to_string(), TlaSort::Int),
            ],
        )
        .unwrap();

    // Assert r.flag = TRUE
    let field_name = RecordFieldName::new(spanned("flag".to_string()));
    let access = spanned(Expr::RecordAccess(
        Box::new(spanned(Expr::Ident(
            "r".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        field_name,
    ));

    // r.flag should translate to a Bool term directly
    let term = trans.translate_bool(&access).unwrap();
    trans.assert(term);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans.get_model().unwrap();
    assert_eq!(model.bool_val("r__flag"), Some(true));
}

// =========================================================================
// Record equality dispatch: r1 = r2
// =========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_record_equality_dispatch() {
    let mut trans = Z4Translator::new();

    // Declare two records with the same structure
    let fields = vec![
        ("x".to_string(), TlaSort::Int),
        ("y".to_string(), TlaSort::Int),
    ];
    trans.declare_record_var("r1", fields.clone()).unwrap();
    trans.declare_record_var("r2", fields).unwrap();

    // Assert r1 = r2 (field-wise equality)
    let eq = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "r1".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Ident(
            "r2".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
    ));

    let term = trans.translate_bool(&eq).unwrap();
    trans.assert(term);

    // Assert r1.x = 10
    let r1_x_eq = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "r1__x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(10)))),
    ));
    let r1_term = trans.translate_bool(&r1_x_eq).unwrap();
    trans.assert(r1_term);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans.get_model().unwrap();
    // r1 = r2 means r2.x must also be 10
    assert_eq!(model.int_val("r2__x").cloned(), Some(bi(10)));
}

// =========================================================================
// Function definition dispatch: [x \in S |-> expr]
// =========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_func_def_dispatch() {
    let mut trans = Z4Translator::new();

    // [x \in {1, 2} |-> x + 1]
    let bound = tla_core::ast::BoundVar {
        name: spanned("x".to_string()),
        domain: Some(Box::new(spanned(Expr::SetEnum(vec![
            spanned(Expr::Int(BigInt::from(1))),
            spanned(Expr::Int(BigInt::from(2))),
        ])))),
        pattern: None,
    };

    let body = spanned(Expr::Add(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(1)))),
    ));

    let func_def = spanned(Expr::FuncDef(vec![bound], Box::new(body)));

    // Should translate without error
    let term = trans.translate_bool(&func_def).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

// =========================================================================
// EXCEPT dispatch: [f EXCEPT ![a] = b] (function EXCEPT)
// =========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_func_except_dispatch() {
    let mut trans = Z4Translator::new();

    // Declare f : {1, 2} -> Int
    trans
        .declare_func_var("f", vec!["1".to_string(), "2".to_string()], TlaSort::Int)
        .unwrap();

    // Assert f[1] = 10 and f[2] = 20
    let f1_eq = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "f__1".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(10)))),
    ));
    let f2_eq = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "f__2".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(20)))),
    ));

    let t1 = trans.translate_bool(&f1_eq).unwrap();
    let t2 = trans.translate_bool(&f2_eq).unwrap();
    trans.assert(t1);
    trans.assert(t2);

    // [f EXCEPT ![1] = 99]
    let except_spec = ExceptSpec {
        path: vec![ExceptPathElement::Index(spanned(Expr::Int(BigInt::from(
            1,
        ))))],
        value: spanned(Expr::Int(BigInt::from(99))),
    };

    let except_expr = spanned(Expr::Except(
        Box::new(spanned(Expr::Ident(
            "f".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        vec![except_spec],
    ));

    let term = trans.translate_bool(&except_expr).unwrap();
    trans.assert(term);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

// =========================================================================
// Record EXCEPT dispatch: [r EXCEPT !.field = value]
// =========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_record_except_dispatch() {
    let mut trans = Z4Translator::new();

    // Declare record r with fields a: Int, b: Int
    trans
        .declare_record_var(
            "r",
            vec![
                ("a".to_string(), TlaSort::Int),
                ("b".to_string(), TlaSort::Int),
            ],
        )
        .unwrap();

    // Assert r.a = 10, r.b = 20
    let ra_eq = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "r__a".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(10)))),
    ));
    let rb_eq = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "r__b".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(20)))),
    ));

    let t1 = trans.translate_bool(&ra_eq).unwrap();
    let t2 = trans.translate_bool(&rb_eq).unwrap();
    trans.assert(t1);
    trans.assert(t2);

    // [r EXCEPT !.a = 99]
    let except_spec = ExceptSpec {
        path: vec![ExceptPathElement::Field(RecordFieldName::new(spanned(
            "a".to_string(),
        )))],
        value: spanned(Expr::Int(BigInt::from(99))),
    };

    let except_expr = spanned(Expr::Except(
        Box::new(spanned(Expr::Ident(
            "r".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        vec![except_spec],
    ));

    let term = trans.translate_bool(&except_expr).unwrap();
    trans.assert(term);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

// =========================================================================
// Subseteq dispatch: S \subseteq T
// =========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_subseteq_dispatch_sat() {
    let mut trans = Z4Translator::new_with_arrays();

    // {1, 2} \subseteq {1, 2, 3} should be SAT (TRUE)
    let subseteq = spanned(Expr::Subseteq(
        Box::new(spanned(Expr::SetEnum(vec![
            spanned(Expr::Int(BigInt::from(1))),
            spanned(Expr::Int(BigInt::from(2))),
        ]))),
        Box::new(spanned(Expr::SetEnum(vec![
            spanned(Expr::Int(BigInt::from(1))),
            spanned(Expr::Int(BigInt::from(2))),
            spanned(Expr::Int(BigInt::from(3))),
        ]))),
    ));

    let term = trans.translate_bool(&subseteq).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_subseteq_dispatch_unsat() {
    let mut trans = Z4Translator::new_with_arrays();

    // {1, 2, 3} \subseteq {1, 2} AND it must be true
    // This is UNSAT because 3 is not in {1, 2}
    let subseteq = spanned(Expr::Subseteq(
        Box::new(spanned(Expr::SetEnum(vec![
            spanned(Expr::Int(BigInt::from(1))),
            spanned(Expr::Int(BigInt::from(2))),
            spanned(Expr::Int(BigInt::from(3))),
        ]))),
        Box::new(spanned(Expr::SetEnum(vec![
            spanned(Expr::Int(BigInt::from(1))),
            spanned(Expr::Int(BigInt::from(2))),
        ]))),
    ));

    let term = trans.translate_bool(&subseteq).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
}

// =========================================================================
// Cardinality dispatch: Cardinality(S) as Int
// =========================================================================

// =========================================================================
// Function equality dispatch (per-variable path): f = g
// Part of #3786: Function encoding — equality.
// =========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_func_equality_same_values_sat() {
    let mut trans = Z4Translator::new();

    // Declare f, g : {1, 2} -> Int
    trans
        .declare_func_var("f", vec!["1".to_string(), "2".to_string()], TlaSort::Int)
        .unwrap();
    trans
        .declare_func_var("g", vec!["1".to_string(), "2".to_string()], TlaSort::Int)
        .unwrap();

    // Assert f[1] = 10, f[2] = 20
    let f1_eq = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "f__1".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(10)))),
    ));
    let f2_eq = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "f__2".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(20)))),
    ));
    let t1 = trans.translate_bool(&f1_eq).unwrap();
    let t2 = trans.translate_bool(&f2_eq).unwrap();
    trans.assert(t1);
    trans.assert(t2);

    // Assert f = g
    let f_eq_g = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "f".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Ident(
            "g".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
    ));
    let eq_term = trans.translate_bool(&f_eq_g).unwrap();
    trans.assert(eq_term);

    // f = g AND f[1]=10, f[2]=20 is SAT
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans.get_model().unwrap();
    // g must have same values as f
    assert_eq!(model.int_val("g__1").cloned(), Some(bi(10)));
    assert_eq!(model.int_val("g__2").cloned(), Some(bi(20)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_func_equality_different_values_unsat() {
    let mut trans = Z4Translator::new();

    // Declare f, g : {1} -> Int
    trans
        .declare_func_var("f", vec!["1".to_string()], TlaSort::Int)
        .unwrap();
    trans
        .declare_func_var("g", vec!["1".to_string()], TlaSort::Int)
        .unwrap();

    // Assert f[1] = 10 and g[1] = 20
    let f1_eq = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "f__1".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(10)))),
    ));
    let g1_eq = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "g__1".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(20)))),
    ));
    let t1 = trans.translate_bool(&f1_eq).unwrap();
    let t2 = trans.translate_bool(&g1_eq).unwrap();
    trans.assert(t1);
    trans.assert(t2);

    // Assert f = g — but f[1]=10 and g[1]=20, so UNSAT
    let f_eq_g = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "f".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Ident(
            "g".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
    ));
    let eq_term = trans.translate_bool(&f_eq_g).unwrap();
    trans.assert(eq_term);

    assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_func_equality_different_domains_false() {
    let mut trans = Z4Translator::new();

    // f : {1, 2} -> Int, g : {1, 2, 3} -> Int
    // Different domain keys => f = g should be FALSE
    trans
        .declare_func_var("f", vec!["1".to_string(), "2".to_string()], TlaSort::Int)
        .unwrap();
    trans
        .declare_func_var(
            "g",
            vec!["1".to_string(), "2".to_string(), "3".to_string()],
            TlaSort::Int,
        )
        .unwrap();

    let f_eq_g = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "f".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Ident(
            "g".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
    ));
    let eq_term = trans.translate_bool(&f_eq_g).unwrap();
    trans.assert(eq_term);

    // Different domain sizes => equality is FALSE => UNSAT
    assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_func_equality_non_function_returns_none() {
    // When both sides are plain scalar variables (not functions),
    // try_translate_func_equality should return None so equality
    // falls through to the scalar path.
    let mut trans = Z4Translator::new();
    trans.declare_var("x", TlaSort::Int).unwrap();
    trans.declare_var("y", TlaSort::Int).unwrap();

    // x = y where x, y are scalars — this should be handled by
    // the Int equality path, not the function path
    let x_eq_y = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Ident(
            "y".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
    ));

    // This should succeed via the Int equality path
    let term = trans.translate_bool(&x_eq_y).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

// =========================================================================
// Function definition stores FuncTerm: [x \in S |-> expr]
// Part of #3786: verify array_func_vars storage.
// =========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_func_def_stores_array_func() {
    let mut trans = Z4Translator::new_with_arrays();

    // [x \in {1, 2, 3} |-> x + 10]
    let bound = tla_core::ast::BoundVar {
        name: spanned("x".to_string()),
        domain: Some(Box::new(spanned(Expr::SetEnum(vec![
            spanned(Expr::Int(BigInt::from(1))),
            spanned(Expr::Int(BigInt::from(2))),
            spanned(Expr::Int(BigInt::from(3))),
        ])))),
        pattern: None,
    };

    let body = spanned(Expr::Add(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(10)))),
    ));

    let func_def = spanned(Expr::FuncDef(vec![bound], Box::new(body)));

    let term = trans.translate_bool(&func_def).unwrap();
    trans.assert(term);

    // After translating the func def, there should be one entry in array_func_vars
    // We can't directly inspect array_func_vars (private), but we can verify
    // the solver is SAT and no errors occurred
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_func_def_empty_domain_trivially_true() {
    let mut trans = Z4Translator::new_with_arrays();

    // [x \in {} |-> x] — empty domain function
    let bound = tla_core::ast::BoundVar {
        name: spanned("x".to_string()),
        domain: Some(Box::new(spanned(Expr::SetEnum(vec![])))),
        pattern: None,
    };

    let body = spanned(Expr::Ident(
        "x".to_string(),
        tla_core::name_intern::NameId::INVALID,
    ));

    let func_def = spanned(Expr::FuncDef(vec![bound], Box::new(body)));

    let term = trans.translate_bool(&func_def).unwrap();
    trans.assert(term);

    // Empty domain function is trivially true
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

// =========================================================================
// Cardinality dispatch: Cardinality(S) as Int
// =========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_cardinality_dispatch() {
    let mut trans = Z4Translator::new_with_arrays();
    trans.declare_var("n", TlaSort::Int).unwrap();

    // n = Cardinality({1, 2, 3})
    let card = spanned(Expr::Apply(
        Box::new(spanned(Expr::Ident(
            "Cardinality".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        vec![spanned(Expr::SetEnum(vec![
            spanned(Expr::Int(BigInt::from(1))),
            spanned(Expr::Int(BigInt::from(2))),
            spanned(Expr::Int(BigInt::from(3))),
        ]))],
    ));

    let n_eq_card = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "n".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(card),
    ));

    let term = trans.translate_bool(&n_eq_card).unwrap();
    trans.assert(term);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans.get_model().unwrap();
    assert_eq!(model.int_val("n").cloned(), Some(bi(3)));
}
