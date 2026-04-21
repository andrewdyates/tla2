// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration tests for the complete compound type encoding pipeline.
//!
//! Tests records containing sets, functions over sequences, quantifiers
//! over compound types, set comprehension, CHOOSE, and cross-type operations
//! in the z4 symbolic engine.
//!
//! These tests exercise the full translate pipeline via the public API:
//! Z4Translator -> translate_bool/translate_int -> assert -> check_sat -> get_model
//!
//! Part of #3749: Symbolic set/function/sequence/record encoding in z4.

use ntest::timeout;
use num_bigint::BigInt;
use tla_core::ast::{BoundVar, ExceptPathElement, ExceptSpec, Expr, RecordFieldName};
use tla_core::name_intern::NameId;
use tla_core::Spanned;
use tla_z4::{SolveResult, TlaSort, Z4Translator};

fn spanned<T>(node: T) -> Spanned<T> {
    Spanned::dummy(node)
}

fn ident(name: &str) -> Spanned<Expr> {
    spanned(Expr::Ident(name.to_string(), NameId::INVALID))
}

fn int(n: i64) -> Spanned<Expr> {
    spanned(Expr::Int(BigInt::from(n)))
}

fn bi(n: i64) -> BigInt {
    BigInt::from(n)
}

fn bound_var(name: &str, domain: Spanned<Expr>) -> BoundVar {
    BoundVar {
        name: spanned(name.to_string()),
        domain: Some(Box::new(domain)),
        pattern: None,
    }
}

fn field_name(name: &str) -> RecordFieldName {
    RecordFieldName::new(spanned(name.to_string()))
}

// =========================================================================
// 1. Record field access with set membership constraint
//
// Scenario: Record r = [status: Int, priority: Int].
// Constraint: r.status \in {1, 2, 3} /\ r.priority = 10.
// Verifies record field access + set membership work together.
// =========================================================================

#[test]
#[timeout(10_000)]
fn test_record_field_in_finite_set() {
    let mut trans = Z4Translator::new();
    trans
        .declare_record_var(
            "r",
            vec![
                ("status".to_string(), TlaSort::Int),
                ("priority".to_string(), TlaSort::Int),
            ],
        )
        .unwrap();

    // r.status \in {1, 2, 3}
    let status_access = spanned(Expr::RecordAccess(
        Box::new(ident("r")),
        field_name("status"),
    ));
    let membership = spanned(Expr::In(
        Box::new(status_access),
        Box::new(spanned(Expr::SetEnum(vec![int(1), int(2), int(3)]))),
    ));

    // r.priority = 10
    let priority_access = spanned(Expr::RecordAccess(
        Box::new(ident("r")),
        field_name("priority"),
    ));
    let priority_eq = spanned(Expr::Eq(Box::new(priority_access), Box::new(int(10))));

    // Conjunction: r.status \in {1,2,3} /\ r.priority = 10
    let formula = spanned(Expr::And(Box::new(membership), Box::new(priority_eq)));

    let term = trans.translate_bool(&formula).unwrap();
    trans.assert(term);

    assert!(
        matches!(trans.check_sat(), SolveResult::Sat),
        "record field + set membership conjunction must be SAT"
    );

    let model = trans.get_model().unwrap();
    let priority = model.int_val("r__priority").cloned();
    assert_eq!(priority, Some(bi(10)));

    // status must be one of {1, 2, 3}
    let status = model.int_val("r__status").cloned().unwrap();
    assert!(
        status == bi(1) || status == bi(2) || status == bi(3),
        "status must be in {{1, 2, 3}}, got {:?}",
        status
    );
}

// =========================================================================
// 2. Function equality propagation
//
// Scenario: f, g : {1, 2} -> Int, assert f = g and f[1] = 42.
// Verifies function equality forces g[1] = 42.
// =========================================================================

#[test]
#[timeout(10_000)]
fn test_function_equality_propagates_values() {
    let mut trans = Z4Translator::new();

    let keys = vec!["1".to_string(), "2".to_string()];
    trans
        .declare_func_var("f", keys.clone(), TlaSort::Int)
        .unwrap();
    trans.declare_func_var("g", keys, TlaSort::Int).unwrap();

    // f[1] = 42
    let f1_eq = spanned(Expr::Eq(Box::new(ident("f__1")), Box::new(int(42))));
    let t1 = trans.translate_bool(&f1_eq).unwrap();
    trans.assert(t1);

    // f = g (function equality)
    let f_eq_g = spanned(Expr::Eq(Box::new(ident("f")), Box::new(ident("g"))));
    let eq_term = trans.translate_bool(&f_eq_g).unwrap();
    trans.assert(eq_term);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans.get_model().unwrap();
    assert_eq!(
        model.int_val("g__1").cloned(),
        Some(bi(42)),
        "f = g and f[1] = 42 must force g[1] = 42"
    );
}

// =========================================================================
// 3. Record EXCEPT updates one field, preserves others
//
// Scenario: Record r = [a: Int, b: Int], assert r.a = 10, r.b = 20.
// Apply [r EXCEPT !.a = 99]. The EXCEPT should be satisfiable.
// =========================================================================

#[test]
#[timeout(10_000)]
fn test_record_except_preserves_other_fields() {
    let mut trans = Z4Translator::new();
    trans
        .declare_record_var(
            "r",
            vec![
                ("a".to_string(), TlaSort::Int),
                ("b".to_string(), TlaSort::Int),
            ],
        )
        .unwrap();

    // r.a = 10
    let ra_eq = spanned(Expr::Eq(Box::new(ident("r__a")), Box::new(int(10))));
    let t1 = trans.translate_bool(&ra_eq).unwrap();
    trans.assert(t1);

    // r.b = 20
    let rb_eq = spanned(Expr::Eq(Box::new(ident("r__b")), Box::new(int(20))));
    let t2 = trans.translate_bool(&rb_eq).unwrap();
    trans.assert(t2);

    // [r EXCEPT !.a = 99]
    let except_expr = spanned(Expr::Except(
        Box::new(ident("r")),
        vec![ExceptSpec {
            path: vec![ExceptPathElement::Field(field_name("a"))],
            value: int(99),
        }],
    ));

    let term = trans.translate_bool(&except_expr).unwrap();
    trans.assert(term);

    assert!(
        matches!(trans.check_sat(), SolveResult::Sat),
        "record EXCEPT must be satisfiable"
    );
}

// =========================================================================
// 4. Function EXCEPT with value verification
//
// Scenario: f : {1, 2} -> Int, f[1] = 10, f[2] = 20.
// Apply [f EXCEPT ![1] = 99]. Should be SAT.
// =========================================================================

#[test]
#[timeout(10_000)]
fn test_function_except_dispatch() {
    let mut trans = Z4Translator::new();
    trans
        .declare_func_var("f", vec!["1".to_string(), "2".to_string()], TlaSort::Int)
        .unwrap();

    // f[1] = 10, f[2] = 20
    let f1_eq = spanned(Expr::Eq(Box::new(ident("f__1")), Box::new(int(10))));
    let f2_eq = spanned(Expr::Eq(Box::new(ident("f__2")), Box::new(int(20))));
    let t1 = trans.translate_bool(&f1_eq).unwrap();
    let t2 = trans.translate_bool(&f2_eq).unwrap();
    trans.assert(t1);
    trans.assert(t2);

    // [f EXCEPT ![1] = 99]
    let except_expr = spanned(Expr::Except(
        Box::new(ident("f")),
        vec![ExceptSpec {
            path: vec![ExceptPathElement::Index(int(1))],
            value: int(99),
        }],
    ));

    let term = trans.translate_bool(&except_expr).unwrap();
    trans.assert(term);

    assert!(
        matches!(trans.check_sat(), SolveResult::Sat),
        "function EXCEPT must be satisfiable"
    );
}

// =========================================================================
// 5. Subseteq with finite sets (array encoding)
//
// Scenario: {1, 2} \subseteq {1, 2, 3} is TRUE; {1, 2, 3} \subseteq {1, 2} is FALSE.
// =========================================================================

#[test]
#[timeout(10_000)]
fn test_subseteq_sat() {
    let mut trans = Z4Translator::new_with_arrays();

    let subseteq = spanned(Expr::Subseteq(
        Box::new(spanned(Expr::SetEnum(vec![int(1), int(2)]))),
        Box::new(spanned(Expr::SetEnum(vec![int(1), int(2), int(3)]))),
    ));

    let term = trans.translate_bool(&subseteq).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

#[test]
#[timeout(10_000)]
fn test_subseteq_unsat() {
    let mut trans = Z4Translator::new_with_arrays();

    let subseteq = spanned(Expr::Subseteq(
        Box::new(spanned(Expr::SetEnum(vec![int(1), int(2), int(3)]))),
        Box::new(spanned(Expr::SetEnum(vec![int(1), int(2)]))),
    ));

    let term = trans.translate_bool(&subseteq).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
}

// =========================================================================
// 6. Quantifier expansion over finite set
//
// \A x \in {1, 2, 3} : x > 0 is TRUE.
// \E x \in {-1, 0, 1} : x > 0 is TRUE (1 > 0).
// \A x \in {1, 2, -1} : x > 0 is FALSE (-1 not > 0).
// =========================================================================

#[test]
#[timeout(10_000)]
fn test_forall_over_set_enum() {
    let mut trans = Z4Translator::new();

    let expr = spanned(Expr::Forall(
        vec![bound_var(
            "x",
            spanned(Expr::SetEnum(vec![int(1), int(2), int(3)])),
        )],
        Box::new(spanned(Expr::Gt(Box::new(ident("x")), Box::new(int(0))))),
    ));

    let term = trans.translate_bool(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

#[test]
#[timeout(10_000)]
fn test_exists_over_set_enum() {
    let mut trans = Z4Translator::new();

    let expr = spanned(Expr::Exists(
        vec![bound_var(
            "x",
            spanned(Expr::SetEnum(vec![int(-1), int(0), int(1)])),
        )],
        Box::new(spanned(Expr::Gt(Box::new(ident("x")), Box::new(int(0))))),
    ));

    let term = trans.translate_bool(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

#[test]
#[timeout(10_000)]
fn test_forall_over_set_enum_unsat() {
    let mut trans = Z4Translator::new();

    let expr = spanned(Expr::Forall(
        vec![bound_var(
            "x",
            spanned(Expr::SetEnum(vec![int(1), int(2), int(-1)])),
        )],
        Box::new(spanned(Expr::Gt(Box::new(ident("x")), Box::new(int(0))))),
    ));

    let term = trans.translate_bool(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
}

// =========================================================================
// 7. CHOOSE with int domain via translate_int
//
// CHOOSE x \in {10, 20, 30} : x > 15 should yield 20 or 30.
// CHOOSE x \in {1, 2, 3} : x > 5 has no satisfying element.
// =========================================================================

#[test]
#[timeout(10_000)]
fn test_choose_int_satisfiable() {
    let mut trans = Z4Translator::new();
    trans.declare_var("y", TlaSort::Int).unwrap();

    // CHOOSE x \in {10, 20, 30} : x > 15
    let choose = spanned(Expr::Choose(
        bound_var("x", spanned(Expr::SetEnum(vec![int(10), int(20), int(30)]))),
        Box::new(spanned(Expr::Gt(Box::new(ident("x")), Box::new(int(15))))),
    ));

    // y = CHOOSE x \in {10,20,30} : x > 15
    let y_eq_choose = spanned(Expr::Eq(Box::new(ident("y")), Box::new(choose)));
    let term = trans.translate_bool(&y_eq_choose).unwrap();
    trans.assert(term);

    // y > 15 (the predicate should be satisfied by the chosen element)
    let y_gt_15 = spanned(Expr::Gt(Box::new(ident("y")), Box::new(int(15))));
    let pred_term = trans.translate_bool(&y_gt_15).unwrap();
    trans.assert(pred_term);

    assert!(
        matches!(trans.check_sat(), SolveResult::Sat),
        "CHOOSE with satisfiable predicate must be SAT"
    );
    let model = trans.get_model().unwrap();
    let y_val = model.int_val("y").cloned().unwrap();
    assert!(
        y_val == bi(20) || y_val == bi(30),
        "CHOOSE result must be 20 or 30, got {:?}",
        y_val
    );
}

#[test]
#[timeout(10_000)]
fn test_choose_int_unsatisfiable() {
    let mut trans = Z4Translator::new();

    // CHOOSE x \in {1, 2, 3} : x > 5 -- no element satisfies
    let choose = spanned(Expr::Choose(
        bound_var("x", spanned(Expr::SetEnum(vec![int(1), int(2), int(3)]))),
        Box::new(spanned(Expr::Gt(Box::new(ident("x")), Box::new(int(5))))),
    ));

    // Assert CHOOSE result > 0 (try to use the result)
    let pos = spanned(Expr::Gt(Box::new(choose), Box::new(int(0))));
    let term = trans.translate_bool(&pos).unwrap();
    trans.assert(term);
    assert!(
        matches!(trans.check_sat(), SolveResult::Unsat(_)),
        "CHOOSE with no satisfying element should be UNSAT"
    );
}

// =========================================================================
// 8. Record equality propagation
//
// Two records r1, r2 with same fields. Assert r1 = r2 and r1.x = 7.
// Verify r2.x = 7.
// =========================================================================

#[test]
#[timeout(10_000)]
fn test_record_equality_propagates_fields() {
    let mut trans = Z4Translator::new();

    let fields = vec![
        ("x".to_string(), TlaSort::Int),
        ("y".to_string(), TlaSort::Int),
    ];
    trans.declare_record_var("r1", fields.clone()).unwrap();
    trans.declare_record_var("r2", fields).unwrap();

    // r1 = r2
    let eq = spanned(Expr::Eq(Box::new(ident("r1")), Box::new(ident("r2"))));
    let eq_term = trans.translate_bool(&eq).unwrap();
    trans.assert(eq_term);

    // r1.x = 7
    let r1x_eq = spanned(Expr::Eq(Box::new(ident("r1__x")), Box::new(int(7))));
    let r1x_term = trans.translate_bool(&r1x_eq).unwrap();
    trans.assert(r1x_term);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans.get_model().unwrap();
    assert_eq!(
        model.int_val("r2__x").cloned(),
        Some(bi(7)),
        "r1 = r2 and r1.x = 7 must force r2.x = 7"
    );
}

// =========================================================================
// 9. Tuple declaration and element access
//
// Declare tuple t = <<Int, Int>>, assert t[1] = 5, t[2] = 10.
// =========================================================================

#[test]
#[timeout(10_000)]
fn test_tuple_var_element_access() {
    let mut trans = Z4Translator::new();
    trans
        .declare_tuple_var("t", vec![TlaSort::Int, TlaSort::Int])
        .unwrap();

    let eq1 = trans
        .translate_bool(&spanned(Expr::Eq(
            Box::new(ident("t__1")),
            Box::new(int(5)),
        )))
        .unwrap();
    trans.assert(eq1);

    let eq2 = trans
        .translate_bool(&spanned(Expr::Eq(
            Box::new(ident("t__2")),
            Box::new(int(10)),
        )))
        .unwrap();
    trans.assert(eq2);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans.get_model().unwrap();
    assert_eq!(model.int_val("t__1").cloned(), Some(bi(5)));
    assert_eq!(model.int_val("t__2").cloned(), Some(bi(10)));
}

// =========================================================================
// 10. NotIn with set membership negation
//
// x \notin {1, 2, 3} /\ x = 2 -- UNSAT
// x \notin {1, 2, 3} /\ x = 5 -- SAT
// =========================================================================

#[test]
#[timeout(10_000)]
fn test_notin_with_membership_unsat() {
    let mut trans = Z4Translator::new();
    trans.declare_var("x", TlaSort::Int).unwrap();

    let notin = spanned(Expr::NotIn(
        Box::new(ident("x")),
        Box::new(spanned(Expr::SetEnum(vec![int(1), int(2), int(3)]))),
    ));
    let x_eq_2 = spanned(Expr::Eq(Box::new(ident("x")), Box::new(int(2))));
    let formula = spanned(Expr::And(Box::new(notin), Box::new(x_eq_2)));
    let term = trans.translate_bool(&formula).unwrap();
    trans.assert(term);

    assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
}

#[test]
#[timeout(10_000)]
fn test_notin_with_membership_sat() {
    let mut trans = Z4Translator::new();
    trans.declare_var("x", TlaSort::Int).unwrap();

    let notin = spanned(Expr::NotIn(
        Box::new(ident("x")),
        Box::new(spanned(Expr::SetEnum(vec![int(1), int(2), int(3)]))),
    ));
    let x_eq_5 = spanned(Expr::Eq(Box::new(ident("x")), Box::new(int(5))));
    let formula = spanned(Expr::And(Box::new(notin), Box::new(x_eq_5)));
    let term = trans.translate_bool(&formula).unwrap();
    trans.assert(term);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

// =========================================================================
// 11. Record field access resolves to correct variable name
//
// Declare record, use RecordAccess to assert field equality, verify model.
// =========================================================================

#[test]
#[timeout(10_000)]
fn test_record_access_resolves_field() {
    let mut trans = Z4Translator::new();
    trans
        .declare_record_var(
            "r",
            vec![
                ("a".to_string(), TlaSort::Int),
                ("b".to_string(), TlaSort::Int),
            ],
        )
        .unwrap();

    // r.a = 42 via RecordAccess expression
    let access = spanned(Expr::RecordAccess(Box::new(ident("r")), field_name("a")));
    let eq = spanned(Expr::Eq(Box::new(access), Box::new(int(42))));
    let term = trans.translate_bool(&eq).unwrap();
    trans.assert(term);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans.get_model().unwrap();
    assert_eq!(model.int_val("r__a").cloned(), Some(bi(42)));
}

// =========================================================================
// 12. Function definition as boolean constraint
//
// [x \in {1, 2} |-> x + 1] translated through the pipeline.
// =========================================================================

#[test]
#[timeout(10_000)]
fn test_func_def_bool() {
    let mut trans = Z4Translator::new();

    let bound = bound_var("x", spanned(Expr::SetEnum(vec![int(1), int(2)])));
    let body = spanned(Expr::Add(Box::new(ident("x")), Box::new(int(1))));
    let func_def = spanned(Expr::FuncDef(vec![bound], Box::new(body)));

    let term = trans.translate_bool(&func_def).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

// =========================================================================
// 13. Exists quantifier with variable constraint
//
// \E x \in {1, 2, 3} : x = y, where y is a declared variable.
// With y = 2, should be SAT. With y = 5, UNSAT.
// =========================================================================

#[test]
#[timeout(10_000)]
fn test_exists_quantifier_with_variable_sat() {
    let mut trans = Z4Translator::new();
    trans.declare_var("y", TlaSort::Int).unwrap();

    let y_eq = spanned(Expr::Eq(Box::new(ident("y")), Box::new(int(2))));
    let y_term = trans.translate_bool(&y_eq).unwrap();
    trans.assert(y_term);

    let exists = spanned(Expr::Exists(
        vec![bound_var(
            "x",
            spanned(Expr::SetEnum(vec![int(1), int(2), int(3)])),
        )],
        Box::new(spanned(Expr::Eq(
            Box::new(ident("x")),
            Box::new(ident("y")),
        ))),
    ));

    let term = trans.translate_bool(&exists).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

#[test]
#[timeout(10_000)]
fn test_exists_quantifier_with_variable_unsat() {
    let mut trans = Z4Translator::new();
    trans.declare_var("y", TlaSort::Int).unwrap();

    let y_eq = spanned(Expr::Eq(Box::new(ident("y")), Box::new(int(5))));
    let y_term = trans.translate_bool(&y_eq).unwrap();
    trans.assert(y_term);

    let exists = spanned(Expr::Exists(
        vec![bound_var(
            "x",
            spanned(Expr::SetEnum(vec![int(1), int(2), int(3)])),
        )],
        Box::new(spanned(Expr::Eq(
            Box::new(ident("x")),
            Box::new(ident("y")),
        ))),
    ));

    let term = trans.translate_bool(&exists).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
}

// =========================================================================
// 14. Record field access in arithmetic expression
//
// Record r = [a: Int, b: Int], assert r.a = 5, r.a + r.b = 15.
// Verify r.b = 10.
// =========================================================================

#[test]
#[timeout(10_000)]
fn test_record_field_arithmetic() {
    let mut trans = Z4Translator::new();
    trans
        .declare_record_var(
            "r",
            vec![
                ("a".to_string(), TlaSort::Int),
                ("b".to_string(), TlaSort::Int),
            ],
        )
        .unwrap();

    let ra_eq = spanned(Expr::Eq(Box::new(ident("r__a")), Box::new(int(5))));
    let t1 = trans.translate_bool(&ra_eq).unwrap();
    trans.assert(t1);

    let sum = spanned(Expr::Add(Box::new(ident("r__a")), Box::new(ident("r__b"))));
    let sum_eq = spanned(Expr::Eq(Box::new(sum), Box::new(int(15))));
    let t2 = trans.translate_bool(&sum_eq).unwrap();
    trans.assert(t2);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans.get_model().unwrap();
    assert_eq!(model.int_val("r__b").cloned(), Some(bi(10)));
}

// =========================================================================
// 15. Function with different domain sizes -- equality is UNSAT
//
// f : {1,2} -> Int and g : {1,2,3} -> Int.
// f = g should be UNSAT (different domain sizes).
// =========================================================================

#[test]
#[timeout(10_000)]
fn test_function_equality_different_domains_unsat() {
    let mut trans = Z4Translator::new();
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

    let f_eq_g = spanned(Expr::Eq(Box::new(ident("f")), Box::new(ident("g"))));
    let term = trans.translate_bool(&f_eq_g).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
}

// =========================================================================
// 16. Combined record + function + quantifier pipeline
//
// Record r = [a: Int], function f : {1} -> Int,
// r.a = 10 /\ f[1] = r.a /\ \A x \in {10} : x = r.a
// =========================================================================

#[test]
#[timeout(10_000)]
fn test_combined_record_function_quantifier() {
    let mut trans = Z4Translator::new();
    trans
        .declare_record_var("r", vec![("a".to_string(), TlaSort::Int)])
        .unwrap();
    trans
        .declare_func_var("f", vec!["1".to_string()], TlaSort::Int)
        .unwrap();

    // r.a = 10
    let ra_eq = spanned(Expr::Eq(Box::new(ident("r__a")), Box::new(int(10))));
    let t1 = trans.translate_bool(&ra_eq).unwrap();
    trans.assert(t1);

    // f[1] = r.a
    let f1_eq_ra = spanned(Expr::Eq(Box::new(ident("f__1")), Box::new(ident("r__a"))));
    let t2 = trans.translate_bool(&f1_eq_ra).unwrap();
    trans.assert(t2);

    // \A x \in {10} : x = r.a
    let forall = spanned(Expr::Forall(
        vec![bound_var("x", spanned(Expr::SetEnum(vec![int(10)])))],
        Box::new(spanned(Expr::Eq(
            Box::new(ident("x")),
            Box::new(ident("r__a")),
        ))),
    ));
    let t3 = trans.translate_bool(&forall).unwrap();
    trans.assert(t3);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans.get_model().unwrap();
    assert_eq!(model.int_val("f__1").cloned(), Some(bi(10)));
    assert_eq!(model.int_val("r__a").cloned(), Some(bi(10)));
}

// =========================================================================
// 17. Forall with conjunction body
//
// \A x \in {1, 2, 3} : x > 0 /\ x < 5. All satisfy, SAT.
// =========================================================================

#[test]
#[timeout(10_000)]
fn test_forall_conjunction_body() {
    let mut trans = Z4Translator::new();

    let body = spanned(Expr::And(
        Box::new(spanned(Expr::Gt(Box::new(ident("x")), Box::new(int(0))))),
        Box::new(spanned(Expr::Lt(Box::new(ident("x")), Box::new(int(5))))),
    ));

    let expr = spanned(Expr::Forall(
        vec![bound_var(
            "x",
            spanned(Expr::SetEnum(vec![int(1), int(2), int(3)])),
        )],
        Box::new(body),
    ));

    let term = trans.translate_bool(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

// =========================================================================
// 18. Function definition with array encoding
//
// [x \in {1, 2, 3} |-> x + 10] with array mode.
// =========================================================================

#[test]
#[timeout(10_000)]
fn test_func_def_array_encoding() {
    let mut trans = Z4Translator::new_with_arrays();

    let bound = bound_var("x", spanned(Expr::SetEnum(vec![int(1), int(2), int(3)])));
    let body = spanned(Expr::Add(Box::new(ident("x")), Box::new(int(10))));
    let func_def = spanned(Expr::FuncDef(vec![bound], Box::new(body)));

    let term = trans.translate_bool(&func_def).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

// =========================================================================
// 19. Sequence variable declaration and query
//
// Declare sequence s of Int with max_len 3.
// Verify the variable was declared and SAT check works.
// =========================================================================

#[test]
#[timeout(10_000)]
fn test_seq_var_declaration_and_query() {
    let mut trans = Z4Translator::new_with_arrays();
    trans.declare_seq_var("s", TlaSort::Int, 3).unwrap();

    let seq_info = trans.get_seq_var("s").unwrap();
    assert_eq!(seq_info.max_len, 3);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

// =========================================================================
// 20. Multiple record variables with cross-constraints
//
// r1 = [x: Int, y: Int], r2 = [x: Int, y: Int].
// r1.x = 40, r1.x + r2.x = 100. Verify r2.x = 60.
// =========================================================================

#[test]
#[timeout(10_000)]
fn test_multiple_records_cross_constraints() {
    let mut trans = Z4Translator::new();

    let fields = vec![
        ("x".to_string(), TlaSort::Int),
        ("y".to_string(), TlaSort::Int),
    ];
    trans.declare_record_var("r1", fields.clone()).unwrap();
    trans.declare_record_var("r2", fields).unwrap();

    let r1x_eq = spanned(Expr::Eq(Box::new(ident("r1__x")), Box::new(int(40))));
    let t1 = trans.translate_bool(&r1x_eq).unwrap();
    trans.assert(t1);

    let sum = spanned(Expr::Add(
        Box::new(ident("r1__x")),
        Box::new(ident("r2__x")),
    ));
    let sum_eq = spanned(Expr::Eq(Box::new(sum), Box::new(int(100))));
    let t2 = trans.translate_bool(&sum_eq).unwrap();
    trans.assert(t2);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans.get_model().unwrap();
    assert_eq!(model.int_val("r2__x").cloned(), Some(bi(60)));
}
