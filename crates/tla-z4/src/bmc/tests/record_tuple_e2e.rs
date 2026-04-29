// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for BMC record and tuple encoding via per-field/per-element SMT variables.
//!
//! Part of #3787: Validates record construction, field access, EXCEPT,
//! tuple construction, indexing, and UNCHANGED operations in the BMC translator.

use super::*;
use tla_core::ast::{ExceptPathElement, ExceptSpec, RecordFieldName};
use z4_dpll::api::SolveResult;

/// Helper: create a BMC translator with array support.
fn bmc_array(k: usize) -> BmcTranslator {
    BmcTranslator::new_with_arrays(k).unwrap()
}

/// Helper: create an Ident expression with INVALID NameId.
fn ident(name: &str) -> Spanned<Expr> {
    spanned(Expr::Ident(
        name.to_string(),
        tla_core::name_intern::NameId::INVALID,
    ))
}

/// Helper: create an integer literal expression.
fn int(n: i64) -> Spanned<Expr> {
    spanned(Expr::Int(BigInt::from(n)))
}

/// Helper: create a spanned string.
fn sstr(s: &str) -> Spanned<String> {
    Spanned::dummy(s.to_string())
}

/// Helper: assert `term == int_val` in solver (avoids double borrow).
fn assert_term_eq_int(bmc: &mut BmcTranslator, term: z4_dpll::api::Term, val: i64) {
    let c = bmc.solver.int_const(val);
    let eq = bmc.solver.try_eq(term, c).unwrap();
    bmc.assert(eq);
}

// ================================================================
// Record declaration
// ================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_declare_record_var_int_fields() {
    let mut bmc = bmc_array(2);
    bmc.declare_record_var(
        "r",
        vec![
            ("a".to_string(), TlaSort::Int),
            ("b".to_string(), TlaSort::Int),
        ],
    )
    .unwrap();
    assert!(bmc.record_vars.contains_key("r"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_declare_record_var_mixed_fields() {
    let mut bmc = bmc_array(1);
    bmc.declare_record_var(
        "r",
        vec![
            ("flag".to_string(), TlaSort::Bool),
            ("count".to_string(), TlaSort::Int),
        ],
    )
    .unwrap();
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_declare_record_var_allows_set_field() {
    let mut bmc = bmc_array(0);
    let result = bmc.declare_record_var(
        "r",
        vec![(
            "s".to_string(),
            TlaSort::Set {
                element_sort: Box::new(TlaSort::Int),
            },
        )],
    );
    assert!(result.is_ok(), "Set fields should be allowed in records");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_declare_record_var_rejects_unsupported_compound_field() {
    let mut bmc = bmc_array(0);
    // Sequence fields are still unsupported
    let result = bmc.declare_record_var(
        "r",
        vec![(
            "s".to_string(),
            TlaSort::Sequence {
                element_sort: Box::new(TlaSort::Int),
                max_len: 5,
            },
        )],
    );
    assert!(result.is_err(), "Sequence fields should still be rejected");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_declare_var_delegates_record_sort() {
    let mut bmc = bmc_array(1);
    bmc.declare_var(
        "r",
        TlaSort::Record {
            field_sorts: vec![
                ("x".to_string(), TlaSort::Int),
                ("y".to_string(), TlaSort::Bool),
            ],
        },
    )
    .unwrap();
    assert!(bmc.record_vars.contains_key("r"));
    assert!(!bmc.vars.contains_key("r"));
}

// ================================================================
// Record field access
// ================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_record_field_access_int() {
    let mut bmc = bmc_array(0);
    bmc.declare_record_var(
        "r",
        vec![
            ("a".to_string(), TlaSort::Int),
            ("b".to_string(), TlaSort::Int),
        ],
    )
    .unwrap();

    // r.a = 42
    let access = spanned(Expr::RecordAccess(
        Box::new(ident("r")),
        RecordFieldName::new(sstr("a")),
    ));
    let eq = spanned(Expr::Eq(Box::new(access), Box::new(int(42))));
    let term = bmc.translate_init(&eq).unwrap();
    bmc.assert(term);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_record_field_access_contradicts_unsat() {
    let mut bmc = bmc_array(0);
    bmc.declare_record_var("r", vec![("x".to_string(), TlaSort::Int)])
        .unwrap();

    // r.x = 10 AND r.x = 20 -> UNSAT
    let rx = spanned(Expr::RecordAccess(
        Box::new(ident("r")),
        RecordFieldName::new(sstr("x")),
    ));

    let eq1 = bmc
        .translate_init(&spanned(Expr::Eq(Box::new(rx.clone()), Box::new(int(10)))))
        .unwrap();
    bmc.assert(eq1);

    let eq2 = bmc
        .translate_init(&spanned(Expr::Eq(Box::new(rx), Box::new(int(20)))))
        .unwrap();
    bmc.assert(eq2);

    assert!(matches!(bmc.check_sat(), SolveResult::Unsat(_)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_record_different_fields_independent() {
    let mut bmc = bmc_array(0);
    bmc.declare_record_var(
        "r",
        vec![
            ("a".to_string(), TlaSort::Int),
            ("b".to_string(), TlaSort::Int),
        ],
    )
    .unwrap();

    // r.a = 10 AND r.b = 20 -> SAT (different fields)
    let ra = spanned(Expr::RecordAccess(
        Box::new(ident("r")),
        RecordFieldName::new(sstr("a")),
    ));
    let rb = spanned(Expr::RecordAccess(
        Box::new(ident("r")),
        RecordFieldName::new(sstr("b")),
    ));

    let eq1 = bmc
        .translate_init(&spanned(Expr::Eq(Box::new(ra), Box::new(int(10)))))
        .unwrap();
    bmc.assert(eq1);

    let eq2 = bmc
        .translate_init(&spanned(Expr::Eq(Box::new(rb), Box::new(int(20)))))
        .unwrap();
    bmc.assert(eq2);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

// ================================================================
// Record literal equality: r' = [a |-> 1, b |-> 2]
// ================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_record_literal_eq() {
    let mut bmc = bmc_array(1);
    bmc.declare_record_var(
        "r",
        vec![
            ("a".to_string(), TlaSort::Int),
            ("b".to_string(), TlaSort::Int),
        ],
    )
    .unwrap();

    // r' = [a |-> 1, b |-> 2]
    let record_literal = spanned(Expr::Record(vec![
        (sstr("a"), Spanned::dummy(Expr::Int(BigInt::from(1)))),
        (sstr("b"), Spanned::dummy(Expr::Int(BigInt::from(2)))),
    ]));
    let r_prime = spanned(Expr::Prime(Box::new(ident("r"))));
    let eq = spanned(Expr::Eq(Box::new(r_prime), Box::new(record_literal)));

    bmc.current_step = 0;
    let term = bmc.translate_bool(&eq).unwrap();
    bmc.assert(term);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));

    // Verify r'.a = 1 and r'.b = 2
    let a_step1 = bmc.get_record_field_at_step("r", "a", 1).unwrap();
    assert_term_eq_int(&mut bmc, a_step1, 1);
    let b_step1 = bmc.get_record_field_at_step("r", "b", 1).unwrap();
    assert_term_eq_int(&mut bmc, b_step1, 2);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

// ================================================================
// Record EXCEPT: r' = [r EXCEPT !.a = 99]
// ================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_record_except_single_field() {
    let mut bmc = bmc_array(1);
    bmc.declare_record_var(
        "r",
        vec![
            ("a".to_string(), TlaSort::Int),
            ("b".to_string(), TlaSort::Int),
        ],
    )
    .unwrap();

    // Init: r.a = 1, r.b = 2
    let init_a = bmc
        .translate_init(&spanned(Expr::Eq(
            Box::new(spanned(Expr::RecordAccess(
                Box::new(ident("r")),
                RecordFieldName::new(sstr("a")),
            ))),
            Box::new(int(1)),
        )))
        .unwrap();
    bmc.assert(init_a);

    let init_b = bmc
        .translate_init(&spanned(Expr::Eq(
            Box::new(spanned(Expr::RecordAccess(
                Box::new(ident("r")),
                RecordFieldName::new(sstr("b")),
            ))),
            Box::new(int(2)),
        )))
        .unwrap();
    bmc.assert(init_b);

    // Next: r' = [r EXCEPT !.a = 99]
    let except_expr = spanned(Expr::Except(
        Box::new(ident("r")),
        vec![ExceptSpec {
            path: vec![ExceptPathElement::Field(RecordFieldName::new(sstr("a")))],
            value: Spanned::dummy(Expr::Int(BigInt::from(99))),
        }],
    ));
    let r_prime = spanned(Expr::Prime(Box::new(ident("r"))));
    let next = spanned(Expr::Eq(Box::new(r_prime), Box::new(except_expr)));

    bmc.current_step = 0;
    let next_term = bmc.translate_bool(&next).unwrap();
    bmc.assert(next_term);

    // Check: r'.a = 99 (overridden), r'.b = 2 (copied)
    let a_prime = bmc.get_record_field_at_step("r", "a", 1).unwrap();
    assert_term_eq_int(&mut bmc, a_prime, 99);
    let b_prime = bmc.get_record_field_at_step("r", "b", 1).unwrap();
    assert_term_eq_int(&mut bmc, b_prime, 2);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_record_except_wrong_value_unsat() {
    let mut bmc = bmc_array(1);
    bmc.declare_record_var(
        "r",
        vec![
            ("a".to_string(), TlaSort::Int),
            ("b".to_string(), TlaSort::Int),
        ],
    )
    .unwrap();

    // Init: r.a = 1, r.b = 2
    let init_a = bmc
        .translate_init(&spanned(Expr::Eq(
            Box::new(spanned(Expr::RecordAccess(
                Box::new(ident("r")),
                RecordFieldName::new(sstr("a")),
            ))),
            Box::new(int(1)),
        )))
        .unwrap();
    bmc.assert(init_a);

    let init_b = bmc
        .translate_init(&spanned(Expr::Eq(
            Box::new(spanned(Expr::RecordAccess(
                Box::new(ident("r")),
                RecordFieldName::new(sstr("b")),
            ))),
            Box::new(int(2)),
        )))
        .unwrap();
    bmc.assert(init_b);

    // Next: r' = [r EXCEPT !.a = 99]
    let except_expr = spanned(Expr::Except(
        Box::new(ident("r")),
        vec![ExceptSpec {
            path: vec![ExceptPathElement::Field(RecordFieldName::new(sstr("a")))],
            value: Spanned::dummy(Expr::Int(BigInt::from(99))),
        }],
    ));
    let r_prime = spanned(Expr::Prime(Box::new(ident("r"))));
    let next = spanned(Expr::Eq(Box::new(r_prime), Box::new(except_expr)));

    bmc.current_step = 0;
    let next_term = bmc.translate_bool(&next).unwrap();
    bmc.assert(next_term);

    // Contradiction: r'.b should be 2 (copied), but we claim it's 999
    let b_prime = bmc.get_record_field_at_step("r", "b", 1).unwrap();
    assert_term_eq_int(&mut bmc, b_prime, 999);

    assert!(matches!(bmc.check_sat(), SolveResult::Unsat(_)));
}

// ================================================================
// Record UNCHANGED
// ================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_record_unchanged() {
    let mut bmc = bmc_array(1);
    bmc.declare_record_var(
        "r",
        vec![
            ("a".to_string(), TlaSort::Int),
            ("b".to_string(), TlaSort::Int),
        ],
    )
    .unwrap();

    // Init: r.a = 5, r.b = 10
    let init_a = bmc
        .translate_init(&spanned(Expr::Eq(
            Box::new(spanned(Expr::RecordAccess(
                Box::new(ident("r")),
                RecordFieldName::new(sstr("a")),
            ))),
            Box::new(int(5)),
        )))
        .unwrap();
    bmc.assert(init_a);

    let init_b = bmc
        .translate_init(&spanned(Expr::Eq(
            Box::new(spanned(Expr::RecordAccess(
                Box::new(ident("r")),
                RecordFieldName::new(sstr("b")),
            ))),
            Box::new(int(10)),
        )))
        .unwrap();
    bmc.assert(init_b);

    // Next: UNCHANGED r
    bmc.current_step = 0;
    let unchanged = bmc
        .translate_bool(&spanned(Expr::Unchanged(Box::new(ident("r")))))
        .unwrap();
    bmc.assert(unchanged);

    // Check: r' values are preserved
    let a1 = bmc.get_record_field_at_step("r", "a", 1).unwrap();
    assert_term_eq_int(&mut bmc, a1, 5);
    let b1 = bmc.get_record_field_at_step("r", "b", 1).unwrap();
    assert_term_eq_int(&mut bmc, b1, 10);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

// ================================================================
// Tuple declaration
// ================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_declare_tuple_var_int_elements() {
    let mut bmc = bmc_array(2);
    bmc.declare_tuple_var("t", vec![TlaSort::Int, TlaSort::Int])
        .unwrap();
    assert!(bmc.tuple_vars.contains_key("t"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_declare_tuple_var_mixed_elements() {
    let mut bmc = bmc_array(1);
    bmc.declare_tuple_var("t", vec![TlaSort::Int, TlaSort::Bool, TlaSort::Int])
        .unwrap();
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_declare_tuple_var_rejects_compound_element() {
    let mut bmc = bmc_array(0);
    let result = bmc.declare_tuple_var(
        "t",
        vec![TlaSort::Set {
            element_sort: Box::new(TlaSort::Int),
        }],
    );
    assert!(result.is_err());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_declare_var_delegates_tuple_sort() {
    let mut bmc = bmc_array(1);
    bmc.declare_var(
        "t",
        TlaSort::Tuple {
            element_sorts: vec![TlaSort::Int, TlaSort::Bool],
        },
    )
    .unwrap();
    assert!(bmc.tuple_vars.contains_key("t"));
    assert!(!bmc.vars.contains_key("t"));
}

// ================================================================
// Tuple indexing
// ================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_tuple_index_int() {
    let mut bmc = bmc_array(0);
    bmc.declare_tuple_var("t", vec![TlaSort::Int, TlaSort::Int])
        .unwrap();

    // t[1] = 42
    let t1 = spanned(Expr::FuncApply(Box::new(ident("t")), Box::new(int(1))));
    let eq = spanned(Expr::Eq(Box::new(t1), Box::new(int(42))));
    let term = bmc.translate_init(&eq).unwrap();
    bmc.assert(term);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_tuple_index_contradicts_unsat() {
    let mut bmc = bmc_array(0);
    bmc.declare_tuple_var("t", vec![TlaSort::Int, TlaSort::Int])
        .unwrap();

    // t[1] = 10 AND t[1] = 20 -> UNSAT
    let t1 = spanned(Expr::FuncApply(Box::new(ident("t")), Box::new(int(1))));

    let eq1 = bmc
        .translate_init(&spanned(Expr::Eq(Box::new(t1.clone()), Box::new(int(10)))))
        .unwrap();
    bmc.assert(eq1);

    let eq2 = bmc
        .translate_init(&spanned(Expr::Eq(Box::new(t1), Box::new(int(20)))))
        .unwrap();
    bmc.assert(eq2);

    assert!(matches!(bmc.check_sat(), SolveResult::Unsat(_)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_tuple_different_indices_independent() {
    let mut bmc = bmc_array(0);
    bmc.declare_tuple_var("t", vec![TlaSort::Int, TlaSort::Int])
        .unwrap();

    // t[1] = 10 AND t[2] = 20 -> SAT (different elements)
    let t1 = spanned(Expr::FuncApply(Box::new(ident("t")), Box::new(int(1))));
    let t2 = spanned(Expr::FuncApply(Box::new(ident("t")), Box::new(int(2))));

    let eq1 = bmc
        .translate_init(&spanned(Expr::Eq(Box::new(t1), Box::new(int(10)))))
        .unwrap();
    bmc.assert(eq1);

    let eq2 = bmc
        .translate_init(&spanned(Expr::Eq(Box::new(t2), Box::new(int(20)))))
        .unwrap();
    bmc.assert(eq2);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

// ================================================================
// Tuple literal equality: t' = <<1, 2>>
// ================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_tuple_literal_eq() {
    let mut bmc = bmc_array(1);
    bmc.declare_tuple_var("t", vec![TlaSort::Int, TlaSort::Int])
        .unwrap();

    // t' = <<1, 2>>
    let tuple_literal = spanned(Expr::Tuple(vec![int(1), int(2)]));
    let t_prime = spanned(Expr::Prime(Box::new(ident("t"))));
    let eq = spanned(Expr::Eq(Box::new(t_prime), Box::new(tuple_literal)));

    bmc.current_step = 0;
    let term = bmc.translate_bool(&eq).unwrap();
    bmc.assert(term);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));

    // Verify t'[1] = 1 and t'[2] = 2
    let e1 = bmc.get_tuple_element_at_step("t", 1, 1).unwrap();
    assert_term_eq_int(&mut bmc, e1, 1);
    let e2 = bmc.get_tuple_element_at_step("t", 2, 1).unwrap();
    assert_term_eq_int(&mut bmc, e2, 2);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

// ================================================================
// Tuple UNCHANGED
// ================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_tuple_unchanged() {
    let mut bmc = bmc_array(1);
    bmc.declare_tuple_var("t", vec![TlaSort::Int, TlaSort::Int])
        .unwrap();

    // Init: t[1] = 5, t[2] = 10
    let eq1 = bmc
        .translate_init(&spanned(Expr::Eq(
            Box::new(spanned(Expr::FuncApply(
                Box::new(ident("t")),
                Box::new(int(1)),
            ))),
            Box::new(int(5)),
        )))
        .unwrap();
    bmc.assert(eq1);

    let eq2 = bmc
        .translate_init(&spanned(Expr::Eq(
            Box::new(spanned(Expr::FuncApply(
                Box::new(ident("t")),
                Box::new(int(2)),
            ))),
            Box::new(int(10)),
        )))
        .unwrap();
    bmc.assert(eq2);

    // UNCHANGED t
    bmc.current_step = 0;
    let unchanged = bmc
        .translate_bool(&spanned(Expr::Unchanged(Box::new(ident("t")))))
        .unwrap();
    bmc.assert(unchanged);

    // t'[1] must be 5, t'[2] must be 10
    let e1 = bmc.get_tuple_element_at_step("t", 1, 1).unwrap();
    assert_term_eq_int(&mut bmc, e1, 5);
    let e2 = bmc.get_tuple_element_at_step("t", 2, 1).unwrap();
    assert_term_eq_int(&mut bmc, e2, 10);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

// ================================================================
// Tuple index out of bounds
// ================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_tuple_index_out_of_bounds() {
    let mut bmc = bmc_array(0);
    bmc.declare_tuple_var("t", vec![TlaSort::Int, TlaSort::Int])
        .unwrap();

    // t[3] should fail (only 2 elements)
    let result = bmc.get_tuple_element_at_step("t", 3, 0);
    assert!(result.is_err());

    // t[0] should also fail (1-indexed)
    let result = bmc.get_tuple_element_at_step("t", 0, 0);
    assert!(result.is_err());
}

// ================================================================
// Record field not found
// ================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_record_field_not_found() {
    let mut bmc = bmc_array(0);
    bmc.declare_record_var("r", vec![("a".to_string(), TlaSort::Int)])
        .unwrap();

    // r.nonexistent should fail
    let result = bmc.get_record_field_at_step("r", "nonexistent", 0);
    assert!(result.is_err());
}

// ================================================================
// Primed record field access: r'.a
// ================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_record_primed_field_access() {
    let mut bmc = bmc_array(1);
    bmc.declare_record_var("r", vec![("a".to_string(), TlaSort::Int)])
        .unwrap();

    // r'.a = 42  (access field on primed record variable)
    let r_prime_a = spanned(Expr::RecordAccess(
        Box::new(spanned(Expr::Prime(Box::new(ident("r"))))),
        RecordFieldName::new(sstr("a")),
    ));
    let eq = spanned(Expr::Eq(Box::new(r_prime_a), Box::new(int(42))));

    bmc.current_step = 0;
    let term = bmc.translate_bool(&eq).unwrap();
    bmc.assert(term);

    // Verify: r__f_a__1 should be 42
    let a1 = bmc.get_record_field_at_step("r", "a", 1).unwrap();
    assert_term_eq_int(&mut bmc, a1, 42);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

// ================================================================
// Primed tuple indexing: t'[1]
// ================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_tuple_primed_index() {
    let mut bmc = bmc_array(1);
    bmc.declare_tuple_var("t", vec![TlaSort::Int]).unwrap();

    // t'[1] = 7  (index on primed tuple variable)
    let t_prime_1 = spanned(Expr::FuncApply(
        Box::new(spanned(Expr::Prime(Box::new(ident("t"))))),
        Box::new(int(1)),
    ));
    let eq = spanned(Expr::Eq(Box::new(t_prime_1), Box::new(int(7))));

    bmc.current_step = 0;
    let term = bmc.translate_bool(&eq).unwrap();
    bmc.assert(term);

    // Verify: t__e_1__1 should be 7
    let e1_1 = bmc.get_tuple_element_at_step("t", 1, 1).unwrap();
    assert_term_eq_int(&mut bmc, e1_1, 7);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}
