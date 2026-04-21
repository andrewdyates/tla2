// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for BMC sequence encoding via SMT arrays.
//!
//! Part of #3793: Validates sequence declaration, Len, Head, Tail,
//! Append, indexing, UNCHANGED, and sequence equality operations
//! in the BMC translator.

use super::*;
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

// --- declare_seq_var ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_declare_seq_var_int() {
    let mut bmc = bmc_array(2);
    bmc.declare_seq_var("s", TlaSort::Int, 5).unwrap();
    assert!(bmc.seq_vars.contains_key("s"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_declare_seq_var_bool() {
    let mut bmc = bmc_array(1);
    bmc.declare_seq_var("s", TlaSort::Bool, 3).unwrap();
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_declare_seq_var_rejects_compound_element() {
    let mut bmc = bmc_array(0);
    let result = bmc.declare_seq_var(
        "s",
        TlaSort::Set {
            element_sort: Box::new(TlaSort::Int),
        },
        5,
    );
    assert!(result.is_err());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_declare_var_delegates_sequence_sort() {
    let mut bmc = bmc_array(1);
    bmc.declare_var(
        "s",
        TlaSort::Sequence {
            element_sort: Box::new(TlaSort::Int),
            max_len: 4,
        },
    )
    .unwrap();
    // The sequence should be in seq_vars, not vars
    assert!(bmc.seq_vars.contains_key("s"));
    assert!(!bmc.vars.contains_key("s"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_declare_seq_var_idempotent() {
    let mut bmc = bmc_array(1);
    bmc.declare_seq_var("s", TlaSort::Int, 5).unwrap();
    // Second declaration should be a no-op
    bmc.declare_seq_var("s", TlaSort::Int, 5).unwrap();
}

// --- Len ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_seq_len_constrained() {
    let mut bmc = bmc_array(0);
    bmc.declare_seq_var("s", TlaSort::Int, 5).unwrap();

    // Assert Len(s) = 3
    let len_expr = spanned(Expr::Apply(Box::new(ident("Len")), vec![ident("s")]));
    let eq = bmc
        .translate_init(&spanned(Expr::Eq(Box::new(len_expr), Box::new(int(3)))))
        .unwrap();
    bmc.assert(eq);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_seq_len_exceeds_max_unsat() {
    let mut bmc = bmc_array(0);
    bmc.declare_seq_var("s", TlaSort::Int, 3).unwrap();

    // Assert Len(s) = 5 with max_len = 3 -> UNSAT
    let len_expr = spanned(Expr::Apply(Box::new(ident("Len")), vec![ident("s")]));
    let eq = bmc
        .translate_init(&spanned(Expr::Eq(Box::new(len_expr), Box::new(int(5)))))
        .unwrap();
    bmc.assert(eq);

    assert!(matches!(bmc.check_sat(), SolveResult::Unsat(_)));
}

// --- Head ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_seq_head_sat() {
    let mut bmc = bmc_array(0);
    bmc.declare_seq_var("s", TlaSort::Int, 5).unwrap();

    // Assert Len(s) >= 1 (so Head is defined)
    let len_expr = spanned(Expr::Apply(Box::new(ident("Len")), vec![ident("s")]));
    let len_ge_1 = bmc
        .translate_init(&spanned(Expr::Geq(Box::new(len_expr), Box::new(int(1)))))
        .unwrap();
    bmc.assert(len_ge_1);

    // Assert Head(s) = 42
    let head_expr = spanned(Expr::Apply(Box::new(ident("Head")), vec![ident("s")]));
    let eq = bmc
        .translate_init(&spanned(Expr::Eq(Box::new(head_expr), Box::new(int(42)))))
        .unwrap();
    bmc.assert(eq);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_seq_head_contradicts_unsat() {
    let mut bmc = bmc_array(0);
    bmc.declare_seq_var("s", TlaSort::Int, 5).unwrap();

    // Assert Head(s) = 10 AND Head(s) = 20 -> UNSAT
    let head = || spanned(Expr::Apply(Box::new(ident("Head")), vec![ident("s")]));
    let eq1 = bmc
        .translate_init(&spanned(Expr::Eq(Box::new(head()), Box::new(int(10)))))
        .unwrap();
    bmc.assert(eq1);

    let eq2 = bmc
        .translate_init(&spanned(Expr::Eq(Box::new(head()), Box::new(int(20)))))
        .unwrap();
    bmc.assert(eq2);

    assert!(matches!(bmc.check_sat(), SolveResult::Unsat(_)));
}

// --- Sequence indexing: s[i] ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_seq_indexing_sat() {
    let mut bmc = bmc_array(0);
    bmc.declare_seq_var("s", TlaSort::Int, 5).unwrap();

    // s[1] = 10 AND s[2] = 20 -> SAT (different indices)
    let s1 = spanned(Expr::FuncApply(Box::new(ident("s")), Box::new(int(1))));
    let s2 = spanned(Expr::FuncApply(Box::new(ident("s")), Box::new(int(2))));

    let eq1 = bmc
        .translate_init(&spanned(Expr::Eq(Box::new(s1), Box::new(int(10)))))
        .unwrap();
    bmc.assert(eq1);

    let eq2 = bmc
        .translate_init(&spanned(Expr::Eq(Box::new(s2), Box::new(int(20)))))
        .unwrap();
    bmc.assert(eq2);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_seq_indexing_same_index_unsat() {
    let mut bmc = bmc_array(0);
    bmc.declare_seq_var("s", TlaSort::Int, 5).unwrap();

    // s[1] = 10 AND s[1] = 20 -> UNSAT
    let s1_a = spanned(Expr::FuncApply(Box::new(ident("s")), Box::new(int(1))));
    let s1_b = spanned(Expr::FuncApply(Box::new(ident("s")), Box::new(int(1))));

    let eq1 = bmc
        .translate_init(&spanned(Expr::Eq(Box::new(s1_a), Box::new(int(10)))))
        .unwrap();
    bmc.assert(eq1);

    let eq2 = bmc
        .translate_init(&spanned(Expr::Eq(Box::new(s1_b), Box::new(int(20)))))
        .unwrap();
    bmc.assert(eq2);

    assert!(matches!(bmc.check_sat(), SolveResult::Unsat(_)));
}

// --- Sequence literal equality: s = <<e1, e2, ...>> ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_seq_literal_eq_sat() {
    let mut bmc = bmc_array(0);
    bmc.declare_seq_var("s", TlaSort::Int, 5).unwrap();

    // s = <<10, 20, 30>>
    let tuple = spanned(Expr::Tuple(vec![int(10), int(20), int(30)]));
    let eq = bmc
        .translate_init(&spanned(Expr::Eq(Box::new(ident("s")), Box::new(tuple))))
        .unwrap();
    bmc.assert(eq);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));

    // Verify: Len(s) should be 3 in the model
    let len = bmc.get_seq_length_at_step("s", 0).unwrap();
    let three = bmc.solver.int_const(3);
    let len_check = bmc.solver.try_eq(len, three).unwrap();
    bmc.assert(len_check);
    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_seq_literal_eq_head_matches() {
    let mut bmc = bmc_array(0);
    bmc.declare_seq_var("s", TlaSort::Int, 5).unwrap();

    // s = <<10, 20, 30>>
    let tuple = spanned(Expr::Tuple(vec![int(10), int(20), int(30)]));
    let eq = bmc
        .translate_init(&spanned(Expr::Eq(Box::new(ident("s")), Box::new(tuple))))
        .unwrap();
    bmc.assert(eq);

    // Head(s) = 10 should be SAT
    let head_expr = spanned(Expr::Apply(Box::new(ident("Head")), vec![ident("s")]));
    let head_eq = bmc
        .translate_init(&spanned(Expr::Eq(Box::new(head_expr), Box::new(int(10)))))
        .unwrap();
    bmc.assert(head_eq);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_seq_literal_eq_wrong_head_unsat() {
    let mut bmc = bmc_array(0);
    bmc.declare_seq_var("s", TlaSort::Int, 5).unwrap();

    // s = <<10, 20>>
    let tuple = spanned(Expr::Tuple(vec![int(10), int(20)]));
    let eq = bmc
        .translate_init(&spanned(Expr::Eq(Box::new(ident("s")), Box::new(tuple))))
        .unwrap();
    bmc.assert(eq);

    // Head(s) = 99 should be UNSAT (Head is 10)
    let head_expr = spanned(Expr::Apply(Box::new(ident("Head")), vec![ident("s")]));
    let head_eq = bmc
        .translate_init(&spanned(Expr::Eq(Box::new(head_expr), Box::new(int(99)))))
        .unwrap();
    bmc.assert(head_eq);

    assert!(matches!(bmc.check_sat(), SolveResult::Unsat(_)));
}

// --- Append ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_seq_append_step() {
    let mut bmc = bmc_array(1);
    bmc.declare_seq_var("s", TlaSort::Int, 5).unwrap();

    // Step 0: s = <<10>>
    let init_tuple = spanned(Expr::Tuple(vec![int(10)]));
    let init = bmc
        .translate_init(&spanned(Expr::Eq(
            Box::new(ident("s")),
            Box::new(init_tuple),
        )))
        .unwrap();
    bmc.assert(init);

    // Step 0->1: s' = Append(s, 20)
    bmc.current_step = 0;
    let primed_s = spanned(Expr::Prime(Box::new(ident("s"))));
    let append_expr = spanned(Expr::Apply(
        Box::new(ident("Append")),
        vec![ident("s"), int(20)],
    ));
    let next = bmc
        .translate_bool(&spanned(Expr::Eq(
            Box::new(primed_s),
            Box::new(append_expr),
        )))
        .unwrap();
    bmc.assert(next);

    // Verify: at step 1, Len(s) should be 2
    let len1 = bmc.get_seq_length_at_step("s", 1).unwrap();
    let two = bmc.solver.int_const(2);
    let len_check = bmc.solver.try_eq(len1, two).unwrap();
    bmc.assert(len_check);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));

    // Verify: at step 1, s[2] = 20
    let arr1 = bmc.get_seq_array_at_step("s", 1).unwrap();
    let two_idx = bmc.solver.int_const(2);
    let twenty = bmc.solver.int_const(20);
    let sel = bmc.solver.try_select(arr1, two_idx).unwrap();
    let sel_eq = bmc.solver.try_eq(sel, twenty).unwrap();
    bmc.assert(sel_eq);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

// --- Tail ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_seq_tail_step() {
    let mut bmc = bmc_array(1);
    bmc.declare_seq_var("s", TlaSort::Int, 5).unwrap();

    // Step 0: s = <<10, 20, 30>>
    let init_tuple = spanned(Expr::Tuple(vec![int(10), int(20), int(30)]));
    let init = bmc
        .translate_init(&spanned(Expr::Eq(
            Box::new(ident("s")),
            Box::new(init_tuple),
        )))
        .unwrap();
    bmc.assert(init);

    // Step 0->1: s' = Tail(s)
    bmc.current_step = 0;
    let primed_s = spanned(Expr::Prime(Box::new(ident("s"))));
    let tail_expr = spanned(Expr::Apply(Box::new(ident("Tail")), vec![ident("s")]));
    let next = bmc
        .translate_bool(&spanned(Expr::Eq(Box::new(primed_s), Box::new(tail_expr))))
        .unwrap();
    bmc.assert(next);

    // Verify: at step 1, Len(s) should be 2
    let len1 = bmc.get_seq_length_at_step("s", 1).unwrap();
    let two = bmc.solver.int_const(2);
    let len_check = bmc.solver.try_eq(len1, two).unwrap();
    bmc.assert(len_check);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));

    // Verify: at step 1, s[1] should be 20 (shifted from s[2] at step 0)
    let arr1 = bmc.get_seq_array_at_step("s", 1).unwrap();
    let one = bmc.solver.int_const(1);
    let twenty = bmc.solver.int_const(20);
    let sel = bmc.solver.try_select(arr1, one).unwrap();
    let sel_eq = bmc.solver.try_eq(sel, twenty).unwrap();
    bmc.assert(sel_eq);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

// --- UNCHANGED ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_seq_unchanged() {
    let mut bmc = bmc_array(1);
    bmc.declare_seq_var("s", TlaSort::Int, 5).unwrap();

    // Step 0: s = <<10, 20>>
    let init_tuple = spanned(Expr::Tuple(vec![int(10), int(20)]));
    let init = bmc
        .translate_init(&spanned(Expr::Eq(
            Box::new(ident("s")),
            Box::new(init_tuple),
        )))
        .unwrap();
    bmc.assert(init);

    // Step 0->1: UNCHANGED s
    bmc.current_step = 0;
    let unchanged = bmc
        .translate_bool(&spanned(Expr::Unchanged(Box::new(ident("s")))))
        .unwrap();
    bmc.assert(unchanged);

    // Verify: at step 1, s[1] = 10 and Len(s) = 2
    let arr1 = bmc.get_seq_array_at_step("s", 1).unwrap();
    let one = bmc.solver.int_const(1);
    let ten = bmc.solver.int_const(10);
    let sel = bmc.solver.try_select(arr1, one).unwrap();
    let sel_eq = bmc.solver.try_eq(sel, ten).unwrap();
    bmc.assert(sel_eq);

    let len1 = bmc.get_seq_length_at_step("s", 1).unwrap();
    let two = bmc.solver.int_const(2);
    let len_eq = bmc.solver.try_eq(len1, two).unwrap();
    bmc.assert(len_eq);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

// --- Sequence variable across steps ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_seq_var_across_steps() {
    let mut bmc = bmc_array(1);
    bmc.declare_seq_var("s", TlaSort::Int, 3).unwrap();

    // At step 0: Len(s) = 1
    let len0 = bmc.get_seq_length_at_step("s", 0).unwrap();
    let one = bmc.solver.int_const(1);
    let eq0 = bmc.solver.try_eq(len0, one).unwrap();
    bmc.assert(eq0);

    // At step 1: Len(s) = 2 (independent value)
    let len1 = bmc.get_seq_length_at_step("s", 1).unwrap();
    let two = bmc.solver.int_const(2);
    let eq1 = bmc.solver.try_eq(len1, two).unwrap();
    bmc.assert(eq1);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

// --- BmcValue::Sequence ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_value_sequence_debug() {
    let val = BmcValue::Sequence(vec![BmcValue::Int(1), BmcValue::Int(2)]);
    let debug = format!("{val:?}");
    assert!(debug.contains("Sequence"));
    assert!(debug.contains("Int(1)"));
    assert!(debug.contains("Int(2)"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_value_sequence_equality() {
    let a = BmcValue::Sequence(vec![BmcValue::Int(1), BmcValue::Int(2)]);
    let b = BmcValue::Sequence(vec![BmcValue::Int(1), BmcValue::Int(2)]);
    let c = BmcValue::Sequence(vec![BmcValue::Int(1), BmcValue::Int(3)]);
    assert_eq!(a, b);
    assert_ne!(a, c);
}

// --- assert_concrete_state with Sequence ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_assert_concrete_seq_state() {
    let mut bmc = bmc_array(0);
    bmc.declare_seq_var("s", TlaSort::Int, 5).unwrap();

    // Assert concrete state: s = <<10, 20>>
    bmc.assert_concrete_state(
        &[(
            "s".to_string(),
            BmcValue::Sequence(vec![BmcValue::Int(10), BmcValue::Int(20)]),
        )],
        0,
    )
    .unwrap();

    // Verify: s[1] = 10
    let arr = bmc.get_seq_array_at_step("s", 0).unwrap();
    let one = bmc.solver.int_const(1);
    let ten = bmc.solver.int_const(10);
    let sel = bmc.solver.try_select(arr, one).unwrap();
    let eq = bmc.solver.try_eq(sel, ten).unwrap();
    bmc.assert(eq);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));

    // Verify: Len(s) = 2
    let len = bmc.get_seq_length_at_step("s", 0).unwrap();
    let two = bmc.solver.int_const(2);
    let len_eq = bmc.solver.try_eq(len, two).unwrap();
    bmc.assert(len_eq);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_assert_concrete_seq_wrong_value_unsat() {
    let mut bmc = bmc_array(0);
    bmc.declare_seq_var("s", TlaSort::Int, 5).unwrap();

    // Assert concrete state: s = <<10, 20>>
    bmc.assert_concrete_state(
        &[(
            "s".to_string(),
            BmcValue::Sequence(vec![BmcValue::Int(10), BmcValue::Int(20)]),
        )],
        0,
    )
    .unwrap();

    // Assert s[1] = 99 -> UNSAT (already constrained to 10)
    let arr = bmc.get_seq_array_at_step("s", 0).unwrap();
    let one = bmc.solver.int_const(1);
    let ninety_nine = bmc.solver.int_const(99);
    let sel = bmc.solver.try_select(arr, one).unwrap();
    let eq = bmc.solver.try_eq(sel, ninety_nine).unwrap();
    bmc.assert(eq);

    assert!(matches!(bmc.check_sat(), SolveResult::Unsat(_)));
}

// --- SubSeq ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_seq_subseq_step() {
    let mut bmc = bmc_array(1);
    bmc.declare_seq_var("s", TlaSort::Int, 5).unwrap();
    bmc.declare_seq_var("t", TlaSort::Int, 5).unwrap();

    // Step 0: s = <<10, 20, 30, 40>>
    let init_tuple = spanned(Expr::Tuple(vec![int(10), int(20), int(30), int(40)]));
    let init = bmc
        .translate_init(&spanned(Expr::Eq(
            Box::new(ident("s")),
            Box::new(init_tuple),
        )))
        .unwrap();
    bmc.assert(init);

    // Step 0->1: t' = SubSeq(s, 2, 3) -> should be <<20, 30>>
    bmc.current_step = 0;
    let primed_t = spanned(Expr::Prime(Box::new(ident("t"))));
    let subseq_expr = spanned(Expr::Apply(
        Box::new(ident("SubSeq")),
        vec![ident("s"), int(2), int(3)],
    ));
    let next = bmc
        .translate_bool(&spanned(Expr::Eq(
            Box::new(primed_t),
            Box::new(subseq_expr),
        )))
        .unwrap();
    bmc.assert(next);

    // Verify: at step 1, Len(t) should be 2
    let len1 = bmc.get_seq_length_at_step("t", 1).unwrap();
    let two = bmc.solver.int_const(2);
    let len_check = bmc.solver.try_eq(len1, two).unwrap();
    bmc.assert(len_check);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));

    // Verify: at step 1, t[1] = 20 (s[2])
    let arr1 = bmc.get_seq_array_at_step("t", 1).unwrap();
    let one = bmc.solver.int_const(1);
    let twenty = bmc.solver.int_const(20);
    let sel = bmc.solver.try_select(arr1, one).unwrap();
    let sel_eq = bmc.solver.try_eq(sel, twenty).unwrap();
    bmc.assert(sel_eq);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));

    // Verify: at step 1, t[2] = 30 (s[3])
    let two_idx = bmc.solver.int_const(2);
    let thirty = bmc.solver.int_const(30);
    let sel2 = bmc.solver.try_select(arr1, two_idx).unwrap();
    let sel2_eq = bmc.solver.try_eq(sel2, thirty).unwrap();
    bmc.assert(sel2_eq);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_seq_subseq_single_element() {
    let mut bmc = bmc_array(1);
    bmc.declare_seq_var("s", TlaSort::Int, 5).unwrap();
    bmc.declare_seq_var("t", TlaSort::Int, 5).unwrap();

    // Step 0: s = <<10, 20, 30>>
    let init_tuple = spanned(Expr::Tuple(vec![int(10), int(20), int(30)]));
    let init = bmc
        .translate_init(&spanned(Expr::Eq(
            Box::new(ident("s")),
            Box::new(init_tuple),
        )))
        .unwrap();
    bmc.assert(init);

    // Step 0->1: t' = SubSeq(s, 2, 2) -> should be <<20>>
    bmc.current_step = 0;
    let primed_t = spanned(Expr::Prime(Box::new(ident("t"))));
    let subseq_expr = spanned(Expr::Apply(
        Box::new(ident("SubSeq")),
        vec![ident("s"), int(2), int(2)],
    ));
    let next = bmc
        .translate_bool(&spanned(Expr::Eq(
            Box::new(primed_t),
            Box::new(subseq_expr),
        )))
        .unwrap();
    bmc.assert(next);

    // Verify: at step 1, Len(t) should be 1
    let len1 = bmc.get_seq_length_at_step("t", 1).unwrap();
    let one = bmc.solver.int_const(1);
    let len_check = bmc.solver.try_eq(len1, one).unwrap();
    bmc.assert(len_check);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));

    // Verify: at step 1, t[1] = 20
    let arr1 = bmc.get_seq_array_at_step("t", 1).unwrap();
    let twenty = bmc.solver.int_const(20);
    let sel = bmc.solver.try_select(arr1, one).unwrap();
    let sel_eq = bmc.solver.try_eq(sel, twenty).unwrap();
    bmc.assert(sel_eq);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_seq_subseq_wrong_element_unsat() {
    let mut bmc = bmc_array(1);
    bmc.declare_seq_var("s", TlaSort::Int, 5).unwrap();
    bmc.declare_seq_var("t", TlaSort::Int, 5).unwrap();

    // Step 0: s = <<10, 20, 30>>
    let init_tuple = spanned(Expr::Tuple(vec![int(10), int(20), int(30)]));
    let init = bmc
        .translate_init(&spanned(Expr::Eq(
            Box::new(ident("s")),
            Box::new(init_tuple),
        )))
        .unwrap();
    bmc.assert(init);

    // Step 0->1: t' = SubSeq(s, 2, 3)
    bmc.current_step = 0;
    let primed_t = spanned(Expr::Prime(Box::new(ident("t"))));
    let subseq_expr = spanned(Expr::Apply(
        Box::new(ident("SubSeq")),
        vec![ident("s"), int(2), int(3)],
    ));
    let next = bmc
        .translate_bool(&spanned(Expr::Eq(
            Box::new(primed_t),
            Box::new(subseq_expr),
        )))
        .unwrap();
    bmc.assert(next);

    // Assert t[1] = 99 at step 1 (should be 20) -> UNSAT
    let arr1 = bmc.get_seq_array_at_step("t", 1).unwrap();
    let one = bmc.solver.int_const(1);
    let ninety_nine = bmc.solver.int_const(99);
    let sel = bmc.solver.try_select(arr1, one).unwrap();
    let sel_eq = bmc.solver.try_eq(sel, ninety_nine).unwrap();
    bmc.assert(sel_eq);

    assert!(matches!(bmc.check_sat(), SolveResult::Unsat(_)));
}

// --- Concatenation: s \o t ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_seq_concat_step() {
    let mut bmc = bmc_array(1);
    bmc.declare_seq_var("s", TlaSort::Int, 5).unwrap();
    bmc.declare_seq_var("t", TlaSort::Int, 5).unwrap();
    bmc.declare_seq_var("r", TlaSort::Int, 10).unwrap();

    // Step 0: s = <<10, 20>>, t = <<30, 40>>
    let s_init = spanned(Expr::Tuple(vec![int(10), int(20)]));
    let t_init = spanned(Expr::Tuple(vec![int(30), int(40)]));
    let s_eq = bmc
        .translate_init(&spanned(Expr::Eq(Box::new(ident("s")), Box::new(s_init))))
        .unwrap();
    bmc.assert(s_eq);
    let t_eq = bmc
        .translate_init(&spanned(Expr::Eq(Box::new(ident("t")), Box::new(t_init))))
        .unwrap();
    bmc.assert(t_eq);

    // Step 0->1: r' = s \o t -> should be <<10, 20, 30, 40>>
    bmc.current_step = 0;
    let primed_r = spanned(Expr::Prime(Box::new(ident("r"))));
    let concat_expr = spanned(Expr::Apply(
        Box::new(ident("\\o")),
        vec![ident("s"), ident("t")],
    ));
    let next = bmc
        .translate_bool(&spanned(Expr::Eq(
            Box::new(primed_r),
            Box::new(concat_expr),
        )))
        .unwrap();
    bmc.assert(next);

    // Verify: at step 1, Len(r) should be 4
    let len1 = bmc.get_seq_length_at_step("r", 1).unwrap();
    let four = bmc.solver.int_const(4);
    let len_check = bmc.solver.try_eq(len1, four).unwrap();
    bmc.assert(len_check);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));

    // Verify: at step 1, r[1] = 10, r[2] = 20, r[3] = 30, r[4] = 40
    let arr1 = bmc.get_seq_array_at_step("r", 1).unwrap();
    for (idx, expected) in [(1, 10), (2, 20), (3, 30), (4, 40)] {
        let i = bmc.solver.int_const(idx);
        let val = bmc.solver.int_const(expected);
        let sel = bmc.solver.try_select(arr1, i).unwrap();
        let sel_eq = bmc.solver.try_eq(sel, val).unwrap();
        bmc.assert(sel_eq);
    }

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_seq_concat_empty_left() {
    let mut bmc = bmc_array(1);
    bmc.declare_seq_var("s", TlaSort::Int, 5).unwrap();
    bmc.declare_seq_var("t", TlaSort::Int, 5).unwrap();
    bmc.declare_seq_var("r", TlaSort::Int, 10).unwrap();

    // Step 0: s = <<>>, t = <<10, 20>>
    let s_init = spanned(Expr::Tuple(vec![]));
    let t_init = spanned(Expr::Tuple(vec![int(10), int(20)]));
    let s_eq = bmc
        .translate_init(&spanned(Expr::Eq(Box::new(ident("s")), Box::new(s_init))))
        .unwrap();
    bmc.assert(s_eq);
    let t_eq = bmc
        .translate_init(&spanned(Expr::Eq(Box::new(ident("t")), Box::new(t_init))))
        .unwrap();
    bmc.assert(t_eq);

    // Step 0->1: r' = s \o t -> should be <<10, 20>>
    bmc.current_step = 0;
    let primed_r = spanned(Expr::Prime(Box::new(ident("r"))));
    let concat_expr = spanned(Expr::Apply(
        Box::new(ident("\\o")),
        vec![ident("s"), ident("t")],
    ));
    let next = bmc
        .translate_bool(&spanned(Expr::Eq(
            Box::new(primed_r),
            Box::new(concat_expr),
        )))
        .unwrap();
    bmc.assert(next);

    // Verify: at step 1, Len(r) should be 2
    let len1 = bmc.get_seq_length_at_step("r", 1).unwrap();
    let two = bmc.solver.int_const(2);
    let len_check = bmc.solver.try_eq(len1, two).unwrap();
    bmc.assert(len_check);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));

    // Verify: r[1] = 10 (from t)
    let arr1 = bmc.get_seq_array_at_step("r", 1).unwrap();
    let one = bmc.solver.int_const(1);
    let ten = bmc.solver.int_const(10);
    let sel = bmc.solver.try_select(arr1, one).unwrap();
    let sel_eq = bmc.solver.try_eq(sel, ten).unwrap();
    bmc.assert(sel_eq);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_seq_concat_wrong_length_unsat() {
    let mut bmc = bmc_array(1);
    bmc.declare_seq_var("s", TlaSort::Int, 5).unwrap();
    bmc.declare_seq_var("t", TlaSort::Int, 5).unwrap();
    bmc.declare_seq_var("r", TlaSort::Int, 10).unwrap();

    // Step 0: s = <<10>>, t = <<20, 30>>
    let s_init = spanned(Expr::Tuple(vec![int(10)]));
    let t_init = spanned(Expr::Tuple(vec![int(20), int(30)]));
    let s_eq = bmc
        .translate_init(&spanned(Expr::Eq(Box::new(ident("s")), Box::new(s_init))))
        .unwrap();
    bmc.assert(s_eq);
    let t_eq = bmc
        .translate_init(&spanned(Expr::Eq(Box::new(ident("t")), Box::new(t_init))))
        .unwrap();
    bmc.assert(t_eq);

    // Step 0->1: r' = s \o t
    bmc.current_step = 0;
    let primed_r = spanned(Expr::Prime(Box::new(ident("r"))));
    let concat_expr = spanned(Expr::Apply(
        Box::new(ident("\\o")),
        vec![ident("s"), ident("t")],
    ));
    let next = bmc
        .translate_bool(&spanned(Expr::Eq(
            Box::new(primed_r),
            Box::new(concat_expr),
        )))
        .unwrap();
    bmc.assert(next);

    // Assert Len(r) = 5 at step 1 (should be 3) -> UNSAT
    let len1 = bmc.get_seq_length_at_step("r", 1).unwrap();
    let five = bmc.solver.int_const(5);
    let len_check = bmc.solver.try_eq(len1, five).unwrap();
    bmc.assert(len_check);

    assert!(matches!(bmc.check_sat(), SolveResult::Unsat(_)));
}
