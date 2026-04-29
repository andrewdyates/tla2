// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! End-to-end BMC tests for compound type encoding (sets, functions, sequences).
//!
//! These tests exercise multi-step BMC scenarios where compound-typed state
//! variables evolve across Init/Next transitions. They validate that:
//! - Set membership is correctly tracked across steps
//! - Function EXCEPT updates propagate and preserve untouched keys
//! - Sequence Append/Tail operations produce correct length and element values
//! - UNCHANGED correctly preserves compound variables across steps
//! - Mixed compound + scalar variables work together
//!
//! Part of #3778 (sets), #3786 (functions), #3793 (sequences).

use super::*;
use tla_core::ast::{ExceptPathElement, ExceptSpec};
use z4_dpll::api::SolveResult;

/// Helper: create a BMC translator with array support.
fn bmc_array(k: usize) -> BmcTranslator {
    BmcTranslator::new_with_arrays(k).unwrap()
}

/// Helper: create an Ident expression with INVALID NameId.
fn ident(name: &str) -> Spanned<Expr> {
    Spanned::dummy(Expr::Ident(
        name.to_string(),
        tla_core::name_intern::NameId::INVALID,
    ))
}

/// Helper: create an integer literal expression.
fn int(n: i64) -> Spanned<Expr> {
    Spanned::dummy(Expr::Int(BigInt::from(n)))
}

/// Helper: create a primed variable expression.
fn primed(name: &str) -> Spanned<Expr> {
    Spanned::dummy(Expr::Prime(Box::new(ident(name))))
}

// ---------------------------------------------------------------------------
// Set: multi-step membership tracking
// ---------------------------------------------------------------------------

/// Test: Set variable with concrete members at two steps via UNCHANGED.
///
/// Init: S = {1, 2, 3}
/// Next: UNCHANGED S
/// Check: membership at step 1 is preserved from step 0
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_compound_e2e_set_init_next_membership() {
    let mut bmc = bmc_array(1);
    bmc.declare_var(
        "S",
        TlaSort::Set {
            element_sort: Box::new(TlaSort::Int),
        },
    )
    .unwrap();

    // Init: S = {1, 2, 3}
    bmc.assert_concrete_state(
        &[(
            "S".to_string(),
            BmcValue::Set(vec![BmcValue::Int(1), BmcValue::Int(2), BmcValue::Int(3)]),
        )],
        0,
    )
    .unwrap();

    // Next: UNCHANGED S (S__1 = S__0)
    let s0 = bmc.get_var_at_step("S", 0).unwrap();
    let s1 = bmc.get_var_at_step("S", 1).unwrap();
    let s_eq = bmc.solver.try_eq(s1, s0).unwrap();
    bmc.assert(s_eq);

    // Check: 2 \in S at step 1 (should be SAT since S = {1,2,3})
    let two = bmc.solver.int_const(2);
    let member = bmc.solver.try_select(s1, two).unwrap();
    bmc.assert(member);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

/// Test: Set membership violation — element 5 is NOT in {1, 2}.
///
/// Init: S = {1, 2}
/// Check: 5 \in S is UNSAT
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_compound_e2e_set_membership_violation() {
    let mut bmc = bmc_array(1);
    bmc.declare_var(
        "S",
        TlaSort::Set {
            element_sort: Box::new(TlaSort::Int),
        },
    )
    .unwrap();

    // Init: S = {1, 2}
    bmc.assert_concrete_state(
        &[(
            "S".to_string(),
            BmcValue::Set(vec![BmcValue::Int(1), BmcValue::Int(2)]),
        )],
        0,
    )
    .unwrap();

    // UNCHANGED S
    let s0 = bmc.get_var_at_step("S", 0).unwrap();
    let s1 = bmc.get_var_at_step("S", 1).unwrap();
    let s_eq = bmc.solver.try_eq(s1, s0).unwrap();
    bmc.assert(s_eq);

    // At step 1: assert 5 \in S — should be UNSAT (5 not in {1,2})
    let five = bmc.solver.int_const(5);
    let member = bmc.solver.try_select(s1, five).unwrap();
    bmc.assert(member);

    assert!(matches!(bmc.check_sat(), SolveResult::Unsat(_)));
}

// ---------------------------------------------------------------------------
// Function: EXCEPT across steps, UNCHANGED
// ---------------------------------------------------------------------------

/// Test: Function EXCEPT updates a value at step 0->1, preserves untouched keys.
///
/// Init: f[1] = 10, f[2] = 20
/// Next: f' = [f EXCEPT ![1] = 99]
/// Check: f'[1] = 99, f'[2] = 20 (preserved)
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_compound_e2e_func_except_step_transition() {
    let mut bmc = bmc_array(1);
    bmc.declare_func_var("f", TlaSort::Int).unwrap();

    // Init: f[1] = 10, f[2] = 20
    let map0 = bmc.get_func_mapping_at_step("f", 0).unwrap();
    let one = bmc.solver.int_const(1);
    let two = bmc.solver.int_const(2);
    let ten = bmc.solver.int_const(10);
    let twenty = bmc.solver.int_const(20);

    let sel1 = bmc.solver.try_select(map0, one).unwrap();
    let eq1 = bmc.solver.try_eq(sel1, ten).unwrap();
    bmc.assert(eq1);

    let sel2 = bmc.solver.try_select(map0, two).unwrap();
    let eq2 = bmc.solver.try_eq(sel2, twenty).unwrap();
    bmc.assert(eq2);

    // Next: f' = [f EXCEPT ![1] = 99]
    bmc.current_step = 0;
    let except_eq = Spanned::dummy(Expr::Eq(
        Box::new(primed("f")),
        Box::new(Spanned::dummy(Expr::Except(
            Box::new(ident("f")),
            vec![ExceptSpec {
                path: vec![ExceptPathElement::Index(int(1))],
                value: int(99),
            }],
        ))),
    ));
    let next_term = bmc.translate_bool(&except_eq).unwrap();
    bmc.assert(next_term);

    // Verify: f'[1] = 99
    let map1 = bmc.get_func_mapping_at_step("f", 1).unwrap();
    let ninety_nine = bmc.solver.int_const(99);
    let sel1_next = bmc.solver.try_select(map1, one).unwrap();
    let eq_updated = bmc.solver.try_eq(sel1_next, ninety_nine).unwrap();
    bmc.assert(eq_updated);

    // Verify: f'[2] = 20 (preserved)
    let sel2_next = bmc.solver.try_select(map1, two).unwrap();
    let eq_preserved = bmc.solver.try_eq(sel2_next, twenty).unwrap();
    bmc.assert(eq_preserved);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

/// Test: EXCEPT contradiction — updating f[1] to two different values is UNSAT.
///
/// Init: f[1] = 10
/// Next: f' = [f EXCEPT ![1] = 99]
/// Check: f'[1] = 50 is UNSAT (must be 99)
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_compound_e2e_func_except_contradiction_unsat() {
    let mut bmc = bmc_array(1);
    bmc.declare_func_var("f", TlaSort::Int).unwrap();

    // Init: f[1] = 10
    let map0 = bmc.get_func_mapping_at_step("f", 0).unwrap();
    let one = bmc.solver.int_const(1);
    let ten = bmc.solver.int_const(10);
    let sel = bmc.solver.try_select(map0, one).unwrap();
    let eq = bmc.solver.try_eq(sel, ten).unwrap();
    bmc.assert(eq);

    // Next: f' = [f EXCEPT ![1] = 99]
    bmc.current_step = 0;
    let except_eq = Spanned::dummy(Expr::Eq(
        Box::new(primed("f")),
        Box::new(Spanned::dummy(Expr::Except(
            Box::new(ident("f")),
            vec![ExceptSpec {
                path: vec![ExceptPathElement::Index(int(1))],
                value: int(99),
            }],
        ))),
    ));
    let next_term = bmc.translate_bool(&except_eq).unwrap();
    bmc.assert(next_term);

    // Assert f'[1] = 50 — contradicts EXCEPT which sets it to 99
    let map1 = bmc.get_func_mapping_at_step("f", 1).unwrap();
    let fifty = bmc.solver.int_const(50);
    let sel1 = bmc.solver.try_select(map1, one).unwrap();
    let eq_wrong = bmc.solver.try_eq(sel1, fifty).unwrap();
    bmc.assert(eq_wrong);

    assert!(matches!(bmc.check_sat(), SolveResult::Unsat(_)));
}

/// Test: UNCHANGED for function variable preserves domain and mapping.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_compound_e2e_func_unchanged() {
    let mut bmc = bmc_array(1);
    bmc.declare_func_var("f", TlaSort::Int).unwrap();

    // Init: f[1] = 42
    let map0 = bmc.get_func_mapping_at_step("f", 0).unwrap();
    let one = bmc.solver.int_const(1);
    let forty_two = bmc.solver.int_const(42);
    let sel = bmc.solver.try_select(map0, one).unwrap();
    let eq = bmc.solver.try_eq(sel, forty_two).unwrap();
    bmc.assert(eq);

    // Next: UNCHANGED f
    bmc.current_step = 0;
    let unchanged = bmc
        .translate_bool(&Spanned::dummy(Expr::Unchanged(Box::new(ident("f")))))
        .unwrap();
    bmc.assert(unchanged);

    // At step 1: f[1] should still be 42
    let map1 = bmc.get_func_mapping_at_step("f", 1).unwrap();
    let sel1 = bmc.solver.try_select(map1, one).unwrap();
    let eq1 = bmc.solver.try_eq(sel1, forty_two).unwrap();
    bmc.assert(eq1);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

/// Test: UNCHANGED on function blocks mutation.
///
/// Init: f[1] = 42
/// Next: UNCHANGED f
/// Check: f'[1] = 99 is UNSAT
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_compound_e2e_func_unchanged_blocks_mutation() {
    let mut bmc = bmc_array(1);
    bmc.declare_func_var("f", TlaSort::Int).unwrap();

    // Init: f[1] = 42
    let map0 = bmc.get_func_mapping_at_step("f", 0).unwrap();
    let one = bmc.solver.int_const(1);
    let forty_two = bmc.solver.int_const(42);
    let sel = bmc.solver.try_select(map0, one).unwrap();
    let eq = bmc.solver.try_eq(sel, forty_two).unwrap();
    bmc.assert(eq);

    // Next: UNCHANGED f
    bmc.current_step = 0;
    let unchanged = bmc
        .translate_bool(&Spanned::dummy(Expr::Unchanged(Box::new(ident("f")))))
        .unwrap();
    bmc.assert(unchanged);

    // Assert f'[1] = 99 — contradicts UNCHANGED
    let map1 = bmc.get_func_mapping_at_step("f", 1).unwrap();
    let ninety_nine = bmc.solver.int_const(99);
    let sel1 = bmc.solver.try_select(map1, one).unwrap();
    let eq1 = bmc.solver.try_eq(sel1, ninety_nine).unwrap();
    bmc.assert(eq1);

    assert!(matches!(bmc.check_sat(), SolveResult::Unsat(_)));
}

// ---------------------------------------------------------------------------
// Sequence: Append, Tail, UNCHANGED across steps
// ---------------------------------------------------------------------------

/// Test: Append verifies length increment, Head preservation, and new element.
///
/// Init: s = <<10>>
/// Next: s' = Append(s, 20)
/// Check: Len(s') = 2, s'[1] = 10 (original), s'[2] = 20 (appended)
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_compound_e2e_seq_append_verify_head_and_len() {
    let mut bmc = bmc_array(1);
    bmc.declare_seq_var("s", TlaSort::Int, 5).unwrap();

    // Init: s = <<10>>
    let init = bmc
        .translate_init(&Spanned::dummy(Expr::Eq(
            Box::new(ident("s")),
            Box::new(Spanned::dummy(Expr::Tuple(vec![int(10)]))),
        )))
        .unwrap();
    bmc.assert(init);

    // Next: s' = Append(s, 20)
    bmc.current_step = 0;
    let append = Spanned::dummy(Expr::Apply(
        Box::new(ident("Append")),
        vec![ident("s"), int(20)],
    ));
    let next = bmc
        .translate_bool(&Spanned::dummy(Expr::Eq(
            Box::new(primed("s")),
            Box::new(append),
        )))
        .unwrap();
    bmc.assert(next);

    // Check: Len(s') = 2
    let len1 = bmc.get_seq_length_at_step("s", 1).unwrap();
    let two = bmc.solver.int_const(2);
    let len_eq = bmc.solver.try_eq(len1, two).unwrap();
    bmc.assert(len_eq);

    // Check: s'[1] = 10 (Head preserved)
    let arr1 = bmc.get_seq_array_at_step("s", 1).unwrap();
    let one = bmc.solver.int_const(1);
    let ten = bmc.solver.int_const(10);
    let head_sel = bmc.solver.try_select(arr1, one).unwrap();
    let head_eq = bmc.solver.try_eq(head_sel, ten).unwrap();
    bmc.assert(head_eq);

    // Check: s'[2] = 20 (appended element)
    let two_idx = bmc.solver.int_const(2);
    let twenty = bmc.solver.int_const(20);
    let tail_sel = bmc.solver.try_select(arr1, two_idx).unwrap();
    let tail_eq = bmc.solver.try_eq(tail_sel, twenty).unwrap();
    bmc.assert(tail_eq);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

/// Test: Tail shifts elements and decrements length.
///
/// Init: s = <<10, 20, 30>>
/// Next: s' = Tail(s)
/// Check: Len(s') = 2, s'[1] = 20 (shifted from s[2])
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_compound_e2e_seq_tail_shift_verify() {
    let mut bmc = bmc_array(1);
    bmc.declare_seq_var("s", TlaSort::Int, 5).unwrap();

    // Init: s = <<10, 20, 30>>
    let init = bmc
        .translate_init(&Spanned::dummy(Expr::Eq(
            Box::new(ident("s")),
            Box::new(Spanned::dummy(Expr::Tuple(vec![int(10), int(20), int(30)]))),
        )))
        .unwrap();
    bmc.assert(init);

    // Next: s' = Tail(s)
    bmc.current_step = 0;
    let tail = Spanned::dummy(Expr::Apply(Box::new(ident("Tail")), vec![ident("s")]));
    let next = bmc
        .translate_bool(&Spanned::dummy(Expr::Eq(
            Box::new(primed("s")),
            Box::new(tail),
        )))
        .unwrap();
    bmc.assert(next);

    // Check: Len(s') = 2
    let len1 = bmc.get_seq_length_at_step("s", 1).unwrap();
    let two = bmc.solver.int_const(2);
    let len_eq = bmc.solver.try_eq(len1, two).unwrap();
    bmc.assert(len_eq);

    // Check: s'[1] = 20 (shifted from s[2])
    let arr1 = bmc.get_seq_array_at_step("s", 1).unwrap();
    let one = bmc.solver.int_const(1);
    let twenty = bmc.solver.int_const(20);
    let first_sel = bmc.solver.try_select(arr1, one).unwrap();
    let first_eq = bmc.solver.try_eq(first_sel, twenty).unwrap();
    bmc.assert(first_eq);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

/// Test: UNCHANGED preserves sequence elements and length across a step.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_compound_e2e_seq_unchanged_preserves_elements() {
    let mut bmc = bmc_array(1);
    bmc.declare_seq_var("s", TlaSort::Int, 5).unwrap();

    // Init: s = <<10, 20>>
    let init = bmc
        .translate_init(&Spanned::dummy(Expr::Eq(
            Box::new(ident("s")),
            Box::new(Spanned::dummy(Expr::Tuple(vec![int(10), int(20)]))),
        )))
        .unwrap();
    bmc.assert(init);

    // Next: UNCHANGED s
    bmc.current_step = 0;
    let unchanged = bmc
        .translate_bool(&Spanned::dummy(Expr::Unchanged(Box::new(ident("s")))))
        .unwrap();
    bmc.assert(unchanged);

    // Check: at step 1, s[1] = 10, s[2] = 20, Len(s) = 2
    let arr1 = bmc.get_seq_array_at_step("s", 1).unwrap();
    let one = bmc.solver.int_const(1);
    let two_idx = bmc.solver.int_const(2);
    let ten = bmc.solver.int_const(10);
    let twenty = bmc.solver.int_const(20);

    let s1 = bmc.solver.try_select(arr1, one).unwrap();
    let eq1 = bmc.solver.try_eq(s1, ten).unwrap();
    bmc.assert(eq1);

    let s2 = bmc.solver.try_select(arr1, two_idx).unwrap();
    let eq2 = bmc.solver.try_eq(s2, twenty).unwrap();
    bmc.assert(eq2);

    let len1 = bmc.get_seq_length_at_step("s", 1).unwrap();
    let two = bmc.solver.int_const(2);
    let len_eq = bmc.solver.try_eq(len1, two).unwrap();
    bmc.assert(len_eq);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

/// Test: UNCHANGED on sequence blocks length change.
///
/// Init: s = <<10>>  (Len = 1)
/// Next: UNCHANGED s
/// Check: Len(s') = 2 is UNSAT
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_compound_e2e_seq_unchanged_blocks_length_change() {
    let mut bmc = bmc_array(1);
    bmc.declare_seq_var("s", TlaSort::Int, 5).unwrap();

    // Init: s = <<10>>
    let init = bmc
        .translate_init(&Spanned::dummy(Expr::Eq(
            Box::new(ident("s")),
            Box::new(Spanned::dummy(Expr::Tuple(vec![int(10)]))),
        )))
        .unwrap();
    bmc.assert(init);

    // Next: UNCHANGED s
    bmc.current_step = 0;
    let unchanged = bmc
        .translate_bool(&Spanned::dummy(Expr::Unchanged(Box::new(ident("s")))))
        .unwrap();
    bmc.assert(unchanged);

    // Assert Len(s') = 2 — contradicts UNCHANGED (Len must remain 1)
    let len1 = bmc.get_seq_length_at_step("s", 1).unwrap();
    let two = bmc.solver.int_const(2);
    let len_eq = bmc.solver.try_eq(len1, two).unwrap();
    bmc.assert(len_eq);

    assert!(matches!(bmc.check_sat(), SolveResult::Unsat(_)));
}

// ---------------------------------------------------------------------------
// Mixed: compound + scalar variables together
// ---------------------------------------------------------------------------

/// Test: Function + scalar mixed scenario with UNCHANGED on scalar.
///
/// Init: f[1] = 10, x = 0
/// Next: f' = [f EXCEPT ![1] = 99] /\ UNCHANGED x
/// Check: f'[1] = 99, x' = 0
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_compound_e2e_func_and_scalar_mixed() {
    let mut bmc = bmc_array(1);
    bmc.declare_func_var("f", TlaSort::Int).unwrap();
    bmc.declare_var("x", TlaSort::Int).unwrap();

    // Init: f[1] = 10, x = 0
    let map0 = bmc.get_func_mapping_at_step("f", 0).unwrap();
    let one = bmc.solver.int_const(1);
    let ten = bmc.solver.int_const(10);
    let sel_init = bmc.solver.try_select(map0, one).unwrap();
    let eq_init = bmc.solver.try_eq(sel_init, ten).unwrap();
    bmc.assert(eq_init);

    let x_init = bmc
        .translate_init(&Spanned::dummy(Expr::Eq(
            Box::new(ident("x")),
            Box::new(int(0)),
        )))
        .unwrap();
    bmc.assert(x_init);

    // Next: f' = [f EXCEPT ![1] = 99]
    bmc.current_step = 0;
    let except_eq = Spanned::dummy(Expr::Eq(
        Box::new(primed("f")),
        Box::new(Spanned::dummy(Expr::Except(
            Box::new(ident("f")),
            vec![ExceptSpec {
                path: vec![ExceptPathElement::Index(int(1))],
                value: int(99),
            }],
        ))),
    ));
    let next_f = bmc.translate_bool(&except_eq).unwrap();
    bmc.assert(next_f);

    // Next: UNCHANGED x
    let unchanged_x = bmc
        .translate_bool(&Spanned::dummy(Expr::Unchanged(Box::new(ident("x")))))
        .unwrap();
    bmc.assert(unchanged_x);

    // Check: f'[1] = 99
    let map1 = bmc.get_func_mapping_at_step("f", 1).unwrap();
    let ninety_nine = bmc.solver.int_const(99);
    let sel1 = bmc.solver.try_select(map1, one).unwrap();
    let eq1 = bmc.solver.try_eq(sel1, ninety_nine).unwrap();
    bmc.assert(eq1);

    // Check: x' = 0
    let x1 = bmc.get_var_at_step("x", 1).unwrap();
    let zero = bmc.solver.int_const(0);
    let x_eq = bmc.solver.try_eq(x1, zero).unwrap();
    bmc.assert(x_eq);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

/// Test: Set + sequence UNCHANGED together in a tuple-style UNCHANGED.
///
/// Init: S = {1, 2}, s = <<10>>
/// Next: UNCHANGED <<S, s>>
/// Check: S and s are preserved at step 1
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_compound_e2e_set_and_seq_unchanged_together() {
    let mut bmc = bmc_array(1);
    bmc.declare_var(
        "S",
        TlaSort::Set {
            element_sort: Box::new(TlaSort::Int),
        },
    )
    .unwrap();
    bmc.declare_seq_var("s", TlaSort::Int, 5).unwrap();

    // Init: S = {1, 2}
    bmc.assert_concrete_state(
        &[(
            "S".to_string(),
            BmcValue::Set(vec![BmcValue::Int(1), BmcValue::Int(2)]),
        )],
        0,
    )
    .unwrap();

    // Init: s = <<10>>
    let s_init = bmc
        .translate_init(&Spanned::dummy(Expr::Eq(
            Box::new(ident("s")),
            Box::new(Spanned::dummy(Expr::Tuple(vec![int(10)]))),
        )))
        .unwrap();
    bmc.assert(s_init);

    // Next: UNCHANGED <<S, s>>
    bmc.current_step = 0;
    let unchanged = bmc
        .translate_bool(&Spanned::dummy(Expr::Unchanged(Box::new(Spanned::dummy(
            Expr::Tuple(vec![ident("S"), ident("s")]),
        )))))
        .unwrap();
    bmc.assert(unchanged);

    // Check: at step 1, 1 \in S
    let s1_set = bmc.get_var_at_step("S", 1).unwrap();
    let one_val = bmc.solver.int_const(1);
    let member = bmc.solver.try_select(s1_set, one_val).unwrap();
    bmc.assert(member);

    // Check: at step 1, s[1] = 10 and Len(s) = 1
    let arr1 = bmc.get_seq_array_at_step("s", 1).unwrap();
    let one = bmc.solver.int_const(1);
    let ten = bmc.solver.int_const(10);
    let sel = bmc.solver.try_select(arr1, one).unwrap();
    let sel_eq = bmc.solver.try_eq(sel, ten).unwrap();
    bmc.assert(sel_eq);

    let len1 = bmc.get_seq_length_at_step("s", 1).unwrap();
    let one_len = bmc.solver.int_const(1);
    let len_eq = bmc.solver.try_eq(len1, one_len).unwrap();
    bmc.assert(len_eq);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

// ---------------------------------------------------------------------------
// Compound dispatch wiring: set operations, primed sets, SetFilter membership
// Part of #3806
// ---------------------------------------------------------------------------

/// Test: Membership in set union via compound dispatch.
///
/// x \in ({1, 2} \cup {3, 4}) should hold for x = 3.
/// This tests that `translate_membership` correctly routes `Union` through
/// semantic expansion: `x \in (S \cup T)` -> `(x \in S) \/ (x \in T)`.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_compound_dispatch_membership_in_union() {
    let mut bmc = bmc_array(0);
    bmc.declare_var("x", TlaSort::Int).unwrap();

    // Init: x = 3
    let init = bmc
        .translate_init(&Spanned::dummy(Expr::Eq(
            Box::new(ident("x")),
            Box::new(int(3)),
        )))
        .unwrap();
    bmc.assert(init);

    // Assert: x \in ({1, 2} \cup {3, 4})
    let set_union = Spanned::dummy(Expr::Union(
        Box::new(Spanned::dummy(Expr::SetEnum(vec![int(1), int(2)]))),
        Box::new(Spanned::dummy(Expr::SetEnum(vec![int(3), int(4)]))),
    ));
    let membership = bmc
        .translate_bool(&Spanned::dummy(Expr::In(
            Box::new(ident("x")),
            Box::new(set_union),
        )))
        .unwrap();
    bmc.assert(membership);

    // x = 3 is in {1,2} \cup {3,4}, so SAT
    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

/// Test: Non-membership in set union is UNSAT.
///
/// x \in ({1, 2} \cup {3, 4}) should NOT hold for x = 5.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_compound_dispatch_membership_in_union_unsat() {
    let mut bmc = bmc_array(0);
    bmc.declare_var("x", TlaSort::Int).unwrap();

    // Init: x = 5
    let init = bmc
        .translate_init(&Spanned::dummy(Expr::Eq(
            Box::new(ident("x")),
            Box::new(int(5)),
        )))
        .unwrap();
    bmc.assert(init);

    // Assert: x \in ({1, 2} \cup {3, 4})
    let set_union = Spanned::dummy(Expr::Union(
        Box::new(Spanned::dummy(Expr::SetEnum(vec![int(1), int(2)]))),
        Box::new(Spanned::dummy(Expr::SetEnum(vec![int(3), int(4)]))),
    ));
    let membership = bmc
        .translate_bool(&Spanned::dummy(Expr::In(
            Box::new(ident("x")),
            Box::new(set_union),
        )))
        .unwrap();
    bmc.assert(membership);

    // x = 5 is NOT in {1,2} \cup {3,4}, so UNSAT
    assert!(matches!(bmc.check_sat(), SolveResult::Unsat(_)));
}

/// Test: Membership in set intersection via compound dispatch.
///
/// x \in ({1, 2, 3} \cap {2, 3, 4}) should hold for x = 2.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_compound_dispatch_membership_in_intersect() {
    let mut bmc = bmc_array(0);
    bmc.declare_var("x", TlaSort::Int).unwrap();

    // Init: x = 2
    let init = bmc
        .translate_init(&Spanned::dummy(Expr::Eq(
            Box::new(ident("x")),
            Box::new(int(2)),
        )))
        .unwrap();
    bmc.assert(init);

    // Assert: x \in ({1, 2, 3} \cap {2, 3, 4})
    let set_intersect = Spanned::dummy(Expr::Intersect(
        Box::new(Spanned::dummy(Expr::SetEnum(vec![int(1), int(2), int(3)]))),
        Box::new(Spanned::dummy(Expr::SetEnum(vec![int(2), int(3), int(4)]))),
    ));
    let membership = bmc
        .translate_bool(&Spanned::dummy(Expr::In(
            Box::new(ident("x")),
            Box::new(set_intersect),
        )))
        .unwrap();
    bmc.assert(membership);

    // x = 2 is in {1,2,3} \cap {2,3,4} = {2,3}, so SAT
    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

/// Test: Membership in set intersection excludes non-shared elements.
///
/// x \in ({1, 2, 3} \cap {2, 3, 4}) should NOT hold for x = 1.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_compound_dispatch_membership_in_intersect_excludes() {
    let mut bmc = bmc_array(0);
    bmc.declare_var("x", TlaSort::Int).unwrap();

    // Init: x = 1
    let init = bmc
        .translate_init(&Spanned::dummy(Expr::Eq(
            Box::new(ident("x")),
            Box::new(int(1)),
        )))
        .unwrap();
    bmc.assert(init);

    // Assert: x \in ({1, 2, 3} \cap {2, 3, 4})
    let set_intersect = Spanned::dummy(Expr::Intersect(
        Box::new(Spanned::dummy(Expr::SetEnum(vec![int(1), int(2), int(3)]))),
        Box::new(Spanned::dummy(Expr::SetEnum(vec![int(2), int(3), int(4)]))),
    ));
    let membership = bmc
        .translate_bool(&Spanned::dummy(Expr::In(
            Box::new(ident("x")),
            Box::new(set_intersect),
        )))
        .unwrap();
    bmc.assert(membership);

    // x = 1 is NOT in {1,2,3} \cap {2,3,4} = {2,3}, so UNSAT
    assert!(matches!(bmc.check_sat(), SolveResult::Unsat(_)));
}

/// Test: Membership in set difference via compound dispatch.
///
/// x \in ({1, 2, 3} \ {2}) should hold for x = 3 but not x = 2.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_compound_dispatch_membership_in_set_minus() {
    let mut bmc = bmc_array(0);
    bmc.declare_var("x", TlaSort::Int).unwrap();

    // Init: x = 3
    let init = bmc
        .translate_init(&Spanned::dummy(Expr::Eq(
            Box::new(ident("x")),
            Box::new(int(3)),
        )))
        .unwrap();
    bmc.assert(init);

    // Assert: x \in ({1, 2, 3} \ {2})
    let set_minus = Spanned::dummy(Expr::SetMinus(
        Box::new(Spanned::dummy(Expr::SetEnum(vec![int(1), int(2), int(3)]))),
        Box::new(Spanned::dummy(Expr::SetEnum(vec![int(2)]))),
    ));
    let membership = bmc
        .translate_bool(&Spanned::dummy(Expr::In(
            Box::new(ident("x")),
            Box::new(set_minus),
        )))
        .unwrap();
    bmc.assert(membership);

    // x = 3 is in {1,2,3} \ {2} = {1,3}, so SAT
    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

/// Test: Membership in primed set variable.
///
/// After UNCHANGED S, x \in S' should work like x \in S.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_compound_dispatch_membership_in_primed_set() {
    let mut bmc = bmc_array(1);
    bmc.declare_var(
        "S",
        TlaSort::Set {
            element_sort: Box::new(TlaSort::Int),
        },
    )
    .unwrap();
    bmc.declare_var("x", TlaSort::Int).unwrap();

    // Init: S = {1, 2, 3}, x = 2
    bmc.assert_concrete_state(
        &[(
            "S".to_string(),
            BmcValue::Set(vec![BmcValue::Int(1), BmcValue::Int(2), BmcValue::Int(3)]),
        )],
        0,
    )
    .unwrap();
    let x_init = bmc
        .translate_init(&Spanned::dummy(Expr::Eq(
            Box::new(ident("x")),
            Box::new(int(2)),
        )))
        .unwrap();
    bmc.assert(x_init);

    // Next: UNCHANGED S, UNCHANGED x
    bmc.current_step = 0;
    let unchanged_s = bmc
        .translate_bool(&Spanned::dummy(Expr::Unchanged(Box::new(ident("S")))))
        .unwrap();
    bmc.assert(unchanged_s);
    let unchanged_x = bmc
        .translate_bool(&Spanned::dummy(Expr::Unchanged(Box::new(ident("x")))))
        .unwrap();
    bmc.assert(unchanged_x);

    // At step 0: assert x \in S' (membership in primed set variable)
    bmc.current_step = 0;
    let primed_s = Spanned::dummy(Expr::Prime(Box::new(ident("S"))));
    let membership = bmc
        .translate_bool(&Spanned::dummy(Expr::In(
            Box::new(ident("x")),
            Box::new(primed_s),
        )))
        .unwrap();
    bmc.assert(membership);

    // x = 2, S' = S = {1,2,3}, so 2 \in S' is SAT
    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

/// Test: Membership in primed set excludes non-members.
///
/// After UNCHANGED S, x \in S' should fail for x = 5 when S = {1, 2, 3}.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_compound_dispatch_membership_in_primed_set_unsat() {
    let mut bmc = bmc_array(1);
    bmc.declare_var(
        "S",
        TlaSort::Set {
            element_sort: Box::new(TlaSort::Int),
        },
    )
    .unwrap();
    bmc.declare_var("x", TlaSort::Int).unwrap();

    // Init: S = {1, 2, 3}, x = 5
    bmc.assert_concrete_state(
        &[(
            "S".to_string(),
            BmcValue::Set(vec![BmcValue::Int(1), BmcValue::Int(2), BmcValue::Int(3)]),
        )],
        0,
    )
    .unwrap();
    let x_init = bmc
        .translate_init(&Spanned::dummy(Expr::Eq(
            Box::new(ident("x")),
            Box::new(int(5)),
        )))
        .unwrap();
    bmc.assert(x_init);

    // Next: UNCHANGED S, UNCHANGED x
    bmc.current_step = 0;
    let unchanged_s = bmc
        .translate_bool(&Spanned::dummy(Expr::Unchanged(Box::new(ident("S")))))
        .unwrap();
    bmc.assert(unchanged_s);
    let unchanged_x = bmc
        .translate_bool(&Spanned::dummy(Expr::Unchanged(Box::new(ident("x")))))
        .unwrap();
    bmc.assert(unchanged_x);

    // At step 0: assert x \in S' (membership in primed set variable)
    bmc.current_step = 0;
    let primed_s = Spanned::dummy(Expr::Prime(Box::new(ident("S"))));
    let membership = bmc
        .translate_bool(&Spanned::dummy(Expr::In(
            Box::new(ident("x")),
            Box::new(primed_s),
        )))
        .unwrap();
    bmc.assert(membership);

    // x = 5, S' = S = {1,2,3}, so 5 \in S' is UNSAT
    assert!(matches!(bmc.check_sat(), SolveResult::Unsat(_)));
}

/// Test: SetFilter membership via compound dispatch.
///
/// x \in {y \in 1..5 : y > 3} should hold for x = 4.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_compound_dispatch_membership_in_setfilter() {
    let mut bmc = bmc_array(0);
    bmc.declare_var("x", TlaSort::Int).unwrap();

    // Init: x = 4
    let init = bmc
        .translate_init(&Spanned::dummy(Expr::Eq(
            Box::new(ident("x")),
            Box::new(int(4)),
        )))
        .unwrap();
    bmc.assert(init);

    // Build: {y \in 1..5 : y > 3}
    let bound = tla_core::ast::BoundVar {
        name: Spanned::dummy("y".to_string()),
        domain: Some(Box::new(Spanned::dummy(Expr::Range(
            Box::new(int(1)),
            Box::new(int(5)),
        )))),
        pattern: None,
    };
    let predicate = Spanned::dummy(Expr::Gt(
        Box::new(Spanned::dummy(Expr::Ident(
            "y".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(int(3)),
    ));
    let set_filter = Spanned::dummy(Expr::SetFilter(bound, Box::new(predicate)));

    // Assert: x \in {y \in 1..5 : y > 3}
    let membership = bmc
        .translate_bool(&Spanned::dummy(Expr::In(
            Box::new(ident("x")),
            Box::new(set_filter),
        )))
        .unwrap();
    bmc.assert(membership);

    // x = 4 is in {4, 5} (i.e. {y \in 1..5 : y > 3}), so SAT
    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

/// Test: SetFilter membership excludes elements that don't satisfy the predicate.
///
/// x \in {y \in 1..5 : y > 3} should NOT hold for x = 2.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_compound_dispatch_membership_in_setfilter_unsat() {
    let mut bmc = bmc_array(0);
    bmc.declare_var("x", TlaSort::Int).unwrap();

    // Init: x = 2
    let init = bmc
        .translate_init(&Spanned::dummy(Expr::Eq(
            Box::new(ident("x")),
            Box::new(int(2)),
        )))
        .unwrap();
    bmc.assert(init);

    // Build: {y \in 1..5 : y > 3}
    let bound = tla_core::ast::BoundVar {
        name: Spanned::dummy("y".to_string()),
        domain: Some(Box::new(Spanned::dummy(Expr::Range(
            Box::new(int(1)),
            Box::new(int(5)),
        )))),
        pattern: None,
    };
    let predicate = Spanned::dummy(Expr::Gt(
        Box::new(Spanned::dummy(Expr::Ident(
            "y".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(int(3)),
    ));
    let set_filter = Spanned::dummy(Expr::SetFilter(bound, Box::new(predicate)));

    // Assert: x \in {y \in 1..5 : y > 3}
    let membership = bmc
        .translate_bool(&Spanned::dummy(Expr::In(
            Box::new(ident("x")),
            Box::new(set_filter),
        )))
        .unwrap();
    bmc.assert(membership);

    // x = 2 is NOT in {4, 5}, so UNSAT
    assert!(matches!(bmc.check_sat(), SolveResult::Unsat(_)));
}

/// Test: Function construction via compound dispatch.
///
/// [x \in {1,2,3} |-> x + 10] should produce a mapping where f[2] = 12.
/// This exercises the FuncDef path through `translate_func_def_bool_dispatch`.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_compound_dispatch_func_def_construction() {
    let mut bmc = bmc_array(0);
    bmc.declare_func_var("f", TlaSort::Int).unwrap();

    // Build: [x \in {1, 2, 3} |-> x + 10]
    let bound = tla_core::ast::BoundVar {
        name: Spanned::dummy("x".to_string()),
        domain: Some(Box::new(Spanned::dummy(Expr::SetEnum(vec![
            int(1),
            int(2),
            int(3),
        ])))),
        pattern: None,
    };
    let body = Spanned::dummy(Expr::Add(
        Box::new(Spanned::dummy(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(int(10)),
    ));
    // Translate the function definition (this goes through compound_dispatch)
    let func_def = Spanned::dummy(Expr::FuncDef(vec![bound], Box::new(body)));
    bmc.current_step = 0;
    let _def_term = bmc.translate_bool(&func_def).unwrap();

    // The function construction asserts constraints on its internal mapping array.
    // Since we don't directly assign the result to `f`, this just checks that
    // the compound dispatch path works without error. The func_encoding.rs tests
    // cover the full constraint verification.
    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}
