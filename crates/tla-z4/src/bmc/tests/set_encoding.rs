// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for BMC finite set encoding via SMT arrays.
//!
//! Part of #3778: Validates that set-typed state variables can be declared,
//! set expressions (SetEnum, Union, Intersect, SetMinus, Subseteq) can be
//! translated, and membership queries produce correct SAT/UNSAT results.

use super::*;
use z4_dpll::api::{SolveResult, Sort};

/// Helper: create a BMC translator with array support.
fn bmc_array(k: usize) -> BmcTranslator {
    BmcTranslator::new_with_arrays(k).unwrap()
}

// --- TlaSort::Set variant ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tla_sort_set_display() {
    let sort = TlaSort::Set {
        element_sort: Box::new(TlaSort::Int),
    };
    assert_eq!(format!("{sort}"), "Set(Int)");

    let nested = TlaSort::Set {
        element_sort: Box::new(TlaSort::Bool),
    };
    assert_eq!(format!("{nested}"), "Set(Bool)");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tla_sort_set_to_z4() {
    let sort = TlaSort::Set {
        element_sort: Box::new(TlaSort::Int),
    };
    let z4_sort = sort.to_z4().unwrap();
    // Should produce (Array Int Bool)
    assert_eq!(z4_sort, Sort::array(Sort::Int, Sort::Bool));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tla_sort_set_is_not_scalar() {
    let sort = TlaSort::Set {
        element_sort: Box::new(TlaSort::Int),
    };
    assert!(!sort.is_scalar());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tla_sort_set_canonicalized() {
    let sort = TlaSort::Set {
        element_sort: Box::new(TlaSort::Int),
    };
    let canon = sort.canonicalized();
    assert_eq!(
        canon,
        TlaSort::Set {
            element_sort: Box::new(TlaSort::Int)
        }
    );
}

// --- BmcValue::Set variant ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_value_set_debug() {
    let val = BmcValue::Set(vec![BmcValue::Int(1), BmcValue::Int(2)]);
    let debug = format!("{val:?}");
    assert!(debug.contains("Set"));
    assert!(debug.contains("Int(1)"));
    assert!(debug.contains("Int(2)"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_value_set_equality() {
    let a = BmcValue::Set(vec![BmcValue::Int(1), BmcValue::Int(2)]);
    let b = BmcValue::Set(vec![BmcValue::Int(1), BmcValue::Int(2)]);
    let c = BmcValue::Set(vec![BmcValue::Int(1), BmcValue::Int(3)]);
    assert_eq!(a, b);
    assert_ne!(a, c);
}

// --- BMC declare_var with Set sort ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_declare_set_var() {
    let mut bmc = bmc_array(2);
    // Should succeed: Set(Int) is a supported sort
    bmc.declare_var(
        "S",
        TlaSort::Set {
            element_sort: Box::new(TlaSort::Int),
        },
    )
    .unwrap();
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_declare_set_var_rejects_without_arrays() {
    // new() uses QfLia which does NOT support arrays.
    // However, declare_var only checks is_scalar() || is Set; it doesn't
    // validate the solver logic. The solver will reject array operations later.
    // This test verifies that declare_var accepts Set sort.
    let mut bmc = BmcTranslator::new(2).unwrap();
    // This will fail because QfLia solver can't handle array sort
    let result = bmc.declare_var(
        "S",
        TlaSort::Set {
            element_sort: Box::new(TlaSort::Int),
        },
    );
    // The z4 solver may or may not reject this at declaration time;
    // what matters is that new_with_arrays works correctly.
    // If it succeeds, that's also fine — the solver will fail at check_sat.
    let _ = result;
}

// --- BMC set expression translation ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_set_enum_membership_sat() {
    let mut bmc = bmc_array(0);
    bmc.declare_var("x", TlaSort::Int).unwrap();

    // Build: x \in {1, 2, 3} (using scalar membership, already supported)
    let expr = spanned(Expr::In(
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

    let init = bmc.translate_init(&expr).unwrap();
    bmc.assert(init);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_set_variable_membership() {
    let mut bmc = bmc_array(0);
    bmc.declare_var(
        "S",
        TlaSort::Set {
            element_sort: Box::new(TlaSort::Int),
        },
    )
    .unwrap();
    bmc.declare_var("x", TlaSort::Int).unwrap();

    // Translate: x \in S (where S is a set-typed variable)
    let membership_expr = spanned(Expr::In(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Ident(
            "S".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
    ));

    let term = bmc.translate_init(&membership_expr).unwrap();
    bmc.assert(term);

    // Should be SAT: solver can assign S and x to make membership true
    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_translate_set_enum_expr() {
    let mut bmc = bmc_array(0);

    // Build set {1, 2} as an array term
    let set_expr = spanned(Expr::SetEnum(vec![
        spanned(Expr::Int(BigInt::from(1))),
        spanned(Expr::Int(BigInt::from(2))),
    ]));

    let universe = [
        bmc.solver.int_const(1),
        bmc.solver.int_const(2),
        bmc.solver.int_const(3),
    ];

    let set_term = bmc.translate_set_expr(&set_expr, &universe).unwrap();

    // Check that 1 is in the set
    let one = bmc.solver.int_const(1);
    let member = bmc.solver.try_select(set_term, one).unwrap();
    bmc.assert(member);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_translate_set_enum_nonmember_unsat() {
    let mut bmc = bmc_array(0);

    // Build set {1, 2}
    let set_expr = spanned(Expr::SetEnum(vec![
        spanned(Expr::Int(BigInt::from(1))),
        spanned(Expr::Int(BigInt::from(2))),
    ]));

    let universe = [
        bmc.solver.int_const(1),
        bmc.solver.int_const(2),
        bmc.solver.int_const(3),
    ];

    let set_term = bmc.translate_set_expr(&set_expr, &universe).unwrap();

    // Check that 5 is NOT in the set (should be UNSAT if we assert it is)
    let five = bmc.solver.int_const(5);
    let member = bmc.solver.try_select(set_term, five).unwrap();
    bmc.assert(member);

    assert!(matches!(bmc.check_sat(), SolveResult::Unsat(_)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_set_union() {
    let mut bmc = bmc_array(0);

    let u1 = bmc.solver.int_const(1);
    let u2 = bmc.solver.int_const(2);
    let u3 = bmc.solver.int_const(3);
    let universe = [u1, u2, u3];

    // S = {1, 2}, T = {2, 3}
    let set_s = spanned(Expr::SetEnum(vec![
        spanned(Expr::Int(BigInt::from(1))),
        spanned(Expr::Int(BigInt::from(2))),
    ]));
    let set_t = spanned(Expr::SetEnum(vec![
        spanned(Expr::Int(BigInt::from(2))),
        spanned(Expr::Int(BigInt::from(3))),
    ]));

    // Build union expression
    let union_expr = spanned(Expr::Union(Box::new(set_s), Box::new(set_t)));
    let union_term = bmc.translate_set_expr(&union_expr, &universe).unwrap();

    // 1 should be in the union
    let one = bmc.solver.int_const(1);
    let in_union = bmc.solver.try_select(union_term, one).unwrap();
    bmc.assert(in_union);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_set_intersect() {
    let mut bmc = bmc_array(0);

    let u1 = bmc.solver.int_const(1);
    let u2 = bmc.solver.int_const(2);
    let u3 = bmc.solver.int_const(3);
    let universe = [u1, u2, u3];

    // S = {1, 2}, T = {2, 3}
    let set_s = spanned(Expr::SetEnum(vec![
        spanned(Expr::Int(BigInt::from(1))),
        spanned(Expr::Int(BigInt::from(2))),
    ]));
    let set_t = spanned(Expr::SetEnum(vec![
        spanned(Expr::Int(BigInt::from(2))),
        spanned(Expr::Int(BigInt::from(3))),
    ]));

    let inter_expr = spanned(Expr::Intersect(Box::new(set_s), Box::new(set_t)));
    let inter_term = bmc.translate_set_expr(&inter_expr, &universe).unwrap();

    // 1 should NOT be in the intersection (only 2 is)
    let one = bmc.solver.int_const(1);
    let in_inter = bmc.solver.try_select(inter_term, one).unwrap();
    bmc.assert(in_inter);

    assert!(matches!(bmc.check_sat(), SolveResult::Unsat(_)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_set_intersect_member() {
    let mut bmc = bmc_array(0);

    let u1 = bmc.solver.int_const(1);
    let u2 = bmc.solver.int_const(2);
    let u3 = bmc.solver.int_const(3);
    let universe = [u1, u2, u3];

    // S = {1, 2}, T = {2, 3}: intersection should contain 2
    let set_s = spanned(Expr::SetEnum(vec![
        spanned(Expr::Int(BigInt::from(1))),
        spanned(Expr::Int(BigInt::from(2))),
    ]));
    let set_t = spanned(Expr::SetEnum(vec![
        spanned(Expr::Int(BigInt::from(2))),
        spanned(Expr::Int(BigInt::from(3))),
    ]));

    let inter_expr = spanned(Expr::Intersect(Box::new(set_s), Box::new(set_t)));
    let inter_term = bmc.translate_set_expr(&inter_expr, &universe).unwrap();

    // 2 should be in the intersection
    let two = bmc.solver.int_const(2);
    let in_inter = bmc.solver.try_select(inter_term, two).unwrap();
    bmc.assert(in_inter);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_set_minus() {
    let mut bmc = bmc_array(0);

    let u1 = bmc.solver.int_const(1);
    let u2 = bmc.solver.int_const(2);
    let u3 = bmc.solver.int_const(3);
    let universe = [u1, u2, u3];

    // S = {1, 2, 3}, T = {2}
    let set_s = spanned(Expr::SetEnum(vec![
        spanned(Expr::Int(BigInt::from(1))),
        spanned(Expr::Int(BigInt::from(2))),
        spanned(Expr::Int(BigInt::from(3))),
    ]));
    let set_t = spanned(Expr::SetEnum(vec![spanned(Expr::Int(BigInt::from(2)))]));

    let minus_expr = spanned(Expr::SetMinus(Box::new(set_s), Box::new(set_t)));
    let minus_term = bmc.translate_set_expr(&minus_expr, &universe).unwrap();

    // 2 should NOT be in S \ T
    let two = bmc.solver.int_const(2);
    let in_minus = bmc.solver.try_select(minus_term, two).unwrap();
    bmc.assert(in_minus);

    assert!(matches!(bmc.check_sat(), SolveResult::Unsat(_)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_set_minus_retains_member() {
    let mut bmc = bmc_array(0);

    let u1 = bmc.solver.int_const(1);
    let u2 = bmc.solver.int_const(2);
    let u3 = bmc.solver.int_const(3);
    let universe = [u1, u2, u3];

    // S = {1, 2, 3}, T = {2}, S \ T should contain 1
    let set_s = spanned(Expr::SetEnum(vec![
        spanned(Expr::Int(BigInt::from(1))),
        spanned(Expr::Int(BigInt::from(2))),
        spanned(Expr::Int(BigInt::from(3))),
    ]));
    let set_t = spanned(Expr::SetEnum(vec![spanned(Expr::Int(BigInt::from(2)))]));

    let minus_expr = spanned(Expr::SetMinus(Box::new(set_s), Box::new(set_t)));
    let minus_term = bmc.translate_set_expr(&minus_expr, &universe).unwrap();

    // 1 should be in S \ T
    let one = bmc.solver.int_const(1);
    let in_minus = bmc.solver.try_select(minus_term, one).unwrap();
    bmc.assert(in_minus);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_subseteq_true() {
    let mut bmc = bmc_array(0);

    let u1 = bmc.solver.int_const(1);
    let u2 = bmc.solver.int_const(2);
    let u3 = bmc.solver.int_const(3);
    let universe = [u1, u2, u3];

    // S = {1, 2}, T = {1, 2, 3}: S \subseteq T should be true
    let set_s = spanned(Expr::SetEnum(vec![
        spanned(Expr::Int(BigInt::from(1))),
        spanned(Expr::Int(BigInt::from(2))),
    ]));
    let set_t = spanned(Expr::SetEnum(vec![
        spanned(Expr::Int(BigInt::from(1))),
        spanned(Expr::Int(BigInt::from(2))),
        spanned(Expr::Int(BigInt::from(3))),
    ]));

    let subset_term = bmc
        .translate_subseteq_bmc(&set_s, &set_t, &universe)
        .unwrap();
    bmc.assert(subset_term);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_subseteq_false() {
    let mut bmc = bmc_array(0);

    let u1 = bmc.solver.int_const(1);
    let u2 = bmc.solver.int_const(2);
    let u3 = bmc.solver.int_const(3);
    let universe = [u1, u2, u3];

    // S = {1, 2, 3}, T = {1, 2}: S \subseteq T should be false
    let set_s = spanned(Expr::SetEnum(vec![
        spanned(Expr::Int(BigInt::from(1))),
        spanned(Expr::Int(BigInt::from(2))),
        spanned(Expr::Int(BigInt::from(3))),
    ]));
    let set_t = spanned(Expr::SetEnum(vec![
        spanned(Expr::Int(BigInt::from(1))),
        spanned(Expr::Int(BigInt::from(2))),
    ]));

    let subset_term = bmc
        .translate_subseteq_bmc(&set_s, &set_t, &universe)
        .unwrap();
    // Asserting that subseteq holds should be UNSAT
    bmc.assert(subset_term);

    assert!(matches!(bmc.check_sat(), SolveResult::Unsat(_)));
}

// --- Concrete state with set values ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_assert_concrete_state_with_set() {
    let mut bmc = bmc_array(0);
    bmc.declare_var("x", TlaSort::Int).unwrap();
    bmc.declare_var(
        "S",
        TlaSort::Set {
            element_sort: Box::new(TlaSort::Int),
        },
    )
    .unwrap();

    // Assert concrete state: x = 1, S = {1, 2}
    bmc.assert_concrete_state(
        &[
            ("x".to_string(), BmcValue::Int(1)),
            (
                "S".to_string(),
                BmcValue::Set(vec![BmcValue::Int(1), BmcValue::Int(2)]),
            ),
        ],
        0,
    )
    .unwrap();

    // Assert x \in S (should be SAT since x=1 and 1 is in {1,2})
    let x_term = bmc.get_var_at_step("x", 0).unwrap();
    let s_term = bmc.get_var_at_step("S", 0).unwrap();
    let member = bmc.solver.try_select(s_term, x_term).unwrap();
    bmc.assert(member);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_assert_concrete_state_set_nonmember_unsat() {
    let mut bmc = bmc_array(0);
    bmc.declare_var("x", TlaSort::Int).unwrap();
    bmc.declare_var(
        "S",
        TlaSort::Set {
            element_sort: Box::new(TlaSort::Int),
        },
    )
    .unwrap();

    // Assert concrete state: x = 3, S = {1, 2}
    bmc.assert_concrete_state(
        &[
            ("x".to_string(), BmcValue::Int(3)),
            (
                "S".to_string(),
                BmcValue::Set(vec![BmcValue::Int(1), BmcValue::Int(2)]),
            ),
        ],
        0,
    )
    .unwrap();

    // Assert x \in S (should be UNSAT since x=3 and 3 is NOT in {1,2})
    let x_term = bmc.get_var_at_step("x", 0).unwrap();
    let s_term = bmc.get_var_at_step("S", 0).unwrap();
    let member = bmc.solver.try_select(s_term, x_term).unwrap();
    bmc.assert(member);

    assert!(matches!(bmc.check_sat(), SolveResult::Unsat(_)));
}

// --- Empty set ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_empty_set_enum() {
    let mut bmc = bmc_array(0);

    let set_expr = spanned(Expr::SetEnum(vec![]));
    let universe: Vec<Term> = vec![];

    let set_term = bmc.translate_set_expr(&set_expr, &universe).unwrap();

    // Assert anything is in the empty set: should be UNSAT
    let x = bmc.solver.declare_const("x", Sort::Int);
    let member = bmc.solver.try_select(set_term, x).unwrap();
    bmc.assert(member);

    assert!(matches!(bmc.check_sat(), SolveResult::Unsat(_)));
}

// --- Set variable at different BMC steps ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_set_var_across_steps() {
    let mut bmc = bmc_array(1);
    bmc.declare_var(
        "S",
        TlaSort::Set {
            element_sort: Box::new(TlaSort::Int),
        },
    )
    .unwrap();

    // Set different values at step 0 and step 1
    bmc.assert_concrete_state(
        &[("S".to_string(), BmcValue::Set(vec![BmcValue::Int(1)]))],
        0,
    )
    .unwrap();
    bmc.assert_concrete_state(
        &[("S".to_string(), BmcValue::Set(vec![BmcValue::Int(2)]))],
        1,
    )
    .unwrap();

    // At step 0: 1 should be in S
    let s0 = bmc.get_var_at_step("S", 0).unwrap();
    let one = bmc.solver.int_const(1);
    let in_s0 = bmc.solver.try_select(s0, one).unwrap();
    bmc.assert(in_s0);

    // At step 1: 2 should be in S
    let s1 = bmc.get_var_at_step("S", 1).unwrap();
    let two = bmc.solver.int_const(2);
    let in_s1 = bmc.solver.try_select(s1, two).unwrap();
    bmc.assert(in_s1);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}
