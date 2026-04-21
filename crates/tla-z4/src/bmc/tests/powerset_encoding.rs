// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for BMC powerset (SUBSET S) encoding.
//!
//! Validates that:
//! - `x \in SUBSET S` (powerset membership) correctly constrains x to be
//!   a subset of S
//! - `\E T \in SUBSET S : P(T)` (existential quantification over powersets)
//!   correctly enumerates subsets
//! - `\A T \in SUBSET S : P(T)` (universal quantification over powersets)
//!   correctly checks all subsets
//! - Powerset enumeration produces correct subset count (2^n)
//! - Edge cases: empty base set, singleton base set

use super::*;
use z4_dpll::api::SolveResult;

/// Helper: create a BMC translator with array support.
fn bmc_array(k: usize) -> BmcTranslator {
    BmcTranslator::new_with_arrays(k).unwrap()
}

// --- Powerset enumeration ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_powerset_enumerate_empty_base() {
    let mut bmc = bmc_array(0);

    // SUBSET {} should produce 1 subset (the empty set)
    let base = spanned(Expr::SetEnum(vec![]));
    let subsets = bmc.enumerate_powerset_subsets(&base).unwrap();
    assert_eq!(subsets.len(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_powerset_enumerate_singleton() {
    let mut bmc = bmc_array(0);

    // SUBSET {1} should produce 2 subsets: {}, {1}
    let base = spanned(Expr::SetEnum(vec![spanned(Expr::Int(BigInt::from(1)))]));
    let subsets = bmc.enumerate_powerset_subsets(&base).unwrap();
    assert_eq!(subsets.len(), 2);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_powerset_enumerate_two_elements() {
    let mut bmc = bmc_array(0);

    // SUBSET {1, 2} should produce 4 subsets: {}, {1}, {2}, {1,2}
    let base = spanned(Expr::SetEnum(vec![
        spanned(Expr::Int(BigInt::from(1))),
        spanned(Expr::Int(BigInt::from(2))),
    ]));
    let subsets = bmc.enumerate_powerset_subsets(&base).unwrap();
    assert_eq!(subsets.len(), 4);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_powerset_enumerate_three_elements() {
    let mut bmc = bmc_array(0);

    // SUBSET {1, 2, 3} should produce 8 subsets
    let base = spanned(Expr::SetEnum(vec![
        spanned(Expr::Int(BigInt::from(1))),
        spanned(Expr::Int(BigInt::from(2))),
        spanned(Expr::Int(BigInt::from(3))),
    ]));
    let subsets = bmc.enumerate_powerset_subsets(&base).unwrap();
    assert_eq!(subsets.len(), 8);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_powerset_enumerate_membership_correct() {
    let mut bmc = bmc_array(0);

    // SUBSET {10, 20}: verify that subset[1] = {10} contains 10 but not 20
    let base = spanned(Expr::SetEnum(vec![
        spanned(Expr::Int(BigInt::from(10))),
        spanned(Expr::Int(BigInt::from(20))),
    ]));
    let subsets = bmc.enumerate_powerset_subsets(&base).unwrap();
    // subsets[0] = {}, [1] = {10}, [2] = {20}, [3] = {10, 20}

    let ten = bmc.solver.int_const(10);
    let twenty = bmc.solver.int_const(20);

    // Check that subset[1] contains 10
    let in_10 = bmc.solver.try_select(subsets[1], ten).unwrap();
    bmc.assert(in_10);

    // Check that subset[1] does NOT contain 20
    let in_20 = bmc.solver.try_select(subsets[1], twenty).unwrap();
    let not_in_20 = bmc.solver.try_not(in_20).unwrap();
    bmc.assert(not_in_20);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

// --- Powerset membership (x \in SUBSET S) ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_powerset_membership_subset_accepted() {
    let mut bmc = bmc_array(0);
    bmc.declare_var(
        "T",
        TlaSort::Set {
            element_sort: Box::new(TlaSort::Int),
        },
    )
    .unwrap();

    // Assert T = {1} (a concrete subset)
    bmc.assert_concrete_state(
        &[("T".to_string(), BmcValue::Set(vec![BmcValue::Int(1)]))],
        0,
    )
    .unwrap();

    // Build: T \in SUBSET {1, 2, 3}
    let membership = spanned(Expr::In(
        Box::new(spanned(Expr::Ident(
            "T".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Powerset(Box::new(spanned(Expr::SetEnum(
            vec![
                spanned(Expr::Int(BigInt::from(1))),
                spanned(Expr::Int(BigInt::from(2))),
                spanned(Expr::Int(BigInt::from(3))),
            ],
        )))))),
    ));

    let term = bmc.translate_init(&membership).unwrap();
    bmc.assert(term);

    // {1} \in SUBSET {1, 2, 3} should be SAT
    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_powerset_membership_non_subset_rejected() {
    let mut bmc = bmc_array(0);
    bmc.declare_var(
        "T",
        TlaSort::Set {
            element_sort: Box::new(TlaSort::Int),
        },
    )
    .unwrap();

    // Assert T = {1, 4} (4 is NOT in the base set)
    bmc.assert_concrete_state(
        &[(
            "T".to_string(),
            BmcValue::Set(vec![BmcValue::Int(1), BmcValue::Int(4)]),
        )],
        0,
    )
    .unwrap();

    // Build: T \in SUBSET {1, 2, 3}
    let membership = spanned(Expr::In(
        Box::new(spanned(Expr::Ident(
            "T".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Powerset(Box::new(spanned(Expr::SetEnum(
            vec![
                spanned(Expr::Int(BigInt::from(1))),
                spanned(Expr::Int(BigInt::from(2))),
                spanned(Expr::Int(BigInt::from(3))),
            ],
        )))))),
    ));

    let term = bmc.translate_init(&membership).unwrap();
    bmc.assert(term);

    // {1, 4} \in SUBSET {1, 2, 3} should be UNSAT (4 not in base)
    assert!(matches!(bmc.check_sat(), SolveResult::Unsat(_)));
}

// --- Quantification over powerset ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_exists_in_subset_sat() {
    use tla_core::ast::BoundVar;
    let mut bmc = bmc_array(0);

    // Declare a set variable S with value {1, 2}
    bmc.declare_var(
        "S",
        TlaSort::Set {
            element_sort: Box::new(TlaSort::Int),
        },
    )
    .unwrap();

    // \E T \in SUBSET {1, 2} : T = S
    // i.e., does there exist a subset of {1, 2} equal to S?
    // This is always SAT because S can be any set, and we're checking
    // if any subset of {1,2} matches it.

    // Actually, let's make it simpler:
    // \E T \in SUBSET {1, 2} : TRUE
    // This should trivially be SAT (there exist subsets of {1,2}).
    let exists_expr = spanned(Expr::Exists(
        vec![BoundVar {
            name: spanned("T".to_string()),
            domain: Some(Box::new(spanned(Expr::Powerset(Box::new(spanned(
                Expr::SetEnum(vec![
                    spanned(Expr::Int(BigInt::from(1))),
                    spanned(Expr::Int(BigInt::from(2))),
                ]),
            )))))),
            pattern: None,
        }],
        Box::new(spanned(Expr::Bool(true))),
    ));

    let term = bmc.translate_init(&exists_expr).unwrap();
    bmc.assert(term);
    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_forall_in_subset_trivially_true() {
    use tla_core::ast::BoundVar;
    let mut bmc = bmc_array(0);

    // \A T \in SUBSET {1} : TRUE
    // Should be SAT (TRUE holds for all subsets)
    let forall_expr = spanned(Expr::Forall(
        vec![BoundVar {
            name: spanned("T".to_string()),
            domain: Some(Box::new(spanned(Expr::Powerset(Box::new(spanned(
                Expr::SetEnum(vec![spanned(Expr::Int(BigInt::from(1)))]),
            )))))),
            pattern: None,
        }],
        Box::new(spanned(Expr::Bool(true))),
    ));

    let term = bmc.translate_init(&forall_expr).unwrap();
    bmc.assert(term);
    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_forall_in_subset_trivially_false() {
    use tla_core::ast::BoundVar;
    let mut bmc = bmc_array(0);

    // \A T \in SUBSET {1} : FALSE
    // Should be UNSAT (FALSE does not hold for any subset)
    let forall_expr = spanned(Expr::Forall(
        vec![BoundVar {
            name: spanned("T".to_string()),
            domain: Some(Box::new(spanned(Expr::Powerset(Box::new(spanned(
                Expr::SetEnum(vec![spanned(Expr::Int(BigInt::from(1)))]),
            )))))),
            pattern: None,
        }],
        Box::new(spanned(Expr::Bool(false))),
    ));

    let term = bmc.translate_init(&forall_expr).unwrap();
    bmc.assert(term);
    assert!(matches!(bmc.check_sat(), SolveResult::Unsat(_)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_exists_subset_with_membership_body() {
    use tla_core::ast::BoundVar;
    let mut bmc = bmc_array(0);
    bmc.declare_var("x", TlaSort::Int).unwrap();

    // Assert x = 1
    let x_eq_1 = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(1)))),
    ));
    let init_term = bmc.translate_init(&x_eq_1).unwrap();
    bmc.assert(init_term);

    // \E T \in SUBSET {1, 2} : x \in T
    // With x = 1, this asks: does there exist a subset of {1,2} that contains 1?
    // Answer: yes ({1} and {1,2} both contain 1).
    let exists_expr = spanned(Expr::Exists(
        vec![BoundVar {
            name: spanned("T".to_string()),
            domain: Some(Box::new(spanned(Expr::Powerset(Box::new(spanned(
                Expr::SetEnum(vec![
                    spanned(Expr::Int(BigInt::from(1))),
                    spanned(Expr::Int(BigInt::from(2))),
                ]),
            )))))),
            pattern: None,
        }],
        Box::new(spanned(Expr::In(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Ident(
                "T".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
        ))),
    ));

    let term = bmc.translate_init(&exists_expr).unwrap();
    bmc.assert(term);
    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

// --- Symbolic subset constraint ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_symbolic_subset_is_sat() {
    let mut bmc = bmc_array(0);

    // Create a symbolic subset of {1, 2, 3}
    let base = spanned(Expr::SetEnum(vec![
        spanned(Expr::Int(BigInt::from(1))),
        spanned(Expr::Int(BigInt::from(2))),
        spanned(Expr::Int(BigInt::from(3))),
    ]));

    let sub = bmc.encode_symbolic_subset(&base).unwrap();

    // Assert that 1 is in the subset
    let one = bmc.solver.int_const(1);
    let in_sub = bmc.solver.try_select(sub, one).unwrap();
    bmc.assert(in_sub);

    // Should be SAT (there exist subsets containing 1)
    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_symbolic_subset_excludes_non_base_elements() {
    let mut bmc = bmc_array(0);

    // Create a symbolic subset of {1, 2}
    let base = spanned(Expr::SetEnum(vec![
        spanned(Expr::Int(BigInt::from(1))),
        spanned(Expr::Int(BigInt::from(2))),
    ]));

    let sub = bmc.encode_symbolic_subset(&base).unwrap();

    // Assert that 3 is in the subset (3 is NOT in the base set)
    let three = bmc.solver.int_const(3);
    let in_sub = bmc.solver.try_select(sub, three).unwrap();
    bmc.assert(in_sub);

    // Should be UNSAT (subset of {1,2} cannot contain 3)
    assert!(matches!(bmc.check_sat(), SolveResult::Unsat(_)));
}

// --- Powerset in Bool context ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_powerset_bool_context() {
    let mut bmc = bmc_array(0);

    // SUBSET {1, 2} in Bool context should return TRUE (set is constructable)
    let powerset_expr = spanned(Expr::Powerset(Box::new(spanned(Expr::SetEnum(vec![
        spanned(Expr::Int(BigInt::from(1))),
        spanned(Expr::Int(BigInt::from(2))),
    ])))));

    let term = bmc.translate_init(&powerset_expr).unwrap();
    bmc.assert(term);
    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

// --- Edge: powerset of range ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_powerset_enumerate_range() {
    let mut bmc = bmc_array(0);

    // SUBSET (1..3) should produce 8 subsets (base has 3 elements: 1, 2, 3)
    let base = spanned(Expr::Range(
        Box::new(spanned(Expr::Int(BigInt::from(1)))),
        Box::new(spanned(Expr::Int(BigInt::from(3)))),
    ));
    let subsets = bmc.enumerate_powerset_subsets(&base).unwrap();
    assert_eq!(subsets.len(), 8);
}
