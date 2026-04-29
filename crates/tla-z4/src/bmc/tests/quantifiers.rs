// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for BMC quantifier translation: expansion and Skolemization.

use super::*;
use tla_core::ast::BoundVar;

fn bound_var(name: &str, domain: Spanned<Expr>) -> BoundVar {
    BoundVar {
        name: spanned(name.to_string()),
        domain: Some(Box::new(domain)),
        pattern: None,
    }
}

// === Direct expansion tests (small domains) ===

/// \A x \in {1, 2, 3} : x > 0  — SAT (all positive)
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_forall_set_enum_sat() {
    let k = 0;
    let mut trans = BmcTranslator::new(k).unwrap();

    let expr = spanned(Expr::Forall(
        vec![bound_var(
            "x",
            spanned(Expr::SetEnum(vec![
                spanned(Expr::Int(BigInt::from(1))),
                spanned(Expr::Int(BigInt::from(2))),
                spanned(Expr::Int(BigInt::from(3))),
            ])),
        )],
        Box::new(spanned(Expr::Gt(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(0)))),
        ))),
    ));
    let term = trans.translate_init(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

/// \A x \in {1, 2, -1} : x > 0  — UNSAT
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_forall_set_enum_unsat() {
    let k = 0;
    let mut trans = BmcTranslator::new(k).unwrap();

    let expr = spanned(Expr::Forall(
        vec![bound_var(
            "x",
            spanned(Expr::SetEnum(vec![
                spanned(Expr::Int(BigInt::from(1))),
                spanned(Expr::Int(BigInt::from(2))),
                spanned(Expr::Int(BigInt::from(-1))),
            ])),
        )],
        Box::new(spanned(Expr::Gt(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(0)))),
        ))),
    ));
    let term = trans.translate_init(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
}

/// \E x \in {-1, 0, 1} : x > 0  — SAT
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_exists_set_enum_sat() {
    let k = 0;
    let mut trans = BmcTranslator::new(k).unwrap();

    let expr = spanned(Expr::Exists(
        vec![bound_var(
            "x",
            spanned(Expr::SetEnum(vec![
                spanned(Expr::Int(BigInt::from(-1))),
                spanned(Expr::Int(BigInt::from(0))),
                spanned(Expr::Int(BigInt::from(1))),
            ])),
        )],
        Box::new(spanned(Expr::Gt(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(0)))),
        ))),
    ));
    let term = trans.translate_init(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

/// \E x \in {-2, -1} : x > 0  — UNSAT
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_exists_set_enum_unsat() {
    let k = 0;
    let mut trans = BmcTranslator::new(k).unwrap();

    let expr = spanned(Expr::Exists(
        vec![bound_var(
            "x",
            spanned(Expr::SetEnum(vec![
                spanned(Expr::Int(BigInt::from(-2))),
                spanned(Expr::Int(BigInt::from(-1))),
            ])),
        )],
        Box::new(spanned(Expr::Gt(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(0)))),
        ))),
    ));
    let term = trans.translate_init(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
}

/// ~(\E x \in {1, 2, 3} : x > 2)  — UNSAT (3 > 2 exists)
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_not_exists_set_enum_unsat() {
    let k = 0;
    let mut trans = BmcTranslator::new(k).unwrap();

    let expr = spanned(Expr::Not(Box::new(spanned(Expr::Exists(
        vec![bound_var(
            "x",
            spanned(Expr::SetEnum(vec![
                spanned(Expr::Int(BigInt::from(1))),
                spanned(Expr::Int(BigInt::from(2))),
                spanned(Expr::Int(BigInt::from(3))),
            ])),
        )],
        Box::new(spanned(Expr::Gt(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(2)))),
        ))),
    )))));
    let term = trans.translate_init(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
}

/// ~(\E x \in {1, 2, 3} : x > 5)  — SAT (no witness exists)
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_not_exists_set_enum_sat() {
    let k = 0;
    let mut trans = BmcTranslator::new(k).unwrap();

    let expr = spanned(Expr::Not(Box::new(spanned(Expr::Exists(
        vec![bound_var(
            "x",
            spanned(Expr::SetEnum(vec![
                spanned(Expr::Int(BigInt::from(1))),
                spanned(Expr::Int(BigInt::from(2))),
                spanned(Expr::Int(BigInt::from(3))),
            ])),
        )],
        Box::new(spanned(Expr::Gt(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(5)))),
        ))),
    )))));
    let term = trans.translate_init(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

/// ~(\E x \in 1..20 : x > 20)  — SAT and avoids exists Skolemization
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_not_exists_range_skolem_sat() {
    let k = 0;
    let mut trans = BmcTranslator::new(k).unwrap();

    let expr = spanned(Expr::Not(Box::new(spanned(Expr::Exists(
        vec![bound_var(
            "x",
            spanned(Expr::Range(
                Box::new(spanned(Expr::Int(BigInt::from(1)))),
                Box::new(spanned(Expr::Int(BigInt::from(20)))),
            )),
        )],
        Box::new(spanned(Expr::Gt(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(20)))),
        ))),
    )))));
    let term = trans.translate_init(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

/// \A x \in {} : P(x)  — vacuous TRUE
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_forall_empty_domain_is_true() {
    let k = 0;
    let mut trans = BmcTranslator::new(k).unwrap();

    let expr = spanned(Expr::Forall(
        vec![bound_var("x", spanned(Expr::SetEnum(vec![])))],
        Box::new(spanned(Expr::Bool(false))),
    ));
    let term = trans.translate_init(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

/// \E x \in {} : P(x)  — FALSE
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_exists_empty_domain_is_false() {
    let k = 0;
    let mut trans = BmcTranslator::new(k).unwrap();

    let expr = spanned(Expr::Exists(
        vec![bound_var("x", spanned(Expr::SetEnum(vec![])))],
        Box::new(spanned(Expr::Bool(true))),
    ));
    let term = trans.translate_init(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
}

// === BOOLEAN domain tests ===

/// \A x \in BOOLEAN : x = TRUE  — UNSAT (FALSE is also in BOOLEAN)
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_forall_boolean_unsat() {
    let k = 0;
    let mut trans = BmcTranslator::new(k).unwrap();

    let expr = spanned(Expr::Forall(
        vec![bound_var(
            "x",
            spanned(Expr::Ident(
                "BOOLEAN".to_string(),
                tla_core::name_intern::NameId::INVALID,
            )),
        )],
        Box::new(spanned(Expr::Eq(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Bool(true))),
        ))),
    ));
    let term = trans.translate_init(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
}

/// \E x \in BOOLEAN : x = TRUE  — SAT
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_exists_boolean_sat() {
    let k = 0;
    let mut trans = BmcTranslator::new(k).unwrap();

    let expr = spanned(Expr::Exists(
        vec![bound_var(
            "x",
            spanned(Expr::Ident(
                "BOOLEAN".to_string(),
                tla_core::name_intern::NameId::INVALID,
            )),
        )],
        Box::new(spanned(Expr::Eq(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Bool(true))),
        ))),
    ));
    let term = trans.translate_init(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

// === Range quantifier tests ===

/// \A x \in 1..5 : x >= 1 /\ x <= 5  — SAT
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_forall_range_sat() {
    let k = 0;
    let mut trans = BmcTranslator::new(k).unwrap();

    let expr = spanned(Expr::Forall(
        vec![bound_var(
            "x",
            spanned(Expr::Range(
                Box::new(spanned(Expr::Int(BigInt::from(1)))),
                Box::new(spanned(Expr::Int(BigInt::from(5)))),
            )),
        )],
        Box::new(spanned(Expr::And(
            Box::new(spanned(Expr::Geq(
                Box::new(spanned(Expr::Ident(
                    "x".to_string(),
                    tla_core::name_intern::NameId::INVALID,
                ))),
                Box::new(spanned(Expr::Int(BigInt::from(1)))),
            ))),
            Box::new(spanned(Expr::Leq(
                Box::new(spanned(Expr::Ident(
                    "x".to_string(),
                    tla_core::name_intern::NameId::INVALID,
                ))),
                Box::new(spanned(Expr::Int(BigInt::from(5)))),
            ))),
        ))),
    ));
    let term = trans.translate_init(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

/// \E x \in 1..3 : x = 2  — SAT
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_exists_range_sat() {
    let k = 0;
    let mut trans = BmcTranslator::new(k).unwrap();

    let expr = spanned(Expr::Exists(
        vec![bound_var(
            "x",
            spanned(Expr::Range(
                Box::new(spanned(Expr::Int(BigInt::from(1)))),
                Box::new(spanned(Expr::Int(BigInt::from(3)))),
            )),
        )],
        Box::new(spanned(Expr::Eq(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(2)))),
        ))),
    ));
    let term = trans.translate_init(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

/// \E x \in 1..3 : x > 3  — UNSAT
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_exists_range_unsat() {
    let k = 0;
    let mut trans = BmcTranslator::new(k).unwrap();

    let expr = spanned(Expr::Exists(
        vec![bound_var(
            "x",
            spanned(Expr::Range(
                Box::new(spanned(Expr::Int(BigInt::from(1)))),
                Box::new(spanned(Expr::Int(BigInt::from(3)))),
            )),
        )],
        Box::new(spanned(Expr::Gt(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(3)))),
        ))),
    ));
    let term = trans.translate_init(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
}

// === Skolemization tests (large domains) ===

fn large_set_enum(n: i64) -> Spanned<Expr> {
    let elements: Vec<Spanned<Expr>> = (1..=n)
        .map(|i| spanned(Expr::Int(BigInt::from(i))))
        .collect();
    spanned(Expr::SetEnum(elements))
}

/// \E x \in {1..20} : x = 15  — Skolemized, SAT
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_skolem_exists_large_set_sat() {
    let k = 0;
    let mut trans = BmcTranslator::new(k).unwrap();

    let expr = spanned(Expr::Exists(
        vec![bound_var("x", large_set_enum(20))],
        Box::new(spanned(Expr::Eq(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(15)))),
        ))),
    ));
    let term = trans.translate_init(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

/// \E x \in {1..20} : x = 99  — Skolemized, UNSAT
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_skolem_exists_large_set_unsat() {
    let k = 0;
    let mut trans = BmcTranslator::new(k).unwrap();

    let expr = spanned(Expr::Exists(
        vec![bound_var("x", large_set_enum(20))],
        Box::new(spanned(Expr::Eq(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(99)))),
        ))),
    ));
    let term = trans.translate_init(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
}

/// \E x \in 1..50 : x = 42  — Skolemized range, SAT
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_skolem_exists_range_sat() {
    let k = 0;
    let mut trans = BmcTranslator::new(k).unwrap();

    let expr = spanned(Expr::Exists(
        vec![bound_var(
            "x",
            spanned(Expr::Range(
                Box::new(spanned(Expr::Int(BigInt::from(1)))),
                Box::new(spanned(Expr::Int(BigInt::from(50)))),
            )),
        )],
        Box::new(spanned(Expr::Eq(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(42)))),
        ))),
    ));
    let term = trans.translate_init(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

/// \E x \in 1..50 : x = 0  — Skolemized range, UNSAT
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_skolem_exists_range_unsat() {
    let k = 0;
    let mut trans = BmcTranslator::new(k).unwrap();

    let expr = spanned(Expr::Exists(
        vec![bound_var(
            "x",
            spanned(Expr::Range(
                Box::new(spanned(Expr::Int(BigInt::from(1)))),
                Box::new(spanned(Expr::Int(BigInt::from(50)))),
            )),
        )],
        Box::new(spanned(Expr::Eq(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(0)))),
        ))),
    ));
    let term = trans.translate_init(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
}

/// \E x \in 1..50 : x > 49  — Skolemized, SAT (x = 50)
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_skolem_exists_range_boundary_sat() {
    let k = 0;
    let mut trans = BmcTranslator::new(k).unwrap();

    let expr = spanned(Expr::Exists(
        vec![bound_var(
            "x",
            spanned(Expr::Range(
                Box::new(spanned(Expr::Int(BigInt::from(1)))),
                Box::new(spanned(Expr::Int(BigInt::from(50)))),
            )),
        )],
        Box::new(spanned(Expr::Gt(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(49)))),
        ))),
    ));
    let term = trans.translate_init(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

/// \E x \in 1..50 : x > 50  — Skolemized, UNSAT
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_skolem_exists_range_boundary_unsat() {
    let k = 0;
    let mut trans = BmcTranslator::new(k).unwrap();

    let expr = spanned(Expr::Exists(
        vec![bound_var(
            "x",
            spanned(Expr::Range(
                Box::new(spanned(Expr::Int(BigInt::from(1)))),
                Box::new(spanned(Expr::Int(BigInt::from(50)))),
            )),
        )],
        Box::new(spanned(Expr::Gt(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(50)))),
        ))),
    ));
    let term = trans.translate_init(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
}

// === Interaction with state variables ===

/// \E x \in 1..50 : x > y  where y is a BMC state variable set to 48
/// Tests Skolem constant interacting with BMC step-indexed variables
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_skolem_with_state_variable() {
    let k = 0;
    let mut trans = BmcTranslator::new(k).unwrap();
    trans.declare_var("y", TlaSort::Int).unwrap();

    // Init: y = 48
    let init = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "y".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(48)))),
    ));
    let init_term = trans.translate_init(&init).unwrap();
    trans.assert(init_term);

    // \E x \in 1..50 : x > y  — SAT (x = 49 or 50)
    let expr = spanned(Expr::Exists(
        vec![bound_var(
            "x",
            spanned(Expr::Range(
                Box::new(spanned(Expr::Int(BigInt::from(1)))),
                Box::new(spanned(Expr::Int(BigInt::from(50)))),
            )),
        )],
        Box::new(spanned(Expr::Gt(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Ident(
                "y".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
        ))),
    ));
    let term = trans.translate_init(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

/// \E x \in 1..50 : x > y  where y = 50  — UNSAT
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_skolem_with_state_variable_unsat() {
    let k = 0;
    let mut trans = BmcTranslator::new(k).unwrap();
    trans.declare_var("y", TlaSort::Int).unwrap();

    // Init: y = 50
    let init = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "y".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(50)))),
    ));
    let init_term = trans.translate_init(&init).unwrap();
    trans.assert(init_term);

    let expr = spanned(Expr::Exists(
        vec![bound_var(
            "x",
            spanned(Expr::Range(
                Box::new(spanned(Expr::Int(BigInt::from(1)))),
                Box::new(spanned(Expr::Int(BigInt::from(50)))),
            )),
        )],
        Box::new(spanned(Expr::Gt(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Ident(
                "y".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
        ))),
    ));
    let term = trans.translate_init(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
}

// === Error cases ===

/// Multi-bound quantifier should error
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_multi_bound_quantifier_error() {
    let k = 0;
    let mut trans = BmcTranslator::new(k).unwrap();

    let expr = spanned(Expr::Forall(
        vec![
            bound_var(
                "x",
                spanned(Expr::SetEnum(vec![spanned(Expr::Int(BigInt::from(1)))])),
            ),
            bound_var(
                "y",
                spanned(Expr::SetEnum(vec![spanned(Expr::Int(BigInt::from(2)))])),
            ),
        ],
        Box::new(spanned(Expr::Bool(true))),
    ));
    let result = trans.translate_init(&expr);
    assert!(result.is_err(), "multi-bound quantifier should error");
}

// === Negated quantifier tests (Fix #3822) ===

/// ~(\E x \in {1,2,3} : x > 2) should be FALSE (UNSAT)
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_negated_exists_set_enum_unsat() {
    let k = 0;
    let mut trans = BmcTranslator::new(k).unwrap();
    let expr = spanned(Expr::Not(Box::new(spanned(Expr::Exists(
        vec![bound_var(
            "x",
            spanned(Expr::SetEnum(vec![
                spanned(Expr::Int(BigInt::from(1))),
                spanned(Expr::Int(BigInt::from(2))),
                spanned(Expr::Int(BigInt::from(3))),
            ])),
        )],
        Box::new(spanned(Expr::Gt(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(2)))),
        ))),
    )))));
    let term = trans.translate_init(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
}

/// ~(\E x \in {1,2,3} : x > 5) should be TRUE (SAT)
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_negated_exists_set_enum_sat() {
    let k = 0;
    let mut trans = BmcTranslator::new(k).unwrap();
    let expr = spanned(Expr::Not(Box::new(spanned(Expr::Exists(
        vec![bound_var(
            "x",
            spanned(Expr::SetEnum(vec![
                spanned(Expr::Int(BigInt::from(1))),
                spanned(Expr::Int(BigInt::from(2))),
                spanned(Expr::Int(BigInt::from(3))),
            ])),
        )],
        Box::new(spanned(Expr::Gt(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(5)))),
        ))),
    )))));
    let term = trans.translate_init(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

/// ~(\E x \in {1..20} : x > 20) should be TRUE (SAT) — large set
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_negated_exists_large_set_sat() {
    let k = 0;
    let mut trans = BmcTranslator::new(k).unwrap();
    let expr = spanned(Expr::Not(Box::new(spanned(Expr::Exists(
        vec![bound_var("x", large_set_enum(20))],
        Box::new(spanned(Expr::Gt(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(20)))),
        ))),
    )))));
    let term = trans.translate_init(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

/// ~(\E x \in 1..50 : x > 20) should be FALSE (UNSAT) — range, witnesses exist
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_negated_exists_range_unsat() {
    let k = 0;
    let mut trans = BmcTranslator::new(k).unwrap();
    let expr = spanned(Expr::Not(Box::new(spanned(Expr::Exists(
        vec![bound_var(
            "x",
            spanned(Expr::Range(
                Box::new(spanned(Expr::Int(BigInt::from(1)))),
                Box::new(spanned(Expr::Int(BigInt::from(50)))),
            )),
        )],
        Box::new(spanned(Expr::Gt(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(20)))),
        ))),
    )))));
    let term = trans.translate_init(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
}

/// ~(\A x \in {1,2,3} : x > 0) should be FALSE (UNSAT) — all > 0
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_negated_forall_set_enum_unsat() {
    let k = 0;
    let mut trans = BmcTranslator::new(k).unwrap();
    let expr = spanned(Expr::Not(Box::new(spanned(Expr::Forall(
        vec![bound_var(
            "x",
            spanned(Expr::SetEnum(vec![
                spanned(Expr::Int(BigInt::from(1))),
                spanned(Expr::Int(BigInt::from(2))),
                spanned(Expr::Int(BigInt::from(3))),
            ])),
        )],
        Box::new(spanned(Expr::Gt(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(0)))),
        ))),
    )))));
    let term = trans.translate_init(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
}

/// ~(\A x \in {1,2,3} : x > 2) should be TRUE (SAT) — 1 and 2 are not > 2
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_negated_forall_set_enum_sat() {
    let k = 0;
    let mut trans = BmcTranslator::new(k).unwrap();
    let expr = spanned(Expr::Not(Box::new(spanned(Expr::Forall(
        vec![bound_var(
            "x",
            spanned(Expr::SetEnum(vec![
                spanned(Expr::Int(BigInt::from(1))),
                spanned(Expr::Int(BigInt::from(2))),
                spanned(Expr::Int(BigInt::from(3))),
            ])),
        )],
        Box::new(spanned(Expr::Gt(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(2)))),
        ))),
    )))));
    let term = trans.translate_init(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

// === Optimized quantifier expansion tests ===

/// Singleton set domain: \A x \in {5} : x = 5  — SAT (trivially)
/// Tests the singleton fast path in expand_bmc_set_enum_quantifier.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_forall_singleton_set_sat() {
    let k = 0;
    let mut trans = BmcTranslator::new(k).unwrap();

    let expr = spanned(Expr::Forall(
        vec![bound_var(
            "x",
            spanned(Expr::SetEnum(vec![spanned(Expr::Int(BigInt::from(5)))])),
        )],
        Box::new(spanned(Expr::Eq(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(5)))),
        ))),
    ));
    let term = trans.translate_init(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

/// Singleton range: \E x \in 7..7 : x > 6  — SAT
/// Tests the singleton fast path in expand_bmc_range_quantifier.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_exists_singleton_range_sat() {
    let k = 0;
    let mut trans = BmcTranslator::new(k).unwrap();

    let expr = spanned(Expr::Exists(
        vec![bound_var(
            "x",
            spanned(Expr::Range(
                Box::new(spanned(Expr::Int(BigInt::from(7)))),
                Box::new(spanned(Expr::Int(BigInt::from(7)))),
            )),
        )],
        Box::new(spanned(Expr::Gt(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(6)))),
        ))),
    ));
    let term = trans.translate_init(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

/// Constant folding: \A x \in {1, 2, 3} : TRUE  — SAT
/// Expanded terms are all TRUE (identity for AND), constant folding should collapse.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_forall_trivially_true_body() {
    let k = 0;
    let mut trans = BmcTranslator::new(k).unwrap();

    let expr = spanned(Expr::Forall(
        vec![bound_var(
            "x",
            spanned(Expr::SetEnum(vec![
                spanned(Expr::Int(BigInt::from(1))),
                spanned(Expr::Int(BigInt::from(2))),
                spanned(Expr::Int(BigInt::from(3))),
            ])),
        )],
        Box::new(spanned(Expr::Bool(true))),
    ));
    let term = trans.translate_init(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

/// Constant folding: \E x \in {1, 2, 3} : FALSE  — UNSAT
/// All expanded terms are FALSE (identity for OR), should collapse to FALSE.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_exists_trivially_false_body() {
    let k = 0;
    let mut trans = BmcTranslator::new(k).unwrap();

    let expr = spanned(Expr::Exists(
        vec![bound_var(
            "x",
            spanned(Expr::SetEnum(vec![
                spanned(Expr::Int(BigInt::from(1))),
                spanned(Expr::Int(BigInt::from(2))),
                spanned(Expr::Int(BigInt::from(3))),
            ])),
        )],
        Box::new(spanned(Expr::Bool(false))),
    ));
    let term = trans.translate_init(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
}

/// Balanced tree for medium-sized range: \A x \in 1..10 : x >= 1 /\ x <= 10  — SAT
/// Ensures the balanced AND tree produces correct results.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_forall_balanced_range_sat() {
    let k = 0;
    let mut trans = BmcTranslator::new(k).unwrap();

    let expr = spanned(Expr::Forall(
        vec![bound_var(
            "x",
            spanned(Expr::Range(
                Box::new(spanned(Expr::Int(BigInt::from(1)))),
                Box::new(spanned(Expr::Int(BigInt::from(10)))),
            )),
        )],
        Box::new(spanned(Expr::And(
            Box::new(spanned(Expr::Geq(
                Box::new(spanned(Expr::Ident(
                    "x".to_string(),
                    tla_core::name_intern::NameId::INVALID,
                ))),
                Box::new(spanned(Expr::Int(BigInt::from(1)))),
            ))),
            Box::new(spanned(Expr::Leq(
                Box::new(spanned(Expr::Ident(
                    "x".to_string(),
                    tla_core::name_intern::NameId::INVALID,
                ))),
                Box::new(spanned(Expr::Int(BigInt::from(10)))),
            ))),
        ))),
    ));
    let term = trans.translate_init(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

/// Balanced tree for medium-sized range: \A x \in 1..10 : x > 5  — UNSAT
/// Ensures the balanced AND tree correctly detects failure.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_forall_balanced_range_unsat() {
    let k = 0;
    let mut trans = BmcTranslator::new(k).unwrap();

    let expr = spanned(Expr::Forall(
        vec![bound_var(
            "x",
            spanned(Expr::Range(
                Box::new(spanned(Expr::Int(BigInt::from(1)))),
                Box::new(spanned(Expr::Int(BigInt::from(10)))),
            )),
        )],
        Box::new(spanned(Expr::Gt(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(5)))),
        ))),
    ));
    let term = trans.translate_init(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
}

/// Balanced OR for exists with 8-element set: \E x \in {1..8} : x = 4  — SAT
/// Exercises balanced tree on an exists disjunction.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_exists_balanced_set_sat() {
    let k = 0;
    let mut trans = BmcTranslator::new(k).unwrap();

    let elements: Vec<Spanned<Expr>> = (1..=8)
        .map(|i| spanned(Expr::Int(BigInt::from(i))))
        .collect();

    let expr = spanned(Expr::Exists(
        vec![bound_var("x", spanned(Expr::SetEnum(elements)))],
        Box::new(spanned(Expr::Eq(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(4)))),
        ))),
    ));
    let term = trans.translate_init(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

/// Balanced OR for exists with 8-element set: \E x \in {1..8} : x > 10  — UNSAT
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_exists_balanced_set_unsat() {
    let k = 0;
    let mut trans = BmcTranslator::new(k).unwrap();

    let elements: Vec<Spanned<Expr>> = (1..=8)
        .map(|i| spanned(Expr::Int(BigInt::from(i))))
        .collect();

    let expr = spanned(Expr::Exists(
        vec![bound_var("x", spanned(Expr::SetEnum(elements)))],
        Box::new(spanned(Expr::Gt(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(10)))),
        ))),
    ));
    let term = trans.translate_init(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
}
