// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// === Quantifier expansion tests (Part of #1181) ===

/// Helper to create a BoundVar with a domain
fn bound_var(name: &str, domain: Spanned<Expr>) -> BoundVar {
    BoundVar {
        name: spanned(name.to_string()),
        domain: Some(Box::new(domain)),
        pattern: None,
    }
}

/// \A x \in {1, 2, 3} : x > 0  should be SAT (all > 0)
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_set_enum_sat() {
    let mut trans = Z4Translator::new();
    // \A x \in {1, 2, 3} : x > 0
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
    let term = trans.translate_bool(&expr).unwrap();
    trans.assert(term);
    // TRUE: 1>0 /\ 2>0 /\ 3>0
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

/// \A x \in {1, 2, -1} : x > 0  should be UNSAT (not all > 0)
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_set_enum_unsat() {
    let mut trans = Z4Translator::new();
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
    let term = trans.translate_bool(&expr).unwrap();
    trans.assert(term);
    // FALSE: 1>0 /\ 2>0 /\ (-1>0) = FALSE
    assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
}

/// \E x \in {-1, 0, 1} : x > 0  should be SAT (1 > 0)
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_exists_set_enum_sat() {
    let mut trans = Z4Translator::new();
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
    let term = trans.translate_bool(&expr).unwrap();
    trans.assert(term);
    // TRUE: (-1>0) \/ (0>0) \/ (1>0) = TRUE
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

/// \E x \in {-2, -1} : x > 0  should be UNSAT (none > 0)
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_exists_set_enum_unsat() {
    let mut trans = Z4Translator::new();
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
    let term = trans.translate_bool(&expr).unwrap();
    trans.assert(term);
    // FALSE: (-2>0) \/ (-1>0) = FALSE
    assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
}

/// ~(\E x \in {1, 2, 3} : x > 2)  should be UNSAT (3 > 2 exists)
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_not_exists_set_enum_unsat() {
    let mut trans = Z4Translator::new();
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
    let term = trans.translate_bool(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
}

/// ~(\E x \in {1, 2, 3} : x > 5)  should be SAT (no witness exists)
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_not_exists_set_enum_sat() {
    let mut trans = Z4Translator::new();
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
    let term = trans.translate_bool(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

/// ~(\E x \in 1..20 : x > 20)  should be SAT and avoid exists Skolemization
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_not_exists_range_skolem_sat() {
    let mut trans = Z4Translator::new();
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
    let term = trans.translate_bool(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

/// \A x \in {} : x > 0  should be TRUE (vacuous truth)
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_empty_domain_is_true() {
    let mut trans = Z4Translator::new();
    let expr = spanned(Expr::Forall(
        vec![bound_var("x", spanned(Expr::SetEnum(vec![])))],
        Box::new(spanned(Expr::Gt(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(0)))),
        ))),
    ));
    let term = trans.translate_bool(&expr).unwrap();
    trans.assert(term);
    // \A x \in {} : P(x) is TRUE
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

/// \E x \in {} : x > 0  should be FALSE
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_exists_empty_domain_is_false() {
    let mut trans = Z4Translator::new();
    let expr = spanned(Expr::Exists(
        vec![bound_var("x", spanned(Expr::SetEnum(vec![])))],
        Box::new(spanned(Expr::Gt(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(0)))),
        ))),
    ));
    let term = trans.translate_bool(&expr).unwrap();
    trans.assert(term);
    // \E x \in {} : P(x) is FALSE
    assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
}

/// \A x \in BOOLEAN : (x = TRUE) \/ (x = FALSE)  should be TRUE
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_boolean_domain() {
    let mut trans = Z4Translator::new();
    let expr = spanned(Expr::Forall(
        vec![bound_var(
            "x",
            spanned(Expr::Ident(
                "BOOLEAN".to_string(),
                tla_core::name_intern::NameId::INVALID,
            )),
        )],
        Box::new(spanned(Expr::Or(
            Box::new(spanned(Expr::Eq(
                Box::new(spanned(Expr::Ident(
                    "x".to_string(),
                    tla_core::name_intern::NameId::INVALID,
                ))),
                Box::new(spanned(Expr::Bool(true))),
            ))),
            Box::new(spanned(Expr::Eq(
                Box::new(spanned(Expr::Ident(
                    "x".to_string(),
                    tla_core::name_intern::NameId::INVALID,
                ))),
                Box::new(spanned(Expr::Bool(false))),
            ))),
        ))),
    ));
    let term = trans.translate_bool(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

/// \E x \in BOOLEAN : x = TRUE  should be TRUE
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_exists_boolean_domain() {
    let mut trans = Z4Translator::new();
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
    let term = trans.translate_bool(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

/// \A x \in 1..5 : x >= 1 /\ x <= 5  should be TRUE
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_range_domain() {
    let mut trans = Z4Translator::new();
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
    let term = trans.translate_bool(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

/// \E x \in 1..3 : x = 2  should be TRUE
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_exists_range_domain() {
    let mut trans = Z4Translator::new();
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
    let term = trans.translate_bool(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

/// Multi-bound quantifier should produce error (not supported)
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_multi_bound_unsupported() {
    let mut trans = Z4Translator::new();
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
        Box::new(spanned(Expr::Gt(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(0)))),
        ))),
    ));
    let result = trans.translate_bool(&expr);
    assert!(
        result.is_err(),
        "multi-bound quantifier should produce error"
    );
}

/// \A x \in {y \in {1, 2, 3} : y > 1} : x > 1  should be TRUE
/// Tests SetFilter domain transform for quantifiers
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_set_filter_domain() {
    let mut trans = Z4Translator::new();
    // \A x \in {y \in {1, 2, 3} : y > 1} : x > 1
    let filter_domain = spanned(Expr::SetFilter(
        BoundVar {
            name: spanned("y".to_string()),
            domain: Some(Box::new(spanned(Expr::SetEnum(vec![
                spanned(Expr::Int(BigInt::from(1))),
                spanned(Expr::Int(BigInt::from(2))),
                spanned(Expr::Int(BigInt::from(3))),
            ])))),
            pattern: None,
        },
        Box::new(spanned(Expr::Gt(
            Box::new(spanned(Expr::Ident(
                "y".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(1)))),
        ))),
    ));
    let expr = spanned(Expr::Forall(
        vec![bound_var("x", filter_domain)],
        Box::new(spanned(Expr::Gt(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(1)))),
        ))),
    ));
    let term = trans.translate_bool(&expr).unwrap();
    trans.assert(term);
    // {y \in {1,2,3} : y > 1} = {2, 3}, and \A x \in {2,3} : x > 1 is TRUE
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

/// \A x \in BOOLEAN : x = TRUE  should be FALSE (UNSAT)
/// Catches bugs where boolean expansion only substitutes one branch
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_boolean_domain_unsat() {
    let mut trans = Z4Translator::new();
    // \A x \in BOOLEAN : x = TRUE
    // Expansion: (TRUE = TRUE) /\ (FALSE = TRUE) = TRUE /\ FALSE = FALSE
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
    let term = trans.translate_bool(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
}

/// \E x \in BOOLEAN : (x = TRUE /\ x = FALSE)  should be FALSE (UNSAT)
/// Catches bugs where exists doesn't properly disjoin both branches
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_exists_boolean_domain_unsat() {
    let mut trans = Z4Translator::new();
    // \E x \in BOOLEAN : (x = TRUE /\ x = FALSE)
    // Expansion: (TRUE=TRUE /\ TRUE=FALSE) \/ (FALSE=TRUE /\ FALSE=FALSE)
    //          = (TRUE /\ FALSE) \/ (FALSE /\ TRUE) = FALSE
    let expr = spanned(Expr::Exists(
        vec![bound_var(
            "x",
            spanned(Expr::Ident(
                "BOOLEAN".to_string(),
                tla_core::name_intern::NameId::INVALID,
            )),
        )],
        Box::new(spanned(Expr::And(
            Box::new(spanned(Expr::Eq(
                Box::new(spanned(Expr::Ident(
                    "x".to_string(),
                    tla_core::name_intern::NameId::INVALID,
                ))),
                Box::new(spanned(Expr::Bool(true))),
            ))),
            Box::new(spanned(Expr::Eq(
                Box::new(spanned(Expr::Ident(
                    "x".to_string(),
                    tla_core::name_intern::NameId::INVALID,
                ))),
                Box::new(spanned(Expr::Bool(false))),
            ))),
        ))),
    ));
    let term = trans.translate_bool(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
}

/// \A x \in 1..3 : x > 3  should be FALSE (UNSAT)
/// Catches bugs where range expansion misses elements
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_range_domain_unsat() {
    let mut trans = Z4Translator::new();
    // \A x \in 1..3 : x > 3
    // Expansion: (1>3) /\ (2>3) /\ (3>3) = FALSE
    let expr = spanned(Expr::Forall(
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
    let term = trans.translate_bool(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
}

/// \E x \in 1..3 : x > 3  should be FALSE (UNSAT)
/// Catches bugs where range exists misses boundary
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_exists_range_domain_unsat() {
    let mut trans = Z4Translator::new();
    // \E x \in 1..3 : x > 3
    // Expansion: (1>3) \/ (2>3) \/ (3>3) = FALSE
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
    let term = trans.translate_bool(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
}

// === Skolemization tests ===

/// Build a large set enumeration {1, 2, ..., n} for Skolemization testing.
fn large_set_enum(n: i64) -> Spanned<Expr> {
    let elements: Vec<Spanned<Expr>> = (1..=n)
        .map(|i| spanned(Expr::Int(BigInt::from(i))))
        .collect();
    spanned(Expr::SetEnum(elements))
}

/// \E x \in {1..20} : x = 15  — Skolemized (set > threshold), SAT
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_skolem_exists_large_set_enum_sat() {
    let mut trans = Z4Translator::new();
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
    let term = trans.translate_bool(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

/// \E x \in {1..20} : x = 99  — Skolemized, UNSAT (99 not in set)
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_skolem_exists_large_set_enum_unsat() {
    let mut trans = Z4Translator::new();
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
    let term = trans.translate_bool(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
}

/// \E x \in {1..20} : x > 0  — Skolemized, SAT (all elements > 0)
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_skolem_exists_large_set_enum_predicate_sat() {
    let mut trans = Z4Translator::new();
    let expr = spanned(Expr::Exists(
        vec![bound_var("x", large_set_enum(20))],
        Box::new(spanned(Expr::Gt(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(0)))),
        ))),
    ));
    let term = trans.translate_bool(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

/// \E x \in {1..20} : x > 20  — Skolemized, UNSAT (no element > 20)
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_skolem_exists_large_set_enum_predicate_unsat() {
    let mut trans = Z4Translator::new();
    let expr = spanned(Expr::Exists(
        vec![bound_var("x", large_set_enum(20))],
        Box::new(spanned(Expr::Gt(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(20)))),
        ))),
    ));
    let term = trans.translate_bool(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
}

// === Skolemized range quantifier tests ===

/// \E x \in 1..50 : x = 42  — Skolemized range, SAT
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_skolem_exists_range_sat() {
    let mut trans = Z4Translator::new();
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
    let term = trans.translate_bool(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

/// \E x \in 1..50 : x = 0  — Skolemized range, UNSAT (0 not in 1..50)
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_skolem_exists_range_unsat() {
    let mut trans = Z4Translator::new();
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
    let term = trans.translate_bool(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
}

/// \E x \in 1..50 : x > 49  — Skolemized range, SAT (x = 50 works)
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_skolem_exists_range_boundary_sat() {
    let mut trans = Z4Translator::new();
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
    let term = trans.translate_bool(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

/// \E x \in 1..50 : x > 50  — Skolemized range, UNSAT
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_skolem_exists_range_boundary_unsat() {
    let mut trans = Z4Translator::new();
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
    let term = trans.translate_bool(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
}

// === CHOOSE tests ===

/// Helper to create a single BoundVar (used for CHOOSE which takes a single bound)
fn choose_bound(name: &str, domain: Spanned<Expr>) -> BoundVar {
    BoundVar {
        name: spanned(name.to_string()),
        domain: Some(Box::new(domain)),
        pattern: None,
    }
}

/// CHOOSE x \in {1, 2, 3} : x > 2  should return 3
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_choose_set_enum_int() {
    let mut trans = Z4Translator::new();
    // CHOOSE x \in {1, 2, 3} : x > 2
    let expr = spanned(Expr::Choose(
        choose_bound(
            "x",
            spanned(Expr::SetEnum(vec![
                spanned(Expr::Int(BigInt::from(1))),
                spanned(Expr::Int(BigInt::from(2))),
                spanned(Expr::Int(BigInt::from(3))),
            ])),
        ),
        Box::new(spanned(Expr::Gt(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(2)))),
        ))),
    ));
    // Translate as Int (CHOOSE returns an Int here)
    let term = trans.translate_int(&expr).unwrap();
    // The result should be 3 (the only element > 2)
    let three = trans.solver_mut().int_const(3);
    let eq = trans.solver_mut().try_eq(term, three).unwrap();
    trans.assert(eq);
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

/// CHOOSE x \in {1, 2, 3} : x > 10  should be UNSAT (no such element)
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_choose_set_enum_unsat() {
    let mut trans = Z4Translator::new();
    let expr = spanned(Expr::Choose(
        choose_bound(
            "x",
            spanned(Expr::SetEnum(vec![
                spanned(Expr::Int(BigInt::from(1))),
                spanned(Expr::Int(BigInt::from(2))),
                spanned(Expr::Int(BigInt::from(3))),
            ])),
        ),
        Box::new(spanned(Expr::Gt(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(10)))),
        ))),
    ));
    // CHOOSE asserts membership + predicate, so the solver should be UNSAT
    let _term = trans.translate_int(&expr).unwrap();
    assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
}

/// CHOOSE x \in 1..10 : x = 7  should return 7
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_choose_range_int() {
    let mut trans = Z4Translator::new();
    let expr = spanned(Expr::Choose(
        choose_bound(
            "x",
            spanned(Expr::Range(
                Box::new(spanned(Expr::Int(BigInt::from(1)))),
                Box::new(spanned(Expr::Int(BigInt::from(10)))),
            )),
        ),
        Box::new(spanned(Expr::Eq(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(7)))),
        ))),
    ));
    let term = trans.translate_int(&expr).unwrap();
    let seven = trans.solver_mut().int_const(7);
    let eq = trans.solver_mut().try_eq(term, seven).unwrap();
    trans.assert(eq);
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

/// CHOOSE x \in 1..10 : x > 5  — multiple solutions, solver picks one
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_choose_range_multiple_witnesses() {
    let mut trans = Z4Translator::new();
    let expr = spanned(Expr::Choose(
        choose_bound(
            "x",
            spanned(Expr::Range(
                Box::new(spanned(Expr::Int(BigInt::from(1)))),
                Box::new(spanned(Expr::Int(BigInt::from(10)))),
            )),
        ),
        Box::new(spanned(Expr::Gt(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(5)))),
        ))),
    ));
    let _term = trans.translate_int(&expr).unwrap();
    // Should be SAT — there exist witnesses (6, 7, 8, 9, 10)
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

/// CHOOSE x \in BOOLEAN : x = TRUE  should return TRUE
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_choose_boolean_domain() {
    let mut trans = Z4Translator::new();
    let expr = spanned(Expr::Choose(
        choose_bound(
            "x",
            spanned(Expr::Ident(
                "BOOLEAN".to_string(),
                tla_core::name_intern::NameId::INVALID,
            )),
        ),
        Box::new(spanned(Expr::Eq(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Bool(true))),
        ))),
    ));
    // Translate as Bool
    let term = trans.translate_bool(&expr).unwrap();
    // The result should be TRUE
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

/// CHOOSE x \in BOOLEAN : (x = TRUE /\ x = FALSE) — UNSAT, impossible predicate
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_choose_boolean_unsat() {
    let mut trans = Z4Translator::new();
    let expr = spanned(Expr::Choose(
        choose_bound(
            "x",
            spanned(Expr::Ident(
                "BOOLEAN".to_string(),
                tla_core::name_intern::NameId::INVALID,
            )),
        ),
        Box::new(spanned(Expr::And(
            Box::new(spanned(Expr::Eq(
                Box::new(spanned(Expr::Ident(
                    "x".to_string(),
                    tla_core::name_intern::NameId::INVALID,
                ))),
                Box::new(spanned(Expr::Bool(true))),
            ))),
            Box::new(spanned(Expr::Eq(
                Box::new(spanned(Expr::Ident(
                    "x".to_string(),
                    tla_core::name_intern::NameId::INVALID,
                ))),
                Box::new(spanned(Expr::Bool(false))),
            ))),
        ))),
    ));
    let _term = trans.translate_bool(&expr).unwrap();
    assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
}

/// CHOOSE x \in {1, 2, 3} : TRUE  — any element is valid
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_choose_trivial_predicate() {
    let mut trans = Z4Translator::new();
    let expr = spanned(Expr::Choose(
        choose_bound(
            "x",
            spanned(Expr::SetEnum(vec![
                spanned(Expr::Int(BigInt::from(1))),
                spanned(Expr::Int(BigInt::from(2))),
                spanned(Expr::Int(BigInt::from(3))),
            ])),
        ),
        Box::new(spanned(Expr::Bool(true))),
    ));
    let _term = trans.translate_int(&expr).unwrap();
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

// === CHOOSE over SetFilter domain ===

/// CHOOSE y \in {z \in {1,2,3,4,5} : z > 3} : y = 4
/// Rewrites to CHOOSE y \in {1,2,3,4,5} : y > 3 /\ y = 4  -- SAT, result = 4
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_choose_set_filter_int() {
    let mut trans = Z4Translator::new();

    let inner_set = spanned(Expr::SetEnum(vec![
        spanned(Expr::Int(BigInt::from(1))),
        spanned(Expr::Int(BigInt::from(2))),
        spanned(Expr::Int(BigInt::from(3))),
        spanned(Expr::Int(BigInt::from(4))),
        spanned(Expr::Int(BigInt::from(5))),
    ]));

    let filter_bound = BoundVar {
        name: spanned("z".to_string()),
        domain: Some(Box::new(inner_set)),
        pattern: None,
    };

    let filter_pred = spanned(Expr::Gt(
        Box::new(spanned(Expr::Ident(
            "z".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(3)))),
    ));

    let filtered_domain = spanned(Expr::SetFilter(filter_bound, Box::new(filter_pred)));

    let expr = spanned(Expr::Choose(
        choose_bound("y", filtered_domain),
        Box::new(spanned(Expr::Eq(
            Box::new(spanned(Expr::Ident(
                "y".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(4)))),
        ))),
    ));

    let term = trans.translate_int(&expr).unwrap();
    let four = trans.solver_mut().int_const(4);
    let eq = trans.solver_mut().try_eq(term, four).unwrap();
    trans.assert(eq);
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

/// CHOOSE y \in {z \in {1,2,3} : z > 5} : TRUE  -- UNSAT (empty filtered domain)
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_choose_set_filter_empty_unsat() {
    let mut trans = Z4Translator::new();

    let inner_set = spanned(Expr::SetEnum(vec![
        spanned(Expr::Int(BigInt::from(1))),
        spanned(Expr::Int(BigInt::from(2))),
        spanned(Expr::Int(BigInt::from(3))),
    ]));

    let filter_bound = BoundVar {
        name: spanned("z".to_string()),
        domain: Some(Box::new(inner_set)),
        pattern: None,
    };

    let filter_pred = spanned(Expr::Gt(
        Box::new(spanned(Expr::Ident(
            "z".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(5)))),
    ));

    let filtered_domain = spanned(Expr::SetFilter(filter_bound, Box::new(filter_pred)));

    let expr = spanned(Expr::Choose(
        choose_bound("y", filtered_domain),
        Box::new(spanned(Expr::Bool(true))),
    ));

    let _term = trans.translate_int(&expr).unwrap();
    // The filter condition z > 5 cannot be satisfied by any element in {1,2,3},
    // so the conjunction (membership AND filter_pred) is UNSAT.
    assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
}

// === Interaction tests: Skolemized \E with other constraints ===

/// \E x \in 1..50 : x > y  where y is a declared Int variable
/// Tests that Skolem constants interact correctly with other solver variables
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_skolem_range_with_external_constraint() {
    let mut trans = Z4Translator::new();
    // Declare y as an Int variable
    let _y = trans
        .declare_var("y", crate::translate::TlaSort::Int)
        .unwrap();

    // Assert y = 48
    let y_term = trans.get_var("y").unwrap().1;
    let forty_eight = trans.solver_mut().int_const(48);
    let y_eq = trans.solver_mut().try_eq(y_term, forty_eight).unwrap();
    trans.assert(y_eq);

    // \E x \in 1..50 : x > y  — should be SAT (x = 49 or 50)
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
    let term = trans.translate_bool(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

/// \E x \in 1..50 : x > y  where y = 50  — UNSAT
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_skolem_range_with_external_constraint_unsat() {
    let mut trans = Z4Translator::new();
    let _y = trans
        .declare_var("y", crate::translate::TlaSort::Int)
        .unwrap();
    let y_term = trans.get_var("y").unwrap().1;
    let fifty = trans.solver_mut().int_const(50);
    let y_eq = trans.solver_mut().try_eq(y_term, fifty).unwrap();
    trans.assert(y_eq);

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
    let term = trans.translate_bool(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
}

// === Negated quantifier tests (Fix #3822) ===

/// ~(\E x \in {1,2,3} : x > 2) should be FALSE (UNSAT) — 3 > 2 is a witness
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_negated_exists_set_enum_unsat() {
    let mut trans = Z4Translator::new();
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
    let term = trans.translate_bool(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
}

/// ~(\E x \in {1,2,3} : x > 5) should be TRUE (SAT) — no x > 5
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_negated_exists_set_enum_sat() {
    let mut trans = Z4Translator::new();
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
    let term = trans.translate_bool(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

/// ~(\E x \in {1..20} : x > 20) should be TRUE (SAT) — large set, no witness
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_negated_exists_large_set_sat() {
    let mut trans = Z4Translator::new();
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
    let term = trans.translate_bool(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

/// ~(\E x \in 1..50 : x > 20) should be FALSE (UNSAT) — range, witnesses exist
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_negated_exists_range_unsat() {
    let mut trans = Z4Translator::new();
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
    let term = trans.translate_bool(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
}

/// ~(\A x \in {1,2,3} : x > 0) should be FALSE (UNSAT) — all > 0
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_negated_forall_set_enum_unsat() {
    let mut trans = Z4Translator::new();
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
    let term = trans.translate_bool(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
}

/// ~(\A x \in {1,2,3} : x > 2) should be TRUE (SAT) — 1 and 2 are not > 2
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_negated_forall_set_enum_sat() {
    let mut trans = Z4Translator::new();
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
    let term = trans.translate_bool(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

// === Optimized quantifier expansion tests ===

/// Singleton set domain: \A x \in {5} : x = 5  — SAT
/// Tests the singleton fast path in expand_set_enum_quantifier.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_singleton_set_sat() {
    let mut trans = Z4Translator::new();
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
    let term = trans.translate_bool(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

/// Singleton range: \E x \in 7..7 : x > 6  — SAT
/// Tests the singleton fast path in expand_range_quantifier.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_exists_singleton_range_sat() {
    let mut trans = Z4Translator::new();
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
    let term = trans.translate_bool(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

/// Constant folding: \A x \in {1, 2, 3} : TRUE  — SAT
/// Expanded terms are all TRUE (identity for AND), constant folding should collapse.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_trivially_true_body() {
    let mut trans = Z4Translator::new();
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
    let term = trans.translate_bool(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

/// Constant folding: \E x \in {1, 2, 3} : FALSE  — UNSAT
/// All expanded terms are FALSE (identity for OR), should collapse to FALSE.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_exists_trivially_false_body() {
    let mut trans = Z4Translator::new();
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
    let term = trans.translate_bool(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
}

/// Balanced tree for medium-sized range: \A x \in 1..10 : x >= 1 /\ x <= 10  — SAT
/// Ensures the balanced AND tree produces correct results.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_balanced_range_sat() {
    let mut trans = Z4Translator::new();
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
    let term = trans.translate_bool(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

/// Balanced tree for medium-sized range: \A x \in 1..10 : x > 5  — UNSAT
/// Ensures the balanced AND tree correctly detects failure.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_balanced_range_unsat() {
    let mut trans = Z4Translator::new();
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
    let term = trans.translate_bool(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
}

/// Balanced OR for exists with 8-element set: \E x \in {1..8} : x = 4  — SAT
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_exists_balanced_set_sat() {
    let mut trans = Z4Translator::new();
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
    let term = trans.translate_bool(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

/// Balanced OR for exists with 8-element set: \E x \in {1..8} : x > 10  — UNSAT
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_exists_balanced_set_unsat() {
    let mut trans = Z4Translator::new();
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
    let term = trans.translate_bool(&expr).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
}
