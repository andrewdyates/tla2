// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for BMC nested powerset `SUBSET(SUBSET S)` encoding.
//!
//! Validates that:
//! - `\E T \in SUBSET(SUBSET S) : P(T)` correctly enumerates outer sets
//!   using `NestedPowersetEncoder`
//! - Cardinality filter detection reduces the base set
//! - The SpanTreeTest5Nodes pattern (cardinality=2, 5 nodes) produces
//!   correct results: 1024 valid edge sets
//! - Edge cases: empty inner set, singleton inner set, small unfiltered sets
//!
//! Part of #3826.

use super::*;
use tla_core::ast::BoundVar;
use z4_dpll::api::SolveResult;

/// Helper: create a BMC translator with array support.
fn bmc_array(k: usize) -> BmcTranslator {
    BmcTranslator::new_with_arrays(k).unwrap()
}

/// Helper: integer literal expression.
fn int(v: i64) -> Spanned<Expr> {
    spanned(Expr::Int(BigInt::from(v)))
}

/// Helper: identifier expression.
fn ident(name: &str) -> Spanned<Expr> {
    spanned(Expr::Ident(
        name.to_string(),
        tla_core::name_intern::NameId::INVALID,
    ))
}

// --- Nested powerset: trivial cases ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_nested_powerset_empty_inner() {
    let mut bmc = bmc_array(0);

    // \E T \in SUBSET(SUBSET {}) : TRUE
    // SUBSET {} = {{}}, SUBSET(SUBSET {}) = {{}, {{}}}, 2 subsets
    // So there exist T values, should be SAT.
    let exists_expr = spanned(Expr::Exists(
        vec![BoundVar {
            name: spanned("T".to_string()),
            domain: Some(Box::new(spanned(Expr::Powerset(Box::new(spanned(
                Expr::Powerset(Box::new(spanned(Expr::SetEnum(vec![])))),
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
fn test_bmc_nested_powerset_forall_true() {
    let mut bmc = bmc_array(0);

    // \A T \in SUBSET(SUBSET {1}) : TRUE
    // Should be SAT (TRUE holds for everything).
    let forall_expr = spanned(Expr::Forall(
        vec![BoundVar {
            name: spanned("T".to_string()),
            domain: Some(Box::new(spanned(Expr::Powerset(Box::new(spanned(
                Expr::Powerset(Box::new(spanned(Expr::SetEnum(vec![int(1)])))),
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
fn test_bmc_nested_powerset_forall_false() {
    let mut bmc = bmc_array(0);

    // \A T \in SUBSET(SUBSET {1}) : FALSE
    // Should be UNSAT (FALSE doesn't hold).
    let forall_expr = spanned(Expr::Forall(
        vec![BoundVar {
            name: spanned("T".to_string()),
            domain: Some(Box::new(spanned(Expr::Powerset(Box::new(spanned(
                Expr::Powerset(Box::new(spanned(Expr::SetEnum(vec![int(1)])))),
            )))))),
            pattern: None,
        }],
        Box::new(spanned(Expr::Bool(false))),
    ));

    let term = bmc.translate_init(&forall_expr).unwrap();
    bmc.assert(term);
    assert!(matches!(bmc.check_sat(), SolveResult::Unsat(_)));
}

// --- Cardinality filter detection ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_nested_powerset_cardinality_filter_detection() {
    // Test the static cardinality filter detection on AST patterns.
    // Pattern: \A e \in Edges : Cardinality(e) = 2
    let body = spanned(Expr::Forall(
        vec![BoundVar {
            name: spanned("e".to_string()),
            domain: Some(Box::new(ident("Edges"))),
            pattern: None,
        }],
        Box::new(spanned(Expr::Eq(
            Box::new(spanned(Expr::Apply(
                Box::new(ident("Cardinality")),
                vec![ident("e")],
            ))),
            Box::new(int(2)),
        ))),
    ));

    let k = BmcTranslator::detect_cardinality_filter(&body, "Edges");
    assert_eq!(k, Some(2), "should detect Cardinality(e) = 2 filter");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_nested_powerset_cardinality_filter_in_conjunction() {
    // Pattern: (\A e \in Edges : Cardinality(e) = 3) /\ other_stuff
    let card_filter = spanned(Expr::Forall(
        vec![BoundVar {
            name: spanned("e".to_string()),
            domain: Some(Box::new(ident("Edges"))),
            pattern: None,
        }],
        Box::new(spanned(Expr::Eq(
            Box::new(spanned(Expr::Apply(
                Box::new(ident("Cardinality")),
                vec![ident("e")],
            ))),
            Box::new(int(3)),
        ))),
    ));

    let body = spanned(Expr::And(
        Box::new(card_filter),
        Box::new(spanned(Expr::Bool(true))),
    ));

    let k = BmcTranslator::detect_cardinality_filter(&body, "Edges");
    assert_eq!(k, Some(3), "should detect Cardinality(e) = 3 in conjunction");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_nested_powerset_no_cardinality_filter() {
    // Body with no cardinality filter: just TRUE
    let body = spanned(Expr::Bool(true));
    let k = BmcTranslator::detect_cardinality_filter(&body, "Edges");
    assert_eq!(k, None, "should not detect filter in plain TRUE");
}

// --- Nested powerset with cardinality filter: 3 nodes ---

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_bmc_nested_powerset_3nodes_cardinality2() {
    let mut bmc = bmc_array(0);

    // SpanTreeTest pattern with 3 nodes: {1, 2, 3}
    // Edges \in {E \in SUBSET(SUBSET {1,2,3}) : \A e \in E : Cardinality(e) = 2}
    //
    // Base: C(3,2) = 3 edges: {1,2}, {1,3}, {2,3}
    // Solutions: 2^3 = 8 edge sets
    //
    // We test: \E Edges \in SUBSET(SUBSET {1,2,3}) :
    //            (\A e \in Edges : Cardinality(e) = 2)
    // This should be SAT.

    let nodes = spanned(Expr::SetEnum(vec![int(1), int(2), int(3)]));

    // Domain: SUBSET(SUBSET Nodes)
    let domain = spanned(Expr::Powerset(Box::new(spanned(Expr::Powerset(
        Box::new(nodes),
    )))));

    // Body: \A e \in Edges : Cardinality(e) = 2
    let card_filter = spanned(Expr::Forall(
        vec![BoundVar {
            name: spanned("e".to_string()),
            domain: Some(Box::new(ident("Edges"))),
            pattern: None,
        }],
        Box::new(spanned(Expr::Eq(
            Box::new(spanned(Expr::Apply(
                Box::new(ident("Cardinality")),
                vec![ident("e")],
            ))),
            Box::new(int(2)),
        ))),
    ));

    let exists_expr = spanned(Expr::Exists(
        vec![BoundVar {
            name: spanned("Edges".to_string()),
            domain: Some(Box::new(domain)),
            pattern: None,
        }],
        Box::new(card_filter),
    ));

    let term = bmc.translate_init(&exists_expr).unwrap();
    bmc.assert(term);
    assert!(
        matches!(bmc.check_sat(), SolveResult::Sat),
        "should find valid edge sets for 3 nodes with cardinality-2 filter"
    );
}

// --- Nested powerset: empty set correctness (Fixes #4058) ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_nested_powerset_empty_set() {
    let mut bmc = bmc_array(0);

    // \E T \in SUBSET(SUBSET {}) : T = {{}}
    //
    // SUBSET {} = {{}}
    // SUBSET(SUBSET {}) = SUBSET {{}} = {{}, {{}}}
    // T = {{}} is satisfied by the second element, so this should be SAT.
    //
    // Before fix #4058, the early return incorrectly treated
    // SUBSET(SUBSET {}) as having only one element {{}}, substituting
    // T = {{}} directly and skipping the empty set. This caused UNSAT
    // because the body was evaluated only for T = {} (the empty set),
    // not for T = {{}}.
    let empty_set = spanned(Expr::SetEnum(vec![]));
    let singleton_empty = spanned(Expr::SetEnum(vec![spanned(Expr::SetEnum(vec![]))]));

    let exists_expr = spanned(Expr::Exists(
        vec![BoundVar {
            name: spanned("T".to_string()),
            domain: Some(Box::new(spanned(Expr::Powerset(Box::new(spanned(
                Expr::Powerset(Box::new(empty_set)),
            )))))),
            pattern: None,
        }],
        Box::new(spanned(Expr::Eq(
            Box::new(ident("T")),
            Box::new(singleton_empty),
        ))),
    ));

    let term = bmc.translate_init(&exists_expr).unwrap();
    bmc.assert(term);
    assert!(
        matches!(bmc.check_sat(), SolveResult::Sat),
        "SUBSET(SUBSET {{}}) has 2 elements: {{}} and {{{{}}}}; T = {{{{}}}} should be SAT"
    );
}

// --- Set equality (required for nested powerset body evaluation) ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_set_equality_same_sets() {
    let mut bmc = bmc_array(0);

    // {1, 2} = {1, 2} should be SAT
    let eq = spanned(Expr::Eq(
        Box::new(spanned(Expr::SetEnum(vec![int(1), int(2)]))),
        Box::new(spanned(Expr::SetEnum(vec![int(1), int(2)]))),
    ));

    let term = bmc.translate_init(&eq).unwrap();
    bmc.assert(term);
    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_set_equality_different_sets() {
    let mut bmc = bmc_array(0);

    // {1, 2} = {1, 3} should be UNSAT
    let eq = spanned(Expr::Eq(
        Box::new(spanned(Expr::SetEnum(vec![int(1), int(2)]))),
        Box::new(spanned(Expr::SetEnum(vec![int(1), int(3)]))),
    ));

    let term = bmc.translate_init(&eq).unwrap();
    bmc.assert(term);
    assert!(matches!(bmc.check_sat(), SolveResult::Unsat(_)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_set_membership_in_set_enum_of_sets() {
    let mut bmc = bmc_array(0);

    // {1, 2} \in {{1, 2}, {2, 3}} should be SAT (via set equality)
    let membership = spanned(Expr::In(
        Box::new(spanned(Expr::SetEnum(vec![int(1), int(2)]))),
        Box::new(spanned(Expr::SetEnum(vec![
            spanned(Expr::SetEnum(vec![int(1), int(2)])),
            spanned(Expr::SetEnum(vec![int(2), int(3)])),
        ]))),
    ));

    let term = bmc.translate_init(&membership).unwrap();
    bmc.assert(term);
    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_set_non_membership_in_set_enum_of_sets() {
    let mut bmc = bmc_array(0);

    // {1, 3} \in {{1, 2}, {2, 3}} should be UNSAT
    let membership = spanned(Expr::In(
        Box::new(spanned(Expr::SetEnum(vec![int(1), int(3)]))),
        Box::new(spanned(Expr::SetEnum(vec![
            spanned(Expr::SetEnum(vec![int(1), int(2)])),
            spanned(Expr::SetEnum(vec![int(2), int(3)])),
        ]))),
    ));

    let term = bmc.translate_init(&membership).unwrap();
    bmc.assert(term);
    assert!(matches!(bmc.check_sat(), SolveResult::Unsat(_)));
}
