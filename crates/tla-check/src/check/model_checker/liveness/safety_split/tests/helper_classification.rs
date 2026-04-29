// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// --- flatten_and_terms ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_flatten_and_single_term() {
    let expr = dummy(Expr::Bool(true));
    let mut out = Vec::new();
    ModelChecker::flatten_and_terms(&expr, &mut out);
    assert_eq!(out.len(), 1);
    assert!(matches!(out[0].node, Expr::Bool(true)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_flatten_and_nested() {
    // (A /\ B) /\ C => [A, B, C]
    let a = Expr::Ident("A".into(), tla_core::name_intern::NameId::INVALID);
    let b = Expr::Ident("B".into(), tla_core::name_intern::NameId::INVALID);
    let c = Expr::Ident("C".into(), tla_core::name_intern::NameId::INVALID);
    let ab = Expr::And(boxed(a), boxed(b));
    let abc = Expr::And(boxed(ab), boxed(c));
    let mut out = Vec::new();
    ModelChecker::flatten_and_terms(&dummy(abc), &mut out);
    assert_eq!(out.len(), 3, "Expected 3 conjuncts, got {}", out.len());
    // Verify actual conjunct identities -- a count-only check would miss
    // a bug that duplicates A and drops C.
    let names: Vec<&str> = out
        .iter()
        .map(|s| match &s.node {
            Expr::Ident(name, _) => name.as_str(),
            other => panic!("Expected Ident, got {:?}", other),
        })
        .collect();
    assert_eq!(names, vec!["A", "B", "C"]);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_flatten_and_deeply_nested() {
    // A /\ (B /\ (C /\ D)) => [A, B, C, D]
    let a = Expr::Ident("A".into(), tla_core::name_intern::NameId::INVALID);
    let b = Expr::Ident("B".into(), tla_core::name_intern::NameId::INVALID);
    let c = Expr::Ident("C".into(), tla_core::name_intern::NameId::INVALID);
    let d = Expr::Ident("D".into(), tla_core::name_intern::NameId::INVALID);
    let cd = Expr::And(boxed(c), boxed(d));
    let bcd = Expr::And(boxed(b), boxed(cd));
    let abcd = Expr::And(boxed(a), boxed(bcd));
    let mut out = Vec::new();
    ModelChecker::flatten_and_terms(&dummy(abcd), &mut out);
    assert_eq!(out.len(), 4, "Expected 4 conjuncts, got {}", out.len());
    // Verify conjunct order and identity -- a bug that reverses right-recursive
    // nesting or drops an intermediate term would pass a count-only check.
    let names: Vec<&str> = out
        .iter()
        .map(|s| match &s.node {
            Expr::Ident(name, _) => name.as_str(),
            other => panic!("Expected Ident, got {:?}", other),
        })
        .collect();
    assert_eq!(names, vec!["A", "B", "C", "D"]);
}

// --- contains_temporal_helper (via expr_contains) ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_temporal_always() {
    let expr = Expr::Always(boxed(Expr::Bool(true)));
    assert!(ModelChecker::contains_temporal_helper(&expr));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_temporal_eventually() {
    let expr = Expr::Eventually(boxed(Expr::Bool(true)));
    assert!(ModelChecker::contains_temporal_helper(&expr));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_temporal_leads_to() {
    let expr = Expr::LeadsTo(boxed(Expr::Bool(true)), boxed(Expr::Bool(false)));
    assert!(ModelChecker::contains_temporal_helper(&expr));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_non_temporal_bool() {
    assert!(!ModelChecker::contains_temporal_helper(&Expr::Bool(true)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_temporal_in_conjunction() {
    let expr = Expr::And(
        boxed(Expr::Bool(true)),
        boxed(Expr::Always(boxed(Expr::Bool(false)))),
    );
    assert!(ModelChecker::contains_temporal_helper(&expr));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_temporal_wf_sf_ident() {
    // WF_ and SF_ prefixed identifiers inside Apply are recognized as temporal
    let wf_op = boxed(Expr::Ident(
        "WF_vars".into(),
        tla_core::name_intern::NameId::INVALID,
    ));
    let expr = Expr::Apply(wf_op, vec![dummy(Expr::Bool(true))]);
    assert!(ModelChecker::contains_temporal_helper(&expr));

    let sf_op = boxed(Expr::Ident(
        "SF_vars".into(),
        tla_core::name_intern::NameId::INVALID,
    ));
    let expr = Expr::Apply(sf_op, vec![dummy(Expr::Bool(true))]);
    assert!(ModelChecker::contains_temporal_helper(&expr));
}

// --- contains_enabled (via expr_contains) ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enabled_direct() {
    let expr = Expr::Enabled(boxed(Expr::Bool(true)));
    assert!(ModelChecker::contains_enabled(&expr));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enabled_nested_in_and() {
    let expr = Expr::And(
        boxed(Expr::Bool(true)),
        boxed(Expr::Enabled(boxed(Expr::Bool(false)))),
    );
    assert!(ModelChecker::contains_enabled(&expr));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_no_enabled() {
    let expr = Expr::And(
        boxed(Expr::Bool(true)),
        boxed(Expr::Ident(
            "x".into(),
            tla_core::name_intern::NameId::INVALID,
        )),
    );
    assert!(!ModelChecker::contains_enabled(&expr));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enabled_inside_case_arm() {
    let arm = tla_core::ast::CaseArm {
        guard: dummy(Expr::Bool(true)),
        body: dummy(Expr::Enabled(boxed(Expr::Ident(
            "x".into(),
            tla_core::name_intern::NameId::INVALID,
        )))),
    };
    let expr = Expr::Case(vec![arm], None);
    assert!(ModelChecker::contains_enabled(&expr));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enabled_inside_func_apply_argument() {
    let expr = Expr::FuncApply(
        boxed(Expr::Ident(
            "f".into(),
            tla_core::name_intern::NameId::INVALID,
        )),
        boxed(Expr::Enabled(boxed(Expr::Ident(
            "x".into(),
            tla_core::name_intern::NameId::INVALID,
        )))),
    );
    assert!(ModelChecker::contains_enabled(&expr));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enabled_inside_record_field() {
    let expr = Expr::Record(vec![(
        tla_core::Spanned::dummy("k".to_string()),
        dummy(Expr::Enabled(boxed(Expr::Ident(
            "x".into(),
            tla_core::name_intern::NameId::INVALID,
        )))),
    )]);
    assert!(ModelChecker::contains_enabled(&expr));
}

// --- has_nested_temporal_for_safety_split ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_nested_temporal_always_eventually() {
    // []<>P has nested temporal
    let expr = Expr::Always(boxed(Expr::Eventually(boxed(Expr::Bool(true)))));
    assert!(ModelChecker::has_nested_temporal_for_safety_split(&expr));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_non_nested_always() {
    // []P where P is non-temporal -- no nesting
    let expr = Expr::Always(boxed(Expr::Bool(true)));
    assert!(!ModelChecker::has_nested_temporal_for_safety_split(&expr));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_leads_to_is_inherently_nested() {
    let expr = Expr::LeadsTo(boxed(Expr::Bool(true)), boxed(Expr::Bool(false)));
    assert!(ModelChecker::has_nested_temporal_for_safety_split(&expr));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_atom_not_nested() {
    assert!(!ModelChecker::has_nested_temporal_for_safety_split(
        &Expr::Bool(true)
    ));
    assert!(!ModelChecker::has_nested_temporal_for_safety_split(
        &Expr::Ident("x".into(), tla_core::name_intern::NameId::INVALID)
    ));
}

// --- wrap_with_let_defs ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_wrap_with_let_defs_none() {
    let expr = dummy(Expr::Bool(true));
    let result = ModelChecker::wrap_with_let_defs(&None, expr);
    assert!(matches!(result.node, Expr::Bool(true)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_wrap_with_let_defs_some() {
    let expr = dummy(Expr::Bool(true));
    let defs = Some(vec![]); // Empty defs still wraps in Let
    let result = ModelChecker::wrap_with_let_defs(&defs, expr);
    // Verify both the Let wrapper structure AND that the inner expression
    // is preserved. The old test only checked `matches!(_, Expr::Let(_, _))`
    // which would pass even if the body was lost or replaced.
    match &result.node {
        Expr::Let(let_defs, body) => {
            assert!(let_defs.is_empty(), "expected empty defs vec");
            assert!(
                matches!(body.node, Expr::Bool(true)),
                "inner expression should be Bool(true), got {:?}",
                body.node
            );
        }
        other => panic!("Expected Let, got {:?}", other),
    }
}
