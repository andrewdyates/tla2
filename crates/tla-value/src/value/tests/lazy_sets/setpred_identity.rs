// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SetPred structural identity and span-leakage regression tests (Part of #2030).

use super::super::super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_setpred_structural_fingerprint_and_hash_ignore_runtime_id() {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    use tla_core::ast::BoundVar;
    use tla_core::Spanned;

    let bound = BoundVar {
        name: Spanned::new("x".to_string(), Default::default()),
        domain: None,
        pattern: None,
    };
    let pred = Spanned::new(Expr::Bool(true), Default::default());

    let spv1 = SetPredValue::new(
        Value::StringSet,
        bound.clone(),
        pred.clone(),
        HashMap::new(),
        None,
        None,
    );
    let spv2 = SetPredValue::new(Value::StringSet, bound, pred, HashMap::new(), None, None);

    let v1 = Value::SetPred(Box::new(spv1));
    let v2 = Value::SetPred(Box::new(spv2));

    assert_eq!(v1, v2, "structurally equal SetPred values must be equal");
    assert_eq!(
        v1.cmp(&v2),
        std::cmp::Ordering::Equal,
        "structurally equal SetPred values must compare equal"
    );

    let seed = 42_u64;
    let fp1 = v1.fingerprint_extend(seed).unwrap();
    let fp2 = v2.fingerprint_extend(seed).unwrap();
    assert_eq!(
        fp1, fp2,
        "runtime ID must not perturb SetPred FP64 fingerprints"
    );

    let mut h1 = DefaultHasher::new();
    let mut h2 = DefaultHasher::new();
    v1.hash(&mut h1);
    v2.hash(&mut h2);
    assert_eq!(
        h1.finish(),
        h2.finish(),
        "runtime ID must not perturb SetPred Hash"
    );
}

/// Helper: assert that two Values are identical across Ord, PartialEq, Hash, and FP64.
/// Used by the span-leakage regression tests below.
fn assert_setpred_identity_equal(v1: &Value, v2: &Value, field: &str) {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};

    assert_eq!(
        v1.cmp(v2),
        std::cmp::Ordering::Equal,
        "SetPred Ord leaks {field}-field spans into comparison. Part of #2030."
    );
    assert_eq!(
        v1, v2,
        "SetPred PartialEq disagrees with Ord on {field}. Part of #2030."
    );

    let mut h1 = DefaultHasher::new();
    let mut h2 = DefaultHasher::new();
    v1.hash(&mut h1);
    v2.hash(&mut h2);
    assert_eq!(
        h1.finish(),
        h2.finish(),
        "SetPred Hash leaks {field} spans. Part of #2030."
    );

    let fp1 = v1.fingerprint_extend(42).unwrap();
    let fp2 = v2.fingerprint_extend(42).unwrap();
    assert_eq!(
        fp1, fp2,
        "SetPred FP64 fingerprint leaks {field} spans. Part of #2030."
    );
}

/// Helper: create a SetPred Value with the given bound and pred.
fn make_setpred(bound: tla_core::ast::BoundVar, pred: tla_core::Spanned<Expr>) -> Value {
    Value::SetPred(Box::new(SetPredValue::new(
        Value::StringSet,
        bound,
        pred,
        HashMap::new(),
        None,
        None,
    )))
}

/// Regression: bound-field span must not leak into Ord/Hash/FP64. Part of #2030.
///
/// `format!("{:?}", self.bound)` includes `Spanned<T>::Debug` with source span.
/// Two SetPred values with the same logical bound at different source locations
/// must compare/hash identically — spans are parser metadata, not semantics.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_setpred_bound_span_must_not_leak_into_ord_hash_fingerprint() {
    use tla_core::ast::BoundVar;
    use tla_core::{FileId, Span, Spanned};

    let span1 = Span::new(FileId(0), 10, 20);
    let span2 = Span::new(FileId(0), 50, 60);
    assert_ne!(span1, span2, "test setup: spans must differ");

    let bound1 = BoundVar {
        name: Spanned::new("x".to_string(), span1),
        domain: None,
        pattern: None,
    };
    let bound2 = BoundVar {
        name: Spanned::new("x".to_string(), span2),
        domain: None,
        pattern: None,
    };
    let pred = Spanned::new(Expr::Bool(true), Default::default());

    let v1 = make_setpred(bound1, pred.clone());
    let v2 = make_setpred(bound2, pred);
    assert_setpred_identity_equal(&v1, &v2, "bound");
}

/// Regression: pred-field span must not leak into Ord/Hash/FP64. Part of #2030.
///
/// The pred field uses `self.pred.node` (correct). This test verifies that
/// the span exclusion holds across Hash and FP64 in addition to Ord.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_setpred_pred_span_must_not_leak_into_hash_fingerprint() {
    use tla_core::ast::BoundVar;
    use tla_core::{FileId, Span, Spanned};

    let bound = BoundVar {
        name: Spanned::new("x".to_string(), Default::default()),
        domain: None,
        pattern: None,
    };
    let pred1 = Spanned::new(Expr::Bool(true), Span::new(FileId(0), 100, 110));
    let pred2 = Spanned::new(Expr::Bool(true), Span::new(FileId(0), 200, 210));

    let v1 = make_setpred(bound.clone(), pred1);
    let v2 = make_setpred(bound, pred2);
    assert_setpred_identity_equal(&v1, &v2, "pred");
}

/// Regression: nested spans inside predicate AST must not leak into identity.
///
/// #2039: using `format!("{:?}", pred.node)` leaks inner `Spanned<Expr>` spans
/// from variants like `Expr::Apply`.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_setpred_nested_pred_spans_must_not_leak_into_identity() {
    use tla_core::ast::BoundVar;
    use tla_core::name_intern::NameId;
    use tla_core::{FileId, Span, Spanned};

    let outer = Span::new(FileId(0), 1, 2);
    let op_span1 = Span::new(FileId(0), 10, 11);
    let arg_span1 = Span::new(FileId(0), 12, 13);
    let op_span2 = Span::new(FileId(0), 20, 21);
    let arg_span2 = Span::new(FileId(0), 22, 23);

    let bound = BoundVar {
        name: Spanned::new("x".to_string(), Default::default()),
        domain: None,
        pattern: None,
    };

    let pred1 = Spanned::new(
        Expr::Apply(
            Box::new(Spanned::new(
                Expr::Ident("P".into(), NameId::INVALID),
                op_span1,
            )),
            vec![Spanned::new(
                Expr::Ident("x".into(), NameId::INVALID),
                arg_span1,
            )],
        ),
        outer,
    );
    let pred2 = Spanned::new(
        Expr::Apply(
            Box::new(Spanned::new(
                Expr::Ident("P".into(), NameId::INVALID),
                op_span2,
            )),
            vec![Spanned::new(
                Expr::Ident("x".into(), NameId::INVALID),
                arg_span2,
            )],
        ),
        outer,
    );

    let v1 = make_setpred(bound.clone(), pred1);
    let v2 = make_setpred(bound, pred2);
    assert_setpred_identity_equal(&v1, &v2, "pred::nested");
}

/// Regression: domain and pattern span must not leak into identity. Part of #2030.
///
/// `bound_var_identity_sig()` uses `.domain.node` and `.pattern` `.node` fields
/// to exclude top-level spans. This test verifies all three BoundVar sub-fields
/// (domain, BoundPattern::Var, BoundPattern::Tuple) are span-free.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_setpred_domain_and_pattern_span_must_not_leak_into_identity() {
    use tla_core::ast::{BoundPattern, BoundVar};
    use tla_core::name_intern::NameId;
    use tla_core::{FileId, Span, Spanned};

    let span1 = Span::new(FileId(0), 10, 20);
    let span2 = Span::new(FileId(0), 50, 60);
    let pred = Spanned::new(Expr::Bool(true), Default::default());

    // Domain span independence: same Expr::Ident("S", NameId::INVALID), different spans.
    let bound_d1 = BoundVar {
        name: Spanned::new("x".to_string(), Default::default()),
        domain: Some(Box::new(Spanned::new(
            Expr::Ident("S".into(), NameId::INVALID),
            span1,
        ))),
        pattern: None,
    };
    let bound_d2 = BoundVar {
        name: Spanned::new("x".to_string(), Default::default()),
        domain: Some(Box::new(Spanned::new(
            Expr::Ident("S".into(), NameId::INVALID),
            span2,
        ))),
        pattern: None,
    };
    let v1 = make_setpred(bound_d1, pred.clone());
    let v2 = make_setpred(bound_d2, pred.clone());
    assert_setpred_identity_equal(&v1, &v2, "domain");

    // BoundPattern::Var span independence.
    let bound_pv1 = BoundVar {
        name: Spanned::new("x".to_string(), Default::default()),
        domain: None,
        pattern: Some(BoundPattern::Var(Spanned::new("y".into(), span1))),
    };
    let bound_pv2 = BoundVar {
        name: Spanned::new("x".to_string(), Default::default()),
        domain: None,
        pattern: Some(BoundPattern::Var(Spanned::new("y".into(), span2))),
    };
    let v3 = make_setpred(bound_pv1, pred.clone());
    let v4 = make_setpred(bound_pv2, pred.clone());
    assert_setpred_identity_equal(&v3, &v4, "pattern::Var");

    // BoundPattern::Tuple span independence.
    let bound_pt1 = BoundVar {
        name: Spanned::new("x".to_string(), Default::default()),
        domain: None,
        pattern: Some(BoundPattern::Tuple(vec![
            Spanned::new("a".into(), span1),
            Spanned::new("b".into(), span1),
        ])),
    };
    let bound_pt2 = BoundVar {
        name: Spanned::new("x".to_string(), Default::default()),
        domain: None,
        pattern: Some(BoundPattern::Tuple(vec![
            Spanned::new("a".into(), span2),
            Spanned::new("b".into(), span2),
        ])),
    };
    let v5 = make_setpred(bound_pt1, pred.clone());
    let v6 = make_setpred(bound_pt2, pred);
    assert_setpred_identity_equal(&v5, &v6, "pattern::Tuple");
}

/// Regression: nested spans inside bound-domain AST must not leak into identity.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_setpred_domain_nested_spans_must_not_leak_into_identity() {
    use tla_core::ast::BoundVar;
    use tla_core::name_intern::NameId;
    use tla_core::{FileId, Span, Spanned};

    let pred = Spanned::new(Expr::Bool(true), Default::default());
    let outer = Span::new(FileId(0), 1, 2);
    let op_span1 = Span::new(FileId(0), 10, 11);
    let arg_span1 = Span::new(FileId(0), 12, 13);
    let op_span2 = Span::new(FileId(0), 20, 21);
    let arg_span2 = Span::new(FileId(0), 22, 23);

    let domain1 = Spanned::new(
        Expr::Apply(
            Box::new(Spanned::new(
                Expr::Ident("Dom".into(), NameId::INVALID),
                op_span1,
            )),
            vec![Spanned::new(
                Expr::Ident("S".into(), NameId::INVALID),
                arg_span1,
            )],
        ),
        outer,
    );
    let domain2 = Spanned::new(
        Expr::Apply(
            Box::new(Spanned::new(
                Expr::Ident("Dom".into(), NameId::INVALID),
                op_span2,
            )),
            vec![Spanned::new(
                Expr::Ident("S".into(), NameId::INVALID),
                arg_span2,
            )],
        ),
        outer,
    );

    let bound1 = BoundVar {
        name: Spanned::new("x".to_string(), Default::default()),
        domain: Some(Box::new(domain1)),
        pattern: None,
    };
    let bound2 = BoundVar {
        name: Spanned::new("x".to_string(), Default::default()),
        domain: Some(Box::new(domain2)),
        pattern: None,
    };

    let v1 = make_setpred(bound1, pred.clone());
    let v2 = make_setpred(bound2, pred);
    assert_setpred_identity_equal(&v1, &v2, "domain::nested");
}
