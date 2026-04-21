// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! SetPred basic/value-variant smoke coverage and distinct fingerprint tests.

use super::super::super::*;
use std::sync::Arc;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_setpred_basic() {
    use tla_core::ast::BoundVar;
    use tla_core::{FileId, Span, Spanned};

    // Create a basic SetPred value with STRING source
    let source = Value::StringSet;
    let bound = BoundVar {
        name: Spanned::new("x".to_string(), Default::default()),
        domain: None,
        pattern: None,
    };
    let pred = Spanned::new(Expr::Bool(true), Default::default());
    let env = HashMap::new();

    let spv = SetPredValue::new(source, bound, pred, env, None, None);

    // Basic properties
    assert!(spv.is_infinite()); // STRING is infinite
    assert!(!spv.is_enumerable()); // Can't enumerate STRING

    // Source contains check
    assert_eq!(spv.source_contains(&Value::string("hello")), Some(true));
    assert_eq!(spv.source_contains(&Value::int(42)), Some(false));

    // FIX #1989: IDs are now deterministic from the predicate span.
    // Same span → same ID (determinism); different span → different ID (uniqueness).
    let source_same = Value::StringSet;
    let bound_same = BoundVar {
        name: Spanned::new("x".to_string(), Default::default()),
        domain: None,
        pattern: None,
    };
    let pred_same = Spanned::new(Expr::Bool(true), Default::default());
    let spv_same = SetPredValue::new(
        source_same,
        bound_same,
        pred_same,
        HashMap::new(),
        None,
        None,
    );
    assert_eq!(spv.id, spv_same.id, "same span must produce same ID");

    // Different span → different ID
    let source2 = Value::StringSet;
    let bound2 = BoundVar {
        name: Spanned::new("y".to_string(), Default::default()),
        domain: None,
        pattern: None,
    };
    let different_span = Span {
        file: FileId(1),
        start: 10,
        end: 20,
    };
    let pred2 = Spanned::new(Expr::Bool(false), different_span);
    let spv2 = SetPredValue::new(source2, bound2, pred2, HashMap::new(), None, None);

    assert_ne!(
        spv.id, spv2.id,
        "different spans must produce different IDs"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_setpred_value_variant() {
    use tla_core::ast::BoundVar;
    use tla_core::Spanned;

    // Create a SetPred Value
    let source = Value::AnySet;
    let bound = BoundVar {
        name: Spanned::new("x".to_string(), Default::default()),
        domain: None,
        pattern: None,
    };
    let pred = Spanned::new(Expr::Bool(true), Default::default());
    let spv = SetPredValue::new(source, bound, pred, HashMap::new(), None, None);
    let val = Value::SetPred(Box::new(spv));

    // Should be recognized as a set
    assert!(val.is_set());

    // set_contains returns None (requires evaluation context)
    assert!(val.set_contains(&Value::int(42)).is_none());

    // iter_set returns None (non-enumerable source)
    assert!(val.iter_set().is_none());

    // to_sorted_set returns None (non-enumerable source)
    assert!(val.to_sorted_set().is_none());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_setpred_ordering() {
    use tla_core::ast::BoundVar;
    use tla_core::{FileId, Span, Spanned};

    // Create two SetPred values with distinct spans → distinct deterministic IDs
    let bound = BoundVar {
        name: Spanned::new("x".to_string(), Default::default()),
        domain: None,
        pattern: None,
    };
    let span1 = Span {
        file: FileId(0),
        start: 0,
        end: 10,
    };
    let span2 = Span {
        file: FileId(0),
        start: 20,
        end: 30,
    };

    let spv1 = SetPredValue::new(
        Value::StringSet,
        bound.clone(),
        Spanned::new(Expr::Bool(true), span1),
        HashMap::new(),
        None,
        None,
    );
    let spv2 = SetPredValue::new(
        Value::StringSet,
        bound.clone(),
        Spanned::new(Expr::Bool(true), span2),
        HashMap::new(),
        None,
        None,
    );

    // Runtime IDs differ, but structural ordering/equality should match.
    assert_ne!(spv1.id, spv2.id);
    assert_eq!(spv1.cmp(&spv2), std::cmp::Ordering::Equal);
    assert_eq!(spv1, spv2);

    // Different predicates should remain distinguishable.
    let spv3 = SetPredValue::new(
        Value::StringSet,
        bound,
        Spanned::new(Expr::Bool(false), Default::default()),
        HashMap::new(),
        None,
        None,
    );
    assert_ne!(spv1.cmp(&spv3), std::cmp::Ordering::Equal);

    // Same SetPred should be equal to itself
    assert_eq!(spv1.cmp(&spv1), std::cmp::Ordering::Equal);
}

/// FIX #1859: Two distinct closures must produce distinct FP64 fingerprints.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_closure_distinct_fingerprints() {
    use tla_core::{FileId, Span, Spanned};

    let span1 = Span {
        file: FileId(0),
        start: 0,
        end: 10,
    };
    let span2 = Span {
        file: FileId(0),
        start: 20,
        end: 30,
    };

    let c1 = ClosureValue::new(
        vec!["x".to_string()],
        Spanned::new(Expr::Bool(true), span1),
        Arc::new(im::HashMap::new()),
        None,
    );
    let c2 = ClosureValue::new(
        vec!["x".to_string()],
        Spanned::new(Expr::Bool(false), span2),
        Arc::new(im::HashMap::new()),
        None,
    );

    assert_ne!(c1.id, c2.id, "distinct closures must have distinct IDs");

    let seed = 42_u64;
    let fp1 = Value::Closure(Arc::new(c1))
        .fingerprint_extend(seed)
        .unwrap();
    let fp2 = Value::Closure(Arc::new(c2))
        .fingerprint_extend(seed)
        .unwrap();

    assert_ne!(
        fp1, fp2,
        "distinct closures must produce distinct FP64 fingerprints"
    );
}

/// FIX #1859: Two distinct SetPred values must produce distinct FP64 fingerprints.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_setpred_distinct_fingerprints() {
    use tla_core::ast::BoundVar;
    use tla_core::{FileId, Span, Spanned};

    let span1 = Span {
        file: FileId(0),
        start: 0,
        end: 10,
    };
    let span2 = Span {
        file: FileId(0),
        start: 20,
        end: 30,
    };

    let bound1 = BoundVar {
        name: Spanned::new("x".to_string(), Default::default()),
        domain: None,
        pattern: None,
    };
    let bound2 = BoundVar {
        name: Spanned::new("y".to_string(), Default::default()),
        domain: None,
        pattern: None,
    };

    let spv1 = SetPredValue::new(
        Value::StringSet,
        bound1,
        Spanned::new(Expr::Bool(true), span1),
        HashMap::new(),
        None,
        None,
    );
    let spv2 = SetPredValue::new(
        Value::StringSet,
        bound2,
        Spanned::new(Expr::Bool(false), span2),
        HashMap::new(),
        None,
        None,
    );

    let seed = 42_u64;
    let fp1 = Value::SetPred(Box::new(spv1))
        .fingerprint_extend(seed)
        .unwrap();
    let fp2 = Value::SetPred(Box::new(spv2))
        .fingerprint_extend(seed)
        .unwrap();

    assert_ne!(
        fp1, fp2,
        "distinct SetPred values must produce distinct FP64 fingerprints"
    );
}
