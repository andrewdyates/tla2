// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for unsupported value types in checkpoint serialization:
//! SetPred, infinite sets, LazyFunc, Closure.

use super::*;

/// Regression test for #2115: from_value must return an error for SetPred.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_from_value_setpred_returns_error() {
    use tla_core::ast::{BoundVar, Expr};
    use tla_core::{FileId, Span, Spanned};

    let dummy_span = Span {
        file: FileId(0),
        start: 0,
        end: 0,
    };
    let spv = crate::value::SetPredValue::new(
        Value::set(vec![Value::SmallInt(1), Value::SmallInt(2)]),
        BoundVar {
            name: Spanned {
                node: "x".to_string(),
                span: dummy_span,
            },
            domain: None,
            pattern: None,
        },
        Spanned {
            node: Expr::Bool(true),
            span: dummy_span,
        },
        im::HashMap::new(),
        None,
        None,
    );
    let setpred = Value::SetPred(Box::new(spv));

    let err = SerializableValue::from_value(&setpred).unwrap_err();
    assert_eq!(err.kind(), io::ErrorKind::InvalidData);
    assert!(
        err.to_string().contains("SetPred"),
        "error message should mention SetPred: {}",
        err
    );
}

/// Regression test for #2115: from_state must propagate the SetPred error.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_from_state_setpred_returns_error() {
    use tla_core::ast::{BoundVar, Expr};
    use tla_core::{FileId, Span, Spanned};

    let dummy_span = Span {
        file: FileId(0),
        start: 0,
        end: 0,
    };
    let spv = crate::value::SetPredValue::new(
        Value::set(vec![Value::SmallInt(1)]),
        BoundVar {
            name: Spanned {
                node: "x".to_string(),
                span: dummy_span,
            },
            domain: None,
            pattern: None,
        },
        Spanned {
            node: Expr::Bool(true),
            span: dummy_span,
        },
        im::HashMap::new(),
        None,
        None,
    );

    let mut state = State::new();
    state = state.with_var("x", Value::SmallInt(42));
    state = state.with_var("pred_set", Value::SetPred(Box::new(spv)));

    let err = SerializableState::from_state(&state).unwrap_err();
    assert_eq!(err.kind(), io::ErrorKind::InvalidData);
    assert!(err.to_string().contains("SetPred"));
}

/// Regression test for #2115: checkpoint save must fail on frontier SetPred.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_checkpoint_save_fails_on_setpred_in_frontier() {
    use tla_core::ast::{BoundVar, Expr};
    use tla_core::{FileId, Span, Spanned};

    let dummy_span = Span {
        file: FileId(0),
        start: 0,
        end: 0,
    };
    let spv = crate::value::SetPredValue::new(
        Value::set(vec![Value::SmallInt(1)]),
        BoundVar {
            name: Spanned {
                node: "x".to_string(),
                span: dummy_span,
            },
            domain: None,
            pattern: None,
        },
        Spanned {
            node: Expr::Bool(true),
            span: dummy_span,
        },
        im::HashMap::new(),
        None,
        None,
    );

    let dir = tempdir().unwrap();
    let checkpoint_dir = dir.path().join("checkpoint");

    let mut checkpoint = Checkpoint::new();
    checkpoint.fingerprints = vec![Fingerprint(42)];
    checkpoint.depths.insert(Fingerprint(42), 0);

    let mut state = State::new();
    state = state.with_var("s", Value::SetPred(Box::new(spv)));
    checkpoint.frontier = vec![state];

    let err = checkpoint.save(&checkpoint_dir).unwrap_err();
    assert!(err.to_string().contains("SetPred"));
}

/// Regression test for #2750: from_value must return an error for infinite sets
/// (StringSet, AnySet, SeqSet). These were previously silently returning Ok(Set([])),
/// which would corrupt checkpoint data.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_from_value_infinite_sets_return_error() {
    use crate::value::SeqSetValue;

    // StringSet — the set of all strings
    let err = SerializableValue::from_value(&Value::StringSet).unwrap_err();
    assert_eq!(err.kind(), io::ErrorKind::InvalidData);
    assert!(
        err.to_string().contains("infinite set"),
        "error message should mention infinite set: {err}"
    );

    // AnySet — the set of all values
    let err = SerializableValue::from_value(&Value::AnySet).unwrap_err();
    assert_eq!(err.kind(), io::ErrorKind::InvalidData);
    assert!(
        err.to_string().contains("infinite set"),
        "error message should mention infinite set: {err}"
    );

    // SeqSet — lazy Seq(S)
    let seqset = Value::SeqSet(SeqSetValue::new(Value::set(vec![Value::SmallInt(1)])));
    let err = SerializableValue::from_value(&seqset).unwrap_err();
    assert_eq!(err.kind(), io::ErrorKind::InvalidData);
    assert!(
        err.to_string().contains("infinite set"),
        "error message should mention infinite set: {err}"
    );
}

/// Regression test for #2115: nested SetPred must also be caught.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_from_value_nested_setpred_returns_error() {
    use tla_core::ast::{BoundVar, Expr};
    use tla_core::{FileId, Span, Spanned};

    let dummy_span = Span {
        file: FileId(0),
        start: 0,
        end: 0,
    };
    let spv = crate::value::SetPredValue::new(
        Value::set(vec![Value::SmallInt(1)]),
        BoundVar {
            name: Spanned {
                node: "x".to_string(),
                span: dummy_span,
            },
            domain: None,
            pattern: None,
        },
        Spanned {
            node: Expr::Bool(true),
            span: dummy_span,
        },
        im::HashMap::new(),
        None,
        None,
    );

    let nested = Value::Tuple(vec![Value::SmallInt(1), Value::SetPred(Box::new(spv))].into());
    let err = SerializableValue::from_value(&nested).unwrap_err();
    assert_eq!(err.kind(), io::ErrorKind::InvalidData);
    assert!(err.to_string().contains("SetPred"));
}

/// Regression test for #2750: from_value must return an error for LazyFunc.
/// LazyFunc values require an EvalCtx for materialization and cannot be
/// serialized to a checkpoint. Previously silently returned Ok(Set([])).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_from_value_lazy_func_returns_error() {
    use crate::value::{LazyDomain, LazyFuncCaptures, LazyFuncValue};
    use tla_core::ast::{BoundVar, Expr};
    use tla_core::{FileId, Span, Spanned};

    let dummy_span = Span {
        file: FileId(0),
        start: 0,
        end: 0,
    };
    let lf = LazyFuncValue::new(
        None,
        LazyDomain::Nat,
        BoundVar {
            name: Spanned {
                node: "n".to_string(),
                span: dummy_span,
            },
            domain: None,
            pattern: None,
        },
        Spanned {
            node: Expr::Bool(true),
            span: dummy_span,
        },
        LazyFuncCaptures::new(Arc::new(im::HashMap::new()), None, None, None),
    );

    let err = SerializableValue::from_value(&Value::LazyFunc(Arc::new(lf))).unwrap_err();
    assert_eq!(err.kind(), io::ErrorKind::InvalidData);
    assert!(
        err.to_string().contains("LazyFunc"),
        "error message should mention LazyFunc: {err}"
    );
}

/// Regression test for #2750: from_value must return an error for Closure.
/// Closures cannot appear in state variables. Previously silently returned
/// Ok(Set([])).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_from_value_closure_returns_error() {
    use crate::value::ClosureValue;
    use tla_core::ast::Expr;
    use tla_core::{FileId, Span, Spanned};

    let dummy_span = Span {
        file: FileId(0),
        start: 0,
        end: 0,
    };
    let cv = ClosureValue::new(
        vec!["x".to_string()],
        Spanned {
            node: Expr::Bool(true),
            span: dummy_span,
        },
        Arc::new(im::HashMap::new()),
        None,
    );

    let err = SerializableValue::from_value(&Value::Closure(Arc::new(cv))).unwrap_err();
    assert_eq!(err.kind(), io::ErrorKind::InvalidData);
    assert!(
        err.to_string().contains("Closure"),
        "error message should mention Closure: {err}"
    );
}
