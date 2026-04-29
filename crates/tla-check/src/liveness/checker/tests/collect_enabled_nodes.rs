// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! collect_enabled_nodes tests
//!
//! Split from liveness/checker/tests.rs — Part of #2779

use crate::liveness::checker::ea_precompute_enabled::collect_enabled_nodes;
use crate::liveness::test_helpers::spanned;
use crate::liveness::LiveExpr;
use std::sync::Arc;
use tla_core::ast::Expr;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_collect_enabled_nodes_empty_for_non_enabled_exprs() {
    // Bool, StatePred, ActionPred — none should produce EnabledInfo entries.
    let cases: Vec<LiveExpr> = vec![
        LiveExpr::Bool(true),
        LiveExpr::Bool(false),
        LiveExpr::state_pred(Arc::new(spanned(Expr::Bool(true))), 0),
        LiveExpr::action_pred(Arc::new(spanned(Expr::Bool(true))), 0),
    ];
    for expr in &cases {
        let mut out = Vec::new();
        collect_enabled_nodes(expr, &mut out);
        assert!(
            out.is_empty(),
            "non-ENABLED expr should produce no EnabledInfo"
        );
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_collect_enabled_nodes_single_enabled() {
    let action = Arc::new(spanned(Expr::Bool(true)));
    let expr = LiveExpr::enabled(Arc::clone(&action), 42);

    let mut out = Vec::new();
    collect_enabled_nodes(&expr, &mut out);
    assert_eq!(out.len(), 1);
    assert_eq!(out[0].tag, 42);
    assert!(!out[0].require_state_change);
    assert!(out[0].subscript.is_none());
    assert!(out[0].bindings.is_none());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_collect_enabled_nodes_nested_and_or_not() {
    // And([Enabled(tag=1), Or([Enabled(tag=2), Not(Enabled(tag=3))])])
    let e1 = LiveExpr::enabled(Arc::new(spanned(Expr::Bool(true))), 1);
    let e2 = LiveExpr::enabled(Arc::new(spanned(Expr::Bool(true))), 2);
    let e3 = LiveExpr::enabled(Arc::new(spanned(Expr::Bool(true))), 3);

    let inner_or = LiveExpr::or(vec![e2, LiveExpr::not(e3)]);
    let root = LiveExpr::and(vec![e1, inner_or]);

    let mut out = Vec::new();
    collect_enabled_nodes(&root, &mut out);
    assert_eq!(out.len(), 3);
    assert_eq!(out[0].tag, 1);
    assert_eq!(out[1].tag, 2);
    assert_eq!(out[2].tag, 3);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_collect_enabled_nodes_preserves_subscript_and_state_change() {
    let action = Arc::new(spanned(Expr::Bool(true)));
    let subscript = Arc::new(spanned(Expr::Ident(
        "x".to_string(),
        tla_core::name_intern::NameId::INVALID,
    )));
    let expr = LiveExpr::enabled_subscripted(Arc::clone(&action), Some(Arc::clone(&subscript)), 7);

    let mut out = Vec::new();
    collect_enabled_nodes(&expr, &mut out);
    assert_eq!(out.len(), 1);
    assert_eq!(out[0].tag, 7);
    assert!(out[0].require_state_change);
    assert!(out[0].subscript.is_some());
}
