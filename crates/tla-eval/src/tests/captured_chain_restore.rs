// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::eval_cache_lifecycle::force_lazy_thunk_if_needed;
use crate::helpers::apply_closure_with_values;
use crate::helpers::function_values::apply_resolved_func_value;
use crate::value::{
    CapturedChain, ClosureValue, LazyDomain, LazyFuncCaptures, LazyFuncValue, SetPredCaptures,
    SetPredValue,
};
use std::sync::Arc;
use tla_core::ast::{BoundVar, Expr};
use tla_core::kani_types::HashMap;
use tla_core::{Span, Spanned};

#[derive(Clone)]
struct MockCapturedChain {
    locals: Vec<(Arc<str>, Value)>,
}

impl CapturedChain for MockCapturedChain {
    fn clone_box(&self) -> Box<dyn CapturedChain> {
        Box::new(self.clone())
    }

    fn as_any(&self) -> &dyn std::any::Any {
        self
    }

    fn materialize_locals(&self, env: &mut HashMap<Arc<str>, Value>) {
        for (name, value) in &self.locals {
            env.insert(Arc::clone(name), value.clone());
        }
    }
}

fn ident_expr(name: &str) -> Spanned<Expr> {
    Spanned::new(
        Expr::Ident(name.to_string(), tla_core::name_intern::NameId::INVALID),
        Span::dummy(),
    )
}

fn simple_bound(name: &str) -> BoundVar {
    BoundVar {
        name: Spanned::new(name.to_string(), Span::dummy()),
        domain: None,
        pattern: None,
    }
}

fn assert_binding_chain_mismatch(err: EvalError, site: &str) {
    match err {
        EvalError::Internal { message, .. } => {
            assert!(
                message.contains(site),
                "expected mismatch message to name {site}, got: {message}"
            );
            assert!(
                message.contains("expected BindingChain"),
                "expected BindingChain invariant message, got: {message}"
            );
        }
        other => panic!("expected internal captured-chain mismatch error, got: {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_closure_restore_rejects_non_binding_chain_capture() {
    let ctx = EvalCtx::new();
    let closure = ClosureValue::new(
        vec!["y".to_string()],
        ident_expr("x"),
        Arc::new(HashMap::new()),
        None,
    )
    .with_captured_chain(
        Box::new(MockCapturedChain {
            locals: vec![(Arc::from("x"), Value::int(42))],
        }),
        1,
    );

    let err = apply_closure_with_values(&ctx, &closure, &[Value::int(7)], None)
        .expect_err("closure restore should reject non-BindingChain captures");
    assert_binding_chain_mismatch(err, "build_closure_ctx");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lazy_func_restore_rejects_non_binding_chain_capture() {
    let ctx = EvalCtx::new();
    let lazy_func = Arc::new(LazyFuncValue::new(
        None,
        LazyDomain::General(Box::new(Value::set([Value::int(1)]))),
        simple_bound("y"),
        ident_expr("x"),
        LazyFuncCaptures::new(Arc::new(HashMap::new()), None, None, None).with_captured_chain(
            Box::new(MockCapturedChain {
                locals: vec![(Arc::from("x"), Value::int(42))],
            }),
            1,
        ),
    ));

    let err = apply_resolved_func_value(
        &ctx,
        &Value::LazyFunc(Arc::clone(&lazy_func)),
        Value::int(1),
        None,
        None,
        None,
    )
    .expect_err("lazy-function restore should reject non-BindingChain captures");
    assert_binding_chain_mismatch(err, "build_lazy_func_ctx");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_setpred_restore_rejects_non_binding_chain_capture() {
    let ctx = EvalCtx::new();
    let captures = SetPredCaptures::new(Arc::new(HashMap::new()), None, None).with_captured_chain(
        Box::new(MockCapturedChain {
            locals: vec![(Arc::from("x"), Value::Bool(true))],
        }),
        1,
    );
    let spv = SetPredValue::new_with_captures(
        Value::set([Value::int(1)]),
        simple_bound("y"),
        ident_expr("x"),
        captures,
    );

    let err = check_set_pred_membership(&ctx, &Value::int(1), &spv, None)
        .expect_err("set-predicate restore should reject non-BindingChain captures");
    assert_binding_chain_mismatch(err, "restore_setpred_ctx");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lazy_thunk_restore_rejects_non_binding_chain_capture() {
    let ctx = EvalCtx::new();
    let thunk = Value::Closure(Arc::new(
        ClosureValue::new(vec![], ident_expr("x"), Arc::new(HashMap::new()), None)
            .with_captured_chain(
                Box::new(MockCapturedChain {
                    locals: vec![(Arc::from("x"), Value::int(42))],
                }),
                1,
            ),
    ));

    let err = force_lazy_thunk_if_needed(&ctx, thunk)
        .expect_err("thunk forcing should reject non-BindingChain captures");
    assert_binding_chain_mismatch(err, "force_lazy_thunk_if_needed");
}
