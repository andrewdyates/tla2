// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::{eval_live_expr_core, LiveExprEvaluator};
use crate::error::EvalResult;
use crate::eval::{BindingChain, EvalCtx};
use crate::liveness::LiveExpr;
use crate::state::State;
use crate::test_support::parse_module;
use crate::Value;
use std::sync::Arc;
use tla_core::ast::{Expr, Module, Unit};
use tla_core::Spanned;
use tla_eval::tir::TirProgram;

const TIR_LIVENESS_MODULE: &str = r#"
---- MODULE TirLivenessLeaves ----
VARIABLE x
StateLeaf == x = 1
ActionLeaf == x' = 2
====
"#;

struct NoopEvaluator;

impl LiveExprEvaluator for NoopEvaluator {
    fn eval_subscript_changed(
        &self,
        _ctx: &EvalCtx,
        _current: &State,
        _next: &State,
        _sub_expr: &Arc<Spanned<Expr>>,
        _tag: u32,
    ) -> EvalResult<bool> {
        unreachable!("subscript evaluation is not used in these leaf tests")
    }

    fn eval_enabled(
        &mut self,
        _ctx: &EvalCtx,
        _current_state: &State,
        _action: &Arc<Spanned<Expr>>,
        _bindings: &Option<BindingChain>,
        _require_state_change: bool,
        _subscript: &Option<Arc<Spanned<Expr>>>,
        _tag: u32,
    ) -> EvalResult<bool> {
        unreachable!("ENABLED evaluation is not used in these leaf tests")
    }
}

fn operator_body(module: &Module, name: &str) -> Arc<Spanned<Expr>> {
    module
        .units
        .iter()
        .find_map(|unit| match &unit.node {
            Unit::Operator(def) if def.name.node == name => Some(Arc::new(def.body.clone())),
            _ => None,
        })
        .unwrap_or_else(|| panic!("operator '{name}' not found"))
}

fn make_ctx_with_registered_var() -> EvalCtx {
    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    ctx
}

#[test]
fn test_eval_live_expr_core_state_pred_accepts_tir_capable_leaf() {
    crate::eval::clear_for_test_reset();

    let module = parse_module(TIR_LIVENESS_MODULE);
    let tir = TirProgram::from_modules(&module, &[]);
    let expr = operator_body(&module, "StateLeaf");
    let live_expr = LiveExpr::StatePred {
        expr: Arc::clone(&expr),
        bindings: None,
        tag: 1,
    };
    let state = State::from_pairs([("x", Value::int(1))]);

    let mut ctx = make_ctx_with_registered_var();
    let registry = ctx.shared().var_registry.clone();
    let values = state.to_values(&registry);
    let _state_guard = ctx.bind_state_array_guard(&values);
    ctx.load_module(&module);

    let tir_value = tir
        .try_eval_expr(&ctx, &expr)
        .expect("StateLeaf should lower to TIR")
        .expect("StateLeaf TIR evaluation should succeed");
    assert_eq!(
        tir_value,
        Value::Bool(true),
        "StateLeaf TIR baseline should be TRUE"
    );

    let mut evaluator = NoopEvaluator;
    let result = eval_live_expr_core(&mut evaluator, &ctx, &live_expr, &state, None, Some(&tir))
        .expect("TIR-capable state predicate should evaluate successfully");
    assert!(result, "StateLeaf should evaluate TRUE via TIR");
}

#[test]
fn test_eval_live_expr_core_action_pred_accepts_tir_capable_leaf() {
    crate::eval::clear_for_test_reset();

    let module = parse_module(TIR_LIVENESS_MODULE);
    let tir = TirProgram::from_modules(&module, &[]);
    let expr = operator_body(&module, "ActionLeaf");
    let live_expr = LiveExpr::ActionPred {
        expr: Arc::clone(&expr),
        bindings: None,
        tag: 2,
    };
    let current_state = State::from_pairs([("x", Value::int(1))]);
    let next_state = State::from_pairs([("x", Value::int(2))]);

    let mut ctx = make_ctx_with_registered_var();
    let registry = ctx.shared().var_registry.clone();
    let current_values = current_state.to_values(&registry);
    let next_values = next_state.to_values(&registry);
    let _state_guard = ctx.bind_state_array_guard(&current_values);
    let _next_guard = ctx.bind_next_state_array_guard(&next_values);
    ctx.load_module(&module);

    let tir_value = tir
        .try_eval_expr(&ctx, &expr)
        .expect("ActionLeaf should lower to TIR")
        .expect("ActionLeaf TIR evaluation should succeed");
    assert_eq!(
        tir_value,
        Value::Bool(true),
        "ActionLeaf TIR baseline should be TRUE"
    );

    let mut evaluator = NoopEvaluator;
    let result = eval_live_expr_core(
        &mut evaluator,
        &ctx,
        &live_expr,
        &current_state,
        Some(&next_state),
        Some(&tir),
    )
    .expect("TIR-capable action predicate should evaluate successfully");
    assert!(result, "ActionLeaf should evaluate TRUE via TIR");
}
