// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

mod guard;
mod overlay;
mod zero_arg_cache;

use self::guard::try_guard_first_shortcircuit;
use self::overlay::eval_let_all_zero_arg;
use self::zero_arg_cache::eval_zero_arg_let_body;
// Re-export for child modules (overlay.rs needs build_lazy_func_from_ctx).
pub(in crate::eval_let) use super::build_lazy_func_from_ctx;
use super::{eval, EvalCtx, EvalError, EvalResult, Expr, LazyDomain, OpEnv, Span, Spanned, Value};
use std::sync::Arc;
use tla_core::ast::{BoundVar, OperatorDef};
use tla_core::expr_mentions_name_v;

/// Evaluate a LET expression: `LET defs IN body`
///
/// LET binds local operator definitions (including zero-arg operators).
/// Definitions can be recursive, so we must register them before evaluating the body.
/// Uses local_ops to avoid cloning the entire shared context.
///
/// Fix for #376: Zero-arg LET definitions must capture context at the LET site.
/// Previously, ALL defs went to local_ops and zero-arg ones used ZERO_ARG_OP_CACHE
/// which didn't properly track dependencies (e.g., `LET exp == 2^n` inside recursive
/// function would return stale cached `exp` when `n` changed).
///
/// New approach (TLC-aligned Option A from designs/2026-01-26-let-zero-arg-lazyvalue.md):
/// - Defs with arity > 0: still go to local_ops
/// - Zero-arg InstanceExpr: still go to local_ops (evaluated via eval_module_ref)
/// - Zero-arg recursive FuncDef: create LazyFuncValue, bind in local_stack
/// - Zero-arg non-recursive: evaluate eagerly at LET site, bind in local_stack
///
/// Using local_stack (via bind_local) ensures lookup finds the value BEFORE checking
/// local_ops, bypassing the broken cache entirely.
pub(super) fn eval_let(
    ctx: &EvalCtx,
    defs: &[OperatorDef],
    body: &Spanned<Expr>,
    span: Option<Span>,
) -> EvalResult<Value> {
    // Part of #2963: Guard-first optimization for LET ... IN /\ guard /\ ...
    //
    // TLC uses LazyValue for LET defs, so disabled action guards like
    // `state = SPLIT_LEAF` short-circuit before evaluating any LET def.
    // TLA2 eagerly evaluates ALL LET defs before the body, wasting work
    // on disabled actions. For btree (374K states, 11 actions), most actions
    // are disabled per state, but their 4-8 LET defs (including expensive
    // CHOOSE/ParentOf/PivotOf) are evaluated regardless.
    //
    // This optimization: if the body starts with And(guard, ...) where the
    // guard doesn't mention any LET def name, evaluate the guard first in
    // the original context. If false, skip all LET def evaluations.
    if let Expr::And(first, _rest) = &body.node {
        if let Some(false) = try_guard_first_shortcircuit(ctx, defs, first) {
            return Ok(Value::Bool(false));
        }
    }

    // Part of #1093 + #3010: All-zero-arg fast path using LetDefOverlay.
    // Handles simple scalars, recursive FuncDefs, and InstanceExprs without
    // cloning OpEnv. Matches TLC's Context.cons model (Tool.java:1848-1860).
    // Only falls to the slow path when arity>0 defs are present.
    if !defs.is_empty() && defs.iter().all(|def| def.params.is_empty()) {
        let result = eval_let_all_zero_arg(ctx, defs, body, span);
        if let Some(r) = result {
            return r;
        }
        // Fall through to general path if overlay path couldn't handle it
        // (e.g., eager eval failed and needs lazy thunk handling).
    }

    let mut local_ops: OpEnv = match &ctx.local_ops {
        Some(ops) => (**ops).clone(),
        None => OpEnv::default(),
    };

    // Only add defs with arity > 0 or special cases to local_ops
    for def in defs {
        // Always add defs with parameters (arity > 0) to local_ops
        if !def.params.is_empty() {
            local_ops.insert(def.name.node.clone(), Arc::new(def.clone()));
            continue;
        }
        // Zero-arg InstanceExpr must stay in local_ops (evaluated specially via eval_module_ref)
        if matches!(&def.body.node, Expr::InstanceExpr(_, _)) {
            local_ops.insert(def.name.node.clone(), Arc::new(def.clone()));
            continue;
        }
        // Zero-arg recursive FuncDef needs to stay in local_ops for recursive lookup,
        // but we'll also bind a LazyFuncValue in local_stack below
        if let Expr::FuncDef(_, func_body) = &def.body.node {
            if expr_mentions_name_v(&func_body.node, def.name.node.as_str()) {
                local_ops.insert(def.name.node.clone(), Arc::new(def.clone()));
            }
        }
        // Other zero-arg defs will be eagerly evaluated and bound in local_stack
        // DO NOT add to local_ops - this avoids the broken ZERO_ARG_OP_CACHE
    }
    let mut new_ctx = ctx.clone();
    {
        let ops = Arc::new(local_ops);
        let id = crate::cache::scope_ids::compute_local_ops_scope_id(&ops);
        let s = new_ctx.stable_mut();
        s.local_ops = Some(ops);
        s.scope_ids.local_ops = id;
    }

    // Process zero-argument definitions - bind as values in local_stack.
    // This avoids the ZERO_ARG_OP_CACHE which doesn't properly capture context.
    for def in defs {
        if def.params.is_empty() {
            // Named instances inside LET (e.g. `LET G == INSTANCE Graphs IN ...`) are
            // represented as zero-arg operator defs whose body is an `InstanceExpr`.
            //
            // `InstanceExpr` is not a value and must not be evaluated eagerly here.
            // Module references (`G!Op`) resolve the instance info from the operator
            // definition body via `eval_module_ref`.
            if matches!(&def.body.node, Expr::InstanceExpr(_, _)) {
                continue;
            }

            if let Expr::FuncDef(bounds, func_body) = &def.body.node {
                // Handle directly-recursive local function definitions by using LazyFunc.
                let def_name = def.name.node.as_str();
                if expr_mentions_name_v(&func_body.node, def_name) {
                    let domain_val = eval_let_func_domain(&new_ctx, bounds, span)?;

                    if !domain_val.is_set() {
                        return Err(EvalError::type_error(
                            "Set",
                            &domain_val,
                            Some(def.body.span),
                        ));
                    }

                    let name = Arc::from(def_name);
                    // Issue #174: capture both env+local_stack and local_ops for closures.
                    // This is critical for recursive LET functions like TC5's CR that
                    // reference outer variables (e.g., operator parameters R, S, s, t).
                    let lazy = build_lazy_func_from_ctx(
                        &new_ctx,
                        Some(Arc::clone(&name)),
                        LazyDomain::General(Box::new(domain_val)),
                        bounds,
                        *func_body.clone(),
                    );

                    // Fix #376: Use bind_local instead of env.insert to add to local_stack.
                    // This ensures lookup finds the value BEFORE checking local_ops.
                    // Part of #1383: new_ctx is owned and reassigned — use into_bind_local
                    new_ctx = new_ctx.into_bind_local(name, Value::LazyFunc(Arc::new(lazy)));
                    continue;
                }
                // Part of #562: Non-self-recursive FuncDef - eagerly evaluate.
                // FuncDef creates Func values which are safe (never fail).
                // Making these lazy causes stack overflow when the Func body
                // references outer recursive functions (e.g., SchedulingAllocator's PermSeqs).
                let val = eval(&new_ctx, &def.body)?;
                // Part of #1383: new_ctx is owned and reassigned — use into_bind_local
                new_ctx = new_ctx.into_bind_local(def.name.node.clone(), val);
                continue;
            }

            // Part of #2955 + #2566: Eagerly evaluate zero-arg LET bodies with
            // constant detection. Constant results are cached for the entire run.
            // Non-constant results use plain eval on subsequent calls (avoiding
            // eval_with_dep_tracking overhead).
            if let Ok(val) = eval_zero_arg_let_body(&new_ctx, &def.body) {
                new_ctx = new_ctx.into_bind_local(def.name.node.clone(), val);
                continue;
            }
            // Eager eval failed — fall through to lazy thunk to defer the error.

            // Fix #562: Lazily bind zero-arg definitions as thunks, matching TLC's LazyValue.
            // This captures the definition-site context (env + local bindings + local_ops)
            // and defers evaluation until the name is actually referenced.
            //
            // TLC reference: Tool.java:1777-1782 creates LazyValue for arity-0 LET defs.
            // This prevents ChooseFailed errors in unreachable branches (e.g., btree's
            // `LET maxKey == Max(keys) IN keys = {} \/ key >= maxKey` where Max({}) fails
            // but is guarded by short-circuit disjunction).
            //
            // We use Value::Closure with empty params as the lazy thunk - TLA+ syntax
            // doesn't allow zero-arg LAMBDAs, so this representation is unambiguous.
            // Part of #2895: Use create_closure for O(1) chain capture.
            let thunk = Value::Closure(Arc::new(new_ctx.create_closure(
                vec![], // No params = lazy thunk marker
                def.body.clone(),
                new_ctx.local_ops.clone(),
            )));
            // Part of #1383: new_ctx is owned and reassigned — use into_bind_local
            new_ctx = new_ctx.into_bind_local(def.name.node.clone(), thunk);
        }
    }

    eval(&new_ctx, body)
}

/// Evaluate the domain for a recursive LET function definition.
/// Handles both single-bound and multi-bound function signatures.
pub(super) fn eval_let_func_domain(
    ctx: &EvalCtx,
    bounds: &[BoundVar],
    span: Option<Span>,
) -> EvalResult<Value> {
    if bounds.len() == 1 {
        let domain_expr = bounds[0]
            .domain
            .as_ref()
            .ok_or_else(|| EvalError::Internal {
                message: "Function definition requires bounded variable".into(),
                span,
            })?;
        eval(ctx, domain_expr)
    } else {
        let mut components = Vec::with_capacity(bounds.len());
        for b in bounds {
            let domain_expr = b.domain.as_ref().ok_or_else(|| EvalError::Internal {
                message: "Function definition requires bounded variable".into(),
                span,
            })?;
            components.push(eval(ctx, domain_expr)?);
        }
        Ok(Value::tuple_set(components))
    }
}
