// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Closure creation from higher-order parameters, and evaluation context builders
//! for closures and lazy functions.
//!
//! Extracted from `apply.rs` to keep files under 500 LOC.

use super::super::{EvalCtx, EvalError, EvalResult, StateEnvRef};
use super::restore_captured_binding_chain;
use crate::value::{ClosureValue, LazyDomain, LazyFuncCaptures, LazyFuncValue, Value};
use std::rc::Rc;
use std::sync::Arc;
use tla_core::ast::{BoundVar, Expr};
use tla_core::name_intern::intern_name;
use tla_core::{Span, Spanned};

/// Create a closure from an argument expression for a higher-order parameter
pub(crate) fn create_closure_from_arg(
    ctx: &EvalCtx,
    arg: &Spanned<Expr>,
    param_name: &str,
    expected_arity: usize,
    _span: Option<Span>,
) -> EvalResult<Value> {
    match &arg.node {
        Expr::Lambda(lambda_params, body) => {
            let params: Vec<String> = lambda_params.iter().map(|p| p.node.clone()).collect();
            if params.len() != expected_arity {
                return Err(EvalError::ArityMismatch {
                    op: format!("<lambda:{param_name}>"),
                    expected: expected_arity,
                    got: params.len(),
                    span: Some(arg.span),
                });
            }
            // Fixes #174: Must capture local_stack bindings (e.g., quantified variables)
            // AND local_ops (e.g., LET-defined operators)
            // Part of #2895: Use create_closure for O(1) chain capture.
            Ok(Value::Closure(Arc::new(ctx.create_closure(
                params,
                (**body).clone(),
                ctx.local_ops.clone(),
            ))))
        }
        Expr::OpRef(op) => {
            // Built-in operator passed as a higher-order argument (e.g., ReduceSet(\\cap, ...)).
            // Represent it as a closure whose body is the OpRef. `apply_closure(_with_values)`
            // has a fast path for OpRef bodies.
            if expected_arity != 2 {
                return Err(EvalError::Internal {
                    message: format!(
                        "Expected {expected_arity}-ary operator for higher-order parameter '{param_name}', got built-in '{op}'"
                    ),
                    span: Some(arg.span),
                });
            }
            // Fixes #174: Must capture local_stack bindings AND local_ops
            // Part of #2895: Use create_closure for O(1) chain capture.
            Ok(Value::Closure(Arc::new(ctx.create_closure(
                vec!["x".to_string(), "y".to_string()],
                Spanned {
                    node: Expr::OpRef(op.clone()),
                    span: arg.span,
                },
                ctx.local_ops.clone(),
            ))))
        }
        Expr::Ident(name, orig_name_id) => {
            // Could be an operator name being passed as argument
            // Check if it's already a closure in env (use lookup for local_stack support)
            if let Some(Value::Closure(ref c)) = ctx.lookup(name) {
                if c.params().len() != expected_arity {
                    return Err(EvalError::ArityMismatch {
                        op: name.clone(),
                        expected: expected_arity,
                        got: c.params().len(),
                        span: Some(arg.span),
                    });
                }
                return Ok(Value::Closure(Arc::clone(c)));
            }
            // Check if it's a user-defined operator
            if let Some(def) = ctx.get_op(name) {
                if def.params.len() != expected_arity {
                    return Err(EvalError::ArityMismatch {
                        op: name.clone(),
                        expected: expected_arity,
                        got: def.params.len(),
                        span: Some(arg.span),
                    });
                }
                // Create a closure that wraps the operator
                // The operator's parameters become the closure's parameters
                // Fixes #174: Must capture local_stack bindings (e.g., quantified variables)
                // AND local_ops (e.g., LET-defined operators like S in `LET S == ... IN`)
                let params: Vec<String> = def.params.iter().map(|p| p.name.node.clone()).collect();
                // Part of #2895: Use create_closure for O(1) chain capture.
                Ok(Value::Closure(Arc::new(ctx.create_closure(
                    params,
                    def.body.clone(),
                    ctx.local_ops.clone(),
                ))))
            } else {
                // Check if it might be a built-in stdlib operator (Add, Half, etc.)
                // Create a closure that calls the built-in via Apply
                // Part of #2993: Pre-intern synthetic param names and pass through
                // the original NameId to avoid runtime lookup_name_id() calls.
                let op_name_id = *orig_name_id;
                let x_name_id = intern_name("__x");
                let y_name_id = intern_name("__y");
                if expected_arity == 2 {
                    // Create parameters for the closure
                    let params = vec!["__x".to_string(), "__y".to_string()];
                    // Create the body: Apply(name, [__x, __y])
                    let body = Spanned {
                        node: Expr::Apply(
                            Box::new(Spanned {
                                node: Expr::Ident(name.clone(), op_name_id),
                                span: arg.span,
                            }),
                            vec![
                                Spanned {
                                    node: Expr::Ident("__x".to_string(), x_name_id),
                                    span: arg.span,
                                },
                                Spanned {
                                    node: Expr::Ident("__y".to_string(), y_name_id),
                                    span: arg.span,
                                },
                            ],
                        ),
                        span: arg.span,
                    };
                    // Fixes #174: Must capture local_stack bindings AND local_ops
                    // Part of #2895: Use create_closure for O(1) chain capture.
                    Ok(Value::Closure(Arc::new(ctx.create_closure(
                        params,
                        body,
                        ctx.local_ops.clone(),
                    ))))
                } else if expected_arity == 1 {
                    let params = vec!["__x".to_string()];
                    let body = Spanned {
                        node: Expr::Apply(
                            Box::new(Spanned {
                                node: Expr::Ident(name.clone(), op_name_id),
                                span: arg.span,
                            }),
                            vec![Spanned {
                                node: Expr::Ident("__x".to_string(), x_name_id),
                                span: arg.span,
                            }],
                        ),
                        span: arg.span,
                    };
                    // Fixes #174: Must capture local_stack bindings AND local_ops
                    // Part of #2895: Use create_closure for O(1) chain capture.
                    Ok(Value::Closure(Arc::new(ctx.create_closure(
                        params,
                        body,
                        ctx.local_ops.clone(),
                    ))))
                } else {
                    Err(EvalError::Internal {
                        message: format!(
                            "Expected operator for higher-order parameter '{param_name}', got undefined '{name}'"
                        ),
                        span: Some(arg.span),
                    })
                }
            }
        }
        _ => Err(EvalError::Internal {
            message: format!(
                "Expected lambda or operator for higher-order parameter '{param_name}'"
            ),
            span: Some(arg.span),
        }),
    }
}

/// Build an EvalCtx from a closure's captured environment.
///
/// CRITICAL FIX (#174): Uses ONLY the closure's captured local_ops, NOT the caller's.
/// TLC's OpLambdaValue.eval() starts from the CAPTURED context, not the caller's.
/// Using caller's local_ops causes name collisions (e.g., TC5's R parameter shadowed by
/// RR's captured R set when RR is defined inside a ForAll over R).
///
/// Part of #1264: Extracted from 2 duplicate sites (apply_closure, apply_closure_with_values).
pub(super) fn build_closure_ctx(ctx: &EvalCtx, closure: &ClosureValue) -> EvalResult<EvalCtx> {
    // Part of #2955: Direct construction with hot/cold split.
    // Clone stable fields (1 deep copy), then override env/local_ops.
    let mut new_stable = (*ctx.stable).clone();
    new_stable.env = Arc::clone(closure.env_arc());
    new_stable.local_ops = closure.local_ops().cloned();
    // Part of #3099: Invalidate scope_ids.local_ops since we replaced local_ops
    // with the closure's captured ops, diverging from the inherited caller id.
    new_stable.scope_ids.local_ops = crate::cache::scope_ids::INVALIDATED;
    let (base_bindings, base_depth) = restore_captured_binding_chain(
        closure.captured_chain(),
        closure.captured_chain_depth(),
        "build_closure_ctx",
        Some(closure.body().span),
    )?;
    Ok(EvalCtx {
        stable: Rc::new(new_stable),
        binding_depth: base_depth,
        // Part of #2956: Closures don't inherit call-by-name subs — the closure body
        // was written in a different scope from the application site.
        call_by_name_subs: None,
        tlc_action_context: ctx.tlc_action_context.clone(),
        recursion_depth: ctx.recursion_depth,
        active_lazy_func: ctx.active_lazy_func.clone(),
        // Fix #2741: Use DEFINITION-site chain, not APPLICATION-site chain.
        bindings: base_bindings,
        let_def_overlay: crate::let_def_chain::LetDefOverlay::empty(),
        sparse_next_state_env: ctx.sparse_next_state_env,
    })
}

/// Build an EvalCtx from a LazyFuncValue's captured environment.
///
/// CRITICAL FIX (#174): Uses ONLY the LazyFunc's captured local_ops, NOT the caller's.
/// This mirrors the fix in build_closure_ctx. TLC evaluates function bodies using the
/// context captured at definition time, not the caller's context.
///
/// Part of #2955: Env is now Arc-shared from the LazyFuncValue — no HashMap clone.
/// Recursive self-reference is pushed onto the BindingChain instead of env.insert,
/// matching TLC's `makeRecursive` pattern (Context.cons(fname, this)).
///
/// Part of #1264: Extracted from 2 duplicate sites (eval_func_apply, apply_except_spec).
pub(super) fn build_lazy_func_ctx(
    ctx: &EvalCtx,
    f: &Arc<LazyFuncValue>,
    recursion_depth: u32,
) -> EvalResult<EvalCtx> {
    // Part of #3395: Fast path for self-recursive calls.
    //
    // When a LazyFunc body references itself (e.g., `reduced[i-1]` inside
    // `reduced[i]`), the caller's ctx already has the correct captured chain and
    // self-reference — it was set up by the first build_lazy_func_ctx call.
    // Detect this by checking whether the caller is already evaluating this exact
    // LazyFuncValue instance, not merely another named function that shares the
    // same env Arc.
    //
    // TLC equivalent: FcnLambdaValue.apply just does Context.cons(param, arg)
    // because the self-reference was set up once by makeRecursive. We now
    // match that efficiency for recursive levels 2+.
    //
    // Cost reduction per self-recursive call:
    //   Before: EvalCtxStable clone + Rc alloc + chain restore + self-ref push
    //   After:  2 refcount bumps + hot-field writes
    if f.name().is_some()
        && ctx
            .active_lazy_func
            .as_ref()
            .is_some_and(|active| Arc::ptr_eq(active, f))
    {
        // Reuse everything — the binding chain already has the self-reference
        // from the first build_lazy_func_ctx call, and previous parameter
        // bindings will be shadowed by the new one pushed by the caller.
        let mut new_ctx = ctx.clone();
        new_ctx.recursion_depth = recursion_depth;
        // Clear call_by_name_subs and let_def_overlay for safety
        // (matching the full path's semantics).
        new_ctx.call_by_name_subs = None;
        new_ctx.let_def_overlay = crate::let_def_chain::LetDefOverlay::empty();
        return Ok(new_ctx);
    }

    // Issue #392: Use captured state_env/next_state_env if present (TLC parity).
    // TLC captures state at definition time; fall back to caller's state if not captured.
    let state_env = f
        .captured_state()
        .map(StateEnvRef::from_slice)
        .or(ctx.state_env);
    let next_state_env = f
        .captured_next_state()
        .map(StateEnvRef::from_slice)
        .or(ctx.next_state_env);
    // Part of #2955: Arc::clone the env from captures instead of cloning the HashMap.
    // This is the single highest-impact optimization for GameOfLife: eliminates ~7.4M
    // HashMap clones (previously ~50 entries × 8.4M applications = ~420M key-value clones).
    let mut new_stable = (*ctx.stable).clone();
    new_stable.env = Arc::clone(f.env_arc());
    new_stable.local_ops = f.local_ops().cloned(); // Use captured local_ops, not ctx's
                                                   // Part of #3099: Invalidate scope_ids.local_ops since we replaced local_ops
                                                   // with the LazyFuncValue's captured ops, diverging from the inherited caller id.
    new_stable.scope_ids.local_ops = crate::cache::scope_ids::INVALIDATED;
    new_stable.state_env = state_env;
    new_stable.next_state_env = next_state_env;
    let (base_bindings, base_depth) = restore_captured_binding_chain(
        f.captured_chain(),
        f.captured_chain_depth(),
        "build_lazy_func_ctx",
        Some(f.body().span),
    )?;
    let mut new_ctx = EvalCtx {
        stable: Rc::new(new_stable),
        binding_depth: base_depth,
        // Part of #2956: LazyFunc doesn't inherit call-by-name subs — the function body
        // was written in a different scope from the application site.
        call_by_name_subs: None,
        tlc_action_context: ctx.tlc_action_context.clone(),
        recursion_depth,
        active_lazy_func: Some(Arc::clone(f)),
        // Fix #2741: Use DEFINITION-site chain, not APPLICATION-site chain.
        // The captured chain IS the definition-site bindings (TLC parity).
        bindings: base_bindings,
        let_def_overlay: crate::let_def_chain::LetDefOverlay::empty(),
        sparse_next_state_env: ctx.sparse_next_state_env,
    };
    // Part of #2955: Push recursive self-reference onto BindingChain instead of env.insert.
    // TLC's FcnLambdaValue.makeRecursive() does: this.con = this.con.cons(fname, this).
    // BindingChain is consulted before env during lookup, so this correctly shadows.
    if let Some(name) = f.name() {
        let name_id = intern_name(name.as_ref());
        new_ctx.push_binding_preinterned(Arc::clone(name), Value::LazyFunc(Arc::clone(f)), name_id);
    }
    Ok(new_ctx)
}

/// Build a LazyFuncValue capturing the current evaluation context.
///
/// Unifies the `if bounds.len() == 1 { new() } else { new_multi() }` dispatch
/// pattern that was duplicated across eval_ident.rs (2 sites) and eval_let.rs (1 site).
///
/// Part of #1264: Extracted from 3 duplicate sites.
pub(crate) fn build_lazy_func_from_ctx(
    ctx: &EvalCtx,
    name: Option<Arc<str>>,
    domain: LazyDomain,
    bounds: &[BoundVar],
    body: Spanned<Expr>,
) -> LazyFuncValue {
    let (captured_state, captured_next_state) = ctx.snapshot_state_envs();
    // Part of #2955: Capture the BindingChain directly — O(1) Arc clone.
    // At application time, build_lazy_func_ctx restores this chain instead of
    // rebuilding from captured_bindings (eliminates ~84M Rc allocs for GameOfLife).
    // Part of #2895, #2989: BindingChain is the sole source of truth for local
    // bindings. env stores only the module-level environment via Arc::clone (O(1)).
    let captures = LazyFuncCaptures::new(
        Arc::clone(&ctx.env),
        ctx.local_ops.clone(),
        captured_state,
        captured_next_state,
    )
    .with_captured_chain(Box::new(ctx.bindings.clone()), ctx.binding_depth);
    if bounds.len() == 1 {
        LazyFuncValue::new(name, domain, bounds[0].clone(), body, captures)
    } else {
        LazyFuncValue::new_multi(name, domain, bounds.to_vec(), body, captures)
    }
}
