// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Operator application dispatch (`eval_apply`) and closure invocation
//! (`apply_closure`, `apply_closure_with_values`).
//!
//! Extracted from `helpers/mod.rs` as part of #1669.

use super::super::{apply_builtin_binary_op, eval, EvalCtx, EvalError, EvalResult};
use super::builtin_dispatch::{eval_builtin, should_prefer_builtin_override};
use super::closures::{build_closure_ctx, create_closure_from_arg};
use super::param_cache::{
    get_closure_param_cache, get_param_cache, is_trivially_evaluable, nary_cache_enabled,
};
use crate::binding_chain::{BindingValue, LazyBinding};
use crate::cache::{
    current_state_lookup_mode, hash_args, nary_insert, nary_lookup, op_cache_entry_valid,
    propagate_cached_deps, CachedOpResult, NaryOpCacheEntry, NaryOpCacheKey, OpDepGuard,
};
use crate::tir::{closure_tir_body_expr, eval_tir, record_closure_body_eval};
use crate::value::{ClosureValue, Value};
use smallvec::SmallVec;
use std::sync::Arc;
use tla_core::ast::{Expr, OperatorDef, Substitution};
use tla_core::name_intern::intern_name;
use tla_core::{NameId, Span, Spanned};

/// Inline capacity for preinterned binding buffers. Operators with <= 4 parameters
/// (the vast majority — TLA+ operators rarely exceed 3-4 params) avoid heap
/// allocation entirely. Part of #3805: eliminates ~5.5% allocator overhead
/// measured by profiling (mi_malloc+mi_free self-time).
type PreinternedBuf = SmallVec<[(Arc<str>, BindingValue, NameId); 4]>;

enum UserOpCacheOutcome {
    Hit(Value),
    Miss(NaryOpCacheKey),
}

pub(crate) fn eval_apply(
    ctx: &EvalCtx,
    op_expr: &Spanned<Expr>,
    args: &[Spanned<Expr>],
    span: Option<Span>,
) -> EvalResult<Value> {
    // Check if it's an identifier (operator name or closure variable)
    if let Expr::Ident(name, _) = &op_expr.node {
        // First check if this is a closure bound in the environment
        // Use lookup() to check local_stack first for O(1) enumeration bindings
        if let Some(Value::Closure(ref closure)) = ctx.lookup(name) {
            return apply_closure(ctx, closure, args, span);
        }
        // If it's a non-closure value in env, fall through to check ops

        // Apply operator replacement if configured (e.g., Seq <- BoundedSeq)
        let resolved_name = ctx.resolve_op_name(name);

        // Check for user-defined operators (allows shadowing stdlib)
        if let Some(def) = ctx.get_op(resolved_name) {
            return apply_user_op_with_exprs(ctx, resolved_name, def, args, span);
        }

        // Check for built-in operators from stdlib (after user-defined)
        // Use resolved name for builtins too
        if let Some(result) = eval_builtin(ctx, resolved_name, args, span)? {
            return Ok(result);
        }

        // Undefined operator
        return Err(EvalError::UndefinedOp {
            name: resolved_name.to_string(),
            span,
        });
    }

    // If we get here with Apply, evaluate the operator expression
    // It might be a closure or other callable value
    let fv = eval(ctx, op_expr)?;
    if let Value::Closure(ref closure) = &fv {
        return apply_closure(ctx, closure, args, span);
    }

    Err(EvalError::Internal {
        message: format!("Cannot apply non-operator value: {fv:?}"),
        span,
    })
}

fn user_op_cacheable(def: &Arc<OperatorDef>) -> bool {
    // TEMP DEBUG #4145: Selective cache disable to isolate which operator is broken.
    if std::env::var("TLA2_DEBUG_NARY_SKIP").ok().as_deref() == Some(&def.name.node) {
        return false;
    }
    !def.is_recursive && !def.params.is_empty() && def.params.iter().all(|p| p.arity == 0)
}

fn prepare_user_op_cache(
    ctx: &EvalCtx,
    resolved_name: &str,
    def: &Arc<OperatorDef>,
    arg_values: &[Value],
) -> Option<UserOpCacheOutcome> {
    if !user_op_cacheable(def) || !nary_cache_enabled() || arg_values.is_empty() {
        return None;
    }

    let is_instance_op = ctx
        .local_ops
        .as_ref()
        .and_then(|lo| lo.get(resolved_name))
        .is_some();
    let key = NaryOpCacheKey {
        shared_id: ctx.shared.id,
        local_ops_id: crate::cache::scope_ids::resolve_local_ops_id(
            ctx.scope_ids.local_ops,
            &ctx.local_ops,
        ),
        instance_subs_id: crate::cache::scope_ids::resolve_instance_subs_id(
            ctx.scope_ids.instance_substitutions,
            &ctx.instance_substitutions,
        ),
        op_name: intern_name(resolved_name),
        def_loc: def.body.span.start,
        is_next_state: current_state_lookup_mode(ctx) == crate::cache::StateLookupMode::Next,
        args_hash: hash_args(arg_values),
        param_args_hash: if is_instance_op {
            ctx.stable.param_args_hash
        } else {
            0
        },
    };

    if let Some(result) = nary_lookup(&key, arg_values, op_cache_entry_valid, ctx) {
        propagate_cached_deps(ctx, &result.deps);
        return Some(UserOpCacheOutcome::Hit(result.value));
    }

    // Part of #3962: Read from EvalRuntimeState shadow instead of TLS.
    if crate::cache::lifecycle::in_enabled_scope_ctx(ctx) {
        if let Some(result) =
            crate::cache::op_result_cache::nary_constant_fallback(&key, arg_values)
        {
            propagate_cached_deps(ctx, &result.deps);
            return Some(UserOpCacheOutcome::Hit(result.value.clone()));
        }
    }

    Some(UserOpCacheOutcome::Miss(key))
}

fn eval_user_op_body_with_bindings(
    ctx: &EvalCtx,
    def: &Arc<OperatorDef>,
    preinterned: PreinternedBuf,
    cache_key: Option<NaryOpCacheKey>,
    cache_values: Option<&[Value]>,
) -> EvalResult<Value> {
    let mut new_ctx = ctx.bind_preinterned(preinterned);
    new_ctx.install_outermost_tlc_action_context(def);

    if let Some(key) = cache_key {
        let base_stack_len = ctx.binding_depth;
        let guard = OpDepGuard::from_ctx(ctx, base_stack_len);
        let result = eval(&new_ctx, &def.body)?;

        if let Some(mut deps) = guard.try_take_deps() {
            // Fix #3024: Strip internal locals to enable nary cache insertion.
            deps.strip_internal_locals(&ctx.bindings, base_stack_len);
            propagate_cached_deps(ctx, &deps);
            // Part of #4158: Taint deps for LazyFunc results that capture state.
            // FuncDef evaluation produces LazyFuncs via `build_lazy_func_from_ctx()`
            // which captures state arrays, but dep tracking sees no state reads
            // during construction. Without this, empty deps → persistent partition →
            // stale captured state in subsequent BFS states.
            if let Value::LazyFunc(ref f) = result {
                if f.captured_state().is_some() || f.captured_next_state().is_some() {
                    deps.instance_lazy_read = true;
                }
            }
            // Part of #3962: Read from EvalRuntimeState shadow instead of TLS.
            if !deps.inconsistent && !crate::cache::lifecycle::in_enabled_scope_ctx(ctx) {
                let args_arc = Arc::from(
                    cache_values.expect("user-op cache insert requires the argument values"),
                );
                nary_insert(
                    key,
                    NaryOpCacheEntry {
                        args: args_arc,
                        result: CachedOpResult {
                            value: result.clone(),
                            deps,
                        },
                    },
                );
            }
        }

        return Ok(result);
    }

    eval(&new_ctx, &def.body)
}

fn apply_user_op_with_exprs(
    ctx: &EvalCtx,
    resolved_name: &str,
    def: &Arc<OperatorDef>,
    args: &[Spanned<Expr>],
    span: Option<Span>,
) -> EvalResult<Value> {
    if should_prefer_builtin_override(resolved_name, def, args.len(), ctx) {
        if let Some(result) = eval_builtin(ctx, resolved_name, args, span)? {
            return Ok(result);
        }
    }

    if def.params.len() != args.len() {
        return Err(EvalError::ArityMismatch {
            op: resolved_name.to_string(),
            expected: def.params.len(),
            got: args.len(),
            span,
        });
    }

    if def.is_recursive {
        if let Some(result) = super::recursive_fold::try_eval_recursive_fold(ctx, def, args, span)?
        {
            return Ok(result);
        }
    }

    if def.has_primed_param {
        let subs: Vec<Substitution> = def
            .params
            .iter()
            .zip(args.iter())
            .map(|(param, arg)| Substitution {
                from: param.name.clone(),
                to: arg.clone(),
            })
            .collect();
        let ctx_with_subs = ctx.with_call_by_name_subs(subs);
        return eval(&ctx_with_subs, &def.body);
    }

    let cached_params = get_param_cache(def);
    let mut cache_key = None;
    let mut forced_values = None;

    if user_op_cacheable(def) && nary_cache_enabled() {
        // Part of #3805: SmallVec avoids heap allocation for operators with <= 4 params.
        let mut arg_values: SmallVec<[Value; 4]> = SmallVec::with_capacity(def.params.len());
        let mut all_forced = true;
        for arg in args {
            match eval(ctx, arg) {
                Ok(v) => arg_values.push(v),
                Err(_) => {
                    all_forced = false;
                    break;
                }
            }
        }

        if all_forced {
            match prepare_user_op_cache(ctx, resolved_name, def, &arg_values) {
                Some(UserOpCacheOutcome::Hit(value)) => return Ok(value),
                Some(UserOpCacheOutcome::Miss(key)) => {
                    cache_key = Some(key);
                    forced_values = Some(arg_values);
                }
                None => {}
            }
        }
    }

    // Part of #3805: SmallVec avoids heap allocation for operators with <= 4 params.
    let mut preinterned: PreinternedBuf = SmallVec::with_capacity(def.params.len());
    for (i, (param, arg)) in def.params.iter().zip(args.iter()).enumerate() {
        let bv = if param.arity > 0 {
            BindingValue::eager(create_closure_from_arg(
                ctx,
                arg,
                &param.name.node,
                param.arity,
                span,
            )?)
        } else if let Some(ref vals) = forced_values {
            BindingValue::eager(vals[i].clone())
        } else if is_trivially_evaluable(&arg.node) {
            BindingValue::eager(eval(ctx, arg)?)
        } else {
            BindingValue::Lazy(Box::new(LazyBinding::new(
                arg as *const Spanned<tla_core::ast::Expr>,
                &ctx.bindings,
            )))
        };
        let (ref interned, name_id) = cached_params[i];
        preinterned.push((Arc::clone(interned), bv, name_id));
    }

    eval_user_op_body_with_bindings(ctx, def, preinterned, cache_key, forced_values.as_deref())
}

pub(crate) fn apply_user_op_with_values(
    ctx: &EvalCtx,
    resolved_name: &str,
    def: &Arc<OperatorDef>,
    arg_values: &[Value],
    span: Option<Span>,
) -> EvalResult<Value> {
    if def.params.len() != arg_values.len() {
        return Err(EvalError::ArityMismatch {
            op: resolved_name.to_string(),
            expected: def.params.len(),
            got: arg_values.len(),
            span,
        });
    }

    if def.has_primed_param {
        return Err(EvalError::Internal {
            message: format!(
                "direct user-op value apply reached primed-parameter operator '{resolved_name}'"
            ),
            span,
        });
    }

    let mut cache_key = None;
    if user_op_cacheable(def) && nary_cache_enabled() {
        match prepare_user_op_cache(ctx, resolved_name, def, arg_values) {
            Some(UserOpCacheOutcome::Hit(value)) => return Ok(value),
            Some(UserOpCacheOutcome::Miss(key)) => cache_key = Some(key),
            None => {}
        }
    }

    let cached_params = get_param_cache(def);
    // Part of #3805: SmallVec avoids heap allocation for operators with <= 4 params.
    let preinterned: PreinternedBuf = arg_values
        .iter()
        .enumerate()
        .map(|(i, value)| {
            let (ref interned, name_id) = cached_params[i];
            (
                Arc::clone(interned),
                BindingValue::eager(value.clone()),
                name_id,
            )
        })
        .collect();

    let cache_values = if cache_key.is_some() {
        Some(arg_values)
    } else {
        None
    };
    eval_user_op_body_with_bindings(ctx, def, preinterned, cache_key, cache_values)
}

fn eval_closure_body(
    ctx: &EvalCtx,
    closure: &ClosureValue,
    preinterned: PreinternedBuf,
) -> EvalResult<Value> {
    let mut closure_ctx = build_closure_ctx(ctx, closure)?;
    if let Some(name) = closure.name() {
        closure_ctx.push_binding_preinterned(
            Arc::clone(name),
            Value::Closure(Arc::new(closure.clone())),
            intern_name(name.as_ref()),
        );
    }
    let ctx_with_bindings = closure_ctx.bind_preinterned(preinterned);
    if let Some(tir_body) = closure_tir_body_expr(closure) {
        record_closure_body_eval();
        // Part of #3392: fall back to AST body if TIR eval fails. This mirrors
        // eval_named_op's fallback pattern and handles TIR expressiveness gaps
        // (e.g., recursive LET functions that TIR lowering doesn't fully support).
        match eval_tir(&ctx_with_bindings, tir_body) {
            Ok(v) => return Ok(v),
            Err(_) => {} // TIR eval failed, fall back to AST body
        }
    }
    eval(&ctx_with_bindings, closure.body())
}

/// Apply a closure to arguments
pub(super) fn apply_closure(
    ctx: &EvalCtx,
    closure: &ClosureValue,
    args: &[Spanned<Expr>],
    span: Option<Span>,
) -> EvalResult<Value> {
    if closure.params().len() != args.len() {
        return Err(EvalError::ArityMismatch {
            op: format!("<closure#{}>", closure.id()),
            expected: closure.params().len(),
            got: args.len(),
            span,
        });
    }

    // Fast-path: closure wraps a built-in operator reference (OpRef).
    if closure.params().len() == 2 {
        if let Expr::OpRef(op) = &closure.body().node {
            let left = eval(ctx, &args[0])?;
            let right = eval(ctx, &args[1])?;
            return apply_builtin_binary_op(op, left, right, span);
        }
    }

    // Part of #3021: Use cached interned params to avoid Arc::from() allocation
    // and 2 DashMap lookups per parameter on every closure application.
    // Part of #3805: SmallVec avoids heap allocation for closures with <= 4 params.
    let cached_params = get_closure_param_cache(closure);
    let mut preinterned: PreinternedBuf = SmallVec::with_capacity(closure.params().len());
    for (i, arg) in args.iter().enumerate() {
        let (ref interned, name_id) = cached_params[i];
        preinterned.push((
            Arc::clone(interned),
            BindingValue::eager(eval(ctx, arg)?),
            name_id,
        ));
    }

    eval_closure_body(ctx, closure, preinterned)
}

/// Apply a closure to already-evaluated arguments.
pub(crate) fn apply_closure_with_values(
    ctx: &EvalCtx,
    closure: &ClosureValue,
    args: &[Value],
    span: Option<Span>,
) -> EvalResult<Value> {
    if closure.params().len() != args.len() {
        return Err(EvalError::ArityMismatch {
            op: format!("<closure#{}>", closure.id()),
            expected: closure.params().len(),
            got: args.len(),
            span,
        });
    }

    // Fast-path: closure wraps a built-in operator reference (OpRef).
    if closure.params().len() == 2 {
        if let Expr::OpRef(op) = &closure.body().node {
            return apply_builtin_binary_op(op, args[0].clone(), args[1].clone(), span);
        }
    }

    // Part of #3021: Use cached interned params to avoid Arc::from() allocation
    // and 2 DashMap lookups per parameter on every closure application.
    // Part of #3805: SmallVec avoids heap allocation for closures with <= 4 params.
    let cached_params = get_closure_param_cache(closure);
    let preinterned: PreinternedBuf = args
        .iter()
        .enumerate()
        .map(|(i, value)| {
            let (ref interned, name_id) = cached_params[i];
            (
                Arc::clone(interned),
                BindingValue::eager(value.clone()),
                name_id,
            )
        })
        .collect();

    eval_closure_body(ctx, closure, preinterned)
}
