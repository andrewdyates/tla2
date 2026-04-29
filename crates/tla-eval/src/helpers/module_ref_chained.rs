// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Chained module reference resolution (A!B!C!D chains).
//!
//! Handles recursive chain resolution and scope merging for
//! multi-level INSTANCE references.
//!
//! Part of #1643 (module_ref.rs decomposition).

use super::super::{eval, EvalCtx, EvalError, EvalResult, InstanceInfo, OpEnv};
use super::module_ref::{
    apply_substitutions, build_binding_chain_from_eager, compose_substitutions, get_instance_info,
    module_ref_compound_key,
};
use super::module_ref_cache::{
    build_eager_subst_bindings, chained_ref_cache_key, eager_bindings_key, ChainedRefCacheEntry,
    MODULE_REF_CACHES,
};
use super::module_ref_chained_label::try_eval_label_from_base_module_ref;
use super::module_ref_operator::ResolvedModuleRefOperator;
use crate::binding_chain::BindingValue;
use crate::value::Value;
use std::hash::{Hash, Hasher};
use std::sync::Arc;
use tla_core::ast::{Expr, ModuleTarget, Substitution};
use tla_core::name_intern::intern_name;
use tla_core::{Span, Spanned};

fn build_chained_ref_cache_entry(
    ctx: &EvalCtx,
    base_target: &ModuleTarget,
    intermediate_op: &str,
    span: Option<Span>,
) -> EvalResult<ChainedRefCacheEntry> {
    let mut intermediate_modules = Vec::new();
    let mut instance_info = resolve_module_ref_chain(
        ctx,
        base_target,
        intermediate_op,
        span,
        &mut intermediate_modules,
    )?;
    instance_info.substitutions = ctx.compute_effective_instance_substitutions(
        &instance_info.module_name,
        &instance_info.substitutions,
    );

    let mut merged_local_ops: OpEnv = ctx
        .shared
        .instance_ops
        .get(&instance_info.module_name)
        .cloned()
        .unwrap_or_default();

    // Merge operators from intermediate modules for implicit substitution.
    // Innermost module operators keep precedence.
    for module_name in &intermediate_modules {
        if let Some(ops) = ctx.shared.instance_ops.get(module_name.as_str()) {
            for (name, def) in ops {
                if !merged_local_ops.contains_key(name.as_str()) {
                    merged_local_ops.insert(name.clone(), def.clone());
                }
            }
        }
    }

    let instance_subs_arc = Arc::new(instance_info.substitutions.clone());
    Ok(ChainedRefCacheEntry {
        instance_info,
        merged_local_ops: Arc::new(merged_local_ops),
        instance_subs_arc,
    })
}

/// Evaluate a chained module reference (A!B!C!D)
///
/// This recursively resolves the chain by:
/// 1. Evaluating the base module reference to get the intermediate instance info
/// 2. Looking up the final operator within that instance's context
///
/// Intermediate modules' operators are merged into `local_ops` so that implicit
/// substitutions work across the chain. For example, in `EWD998Chan!EWD998!TD!Safe`,
/// `Safe` in AsyncTerminationDetection references the VARIABLE `terminationDetected`,
/// which needs to resolve to EWD998's OPERATOR `terminationDetected` via implicit
/// substitution. Without merging EWD998's operators into local_ops, that name is
/// invisible and evaluation fails or resolves to the wrong definition.
pub(crate) fn eval_chained_module_ref(
    ctx: &EvalCtx,
    base_expr: &Spanned<Expr>,
    final_op_name: &str,
    final_args: &[Spanned<Expr>],
    span: Option<Span>,
) -> EvalResult<Value> {
    if let Some(label_value) =
        try_eval_label_from_base_module_ref(ctx, base_expr, final_op_name, final_args, span)?
    {
        return Ok(label_value);
    }

    let resolved =
        resolve_chained_module_ref_operator(ctx, base_expr, final_op_name, final_args, span)?;
    eval(&resolved.eval_ctx, &resolved.op_def.body)
}

pub(super) fn build_parameterized_target_ctx(
    ctx: &EvalCtx,
    name: &str,
    param_exprs: &[Spanned<Expr>],
) -> EvalResult<EvalCtx> {
    let Some(def) = ctx.get_op(name) else {
        return Ok(ctx.clone());
    };
    if def.params.is_empty() {
        return Ok(ctx.clone());
    }

    let mut pctx = ctx.clone();
    let mut args_hasher = rustc_hash::FxHasher::default();
    for (param, arg_expr) in def.params.iter().zip(param_exprs.iter()) {
        let value = eval(ctx, arg_expr)?;
        value.hash(&mut args_hasher);
        let name_id = intern_name(param.name.node.as_str());
        pctx.bindings =
            pctx.bindings
                .cons_local(name_id, BindingValue::eager(value), pctx.binding_depth);
        pctx.binding_depth += 1;
    }
    pctx.stable_mut().param_args_hash = args_hasher.finish();
    let subs: Vec<Substitution> = def
        .params
        .iter()
        .zip(param_exprs.iter())
        .map(|(param, arg_expr)| Substitution {
            from: param.name.clone(),
            to: arg_expr.clone(),
        })
        .collect();
    {
        let id = crate::cache::scope_ids::compute_instance_subs_id(&subs);
        let s = pctx.stable_mut();
        s.instance_substitutions = Some(Arc::new(subs));
        s.scope_ids.instance_substitutions = id;
    }
    Ok(pctx)
}

pub(super) fn resolve_chained_module_ref_operator(
    ctx: &EvalCtx,
    base_expr: &Spanned<Expr>,
    final_op_name: &str,
    final_args: &[Spanned<Expr>],
    span: Option<Span>,
) -> EvalResult<ResolvedModuleRefOperator> {
    let Expr::ModuleRef(base_target, intermediate_op, _intermediate_args) = &base_expr.node else {
        return Err(EvalError::Internal {
            message: format!(
                "Chained module reference base must be ModuleRef, got: {:?}",
                base_expr.node
            ),
            span,
        });
    };

    // Resolve the chain once per context/scope and cache the merged scope.
    let chain_entry = if let Some(chain_key) = module_ref_compound_key(base_target, intermediate_op)
    {
        let cache_key = chained_ref_cache_key(ctx, chain_key);
        if let Some(cached) =
            MODULE_REF_CACHES.with(|c| c.borrow().chained_ref.get(&cache_key).cloned())
        {
            cached
        } else {
            let entry = build_chained_ref_cache_entry(ctx, base_target, intermediate_op, span)?;
            MODULE_REF_CACHES.with(|c| {
                c.borrow_mut().chained_ref.insert(cache_key, entry.clone());
            });
            entry
        }
    } else {
        build_chained_ref_cache_entry(ctx, base_target, intermediate_op, span)?
    };

    // Now look up the final operator in that instance's module
    let op_def = ctx
        .get_instance_op(&chain_entry.instance_info.module_name, final_op_name)
        .ok_or_else(|| EvalError::UndefinedOp {
            name: format!("...!{final_op_name}"),
            span,
        })?
        .clone();

    // Check arity
    if op_def.params.len() != final_args.len() {
        return Err(EvalError::ArityMismatch {
            op: format!("...!{final_op_name}"),
            expected: op_def.params.len(),
            got: final_args.len(),
            span,
        });
    }

    // Build argument bindings
    let mut bindings = Vec::new();
    for (param, arg) in op_def.params.iter().zip(final_args.iter()) {
        let value = eval(ctx, arg)?;
        bindings.push((Arc::from(param.name.node.as_str()), value));
    }

    // Evaluate with instance context. Set chained_ref_eval flag so that substitution
    // RHS evaluation preserves local_ops and sibling subs instead of clearing to global.
    //
    // Fix #2364: Reuse the pre-wrapped Arc for instance_substitutions from the cached
    // chain entry. This stabilizes the Arc pointer across eval_entry calls, enabling
    // SUBST_CACHE hits when the same chained operator is evaluated multiple times for
    // the same state (e.g., invariant + constraint + property checks).
    let mut new_ctx = ctx.with_module_scope_arced_subs(
        Arc::clone(&chain_entry.merged_local_ops),
        bindings,
        Arc::clone(&chain_entry.instance_subs_arc),
    );
    new_ctx.stable_mut().chained_ref_eval = true;

    // Fix #2364: Eagerly evaluate substitution RHS values at scope entry.
    // Cache the eager bindings to avoid re-evaluation within the same state.
    new_ctx.stable_mut().eager_subst_bindings = if !chain_entry.instance_subs_arc.is_empty() {
        let eb_key = eager_bindings_key(
            ctx,
            Arc::as_ptr(&chain_entry.instance_subs_arc) as usize,
            Arc::as_ptr(&chain_entry.merged_local_ops) as usize,
        );
        let cached = MODULE_REF_CACHES.with(|c| c.borrow().eager_bindings.get(&eb_key).cloned());
        if let Some(bindings_arc) = cached {
            Some(bindings_arc)
        } else {
            let bindings_arc = Arc::new(build_eager_subst_bindings(
                &new_ctx,
                &chain_entry.instance_subs_arc,
            )?);
            MODULE_REF_CACHES.with(|c| {
                c.borrow_mut()
                    .eager_bindings
                    .insert(eb_key, Arc::clone(&bindings_arc));
            });
            Some(bindings_arc)
        }
    } else {
        None
    };

    // Part of #2364 Phase 3: Populate BindingChain (parallel path with eager_subst_bindings).
    if let Some(ref eb) = new_ctx.eager_subst_bindings {
        new_ctx.bindings = build_binding_chain_from_eager(eb);
    }

    Ok(ResolvedModuleRefOperator {
        op_def: op_def.into(),
        eval_ctx: new_ctx,
    })
}

/// Resolve a module reference chain to get the final InstanceInfo
///
/// For A!B!C, this resolves:
/// 1. A -> get InstanceInfo for A
/// 2. B in A's module -> get InstanceInfo for B (with A's substitutions composed)
///
/// Also collects intermediate module names into `intermediate_modules` so that
/// callers can merge their operators into local_ops for implicit substitution.
pub(crate) fn resolve_module_ref_chain(
    ctx: &EvalCtx,
    target: &ModuleTarget,
    op_name: &str,
    span: Option<Span>,
    intermediate_modules: &mut Vec<String>,
) -> EvalResult<InstanceInfo> {
    match target {
        ModuleTarget::Named(name) | ModuleTarget::Parameterized(name, _) => {
            let instance_info = get_instance_info(ctx, name, op_name, span)?;

            // Track the module that the instance directly resolves to as intermediate
            // (if it differs from the returned module, it was traversed internally
            // by get_instance_info and its operators may be needed for implicit
            // substitution in deeper modules).
            let direct_module = if let Some(def) = ctx.get_op(name) {
                if let Expr::InstanceExpr(module_name, _) = &def.body.node {
                    Some(module_name.clone())
                } else {
                    None
                }
            } else {
                ctx.get_instance(name).map(|info| info.module_name.clone())
            };
            if let Some(dm) = direct_module {
                if dm != instance_info.module_name {
                    intermediate_modules.push(dm);
                }
            }

            Ok(instance_info)
        }
        ModuleTarget::Chained(base_expr) => {
            // Recursive case: first resolve the base chain
            let Expr::ModuleRef(base_target, base_op, _) = &base_expr.node else {
                return Err(EvalError::Internal {
                    message: "Chained base must be ModuleRef".to_string(),
                    span,
                });
            };

            // Resolve the base chain first
            let base_info =
                resolve_module_ref_chain(ctx, base_target, base_op, span, intermediate_modules)?;

            // Record the base module as intermediate — its operators may be needed
            // for implicit substitution in deeper modules.
            intermediate_modules.push(base_info.module_name.clone());

            // Now look up op_name in base_info's module
            // It should be an operator that evaluates to an InstanceExpr
            let op_def = ctx
                .get_instance_op(&base_info.module_name, op_name)
                .ok_or_else(|| EvalError::UndefinedOp {
                    name: format!("...!{op_name}"),
                    span,
                })?
                .clone();

            // Part of #3056 Phase B: SubstIn wrapping instead of eager rewriting.
            // The operator body should be an InstanceExpr — wrap in SubstIn
            // and let instance_info_from_substituted_expr compose and recurse.
            let wrapped = Spanned::new(
                Expr::SubstIn(
                    base_info.substitutions.clone(),
                    Box::new(op_def.body.clone()),
                ),
                op_def.body.span,
            );
            instance_info_from_substituted_expr(
                &wrapped,
                None, // SubstIn wrapping carries the subs; no separate outer composition
                format!(
                    "{}!{} is not an instance definition",
                    base_info.module_name, op_name
                ),
                span,
            )
        }
    }
}

pub(super) fn instance_info_from_substituted_expr(
    substituted: &Spanned<Expr>,
    outer_subs: Option<&[Substitution]>,
    undefined_name: String,
    span: Option<Span>,
) -> EvalResult<InstanceInfo> {
    match &substituted.node {
        Expr::InstanceExpr(module_name, inner_subs) => Ok(InstanceInfo {
            module_name: module_name.clone(),
            substitutions: compose_substitutions(inner_subs, outer_subs),
        }),
        // Part of #3056 Phase B: Handle SubstIn wrapping — the caller emitted
        // SubstIn(subs, body) instead of eagerly rewriting via apply_substitutions.
        // Compute effective substitutions once from wrap_subs + outer_subs, then
        // use consistently across all body types. Callers pass outer_subs=None
        // when SubstIn already carries the subs; outer_subs is non-None only from
        // recursive calls (nested SubstIn).
        Expr::SubstIn(wrap_subs, body) => {
            let effective = compose_substitutions(wrap_subs, outer_subs);
            match &body.node {
                // Direct InstanceExpr body: compose inner_subs with effective subs.
                // apply_substitutions is a no-op on InstanceExpr (fold visitor
                // short-circuits), so compose_substitutions does all the work.
                Expr::InstanceExpr(module_name, inner_subs) => Ok(InstanceInfo {
                    module_name: module_name.clone(),
                    substitutions: compose_substitutions(inner_subs, Some(&effective)),
                }),
                // Nested SubstIn: pass effective as outer and recurse.
                Expr::SubstIn(_, _) => instance_info_from_substituted_expr(
                    body,
                    Some(&effective),
                    undefined_name,
                    span,
                ),
                // Body is not directly an InstanceExpr (e.g., an identifier that
                // becomes InstanceExpr after substitution). Fall back to eager
                // apply_substitutions — structural metadata extraction requires the
                // substituted form. See Correction Addendum in the design doc.
                _ => {
                    let substituted = apply_substitutions(body, &effective);
                    instance_info_from_substituted_expr(
                        &substituted,
                        Some(&effective),
                        undefined_name,
                        span,
                    )
                }
            }
        }
        _ => Err(EvalError::UndefinedOp {
            name: undefined_name,
            span,
        }),
    }
}
