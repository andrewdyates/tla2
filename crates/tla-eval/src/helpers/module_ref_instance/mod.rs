// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Non-chained INSTANCE evaluation and substitution helpers.
//!
//! Contains `eval_module_ref` (M!Op), `get_instance_info`, `compose_substitutions`,
//! `build_binding_chain_from_eager`, and AST utility wrappers.
//!
//! Part of #1643 (module_ref.rs decomposition).

mod binding_builders;
mod instance_resolution;

// Re-export public API — preserves all existing import paths.
pub(super) use binding_builders::build_binding_chain_from_eager;
pub(crate) use binding_builders::build_lazy_subst_bindings;
pub use binding_builders::{expr_has_any_prime, expr_has_primed_param};
pub(super) use instance_resolution::get_instance_info;
pub use instance_resolution::{apply_substitutions, compose_substitutions};

#[cfg(debug_assertions)]
use super::super::debug_module_ref;
use super::super::{eval, EvalCtx, EvalError, EvalResult, InstanceInfo, OpEnv};
use super::module_ref_cache::{ModuleRefScopeEntry, ModuleRefScopeKey, MODULE_REF_CACHES};
use super::module_ref_label::select_named_label;
use crate::binding_chain::BindingValue;
use crate::eval_dispatch::EMPTY_EAGER_SUBST;
use crate::value::Value;
use std::sync::Arc;
use tla_core::ast::Expr;
use tla_core::name_intern::intern_name;
use tla_core::{Span, Spanned};

// Part of #4114: Cache debug env vars with OnceLock instead of calling
// std::env::var on every INSTANCE evaluation.
debug_flag!(debug_3447, "TLA2_DEBUG_3447");
debug_flag!(debug_3147_mri, "TLA2_DEBUG_3147");

pub(crate) fn eval_module_ref(
    ctx: &EvalCtx,
    instance_name: &str,
    op_name: &str,
    args: &[Spanned<Expr>],
    span: Option<Span>,
) -> EvalResult<Value> {
    // Check for conjunct selection: Def!n where Def is an operator with a conjunction body
    // and n is a numeric index (1-based)
    if let Ok(conjunct_idx) = op_name.parse::<usize>() {
        if conjunct_idx > 0 {
            // This might be conjunct selection, not module reference
            if let Some(def) = ctx.get_op(instance_name) {
                // Check if the operator body is a conjunction
                if let Expr::And(_, _) = &def.body.node {
                    // Collect all conjuncts from the definition
                    let conjuncts = tla_core::collect_conjuncts_v(&def.body);
                    let idx = conjunct_idx - 1; // Convert to 0-based
                    if idx < conjuncts.len() {
                        // Evaluate the selected conjunct
                        return eval(ctx, &conjuncts[idx]);
                    }
                    return Err(EvalError::UndefinedOp {
                        name: format!(
                            "{}!{} (conjunct index {} out of range, definition has {} conjuncts)",
                            instance_name,
                            op_name,
                            conjunct_idx,
                            conjuncts.len()
                        ),
                        span,
                    });
                }
            }
        }
    }

    if let Some(def) = ctx.get_op(instance_name) {
        if let Some(selected) = select_named_label(def, op_name) {
            if !args.is_empty() {
                return Err(EvalError::ArityMismatch {
                    op: format!("{instance_name}!{op_name}"),
                    expected: 0,
                    got: args.len(),
                    span,
                });
            }
            return eval(ctx, &selected);
        }
    }

    // Resolve the instance.
    //
    // TLC allows nested named instances: when evaluating `Outer!Op` we must be able to resolve
    // instance references inside that module (e.g., `cleanInstance!Spec`) even if those
    // instances are not declared in the main module.
    //
    // We support this by:
    // 1) looking for a globally-registered instance (from loading the main/extended modules), and
    // 2) falling back to a locally-visible operator definition whose body is an `InstanceExpr`
    //    (available via `instance_local_ops` when evaluating an instanced module).
    let instance_info: InstanceInfo = if let Some(info) = ctx.get_instance(instance_name) {
        info.clone()
    } else if let Some(def) = ctx.get_op(instance_name) {
        match &def.body.node {
            Expr::InstanceExpr(module_name, substitutions) => InstanceInfo {
                module_name: module_name.clone(),
                substitutions: substitutions.clone(),
            },
            _ => {
                return Err(EvalError::UndefinedOp {
                    name: format!("{instance_name}!{op_name}"),
                    span,
                });
            }
        }
    } else {
        return Err(EvalError::UndefinedOp {
            name: format!("{instance_name}!{op_name}"),
            span,
        });
    };

    let effective_substitutions = compose_substitutions(
        &ctx.compute_effective_instance_substitutions(
            &instance_info.module_name,
            &instance_info.substitutions,
        ),
        ctx.instance_substitutions(),
    );

    // Get the operator from the instanced module
    // If it is not an operator body, resolve it through the effective substitution list.
    let op_def = match ctx.get_instance_op(&instance_info.module_name, op_name) {
        Some(def) => def.clone(),
        None => {
            if let Some(sub) = effective_substitutions
                .iter()
                .find(|sub| sub.from.node == op_name)
            {
                return eval(ctx, &sub.to);
            }

            return Err(EvalError::UndefinedOp {
                name: format!("{instance_name}!{op_name}"),
                span,
            });
        }
    };

    // Check arity
    if op_def.params.len() != args.len() {
        return Err(EvalError::ArityMismatch {
            op: format!("{instance_name}!{op_name}"),
            expected: op_def.params.len(),
            got: args.len(),
            span,
        });
    }

    // Fix #2364: Cache the composed substitutions and merged local_ops in pre-wrapped
    // Arcs so that SUBST_CACHE keys are stable across eval_entry calls. Without this,
    // every eval_module_ref creates a new Arc wrapping the same substitution content,
    // making SUBST_CACHE effectively useless across eval_entry boundaries.
    let scope_key = ModuleRefScopeKey {
        shared_id: ctx.shared.id,
        instance_name_id: intern_name(instance_name),
        outer_subs_id: ctx
            .instance_substitutions
            .as_ref()
            .map_or(0, |subs| Arc::as_ptr(subs) as usize),
        outer_local_ops_id: ctx
            .local_ops
            .as_ref()
            .map_or(0, |ops| Arc::as_ptr(ops) as usize),
    };

    let scope_entry = MODULE_REF_CACHES
        .with(|c| c.borrow().module_ref_scope.get(&scope_key).cloned())
        .unwrap_or_else(|| {
            // Evaluate instance module operators in a scope where unqualified operator names
            // resolve to the instanced module's definitions (not the current module's).
            let mut instance_local_ops: OpEnv = ctx
                .shared
                .instance_ops
                .get(&instance_info.module_name)
                .cloned()
                .unwrap_or_default();

            // Merge parent local_ops as fallback so operators from enclosing
            // INSTANCE scopes remain visible. Always merge (with
            // instance_local_ops taking priority): instance-local operators
            // shadow parent operators via the contains_key check.
            if let Some(parent_local_ops) = ctx.local_ops.as_ref() {
                for (name, def) in parent_local_ops.iter() {
                    if !instance_local_ops.contains_key(name.as_str()) {
                        instance_local_ops.insert(name.clone(), def.clone());
                    }
                }
            }

            let entry = ModuleRefScopeEntry {
                effective_subs_arc: Arc::new(effective_substitutions.clone()),
                local_ops_arc: Arc::new(instance_local_ops),
            };
            MODULE_REF_CACHES
                .with(|c| c.borrow_mut().module_ref_scope.insert(scope_key, entry.clone()));
            entry
        });

    let has_effective_substitutions = !scope_entry.effective_subs_arc.is_empty();

    debug_eprintln!(
        debug_module_ref(),
        "[MODULE_REF] {}!{}: module={}, subs=[{}]",
        instance_name,
        op_name,
        instance_info.module_name,
        scope_entry
            .effective_subs_arc
            .iter()
            .map(|s| format!("{} <- {:?}", s.from.node, s.to.node))
            .collect::<Vec<_>>()
            .join(", ")
    );

    // Bind parameters to arguments
    let mut bindings = Vec::new();
    for (param, arg) in op_def.params.iter().zip(args.iter()) {
        let value = eval(ctx, arg)?;
        bindings.push((Arc::from(param.name.node.as_str()), value));
    }

    // Part of #2981: Save operator param bindings before they're consumed by
    // with_module_scope_arced_subs. The BindingChain will be rebuilt by
    // build_binding_chain_from_eager (substitution bindings only), so operator
    // param bindings must be re-pushed onto the chain afterward. Without this,
    // INSTANCE operators with parameters (e.g., Buffer!IndexOf(next)) lose
    // their parameter bindings when INSTANCE WITH substitutions exist.
    let saved_param_bindings: Vec<(tla_core::name_intern::NameId, Value)> = bindings
        .iter()
        .map(|(name, value)| (intern_name(name), value.clone()))
        .collect();

    let is_chained =
        ctx.chained_ref_eval || (ctx.local_ops.is_some() && has_effective_substitutions);

    // Evaluate the operator body with parameter bindings and instance-local operator scope.
    let mut new_ctx = ctx.with_module_scope_arced_subs(
        Arc::clone(&scope_entry.local_ops_arc),
        bindings,
        Arc::clone(&scope_entry.effective_subs_arc),
    );
    // Preserve merged local-operator visibility for nested INSTANCE substitutions.
    if is_chained {
        new_ctx.stable_mut().chained_ref_eval = true;
    }

    // Part of #3056 Phase B: Uniform lazy substitution bindings for all paths.
    // Previously, chained refs used build_eager_subst_bindings (evaluating all
    // substitution RHS upfront) while non-chained used build_lazy_subst_bindings
    // (deferring to first access via LazyBinding + OnceLock). Lazy bindings are
    // correct for both cases: each sub becomes a LazyBinding capturing the
    // definition-site context (ctx.bindings before module scope entry), matching
    // TLC's Context.cons + LazyValue pattern in evalImplSubstInKind.
    //
    // Empty marker enables eval_ident fast path (can_take_fast_path requires
    // eager_subst_bindings.is_some() when instance_subs active). Actual
    // substitution bindings are in the BindingChain as lazy entries.
    if has_effective_substitutions {
        new_ctx.stable_mut().eager_subst_bindings = Some(Arc::clone(&EMPTY_EAGER_SUBST));
        // SAFETY: expr_ptr points into scope_entry.effective_subs_arc (Arc<Vec<Substitution>>).
        // The Arc is kept alive by new_ctx.instance_substitutions for the entire body evaluation.
        // LazyBindings are only accessible through new_ctx.bindings and cannot outlive the Arc.
        new_ctx.bindings = binding_builders::build_lazy_subst_bindings(
            &ctx.bindings,
            &scope_entry.effective_subs_arc,
        );
        // Part of #2981: Re-push operator parameter bindings onto the chain head.
        for (name_id, value) in saved_param_bindings.iter().rev() {
            new_ctx.bindings = new_ctx.bindings.cons_local(
                *name_id,
                BindingValue::eager(value.clone()),
                new_ctx.binding_depth,
            );
        }
    }

    // Part of #3465: nested INSTANCE bodies can otherwise reuse eval-scope
    // caches built for a different INSTANCE depth within the same top-level
    // invariant/property evaluation, causing deterministic MCPaxosSmall false
    // positives. Reset the eval-scope boundary before entering the nested body.
    //
    // Part of #3805: Deduplicate per-state: MCNanoMedium evaluates dozens of
    // N!Op references per state. Only the first clear per state is needed —
    // subsequent clears within the same state are redundant work that caused
    // the spec to be 6x slower than TLC instead of ~3x. Uses state_env
    // pointer identity as dedup key (stable within a state's evaluation).
    crate::cache::lifecycle::clear_for_eval_scope_boundary_if_needed(
        ctx.state_env.map_or(0, |s| s.identity()),
    );
    let result = eval(&new_ctx, &op_def.body);

    // #3447 debug: trace ShowsSafeAt calls with args and votes binding
    if debug_3447() && op_name == "ShowsSafeAt" {
        if let Ok(ref v) = result {
            if v == &Value::Bool(false) {
                // Print args for the failing call
                let args_str: Vec<String> = saved_param_bindings
                    .iter()
                    .zip(op_def.params.iter())
                    .map(|((_, val), param)| format!("{}={:?}", param.name.node, val))
                    .collect();
                // Look up votes in the binding chain
                let votes_val = {
                    let votes_id = intern_name("votes");
                    new_ctx
                        .bindings
                        .lookup(votes_id)
                        .map(|(bv, source)| {
                            bv.get_if_ready(crate::cache::StateLookupMode::Current, source)
                                .map(|v| format!("{:?}", v))
                                .unwrap_or_else(|| "UNFORCED".to_string())
                        })
                        .unwrap_or_else(|| "NOT_IN_CHAIN".to_string())
                };
                let maxbal_val = {
                    let maxbal_id = intern_name("maxBal");
                    new_ctx
                        .bindings
                        .lookup(maxbal_id)
                        .map(|(bv, source)| {
                            bv.get_if_ready(crate::cache::StateLookupMode::Current, source)
                                .map(|v| format!("{:?}", v))
                                .unwrap_or_else(|| "UNFORCED".to_string())
                        })
                        .unwrap_or_else(|| "NOT_IN_CHAIN".to_string())
                };
                eprintln!(
                    "[DEBUG_3447] ShowsSafeAt=FALSE args=[{}] votes={} maxBal={} state_env_id={}",
                    args_str.join(", "),
                    votes_val,
                    maxbal_val,
                    new_ctx.state_env.map_or(0, |s| s.identity()),
                );
            }
        }
    }

    // #3147 debug: trace ModuleRef evaluation results
    if debug_3147_mri() {
        eprintln!(
            "[DEBUG_3147] eval_module_ref: {}!{} => {:?}, state_env_id={}, next_state_env_id={}",
            instance_name,
            op_name,
            result
                .as_ref()
                .map(|v| format!("{:?}", v))
                .unwrap_or_else(|e| format!("ERR: {:?}", e)),
            new_ctx.state_env.map_or(0, |s| s.identity()),
            new_ctx.next_state_env.map_or(0, |s| s.identity()),
        );
    }

    result
}
