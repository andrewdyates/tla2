// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Scope-managing conjunct dispatch helpers for unified successor enumeration.
//!
//! These handlers process AND conjuncts that manage evaluation scope: LET
//! definitions, operator application (Apply), identifier inlining (Ident),
//! and INSTANCE operator references (ModuleRef). All share the pattern of
//! saving/restoring `local_ops`, `skip_prime_validation`, and binding marks.
//!
//! Extracted from unified.rs as part of #2360.

use std::rc::Rc;
use std::sync::Arc;

use tla_core::ast::{Expr, ModuleTarget, Substitution};
use tla_core::expr_mentions_name_v;
use tla_core::Spanned;

use crate::error::EvalError;
use crate::eval::{apply_substitutions, EvalCtx};
use crate::OpEnv;

use super::expr_is_action_level;
use super::is_let_lazy_safe_error;
use super::tir_leaf::eval_leaf;
use super::unified::enumerate_conjuncts;
use super::unified_emit::process_conjunct_guard_or_assignment;
use super::unified_types::{Cont, EnumMut, EnumParams, ScopeRestore};

pub(super) fn try_let_guard_first_shortcircuit(
    ctx: &mut EvalCtx,
    defs: &[tla_core::ast::OperatorDef],
    body: &Spanned<Expr>,
    next_env: tla_eval::StateEnvRef,
    p: &EnumParams<'_>,
) -> Option<bool> {
    let Expr::And(first_conjunct, _) = &body.node else {
        return None;
    };

    // Only ordinary boolean guards are safe to speculate here. Action-level
    // conjuncts like `x' = e` or `UNCHANGED x` must flow through assignment
    // extraction instead of being pre-evaluated against the current working env.
    if expr_is_action_level(ctx, &first_conjunct.node) {
        return None;
    }

    for def in defs {
        if expr_mentions_name_v(&first_conjunct.node, def.name.node.as_str()) {
            return None;
        }
    }

    let guard_val = {
        let _env = ctx.bind_next_state_env_guard(next_env);
        eval_leaf(ctx, first_conjunct, p.tir_leaf).ok()?
    };
    match guard_val.as_bool() {
        Some(false) => Some(false),
        _ => None,
    }
}

/// LET within conjuncts: bind definitions, continue with body + remaining.
///
/// Fix #804: LET bindings must be scoped to the body only, NOT leaked to
/// continuation conjuncts from the outer scope. Previously, the outer
/// continuation `c` was passed directly to the body enumeration, causing
/// LET-defined names to shadow outer bindings when continuation conjuncts
/// were processed. For example, ProcessSendBlock's `LET block == signedBlock.block`
/// would shadow the EXISTS-bound `block` in the continuation
/// `received' = [received EXCEPT ![node] = @ \ {block}]`, producing phantom
/// states where received was unchanged.
///
/// The fix creates an inner `Cont` with `scope_restore` that will pop the
/// LET bindings before processing the outer continuation. When the inner
/// conjuncts (body) are exhausted, `enumerate_conjuncts`'s base case detects
/// the `scope_restore`, restores the evaluation context, and continues with
/// the parent Cont.
pub(super) fn conjunct_let(
    ctx: &mut EvalCtx,
    defs: &[tla_core::ast::OperatorDef],
    body: &Spanned<Expr>,
    c: &Cont<'_>,
    p: &EnumParams<'_>,
    m: &mut EnumMut<'_>,
) -> Result<(), EvalError> {
    // Part of #2399/#2963: match eval_let's guard-first behavior for unified
    // successor enumeration. btree has many disabled LET-wrapped actions whose
    // first conjunct is a cheap state guard. If that guard is false and does
    // not mention a LET def, skip all zero-arg LET evaluation for this branch.
    if let Some(false) =
        try_let_guard_first_shortcircuit(ctx, defs, body, m.rec.working.env_ref(), p)
    {
        return Ok(());
    }

    let mark = ctx.mark_stack();

    let all_guards_safe = defs
        .iter()
        .all(|def| !def.guards_depend_on_prime && !def.contains_prime);
    let skip_guard = ctx.skip_prime_guard(all_guards_safe);

    // Part of #1433: empty default is correct — no existing local_ops means
    // no prior LET definitions in scope. Not error-swallowing.
    let mut local_ops = ctx
        .local_ops()
        .as_ref()
        .map(|o| (**o).clone())
        .unwrap_or_default();
    for def in defs {
        local_ops.insert(def.name.node.clone(), Arc::new(def.clone()));
    }
    let saved_local_ops = ctx.local_ops().clone();
    *ctx.local_ops_mut() = Some(Arc::new(local_ops));

    // Part of #1262: Same lazy-tolerant LET binding as in enumerate_unified above.
    for def in defs {
        if def.params.is_empty() {
            match eval_leaf(ctx, &def.body, p.tir_leaf) {
                Ok(val) => {
                    ctx.push_binding(Arc::from(def.name.node.as_str()), val);
                }
                Err(e) if is_let_lazy_safe_error(&e) => {
                    // Skip binding — lazy fallback via local_ops.
                }
                Err(e) => {
                    ctx.pop_to_mark(&mark);
                    *ctx.local_ops_mut() = saved_local_ops;
                    return Err(e);
                }
            }
        }
    }

    // Check if continuation has remaining conjuncts (or a pending scope_restore).
    // If so, use scope_restore to isolate LET bindings from the continuation.
    let has_continuation = c.next_idx < c.conjuncts.len() || c.scope_restore.is_some();

    if has_continuation {
        // Create inner Cont that processes only the body, then restores
        // scope before continuing with the outer continuation.
        let inner = Cont {
            conjuncts: &[],
            next_idx: 0,
            scope_restore: Some(Rc::new(ScopeRestore {
                parent_conjuncts: c.conjuncts,
                parent_next_idx: c.next_idx,
                parent_scope_restore: c.scope_restore.clone(),
                binding_mark: mark.clone(),
                saved_local_ops: saved_local_ops.clone(),
                saved_skip_prime: skip_guard.prev(),
            })),
        };
        let result = enumerate_conjuncts(ctx, &inner, Some(body), p, m);

        // Cleanup: the scope_restore in the base case pops to our mark
        // and restores local_ops when it fires. For nested scope_restores
        // (LET within LET), the outer scope_restore may pop PAST our mark.
        // Only clean up if the stack is still at or above our mark (i.e.,
        // scope_restore chain didn't fire, e.g., a guard failed during body
        // processing). skip_prime_validation is restored by skip_guard on drop.
        if ctx.local_stack_len() >= mark.depth() {
            ctx.pop_to_mark(&mark);
            *ctx.local_ops_mut() = saved_local_ops;
        }
        result
    } else {
        // No continuation — process body directly (simple path).
        // LET scope covers everything and cleanup happens after.
        // skip_prime_validation is restored by skip_guard on drop.
        let result = enumerate_conjuncts(ctx, c, Some(body), p, m);
        ctx.pop_to_mark(&mark);
        *ctx.local_ops_mut() = saved_local_ops;
        result
    }
}

/// Apply within conjuncts: try to inline operator.
pub(super) fn conjunct_apply(
    ctx: &mut EvalCtx,
    op_expr: &Spanned<Expr>,
    args: &[Spanned<Expr>],
    conjunct: &Spanned<Expr>,
    c: &Cont<'_>,
    p: &EnumParams<'_>,
    m: &mut EnumMut<'_>,
) -> Result<(), EvalError> {
    if let Expr::Ident(op_name, _) = &op_expr.node {
        let resolved_name = ctx.resolve_op_name(op_name.as_str());
        if let Some(def) = ctx.get_op(resolved_name) {
            let resolved_def_ptr = Arc::as_ptr(def) as usize;
            let def = Arc::clone(def);
            // Part of #3073: use precomputed field instead of per-call AST walk.
            let needs_substitution = def.has_primed_param;
            let args_are_action = args.iter().any(|arg| expr_is_action_level(ctx, &arg.node));

            // Use call-by-name when the operator body primes one of its formal
            // parameters or when an argument is already action-level.
            // Part of #3063: cache substituted body per call site.
            if needs_substitution || args_are_action {
                let substituted_body =
                    super::subst_cache::cached_substitute(ctx, conjunct, resolved_def_ptr, || {
                        let subs: Vec<Substitution> = def
                            .params
                            .iter()
                            .zip(args.iter())
                            .map(|(param, arg)| Substitution {
                                from: param.name.clone(),
                                to: arg.clone(),
                            })
                            .collect();
                        apply_substitutions(&def.body, &subs)
                    });
                let _guard =
                    ctx.skip_prime_guard(!def.guards_depend_on_prime && !def.contains_prime);
                return enumerate_conjuncts(ctx, c, Some(&substituted_body), p, m);
            }

            // No primed parameters and no action-level args: call-by-value with
            // scope_restore.
            //
            // Call-by-name has variable capture issues: when arg is Ident("x")
            // and the operator body has LET x == ... IN ..., the capture-
            // avoiding substitution drops the substitution, leaving the formal
            // parameter name unresolved (MCNanoSmall: "Undefined variable:
            // signedBlock"). Call-by-value avoids this because VALUES have no
            // free variables to capture.
            //
            // When there's an outer scope_restore (from conjunct_let), we wrap
            // with our own scope_restore to prevent the outer one from popping
            // past our parameter bindings. Without this, the outer scope_restore
            // base-case pops the entire stack back to its mark, silently removing
            // our parameter bindings mid-enumeration.
            let mark = ctx.mark_stack();
            for (param, arg) in def.params.iter().zip(args.iter()) {
                match eval_leaf(ctx, arg, p.tir_leaf) {
                    Ok(arg_val) => {
                        ctx.push_binding(Arc::from(param.name.node.as_str()), arg_val);
                    }
                    Err(e) => {
                        ctx.pop_to_mark(&mark);
                        return Err(e);
                    }
                }
            }

            let skip_guard =
                ctx.skip_prime_guard(!def.guards_depend_on_prime && !def.contains_prime);

            let has_outer_scope_restore = c.scope_restore.is_some();
            let result = if has_outer_scope_restore {
                // Wrap with scope_restore to protect our parameter bindings
                // from being popped by the outer conjunct_let's scope_restore.
                let inner = Cont {
                    conjuncts: &[],
                    next_idx: 0,
                    scope_restore: Some(Rc::new(ScopeRestore {
                        parent_conjuncts: c.conjuncts,
                        parent_next_idx: c.next_idx,
                        parent_scope_restore: c.scope_restore.clone(),
                        binding_mark: mark.clone(),
                        saved_local_ops: ctx.local_ops().clone(),
                        saved_skip_prime: skip_guard.prev(),
                    })),
                };
                let r = enumerate_conjuncts(ctx, &inner, Some(&def.body), p, m);
                // scope_restore base-case may have already popped past mark
                if ctx.local_stack_len() >= mark.depth() {
                    ctx.pop_to_mark(&mark);
                }
                r
            } else {
                // No outer scope_restore — simple call-by-value path.
                let r = enumerate_conjuncts(ctx, c, Some(&def.body), p, m);
                ctx.pop_to_mark(&mark);
                r
            };

            drop(skip_guard);
            return result;
        }
    }
    // Unknown operator — process as guard/assignment
    process_conjunct_guard_or_assignment(ctx, conjunct, c, p, m)
}

/// Ident within conjuncts: try to inline zero-arg operator.
pub(super) fn conjunct_ident(
    ctx: &mut EvalCtx,
    name: &str,
    conjunct: &Spanned<Expr>,
    c: &Cont<'_>,
    p: &EnumParams<'_>,
    m: &mut EnumMut<'_>,
) -> Result<(), EvalError> {
    let resolved = ctx.resolve_op_name(name);
    if let Some(def) = ctx.get_op(resolved).cloned() {
        if def.params.is_empty() {
            let _guard = ctx.skip_prime_guard(!def.guards_depend_on_prime && !def.contains_prime);
            return enumerate_conjuncts(ctx, c, Some(&def.body), p, m);
        }
    }
    // Not an operator — process as guard/assignment
    process_conjunct_guard_or_assignment(ctx, conjunct, c, p, m)
}

/// ModuleRef within conjuncts: inline INSTANCE operator with scope setup.
///
/// This mirrors `enumerate_module_ref` but uses the conjunct continuation pattern
/// so that the inlined body is processed as part of the AND chain rather than
/// independently. Without this, `Sched!Allocate(c,S)` inside an AND falls to
/// the catch-all which tries eval-as-guard, fails, and silently skips the
/// guard — allowing actions to fire when they should be disabled.
///
/// FIX #1427: AllocatorImplementation parity regression.
#[allow(clippy::too_many_arguments)]
pub(super) fn conjunct_module_ref(
    ctx: &mut EvalCtx,
    conjunct: &Spanned<Expr>,
    instance_name: &ModuleTarget,
    op_name: &str,
    args: &[Spanned<Expr>],
    c: &Cont<'_>,
    p: &EnumParams<'_>,
    m: &mut EnumMut<'_>,
) -> Result<(), EvalError> {
    // Look up instance metadata
    let instance_info = match ctx.get_instance(instance_name.name()) {
        Some(info) => info.clone(),
        None => {
            return Err(EvalError::UndefinedOp {
                name: format!("{}!{}", instance_name, op_name),
                span: None,
            });
        }
    };

    // Get the operator definition from the instanced module
    let op_def = match ctx.get_instance_op_arc(&instance_info.module_name, op_name) {
        Some(def) => def,
        None => {
            return Err(EvalError::UndefinedOp {
                name: format!("{}!{}", instance_name, op_name),
                span: None,
            });
        }
    };
    let resolved_def_ptr = Arc::as_ptr(op_def) as usize;

    // Apply INSTANCE ... WITH substitutions and parameter substitutions.
    // Part of #3063: cache substituted body per call site.
    let inlined = super::subst_cache::cached_substitute(ctx, conjunct, resolved_def_ptr, || {
        let mut body = apply_substitutions(&op_def.body, &instance_info.substitutions);
        if !op_def.params.is_empty() && op_def.params.len() == args.len() {
            let param_subs: Vec<Substitution> = op_def
                .params
                .iter()
                .zip(args.iter())
                .map(|(param, arg)| Substitution {
                    from: param.name.clone(),
                    to: arg.clone(),
                })
                .collect();
            body = apply_substitutions(&body, &param_subs);
        }
        body
    });

    // Set up instance-local operator scope (same as enumerate_module_ref)
    // Part of #1433: empty default is correct — modules without registered
    // instance operators simply have no local ops in scope. Not error-swallowing.
    let instance_local_ops: OpEnv = ctx
        .instance_ops()
        .get(&instance_info.module_name)
        .cloned()
        .unwrap_or_default();

    let merged_ops = if let Some(outer_ops) = ctx.local_ops().as_deref() {
        let mut merged = instance_local_ops.clone();
        for (name, def) in outer_ops.iter() {
            merged.entry(name.clone()).or_insert_with(|| def.clone());
        }
        merged
    } else {
        instance_local_ops
    };

    let saved_local_ops = ctx.local_ops().clone();
    *ctx.local_ops_mut() = Some(Arc::new(merged_ops));

    // Continue conjunct enumeration with inlined body as pending expression
    let result = enumerate_conjuncts(ctx, c, Some(&inlined), p, m);

    *ctx.local_ops_mut() = saved_local_ops;
    result
}
