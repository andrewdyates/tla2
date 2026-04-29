// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Extraction handlers for complex AST nodes: EXISTS, Apply, ModuleRef, LET.
//!
//! Each handler walks a specific AST form, extracting primed-variable
//! assignments into `SymbolicAssignment` values.

use std::sync::Arc;

use tla_core::ast::{Expr, Substitution};
use tla_core::Spanned;

use tla_eval::tir::TirProgram;

use crate::error::EvalError;
use crate::eval::{apply_substitutions, eval_iter_set_tlc_normalized, EvalCtx, OpEnv};
use crate::Value;

use super::super::tir_leaf::eval_leaf;

#[cfg(debug_assertions)]
use super::super::debug_enum;
use super::super::{
    check_and_guards, classify_iter_error_for_speculative_path, expr_contains_any_prime,
    expr_is_action_level, IterDomainAction, SymbolicAssignment,
};
use super::extract_symbolic_assignments_inner;

use crate::var_index::VarRegistry;

pub(super) fn extract_exists_symbolic_assignments(
    ctx: &EvalCtx,
    expr: &Spanned<Expr>,
    vars: &[Arc<str>],
    assignments: &mut Vec<SymbolicAssignment>,
    eager_eval: bool,
    registry: &VarRegistry,
    tir: Option<&TirProgram<'_>>,
) -> Result<(), EvalError> {
    let Expr::Exists(bounds, body) = &expr.node else {
        return Err(EvalError::Internal {
            message: "extract_exists_symbolic_assignments requires Expr::Exists".to_string(),
            span: Some(expr.span),
        });
    };

    // Only handle simple cases: single bound variable
    if bounds.len() != 1 {
        // For multiple bounds, fall back to not extracting (will be handled by enumerate_next_rec)
        return Ok(());
    }
    let bound = &bounds[0];
    let var_name = Arc::from(bound.name.node.as_str());

    // Evaluate the domain
    // Part of #1426: propagate domain eval errors (TLC treats these as fatal).
    let domain = match &bound.domain {
        Some(dom_expr) => eval_leaf(ctx, dom_expr, tir)?,
        None => return Ok(()), // No domain, skip
    };

    // Part of #1828: use eval_iter_set for SetPred-aware iteration.
    // Part of #1886: discriminate "not enumerable" (defer) from fatal eval errors.
    // Part of #2987: use TLC-normalized ordering for BFS parity.
    let domain_elems: Vec<Value> =
        match eval_iter_set_tlc_normalized(ctx, &domain, bound.domain.as_ref().map(|d| d.span)) {
            Ok(iter) => iter.collect(),
            Err(ref e)
                if classify_iter_error_for_speculative_path(e) == IterDomainAction::Defer =>
            {
                return Ok(());
            }
            Err(e) => return Err(e),
        };

    // For each value in the domain, evaluate the body to find assignments
    // Collect all possible values for primed variables
    let mut primed_values: rustc_hash::FxHashMap<Arc<str>, Vec<Value>> =
        rustc_hash::FxHashMap::default();

    for val in domain_elems {
        // Bind the quantified variable using bind_local so the binding
        // is captured in local_stack for deferred expression evaluation.
        // This fixes #87 where EXISTS bindings were not properly captured.
        let new_ctx = ctx.bind_local(Arc::clone(&var_name), val);

        // Check if guards pass before extracting assignments.
        // This ensures we only extract assignments from EXISTS body when guards
        // are satisfied. Without this check, we'd extract assignments from ALL
        // domain values, not just those where `\E i : guard /\ x' = f(i)` holds.
        // The guard check filters out values that don't satisfy the preconditions.
        if !check_and_guards(&new_ctx, body, false, tir)? {
            continue; // Skip this value - guards not satisfied
        }

        // Extract assignments from the body with this binding
        let mut body_assignments = Vec::new();
        extract_symbolic_assignments_inner(
            &new_ctx,
            body,
            vars,
            &mut body_assignments,
            eager_eval,
            registry,
            tir,
        )?;

        // Collect all Value assignments
        for assign in body_assignments {
            match assign {
                SymbolicAssignment::Value(var, value) => {
                    primed_values.entry(var).or_default().push(value);
                }
                SymbolicAssignment::Expr(var, ref expr_spanned, ref bindings) => {
                    // Restore captured bindings before evaluation
                    let eval_ctx = new_ctx.with_captured_bindings(bindings);
                    // Evaluate the expression with the current binding.
                    // Part of #1426: propagate eval errors (TLC treats these as fatal).
                    let value = eval_leaf(&eval_ctx, expr_spanned, tir)?;
                    primed_values.entry(var).or_default().push(value);
                }
                SymbolicAssignment::Unchanged(var) => {
                    // UNCHANGED inside existential - keep current value
                    if let Some(current) = new_ctx.env().get(&var) {
                        primed_values.entry(var).or_default().push(current.clone());
                    }
                }
                SymbolicAssignment::InSet(var, ref set_expr, ref bindings) => {
                    // Restore captured bindings before evaluation
                    let eval_ctx = new_ctx.with_captured_bindings(bindings);
                    // Part of #1426: propagate eval errors (TLC treats these as fatal).
                    // Part of #1828: use eval_iter_set for SetPred-aware iteration.
                    // Part of #2987: use TLC-normalized ordering for BFS parity.
                    let set_val = eval_leaf(&eval_ctx, set_expr, tir)?;
                    // Part of #1886: discriminate "not enumerable" (defer) from
                    // fatal eval errors. Empty Vec only for defer-class errors.
                    let values: Vec<_> = match eval_iter_set_tlc_normalized(
                        &eval_ctx,
                        &set_val,
                        Some(set_expr.span),
                    ) {
                        Ok(iter) => iter.collect(),
                        Err(ref e)
                            if classify_iter_error_for_speculative_path(e)
                                == IterDomainAction::Defer =>
                        {
                            // Part of #1433: warn when InSet iteration is deferred
                            // inside EXISTS body. Empty Vec means this InSet contributes
                            // zero values, potentially missing successor states.
                            debug_eprintln!(
                                    debug_enum(),
                                    "evaluate_symbolic_assignments: InSet iteration deferred for {:?} (error: {:?})",
                                    var, e
                                );
                            Vec::new()
                        }
                        Err(e) => return Err(e),
                    };
                    primed_values.entry(var).or_default().extend(values);
                }
            }
        }
    }

    // Convert collected values to Value assignments with SetEnum
    // Use Value variant directly since we've already evaluated all possibilities
    // Part of #263: Sort by variable name for deterministic iteration order.
    // HashMap iteration order depends on RandomState seed, causing non-deterministic
    // successor generation and state count variance across runs.
    let mut primed_values_sorted: Vec<_> = primed_values.into_iter().collect();
    primed_values_sorted.sort_by(|(a, _), (b, _)| a.cmp(b));
    for (var, values) in primed_values_sorted {
        if !values.is_empty() {
            // Deduplicate values using a sorted set
            let unique: crate::value::SortedSet = values.into_iter().collect();
            // Build a SetEnum expression containing all the values
            let set_elems: Vec<Spanned<Expr>> = unique
                .iter()
                .map(|v| Spanned::new(super::super::value_to_expr(v), body.span))
                .collect();
            let set_expr = Spanned::new(Expr::SetEnum(set_elems), body.span);
            // No bindings needed - set_expr is already fully evaluated
            assignments.push(SymbolicAssignment::InSet(var, set_expr, Vec::new()));
        }
    }

    Ok(())
}

pub(super) fn extract_apply_symbolic_assignments(
    ctx: &EvalCtx,
    expr: &Spanned<Expr>,
    vars: &[Arc<str>],
    assignments: &mut Vec<SymbolicAssignment>,
    eager_eval: bool,
    registry: &VarRegistry,
    tir: Option<&TirProgram<'_>>,
) -> Result<(), EvalError> {
    let Expr::Apply(op_expr, args) = &expr.node else {
        return Err(EvalError::Internal {
            message: "extract_apply_symbolic_assignments requires Expr::Apply".to_string(),
            span: Some(expr.span),
        });
    };

    if let Expr::Ident(op_name, _) = &op_expr.node {
        // Part of #286: Apply config operator replacement (e.g., `Send <- MCSend`)
        let resolved_name = ctx.resolve_op_name(op_name);
        if let Some(def) = ctx.get_op(resolved_name) {
            let resolved_def_ptr = Arc::as_ptr(def) as usize;
            // Check if any parameter appears primed in the body
            // If so, use expression substitution (call-by-name) instead of value binding
            // This is required for TLA+ semantics like Action1(x,y) == x' = [x EXCEPT ![1] = y']
            // Part of #3073: use precomputed field instead of per-call AST walk.
            let needs_substitution = def.has_primed_param;

            // If any argument expression is an action (contains primes or calls operators
            // with primes), we MUST substitute call-by-name.
            //
            // Example (MCWriteThroughCache):
            //   MCSend(p, d, oldMemInt, newMemInt) == newMemInt = <<p, d>>
            //   Send(p, req, memInt, memInt')  (via config replacement Send <- MCSend)
            //
            // Here `memInt'` cannot be evaluated in the current-state context, so a
            // call-by-value bind would silently skip binding `newMemInt` and we'd miss
            // the implied assignment to `memInt'`.
            //
            // Part of #141: Also check for action-level arguments like NoHistoryChange(l0(self))
            // where l0 is an action operator. Using expr_is_action_level instead of
            // expr_contains_prime catches these cases.
            let args_are_action = args.iter().any(|a| expr_is_action_level(ctx, &a.node));

            if needs_substitution || args_are_action {
                // Use call-by-name: substitute argument expressions into body.
                // Part of #3063: cache substituted body per call site.
                let substituted_body = super::super::subst_cache::cached_substitute(
                    ctx,
                    expr,
                    resolved_def_ptr,
                    || {
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
                    },
                );
                return extract_symbolic_assignments_inner(
                    ctx,
                    &substituted_body,
                    vars,
                    assignments,
                    eager_eval,
                    registry,
                    tir,
                );
            }

            // No primed parameters - use call-by-value (faster)
            // Fixes #167: Use bind_local instead of env.insert so that parameter
            // bindings are captured in local_stack for get_local_bindings().
            // Without this, deferred expressions like `msgs \cup {m}` lose the
            // binding of `m` when evaluated later in build_successor_states.
            let mut new_ctx = ctx.clone();
            for (param, arg) in def.params.iter().zip(args.iter()) {
                // Part of #1426: propagate eval errors (TLC treats these as fatal).
                // Previously silently skipped binding on error, leaving params unbound.
                let arg_val = eval_leaf(ctx, arg, tir)?;
                // Part of #1383: new_ctx is owned and reassigned — use into_bind_local
                new_ctx = new_ctx.into_bind_local(param.name.node.as_str(), arg_val);
            }
            extract_symbolic_assignments_inner(
                &new_ctx,
                &def.body,
                vars,
                assignments,
                eager_eval,
                registry,
                tir,
            )?;
        }
    }
    Ok(())
}

pub(super) fn extract_module_ref_symbolic_assignments(
    ctx: &EvalCtx,
    expr: &Spanned<Expr>,
    vars: &[Arc<str>],
    assignments: &mut Vec<SymbolicAssignment>,
    eager_eval: bool,
    registry: &VarRegistry,
    tir: Option<&TirProgram<'_>>,
) -> Result<(), EvalError> {
    let Expr::ModuleRef(instance_name, op_name, args) = &expr.node else {
        return Err(EvalError::Internal {
            message: "extract_module_ref_symbolic_assignments requires Expr::ModuleRef".to_string(),
            span: Some(expr.span),
        });
    };

    // Look up instance metadata (module name + WITH substitutions)
    let instance_info =
        ctx.get_instance(instance_name.name())
            .ok_or_else(|| EvalError::UndefinedOp {
                name: format!("{}!{}", instance_name, op_name),
                span: Some(expr.span),
            })?;

    // Find the referenced operator definition in the instanced module.
    let op_def = ctx
        .get_instance_op_arc(&instance_info.module_name, op_name)
        .ok_or_else(|| EvalError::UndefinedOp {
            name: format!("{}!{}", instance_name, op_name),
            span: Some(expr.span),
        })?;
    let resolved_def_ptr = Arc::as_ptr(op_def) as usize;

    if op_def.params.len() != args.len() {
        return Err(EvalError::ArityMismatch {
            op: format!("{}!{}", instance_name, op_name),
            expected: op_def.params.len(),
            got: args.len(),
            span: Some(expr.span),
        });
    }

    // Apply INSTANCE ... WITH substitutions and parameter substitutions.
    // Part of #3063: cache substituted body per call site.
    let inlined = super::super::subst_cache::cached_substitute(ctx, expr, resolved_def_ptr, || {
        let mut body = apply_substitutions(&op_def.body, &instance_info.substitutions);
        if !op_def.params.is_empty() {
            let subs: Vec<Substitution> = op_def
                .params
                .iter()
                .zip(args.iter())
                .map(|(param, arg)| Substitution {
                    from: param.name.clone(),
                    to: arg.clone(),
                })
                .collect();
            body = apply_substitutions(&body, &subs);
        }
        body
    });

    // Evaluate/extract inside a scope where unqualified operator names resolve
    // to the instanced module's definitions.
    // Part of #1433: empty default is correct — modules without registered
    // instance operators simply have no local ops in scope. Not error-swallowing.
    let mut instance_local_ops: OpEnv = ctx
        .instance_ops()
        .get(&instance_info.module_name)
        .cloned()
        .unwrap_or_default();

    // Preserve any existing local ops (e.g. from surrounding LET) for names
    // not defined by the instanced module (needed for substitution expressions).
    if let Some(outer_local) = ctx.local_ops().as_deref() {
        for (name, def) in outer_local.iter() {
            instance_local_ops
                .entry(name.clone())
                .or_insert_with(|| def.clone());
        }
    }

    let scoped_ctx = ctx.with_local_ops(instance_local_ops);
    extract_symbolic_assignments_inner(
        &scoped_ctx,
        &inlined,
        vars,
        assignments,
        eager_eval,
        registry,
        tir,
    )
}

pub(super) fn extract_let_symbolic_assignments(
    ctx: &EvalCtx,
    expr: &Spanned<Expr>,
    vars: &[Arc<str>],
    assignments: &mut Vec<SymbolicAssignment>,
    eager_eval: bool,
    registry: &VarRegistry,
    tir: Option<&TirProgram<'_>>,
) -> Result<(), EvalError> {
    let Expr::Let(defs, body) = &expr.node else {
        return Err(EvalError::Internal {
            message: "extract_let_symbolic_assignments requires Expr::Let".to_string(),
            span: Some(expr.span),
        });
    };

    let mut new_ctx = ctx.clone();
    // For action-level LET bindings that depend on primed variables, we can't
    // eagerly evaluate them in the current-state context. Instead, we inline
    // the binding into the body so it can be evaluated later under an
    // appropriate (progressive) next-state context.
    let mut inlined_body: Spanned<Expr> = (**body).clone();
    for def in defs {
        if def.params.is_empty() {
            // Zero-param definition: only eagerly evaluate when it is state-level.
            //
            // Action-level LET bindings can depend on primed variables (e.g. `LET x == y' IN ...`)
            // and must be evaluated under a next-state context. In those cases we keep the
            // definition as an operator so it can be evaluated later with progressive
            // next-state bindings during successor construction.
            if expr_contains_any_prime(&def.body.node) {
                let subs = vec![Substitution {
                    from: def.name.clone(),
                    to: def.body.clone(),
                }];
                inlined_body = apply_substitutions(&inlined_body, &subs);
            } else {
                // State-level LET binding: evaluate now and bind to local_stack.
                // This handles cases like: LET r == ChooseOne(...) IN ...
                // Fix #564: Use bind_local instead of env.insert so the binding
                // is captured by get_local_bindings() for deferred expression evaluation.
                let val = eval_leaf(&new_ctx, &def.body, tir)?;
                // Part of #1383: new_ctx is owned and reassigned — use into_bind_local
                new_ctx = new_ctx.into_bind_local(def.name.node.as_str(), val);
            }
        } else {
            // Operator definition with params: store for later application
            new_ctx.define_op(def.name.node.clone(), def.clone());
        }
    }
    extract_symbolic_assignments_inner(
        &new_ctx,
        &inlined_body,
        vars,
        assignments,
        eager_eval,
        registry,
        tir,
    )
}
