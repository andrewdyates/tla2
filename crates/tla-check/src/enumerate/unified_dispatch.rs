// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Main recursive dispatch for unified successor enumeration.
//!
//! `enumerate_unified_inner` is the core recursive function that handles all
//! TLA+ expression types (Or, And, Exists, If, Let, Case, Apply, Ident,
//! ModuleRef, and catch-all guard/assignment). It dispatches to specialized
//! handlers for each expression type.
//!
//! Extracted from unified.rs as part of #2360.

use std::sync::Arc;

use smallvec::SmallVec;
use tla_core::ast::{Expr, Substitution};
use tla_core::Spanned;

use crate::error::EvalError;
use crate::eval::{apply_substitutions, EvalCtx};
use crate::Value;

use super::action_validation::action_holds_in_next_state_array;
use super::build_diff::build_successor_diffs_from_array_into;
use super::expr_analysis::{expr_is_action_level, flatten_and_spanned, might_need_prime_binding};
use super::guard_check::check_and_guards;
use super::symbolic_assignments::{
    evaluate_symbolic_assignments, extract_symbolic_assignments_with_registry,
};
use super::tir_leaf::eval_leaf;
use super::unified::enumerate_conjuncts;
use super::unified_exists::enumerate_exists;
use super::unified_module_ref::enumerate_module_ref;
use super::unified_scope::try_let_guard_first_shortcircuit;
use super::unified_types::{Cont, EnumMut, EnumParams, RecState};
use super::{case_guard_error, debug_enum, enabled_early_exit, is_let_lazy_safe_error};

/// Inner recursive dispatch for `enumerate_unified`.
pub(super) fn enumerate_unified_inner(
    ctx: &mut EvalCtx,
    expr: &Spanned<Expr>,
    p: &EnumParams<'_>,
    s: &mut RecState<'_>,
) -> Result<(), EvalError> {
    crate::eval::stack_safe(|| {
        let debug = debug_enum();

        if debug {
            eprintln!(
                "enumerate_unified: expr type={:?}",
                std::mem::discriminant(&expr.node)
            );
        }

        match &expr.node {
            // Label: transparent wrapper — unwrap and recurse into body.
            Expr::Label(label) => return enumerate_unified_inner(ctx, &label.body, p, s),

            // Disjunction: try each branch, accumulate results.
            // Clone-at-branch pattern (#2834): each branch gets a cloned EvalCtx,
            // guaranteeing ctx is never mutated by either branch.
            Expr::Or(a, b) => {
                let save_point = s.undo.len();

                // Part of #3923: PlusCal pc-guard hoisting.
                // When pc_guard_hoist is active, check if each Or branch has a
                // `pc = "label"` guard that doesn't match the current state.
                // Skip branches with non-matching guards — they produce zero successors.
                let skip_left = p.pc_guard_hoist.as_ref().is_some_and(|h| {
                    crate::checker_ops::pc_dispatch::or_branch_pc_guard_mismatches(
                        &a.node,
                        &h.current_pc,
                        ctx,
                    )
                });
                let skip_right = p.pc_guard_hoist.as_ref().is_some_and(|h| {
                    crate::checker_ops::pc_dispatch::or_branch_pc_guard_mismatches(
                        &b.node,
                        &h.current_pc,
                        ctx,
                    )
                });

                // Part of #3893: mark/restore replaces ctx.clone() per branch.
                let enum_mark = ctx.mark_enum();

                // Left branch — mark/restore isolates all ctx state
                if !skip_left {
                    let left_result = enumerate_unified_inner(ctx, a, p, s);
                    ctx.pop_to_enum_mark(&enum_mark);
                    s.working.unbind_to_no_invalidate(s.undo, save_point);
                    left_result?;
                }

                // Part of #1285: ENABLED early-exit — skip right branch if we found a successor.
                if enabled_early_exit() && s.results.has_results() {
                    return Ok(());
                }

                // Part of #3027: Early termination — skip right branch if sink stopped.
                if s.results.is_stopped() {
                    return Ok(());
                }

                // Right branch — ctx restored by mark, still pristine
                if !skip_right {
                    let right_result = enumerate_unified_inner(ctx, b, p, s);
                    ctx.pop_to_enum_mark(&enum_mark);
                    s.working.unbind_to_no_invalidate(s.undo, save_point);
                    right_result?;
                }

                Ok(())
            }

            // Conjunction: flatten and process via continuation-based enumeration.
            Expr::And(_, _) => {
                // Check guards before enumeration (TLA2-specific optimization, no TLC analog).
                // Correctness depends on check_and_guards correctly identifying disabled actions.
                if !check_and_guards(ctx, expr, debug, p.tir_leaf)? {
                    if debug {
                        eprintln!("enumerate_unified: AND guard check failed");
                    }
                    return Ok(());
                }

                // Flatten AND tree into conjuncts
                // Part of #3897: SmallVec avoids heap allocation for <=8 conjuncts.
                let mut conjuncts = SmallVec::new();
                flatten_and_spanned(expr, &mut conjuncts);

                // Check might_need_prime_binding BEFORE allocating buffers.
                // This is cached per AST node pointer so it's O(1) after first call.
                // The common case (~95%+ of AND conjuncts) does NOT need prime binding
                // validation, so we can skip the intermediate local_results buffer
                // entirely and enumerate directly into the outer sink.
                let needs_prime_filter = might_need_prime_binding(ctx, &expr.node);

                if needs_prime_filter {
                    // Slow path: need intermediate buffer for post-filtering.
                    // Part of #3027: Enumerate into a local Vec buffer so that
                    // might_need_prime_binding post-filtering (which needs random access:
                    // swap/truncate/indexing) works regardless of whether the outer sink
                    // is a Vec or a streaming callback.
                    let mut accumulated = Vec::with_capacity(p.vars.len());
                    let mut local_results: Vec<crate::state::DiffSuccessor> = Vec::new();
                    {
                        let mut m = EnumMut {
                            rec: RecState {
                                working: s.working,
                                undo: s.undo,
                                results: &mut local_results,
                            },
                            accumulated: &mut accumulated,
                            assigned_mask: 0,
                            has_complex: false,
                        };
                        let cont = Cont {
                            conjuncts: &conjuncts,
                            next_idx: 0,
                            scope_restore: None,
                        };
                        enumerate_conjuncts(ctx, &cont, None, p, &mut m)?;
                    }

                    // Validate successors: expression contains operators with hidden primes.
                    // Keep the surviving suffix in stable order while compacting in O(n).
                    // This avoids repeated Vec::remove shifts and does not reorder accepted
                    // successors, which keeps downstream traversal deterministic.
                    let end = local_results.len();
                    let mut write = 0;
                    for read in 0..end {
                        let succ_arr = local_results[read].materialize(p.base_with_fp, p.registry);
                        if action_holds_in_next_state_array(
                            ctx, expr, &succ_arr, p.registry, p.tir_leaf,
                        )? {
                            if write != read {
                                local_results.swap(write, read);
                            }
                            write += 1;
                        }
                    }
                    local_results.truncate(write);

                    // Push survivors to the real sink.
                    // Part of #3027: Propagate ControlFlow — stop pushing if
                    // the sink signals early termination (Break).
                    for diff in local_results {
                        if s.results.push_with_ctx(ctx, diff).is_break() {
                            break;
                        }
                    }
                } else {
                    // Fast path: no prime binding validation needed — enumerate
                    // directly into the outer sink, avoiding the intermediate
                    // local_results Vec allocation entirely. This eliminates one
                    // heap allocation + final copy loop per AND conjunct in the
                    // common case (called millions of times in BFS).
                    let mut accumulated = Vec::with_capacity(p.vars.len());
                    {
                        let mut m = EnumMut {
                            rec: RecState {
                                working: s.working,
                                undo: s.undo,
                                results: s.results,
                            },
                            accumulated: &mut accumulated,
                            assigned_mask: 0,
                            has_complex: false,
                        };
                        let cont = Cont {
                            conjuncts: &conjuncts,
                            next_idx: 0,
                            scope_restore: None,
                        };
                        enumerate_conjuncts(ctx, &cont, None, p, &mut m)?;
                    }
                }

                Ok(())
            }

            // Apply: inline operator and recurse
            Expr::Apply(op_expr, args) => {
                if let Expr::Ident(op_name, _) = &op_expr.node {
                    let resolved_name = ctx.resolve_op_name(op_name.as_str());
                    if let Some(def) = ctx.get_op(resolved_name) {
                        let resolved_def_ptr = Arc::as_ptr(def) as usize;
                        let def = Arc::clone(def);
                        // Part of #3073: use precomputed field instead of per-call AST walk.
                        let needs_substitution = def.has_primed_param;
                        let args_are_action =
                            args.iter().any(|arg| expr_is_action_level(ctx, &arg.node));

                        if needs_substitution || args_are_action {
                            // Call-by-name: substitute argument expressions into body.
                            // Part of #3063: cache substituted body per call site —
                            // apply_substitutions deep-clones the entire AST tree but
                            // always produces the same result for a given call site.
                            let substituted_body = super::subst_cache::cached_substitute(
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
                            let _guard = ctx.skip_prime_guard(
                                !def.guards_depend_on_prime && !def.contains_prime,
                            );
                            return enumerate_unified_inner(ctx, &substituted_body, p, s);
                        }

                        // Call-by-value: bind parameters to evaluated argument values
                        // Part of #3194: use eval_leaf to try TIR for arguments.
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
                        let _guard = ctx
                            .skip_prime_guard(!def.guards_depend_on_prime && !def.contains_prime);
                        let result = enumerate_unified_inner(ctx, &def.body, p, s);
                        drop(_guard);
                        ctx.pop_to_mark(&mark);
                        return result;
                    }
                }
                // Unknown operator — try to evaluate as boolean guard
                // Part of #3194: use eval_leaf to try TIR first.
                match eval_leaf(ctx, expr, p.tir_leaf) {
                    Ok(Value::Bool(true)) => Ok(()),
                    Ok(Value::Bool(false)) => Ok(()),
                    // Part of #1433: Preserve original eval error instead of replacing
                    // with generic Internal error. Non-boolean Ok is still an internal error.
                    Ok(_) => Err(EvalError::Internal {
                        message: format!(
                            "enumerate_unified: cannot resolve Apply operator at {:?}",
                            expr.span
                        ),
                        span: Some(expr.span),
                    }),
                    Err(e) => Err(e),
                }
            }

            // Ident: lookup zero-arg operator and inline
            Expr::Ident(name, _) => {
                let resolved = ctx.resolve_op_name(name.as_str());
                if let Some(def) = ctx.get_op(resolved).cloned() {
                    if def.params.is_empty() {
                        let _guard = ctx
                            .skip_prime_guard(!def.guards_depend_on_prime && !def.contains_prime);
                        return enumerate_unified_inner(ctx, &def.body, p, s);
                    }
                }
                // Try evaluating as boolean (could be TRUE/FALSE constant)
                // Part of #3194: use eval_leaf to try TIR first.
                match eval_leaf(ctx, expr, p.tir_leaf) {
                    Ok(Value::Bool(true)) => Ok(()),
                    Ok(Value::Bool(false)) => Ok(()),
                    // Part of #1433: Preserve original eval error instead of replacing
                    // with generic Internal error. Non-boolean Ok is still an internal error.
                    Ok(_) => Err(EvalError::Internal {
                        message: format!(
                            "enumerate_unified: cannot resolve Ident operator '{}' at {:?}",
                            name, expr.span
                        ),
                        span: Some(expr.span),
                    }),
                    Err(e) => Err(e),
                }
            }

            // Existential quantification: iterate domain, recurse into body
            Expr::Exists(bounds, body) => {
                let mut accumulated = Vec::new();
                let mut m = EnumMut {
                    rec: RecState {
                        working: s.working,
                        undo: s.undo,
                        results: s.results,
                    },
                    accumulated: &mut accumulated,
                    assigned_mask: 0,
                    has_complex: false,
                };
                enumerate_exists(ctx, bounds, 0, body, p, &mut m)
            }

            // IF: evaluate condition, recurse into chosen branch
            Expr::If(cond, then_branch, else_branch) => {
                // Bind working state so condition can access primed variables
                // Part of #3194: use eval_leaf to try TIR first at this leaf site.
                let guard_result = {
                    let _env = ctx.bind_next_state_env_guard(s.working.env_ref());
                    eval_leaf(ctx, cond, p.tir_leaf)
                };

                let guard = guard_result?;
                match guard.as_bool() {
                    Some(true) => enumerate_unified_inner(ctx, then_branch, p, s),
                    Some(false) => enumerate_unified_inner(ctx, else_branch, p, s),
                    None => Err(EvalError::TypeError {
                        expected: "BOOLEAN",
                        got: guard.type_name(),
                        span: Some(cond.span),
                    }),
                }
            }

            // LET: bind definitions, recurse into body
            Expr::Let(defs, body) => {
                if let Some(false) =
                    try_let_guard_first_shortcircuit(ctx, defs, body, s.working.env_ref(), p)
                {
                    return Ok(());
                }

                let mark = ctx.mark_stack();

                let all_guards_safe = defs
                    .iter()
                    .all(|def| !def.guards_depend_on_prime && !def.contains_prime);
                let _skip_guard = ctx.skip_prime_guard(all_guards_safe);

                // Register all definitions (including parameterized) in local_ops
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

                // Bind zero-arg definitions to values eagerly when possible.
                // Part of #1262: TLC evaluates LET bindings lazily — unused bindings that
                // would fail (e.g., `LET parent == CHOOSE p \in {} : TRUE IN ...` where
                // `parent` is never used) don't cause errors. We attempt eager evaluation
                // as an optimization, but on "disabled action" errors (ChooseFailed,
                // NotInDomain, TypeError, etc.) we skip the binding and fall through to
                // local_ops lazy lookup.
                // Part of #3194: use eval_leaf for LET binding evaluation.
                for def in defs {
                    if def.params.is_empty() {
                        match eval_leaf(ctx, &def.body, p.tir_leaf) {
                            Ok(val) => {
                                ctx.push_binding(Arc::from(def.name.node.as_str()), val);
                            }
                            Err(e) if is_let_lazy_safe_error(&e) => {
                                // Skip binding — if the def is actually used, the reference
                                // will re-evaluate via local_ops and propagate the error then.
                            }
                            Err(e) => {
                                ctx.pop_to_mark(&mark);
                                *ctx.local_ops_mut() = saved_local_ops;
                                return Err(e);
                            }
                        }
                    }
                }

                let result = enumerate_unified_inner(ctx, body, p, s);

                ctx.pop_to_mark(&mark);
                *ctx.local_ops_mut() = saved_local_ops;
                result
            }

            // CASE: evaluate arm guards in order, take first match
            // Part of #3194: use eval_leaf for CASE guard evaluation.
            Expr::Case(arms, other) => {
                for arm in arms {
                    match eval_leaf(ctx, &arm.guard, p.tir_leaf) {
                        Ok(Value::Bool(true)) => {
                            return enumerate_unified_inner(ctx, &arm.body, p, s);
                        }
                        Ok(Value::Bool(false)) => {}
                        // Part of #1425: Non-boolean CASE guard is a type error.
                        // TLC: Assert.fail("A non-boolean expression was used as guard condition of CASE")
                        Ok(other) => {
                            return Err(case_guard_error(
                                EvalError::TypeError {
                                    expected: "BOOLEAN",
                                    got: other.type_name(),
                                    span: Some(arm.guard.span),
                                },
                                arm.guard.span,
                            ));
                        }
                        Err(e) => return Err(case_guard_error(e, arm.guard.span)),
                    }
                }
                // No arm matched — use OTHER if present
                if let Some(other_expr) = other {
                    enumerate_unified_inner(ctx, other_expr, p, s)
                } else {
                    // Part of #1425: TLC raises fatal error when no CASE arm matches
                    // and no OTHER clause is present. Previously returned Ok(()) silently.
                    Err(EvalError::CaseNoMatch {
                        span: Some(expr.span),
                    })
                }
            }

            // ModuleRef: INSTANCE operator inlining with substitutions
            Expr::ModuleRef(instance_name, op_name, args) => {
                enumerate_module_ref(ctx, expr, instance_name, op_name, args, p, s)
            }

            // Default: try symbolic assignment extraction first, then boolean guard.
            // Part of #1275: Assignment extraction must come before boolean eval because
            // expressions like `x' = x + 1` evaluate to false (comparing current working
            // state) but are actually primed assignments that should produce successors.
            _ => {
                // First, try extracting symbolic assignments (handles primed assignments)
                let mut symbolic = Vec::new();
                extract_symbolic_assignments_with_registry(
                    ctx,
                    expr,
                    p.vars,
                    &mut symbolic,
                    p.registry,
                    p.tir_leaf,
                )?;
                if debug {
                    let expr_name = match &expr.node {
                        Expr::Unchanged(_) => "Unchanged",
                        Expr::Not(_) => "Not",
                        Expr::Prime(_) => "Prime",
                        Expr::Eq(_, _) => "Eq",
                        _ => "Other",
                    };
                    eprintln!(
                        "enumerate_unified: catch-all expr={}, symbolic len={}, results_before={}",
                        expr_name,
                        symbolic.len(),
                        s.results.count()
                    );
                }
                if !symbolic.is_empty() {
                    let assignments = evaluate_symbolic_assignments(ctx, &symbolic, p.tir_leaf)?;
                    if debug {
                        eprintln!(
                            "enumerate_unified: evaluated {} assignments, results_before={}",
                            assignments.len(),
                            s.results.count()
                        );
                    }
                    build_successor_diffs_from_array_into(
                        ctx,
                        p.base_with_fp,
                        p.vars,
                        &assignments,
                        p.registry,
                        s.results,
                    );
                    if debug {
                        eprintln!(
                            "enumerate_unified: after build, results_after={}",
                            s.results.count()
                        );
                    }
                    return Ok(());
                }

                // No assignments found — evaluate as boolean guard.
                // Part of #1432: Previously discarded eval result entirely. TLC propagates
                // all eval errors fatally in getNextStates; we now match that behavior.
                // Part of #3194: use eval_leaf to try TIR first.
                let eval_result = {
                    let _env = ctx.bind_next_state_env_guard(s.working.env_ref());
                    eval_leaf(ctx, expr, p.tir_leaf)
                };

                match eval_result {
                    Ok(Value::Bool(_)) => Ok(()),
                    Ok(other) => Err(EvalError::TypeError {
                        expected: "BOOLEAN",
                        got: other.type_name(),
                        span: Some(expr.span),
                    }),
                    Err(e) => Err(e),
                }
            }
        }
    })
}
