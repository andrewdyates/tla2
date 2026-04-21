// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Branch merging for IF/CASE expressions with action-level conditions.
//!
//! When IF/CASE conditions depend on primed variables that aren't yet resolved,
//! we merge assignments from both branches into conditional expressions that
//! can be evaluated later with progressive next-state context.

use std::sync::Arc;

use tla_core::ast::Expr;
use tla_core::Spanned;

use tla_eval::tir::TirProgram;

use crate::error::EvalError;
use crate::eval::EvalCtx;
use crate::Value;

use super::super::tir_leaf::eval_leaf;
use super::super::{
    case_guard_error, check_and_guards, is_action_level_error, is_guard_expression,
    is_speculative_eval_fallback, PrimedAssignment, SymbolicAssignment,
};
use super::evaluate::evaluate_symbolic_assignments;
use super::extract_symbolic_assignments_inner;

use crate::var_index::VarRegistry;

#[derive(Clone)]
enum BranchAssignKind {
    Expr(Spanned<Expr>),
    Unchanged,
    InSet(Spanned<Expr>),
}

fn collect_branch_assignments(
    assignments: Vec<SymbolicAssignment>,
    track_order: bool,
) -> (
    Vec<Arc<str>>,
    rustc_hash::FxHashMap<Arc<str>, BranchAssignKind>,
) {
    let mut order = Vec::new();
    let mut map = rustc_hash::FxHashMap::default();
    for assign in assignments {
        let (name, kind) = match assign {
            SymbolicAssignment::Expr(name, rhs, _bindings) => {
                // Ignore bindings - will use merged bindings at capture point
                (name, BranchAssignKind::Expr(rhs))
            }
            SymbolicAssignment::Unchanged(name) => (name, BranchAssignKind::Unchanged),
            SymbolicAssignment::InSet(name, set_expr, _bindings) => {
                // Ignore bindings - will use merged bindings at capture point
                (name, BranchAssignKind::InSet(set_expr))
            }
            SymbolicAssignment::Value(_, _) => {
                // No-eager-eval mode should not produce Value, but ignore if it does.
                continue;
            }
        };

        if track_order && !map.contains_key(&name) {
            order.push(name.clone());
        }
        map.insert(name, kind);
    }
    (order, map)
}

/// Try to evaluate a condition that references primed variables by building a
/// partial next-state from accumulated symbolic assignments. Falls back to
/// plain eval if assignments can't be resolved.
fn eval_cond_with_partial_next_state(
    ctx: &EvalCtx,
    cond: &Spanned<Expr>,
    assignments: &[SymbolicAssignment],
    tir: Option<&TirProgram<'_>>,
) -> Result<Value, EvalError> {
    let partial_assignments = match evaluate_symbolic_assignments(ctx, assignments, tir) {
        Ok(pa) => pa,
        // Part of #1433: Only fall back to plain eval for speculative/action-level
        // errors (unresolved references, primed vars not yet bound). Fatal errors
        // (TypeError, etc.) propagate instead of being masked by fallback eval.
        Err(e) if is_speculative_eval_fallback(&e) || is_action_level_error(&e) => {
            return eval_leaf(ctx, cond, tir)
        }
        Err(e) => return Err(e),
    };

    // If any assignment is deferred or InSet, we can't build a complete next-state
    let has_unresolved = partial_assignments.iter().any(|a| {
        matches!(
            a,
            PrimedAssignment::DeferredExpr(_, _) | PrimedAssignment::InSet(_, _)
        )
    });
    if has_unresolved {
        return eval_leaf(ctx, cond, tir);
    }

    // Build partial next-state environment from resolved assignments
    let mut next_env = ctx.env().clone();
    for assign in &partial_assignments {
        match assign {
            PrimedAssignment::Assign(name, value) => {
                next_env.insert(Arc::clone(name), value.clone());
            }
            PrimedAssignment::Unchanged(name) => {
                if let Some(current) = ctx.env().get(name) {
                    next_env.insert(Arc::clone(name), current.clone());
                }
            }
            PrimedAssignment::InSet(_, _) | PrimedAssignment::DeferredExpr(_, _) => {
                return Err(EvalError::Internal {
                    message: "eval_cond_with_partial_next_state: InSet/DeferredExpr should have been filtered".to_string(),
                    span: Some(cond.span),
                });
            }
        }
    }
    // Part of #3416: conservative cache boundary for eval_leaf() path
    let eval_ctx = ctx.with_next_state_for_eval_scope(next_env);
    eval_leaf(&eval_ctx, cond, tir)
}

pub(super) fn extract_if_symbolic_assignments(
    ctx: &EvalCtx,
    expr: &Spanned<Expr>,
    vars: &[Arc<str>],
    assignments: &mut Vec<SymbolicAssignment>,
    eager_eval: bool,
    registry: &VarRegistry,
    tir: Option<&TirProgram<'_>>,
) -> Result<(), EvalError> {
    let Expr::If(cond, then_branch, else_branch) = &expr.node else {
        return Err(EvalError::Internal {
            message: "extract_if_symbolic_assignments requires Expr::If".to_string(),
            span: Some(expr.span),
        });
    };

    // Check if condition contains primed variables (action predicate)
    // If so, we need to build a partial next-state context from accumulated assignments
    let cond_is_guard = is_guard_expression(&cond.node);
    let cond_result = if cond_is_guard {
        eval_leaf(ctx, cond, tir)
    } else {
        eval_cond_with_partial_next_state(ctx, cond, assignments, tir)
    };

    match cond_result {
        Ok(Value::Bool(true)) => extract_symbolic_assignments_inner(
            ctx,
            then_branch,
            vars,
            assignments,
            eager_eval,
            registry,
            tir,
        ),
        Ok(Value::Bool(false)) => extract_symbolic_assignments_inner(
            ctx,
            else_branch,
            vars,
            assignments,
            eager_eval,
            registry,
            tir,
        ),
        // Part of #1723: Non-boolean IF condition is always a type error per TLC.
        // TLC: Assert.fail("A non-boolean expression was used as the condition of an IF")
        Ok(other_val) => Err(EvalError::TypeError {
            expected: "BOOLEAN",
            got: other_val.type_name(),
            span: Some(cond.span),
        }),
        // Part of #1723: Eval error in IF condition.
        // Guard expressions (no primed vars) must evaluate cleanly — propagate errors.
        // Non-guard conditions may fail because primed variables aren't resolved yet —
        // fall through to branch merging.
        Err(e) if cond_is_guard => Err(e),
        // Part of #1433: Only merge branches for speculative/action-level errors
        // (unresolved primed variables, unbound references). Fatal errors propagate.
        Err(e) if is_speculative_eval_fallback(&e) || is_action_level_error(&e) => {
            // Condition couldn't be evaluated in the current-state context (likely
            // depends on primed variables). Merge assignments from both branches into
            // conditional assignments that can be evaluated later with progressive
            // next-state context.
            let mut then_assignments = Vec::new();
            extract_symbolic_assignments_inner(
                ctx,
                then_branch,
                vars,
                &mut then_assignments,
                false,
                registry,
                tir,
            )?;
            let mut else_assignments = Vec::new();
            extract_symbolic_assignments_inner(
                ctx,
                else_branch,
                vars,
                &mut else_assignments,
                false,
                registry,
                tir,
            )?;

            let (then_order, then_map) = collect_branch_assignments(then_assignments, true);
            let (_, else_map) = collect_branch_assignments(else_assignments, false);

            // Capture bindings for the merged IF expression
            let captured_bindings = ctx.get_local_bindings().clone();

            for name in then_order {
                let Some(then_kind) = then_map.get(&name) else {
                    continue;
                };
                let Some(else_kind) = else_map.get(&name) else {
                    continue;
                };

                match (then_kind, else_kind) {
                    (BranchAssignKind::Expr(then_rhs), BranchAssignKind::Expr(else_rhs)) => {
                        let merged = Spanned::new(
                            Expr::If(
                                cond.clone(),
                                Box::new(then_rhs.clone()),
                                Box::new(else_rhs.clone()),
                            ),
                            expr.span,
                        );
                        assignments.push(SymbolicAssignment::Expr(
                            name.clone(),
                            merged,
                            captured_bindings.clone(),
                        ));
                    }
                    (BranchAssignKind::InSet(then_set), BranchAssignKind::InSet(else_set)) => {
                        let merged_set = Spanned::new(
                            Expr::If(
                                cond.clone(),
                                Box::new(then_set.clone()),
                                Box::new(else_set.clone()),
                            ),
                            expr.span,
                        );
                        assignments.push(SymbolicAssignment::InSet(
                            name.clone(),
                            merged_set,
                            captured_bindings.clone(),
                        ));
                    }
                    (BranchAssignKind::Unchanged, BranchAssignKind::Unchanged) => {
                        assignments.push(SymbolicAssignment::Unchanged(name.clone()));
                    }
                    _ => {}
                }
            }

            Ok(())
        }
        // Part of #1433: Fatal error in non-guard IF condition — propagate.
        Err(e) => Err(e),
    }
}

#[allow(clippy::too_many_arguments)]
pub(super) fn extract_case_symbolic_assignments(
    ctx: &EvalCtx,
    expr: &Spanned<Expr>,
    vars: &[Arc<str>],
    assignments: &mut Vec<SymbolicAssignment>,
    eager_eval: bool,
    debug: bool,
    registry: &VarRegistry,
    tir: Option<&TirProgram<'_>>,
) -> Result<(), EvalError> {
    let Expr::Case(arms, other) = &expr.node else {
        return Err(EvalError::Internal {
            message: "extract_case_symbolic_assignments requires Expr::Case".to_string(),
            span: Some(expr.span),
        });
    };

    if debug {
        eprintln!(
            "EXTRACT: Case - {} arms, other={}",
            arms.len(),
            other.is_some()
        );
    }
    for (i, arm) in arms.iter().enumerate() {
        match eval_leaf(ctx, &arm.guard, tir) {
            Ok(Value::Bool(true)) => {
                // Part of #342: Validate body guards BEFORE extracting assignments.
                // CASE arm bodies may have guards like `active_read = FALSE` that must
                // be checked - otherwise we extract invalid assignments causing false positives.
                if !check_and_guards(ctx, &arm.body, debug, tir)? {
                    if debug {
                        eprintln!(
                            "EXTRACT: Case arm {} body guards failed, skipping to next arm",
                            i
                        );
                    }
                    continue; // Skip this arm - body guards not satisfied
                }
                if debug {
                    eprintln!(
                        "EXTRACT: Case arm {} guard=true, body guards passed, extracting",
                        i
                    );
                }
                return extract_symbolic_assignments_inner(
                    ctx,
                    &arm.body,
                    vars,
                    assignments,
                    eager_eval,
                    registry,
                    tir,
                );
            }
            Ok(Value::Bool(false)) => {
                if debug {
                    eprintln!("EXTRACT: Case arm {} guard=false, continuing", i);
                }
            }
            // Part of #1703: Non-boolean CASE guard is a type error.
            // TLC: Assert.fail("A non-boolean expression was used as guard condition of CASE")
            Ok(other_val) => {
                return Err(case_guard_error(
                    EvalError::TypeError {
                        expected: "BOOLEAN",
                        got: other_val.type_name(),
                        span: Some(arm.guard.span),
                    },
                    arm.guard.span,
                ));
            }
            // Part of #1703: Propagate eval errors from CASE guards.
            // TLC: EvalException propagates fatally from guard evaluation.
            Err(e) => return Err(case_guard_error(e, arm.guard.span)),
        }
    }
    // No arm matched - try OTHER
    if let Some(other_body) = other {
        if debug {
            eprintln!("EXTRACT: Case - no arm matched, extracting from OTHER");
        }
        extract_symbolic_assignments_inner(
            ctx,
            other_body,
            vars,
            assignments,
            eager_eval,
            registry,
            tir,
        )
    } else {
        // Part of #1732: TLC raises fatal error when no CASE arm matches
        // and no OTHER clause is present. Previously returned Ok(()) silently,
        // which treated unmatched CASE as a disabled action instead of an error.
        // TLC: Assert.fail("Attempted to evaluate a CASE expression, and none of the conditions were true.")
        Err(EvalError::CaseNoMatch {
            span: Some(expr.span),
        })
    }
}
