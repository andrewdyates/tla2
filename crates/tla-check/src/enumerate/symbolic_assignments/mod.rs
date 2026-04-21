// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Symbolic extraction and evaluation of primed-variable assignments.
//!
//! This module walks TLA+ Next relations to extract symbolic assignments
//! of the form `x' = expr`, `x' \in S`, or `UNCHANGED x`, then evaluates
//! them with progressive next-state context to produce concrete successor values.

use std::sync::Arc;

use tla_core::ast::Expr;
use tla_core::Spanned;

use tla_eval::tir::TirProgram;

use crate::error::EvalError;
use crate::eval::EvalCtx;

use super::tir_leaf::eval_leaf;

use super::unchanged_extraction::extract_unchanged_vars_symbolic_with_ctx;
use super::{
    debug_extract, expr_references_state_vars, is_action_level_error, is_speculative_eval_fallback,
    SymbolicAssignment,
};

use crate::var_index::VarRegistry;

mod branch;
pub(in crate::enumerate) mod evaluate;
mod extract_handlers;
pub(in crate::enumerate) mod toposort;

// Re-export the public API for the parent module.
pub(in crate::enumerate) use evaluate::evaluate_symbolic_assignments;

/// O(1) variable lookup via registry.
pub(crate) fn find_state_var<'a>(
    name: &str,
    vars: &'a [Arc<str>],
    registry: &VarRegistry,
) -> Option<&'a Arc<str>> {
    registry.get(name).map(|idx| &vars[idx.as_usize()])
}

/// Extract symbolic assignments (expressions, not values) from a Next relation.
/// Test-only entry point that builds a VarRegistry from the vars slice.
/// Production callers should use `extract_symbolic_assignments_with_registry`.
#[cfg(test)]
pub(in crate::enumerate) fn extract_symbolic_assignments(
    ctx: &EvalCtx,
    expr: &Spanned<Expr>,
    vars: &[Arc<str>],
    assignments: &mut Vec<SymbolicAssignment>,
) -> Result<(), EvalError> {
    let registry = VarRegistry::from_names(vars.iter().cloned());
    extract_symbolic_assignments_inner(ctx, expr, vars, assignments, true, &registry, None)
}

/// Extract symbolic assignments with O(1) registry lookups for hot-path callers.
pub(in crate::enumerate) fn extract_symbolic_assignments_with_registry(
    ctx: &EvalCtx,
    expr: &Spanned<Expr>,
    vars: &[Arc<str>],
    assignments: &mut Vec<SymbolicAssignment>,
    registry: &VarRegistry,
    tir: Option<&TirProgram<'_>>,
) -> Result<(), EvalError> {
    extract_symbolic_assignments_inner(ctx, expr, vars, assignments, true, registry, tir)
}

pub(crate) fn extract_symbolic_assignments_inner(
    ctx: &EvalCtx,
    expr: &Spanned<Expr>,
    vars: &[Arc<str>],
    assignments: &mut Vec<SymbolicAssignment>,
    eager_eval: bool,
    registry: &VarRegistry,
    tir: Option<&TirProgram<'_>>,
) -> Result<(), EvalError> {
    let debug = debug_extract();
    if debug {
        eprintln!(
            "EXTRACT: expr type={:?}, span={:?}",
            std::mem::discriminant(&expr.node),
            expr.span
        );
    }

    match &expr.node {
        // Conjunction: extract from both sides
        Expr::And(a, b) => {
            if debug {
                eprintln!("EXTRACT: And - processing both sides");
            }
            extract_symbolic_assignments_inner(
                ctx,
                a,
                vars,
                assignments,
                eager_eval,
                registry,
                tir,
            )?;
            extract_symbolic_assignments_inner(
                ctx,
                b,
                vars,
                assignments,
                eager_eval,
                registry,
                tir,
            )?;
            Ok(())
        }
        Expr::Eq(_, _) => {
            extract_eq_symbolic_assignments(ctx, expr, vars, assignments, eager_eval, registry, tir)
        }
        // UNCHANGED <<x, y>> or UNCHANGED x
        // Use _with_ctx to resolve definition aliases from EXTENDS (#124)
        Expr::Unchanged(inner_expr) => {
            extract_unchanged_vars_symbolic_with_ctx(
                &inner_expr.node,
                vars,
                assignments,
                Some(ctx),
                registry,
            );
            Ok(())
        }
        // Membership with primed variable: x' \in S
        Expr::In(lhs, rhs) => {
            if let Expr::Prime(inner_lhs) = &lhs.node {
                if let Expr::Ident(name, _) | Expr::StateVar(name, _, _) = &inner_lhs.node {
                    if let Some(var) = find_state_var(name.as_str(), vars, registry) {
                        // Capture bindings (O(n)) instead of substituting (O(AST))
                        assignments.push(SymbolicAssignment::InSet(
                            Arc::clone(var),
                            (**rhs).clone(),
                            ctx.get_local_bindings().clone(),
                        ));
                    }
                }
            }
            Ok(())
        }
        Expr::Exists(_, _) => extract_handlers::extract_exists_symbolic_assignments(
            ctx,
            expr,
            vars,
            assignments,
            eager_eval,
            registry,
            tir,
        ),
        // TRUE is always satisfied
        Expr::Bool(true) => Ok(()),
        // Zero-param operator reference - recurse into operator body
        Expr::Ident(name, _) => {
            // Apply config operator replacement (e.g., `Send <- MCSend`) before lookup.
            let resolved_name = ctx.resolve_op_name(name);
            if let Some(def) = ctx.get_op(resolved_name) {
                if def.params.is_empty() {
                    if debug {
                        eprintln!(
                            "EXTRACT: Ident {resolved_name} is zero-param op, recursing into body"
                        );
                    }
                    extract_symbolic_assignments_inner(
                        ctx,
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
        Expr::Apply(_, _) => extract_handlers::extract_apply_symbolic_assignments(
            ctx,
            expr,
            vars,
            assignments,
            eager_eval,
            registry,
            tir,
        ),
        Expr::ModuleRef(_, _, _) => extract_handlers::extract_module_ref_symbolic_assignments(
            ctx,
            expr,
            vars,
            assignments,
            eager_eval,
            registry,
            tir,
        ),
        Expr::Let(_, _) => extract_handlers::extract_let_symbolic_assignments(
            ctx,
            expr,
            vars,
            assignments,
            eager_eval,
            registry,
            tir,
        ),
        Expr::If(_, _, _) => branch::extract_if_symbolic_assignments(
            ctx,
            expr,
            vars,
            assignments,
            eager_eval,
            registry,
            tir,
        ),
        Expr::Case(_, _) => branch::extract_case_symbolic_assignments(
            ctx,
            expr,
            vars,
            assignments,
            eager_eval,
            debug,
            registry,
            tir,
        ),
        Expr::Label(label) => extract_symbolic_assignments_inner(
            ctx,
            &label.body,
            vars,
            assignments,
            eager_eval,
            registry,
            tir,
        ),
        _ => Ok(()),
    }
}

fn extract_eq_symbolic_assignments(
    ctx: &EvalCtx,
    expr: &Spanned<Expr>,
    vars: &[Arc<str>],
    assignments: &mut Vec<SymbolicAssignment>,
    eager_eval: bool,
    registry: &VarRegistry,
    tir: Option<&TirProgram<'_>>,
) -> Result<(), EvalError> {
    let Expr::Eq(lhs, rhs) = &expr.node else {
        return Err(EvalError::Internal {
            message: "extract_eq_symbolic_assignments requires Expr::Eq".to_string(),
            span: Some(expr.span),
        });
    };

    if extract_eq_prime_side(ctx, lhs, rhs, vars, assignments, eager_eval, registry, tir)? {
        return Ok(());
    }
    if extract_eq_prime_side(ctx, rhs, lhs, vars, assignments, eager_eval, registry, tir)? {
        return Ok(());
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn extract_eq_prime_side(
    ctx: &EvalCtx,
    prime_side: &Spanned<Expr>,
    value_side: &Spanned<Expr>,
    vars: &[Arc<str>],
    assignments: &mut Vec<SymbolicAssignment>,
    eager_eval: bool,
    registry: &VarRegistry,
    tir: Option<&TirProgram<'_>>,
) -> Result<bool, EvalError> {
    let Expr::Prime(inner_prime) = &prime_side.node else {
        return Ok(false);
    };
    let (Expr::Ident(name, _) | Expr::StateVar(name, _, _)) = &inner_prime.node else {
        return Ok(false);
    };
    let Some(var) = find_state_var(name.as_str(), vars, registry) else {
        return Ok(false);
    };

    // Fast path: x' = x (or symmetric x = x') when `x` is not shadowed by a
    // locally-bound variable.
    if let Expr::Ident(value_name, _) | Expr::StateVar(value_name, _, _) = &value_side.node {
        if value_name == name && !ctx.has_local_binding(value_name.as_str()) {
            assignments.push(SymbolicAssignment::Unchanged(Arc::clone(var)));
            return Ok(true);
        }
    }

    // Only eager-eval if the non-primed side doesn't reference state variables.
    // If it contains state vars (like `messages \union {m}`), defer to runtime.
    let value_refs_state = expr_references_state_vars(&value_side.node, vars);
    if eager_eval && !value_refs_state {
        match eval_leaf(ctx, value_side, tir) {
            Ok(value) => assignments.push(SymbolicAssignment::Value(Arc::clone(var), value)),
            // Part of #1433: Only defer for speculative/action-level errors
            // (unresolved references, primed vars not yet bound). All other
            // errors (TypeError, DivisionByZero, etc.) propagate as fatal.
            Err(e) if is_speculative_eval_fallback(&e) || is_action_level_error(&e) => {
                push_expr_symbolic_assignment(
                    ctx,
                    Arc::clone(var),
                    value_side.clone(),
                    assignments,
                );
            }
            Err(e) => return Err(e),
        }
    } else {
        push_expr_symbolic_assignment(ctx, Arc::clone(var), value_side.clone(), assignments);
    }

    Ok(true)
}

pub(crate) fn push_expr_symbolic_assignment(
    ctx: &EvalCtx,
    var: Arc<str>,
    rhs: Spanned<Expr>,
    assignments: &mut Vec<SymbolicAssignment>,
) {
    // Capture bindings (O(n)) instead of substituting (O(AST))
    assignments.push(SymbolicAssignment::Expr(
        var,
        rhs,
        ctx.get_local_bindings().clone(),
    ));
}
