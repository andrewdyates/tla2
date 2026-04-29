// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Helper functions for expression evaluation during init constraint extraction.
//!
//! These utilities wrap the evaluator with logging for swallowed errors
//! and handle the distinction between expected deferrals (unbound variables)
//! and unexpected errors (type errors, arithmetic errors).

use super::super::{value_to_expr, InitDomain};
use crate::error::EvalError;
use crate::eval::eval_iter_set_tlc_normalized;
use crate::eval::EvalCtx;
use crate::Value;
use tla_core::ast::Expr;
use tla_core::{ExprFold, SpanPolicy, SubstituteExpr};
use tla_core::{Span, Spanned};
use tla_eval::tir::TirProgram;

use super::super::tir_leaf::eval_leaf;

// Debug flag: detailed trace of ALL swallowed eval errors (debug builds only).
// Part of #1433: TLA2_WARN_INIT_ERRORS removed — unexpected errors are now always warned.
debug_flag!(debug_init_errors, "TLA2_DEBUG_INIT_ERRORS");

/// Returns true if this eval error is expected during init constraint extraction.
///
/// During constraint extraction, expressions referencing state variables that aren't
/// yet bound will fail evaluation. These are legitimate — the constraint is deferred
/// to be evaluated later when all variables are bound.
///
/// Unexpected errors (TypeError, DivisionByZero, etc.) indicate genuine spec bugs
/// or evaluator issues that would otherwise be silently masked by the deferral.
pub(super) fn is_expected_init_deferral(err: &EvalError) -> bool {
    match err {
        EvalError::UndefinedVar { .. }
        | EvalError::UndefinedOp { .. }
        | EvalError::PrimedVariableNotBound { .. }
        | EvalError::UnchangedNotEvaluable { .. } => true,
        // CaseGuardError wraps an inner error — classify based on the root cause.
        // A CASE guard referencing an unbound state variable produces
        // CaseGuardError(UndefinedVar), which is a legitimate deferral.
        EvalError::CaseGuardError { source, .. } => is_expected_init_deferral(source),
        _ => false,
    }
}

/// Log an eval error that is being swallowed during init constraint extraction.
///
/// Expected errors (unbound variable, undefined op) are traced only in debug builds.
/// Unexpected errors (type errors, arithmetic errors) are always warned — these
/// could mask correctness divergences from TLC. The expression is still evaluated
/// at runtime as a filter, so genuine errors will be caught downstream.
///
/// Part of #1433: warnings are unconditional for unexpected errors (previously
/// required `TLA2_WARN_INIT_ERRORS`). The flag now controls verbose expected-deferral
/// tracing only.
fn log_swallowed_eval_error(context: &str, err: &EvalError) {
    if is_expected_init_deferral(err) {
        debug_eprintln!(
            debug_init_errors(),
            "init_constraints({}): expected deferral: {}",
            context,
            err
        );
        return;
    }
    // Part of #1433: unconditional warning for unexpected eval errors.
    // These indicate potential spec bugs or evaluator issues. The constraint
    // extraction will defer to a runtime filter, so errors are not lost,
    // but users should know the optimization path encountered a problem.
    eprintln!("WARNING init_constraints({context}): unexpected eval error swallowed: {err}");
}

/// Evaluate an expression for init constraint extraction, logging swallowed errors.
///
/// Returns `Some(value)` on success, `None` on failure (with appropriate logging).
/// Part of #3194: uses TIR leaf eval when `tir` is `Some`.
pub(super) fn eval_for_init(
    ctx: &EvalCtx,
    expr: &Spanned<Expr>,
    context: &str,
    tir: Option<&TirProgram<'_>>,
) -> Option<Value> {
    match eval_leaf(ctx, expr, tir) {
        Ok(v) => Some(v),
        Err(ref e) => {
            log_swallowed_eval_error(context, e);
            None
        }
    }
}

/// Evaluate an expression for init constraint extraction, returning a bool if possible.
///
/// Returns `Some(b)` if eval succeeds and yields `Value::Bool(b)`, `None` otherwise.
/// Part of #3194: uses TIR leaf eval when `tir` is `Some`.
pub(super) fn eval_bool_for_init(
    ctx: &EvalCtx,
    expr: &Spanned<Expr>,
    context: &str,
    tir: Option<&TirProgram<'_>>,
) -> Option<bool> {
    match eval_leaf(ctx, expr, tir) {
        Ok(Value::Bool(b)) => Some(b),
        Ok(_) => None, // Non-bool result: not usable as a constraint, but not an error
        Err(ref e) => {
            log_swallowed_eval_error(context, e);
            None
        }
    }
}

/// Iterate over a set value for init constraint extraction, logging swallowed errors.
/// Part of #2987: uses TLC-normalized ordering for BFS parity.
pub(super) fn eval_iter_set_for_init<'a>(
    ctx: &EvalCtx,
    value: &'a Value,
    span: Option<Span>,
    context: &str,
) -> Option<Box<dyn Iterator<Item = Value> + 'a>> {
    match eval_iter_set_tlc_normalized(ctx, value, span) {
        Ok(iter) => Some(iter),
        Err(ref e) => {
            log_swallowed_eval_error(context, e);
            None
        }
    }
}

/// Returns true when this lazy set filter still depends on an unbound state var
/// and init extraction must fall back to `DeferredIn`.
fn setpred_references_unbound_state_var(ctx: &EvalCtx, spv: &crate::eval::SetPredValue) -> bool {
    let mut free_vars = tla_core::free_vars(&spv.pred().node);
    if let Some((name, _)) = spv.cached_simple_bound_name() {
        free_vars.remove(name.as_ref());
    }
    if let Some(entries) = spv.cached_tuple_bound_names() {
        for (name, _) in entries {
            free_vars.remove(name.as_ref());
        }
    }

    free_vars.into_iter().any(|name| {
        ctx.var_registry().get(&name).is_some() && !ctx.env().contains_key(name.as_str())
    })
}

/// Convert an evaluated set-like value into an init domain.
///
/// Eager materialization is kept for plain `Set`/`Interval` values, while
/// larger lazy finite sets (RecordSet, FuncSet, SetPred, etc.) stay lazy until
/// enumeration time.
pub(super) fn init_domain_from_value(
    ctx: &EvalCtx,
    value: Value,
    span: Option<Span>,
    context: &str,
) -> Option<InitDomain> {
    match value {
        Value::Set(_) | Value::Interval(_) => {
            let iter = eval_iter_set_for_init(ctx, &value, span, context)?;
            Some(InitDomain::Concrete(iter.collect()))
        }
        // Preserve state-independent SetPred domains lazily so CoffeeCan-style
        // record filters can stream at enumeration time, but still defer when
        // the predicate reads another state variable that has not been bound
        // yet (e.g. `{s \in SUBSET D : Cardinality(s) = x}` for `y \in ...`).
        Value::SetPred(ref spv) => {
            if setpred_references_unbound_state_var(ctx, spv) {
                return None;
            }
            if value.is_finite_set() {
                Some(InitDomain::Enumerable(value))
            } else {
                let iter = eval_iter_set_for_init(ctx, &value, span, context)?;
                Some(InitDomain::Concrete(iter.collect()))
            }
        }
        _ if value.is_set() && value.is_finite_set() => Some(InitDomain::Enumerable(value)),
        _ => {
            let iter = eval_iter_set_for_init(ctx, &value, span, context)?;
            Some(InitDomain::Concrete(iter.collect()))
        }
    }
}

/// Substitute parameters in an expression with argument expressions
///
/// Used to inline operator definitions during constraint extraction.
/// For example, if we have `XInit(v) == v = 0` and we call `XInit(x)`,
/// this substitutes `v -> x` to get `x = 0`.
///
/// Uses `SubstituteExpr` (capture-avoiding fold over all 65 Expr variants)
/// instead of a partial manual match that silently dropped substitutions
/// for 57/64 variants (#1374).
pub(super) fn substitute_params(
    expr: &Expr,
    params: &[tla_core::ast::OpParam],
    args: &[Spanned<Expr>],
) -> Expr {
    let subs: std::collections::HashMap<&str, &Spanned<Expr>> = params
        .iter()
        .zip(args.iter())
        .map(|(p, a)| (p.name.node.as_str(), a))
        .collect();
    let mut sub = SubstituteExpr {
        subs,
        span_policy: SpanPolicy::Preserve,
    };
    sub.fold_expr(Spanned::new(expr.clone(), Span::dummy()))
        .node
}

/// Substitute a bound variable name with a value in an expression.
/// Returns a new expression with all occurrences of `var_name` replaced with the value.
pub(super) fn substitute_bound_var(expr: &Expr, var_name: &str, value: &Value) -> Expr {
    let value_expr = value_to_expr(value);
    substitute_bound_var_with_expr(expr, var_name, &value_expr)
}

pub(super) fn substitute_bound_var_with_expr(
    expr: &Expr,
    var_name: &str,
    replacement: &Expr,
) -> Expr {
    let replacement_spanned = Spanned::new(replacement.clone(), Span::dummy());
    let mut sub = SubstituteExpr {
        subs: std::collections::HashMap::from([(var_name, &replacement_spanned)]),
        span_policy: SpanPolicy::Preserve,
    };
    let input = Spanned::new(expr.clone(), Span::dummy());
    sub.fold_expr(input).node
}

/// Maximum expression complexity for constraint extraction.
/// This limit exists because extract_constraints_rec uses recursion.
/// With stack_safe() (stacker::maybe_grow with 1MB red zone / 16MB growth), much larger
/// expressions can be handled. The limit is set conservatively to avoid
/// excessive memory usage from very deeply nested expressions.
///
/// To fully remove this limit, convert extract_constraints_rec to iterative
/// using an explicit task stack (similar to count_expr_nodes pattern above).
/// This requires handling the complex result combination logic (cross-product
/// for AND, concatenation for OR, operator inlining, etc.) iteratively.
pub(super) const MAX_EXPR_NODES: usize = 4096;

/// Count the approximate number of "structural" nodes in an expression tree.
///
/// This is iterative to avoid stack overflow, and intentionally ignores leaf nodes
/// (identifiers, literals, etc.) so that long conjunctions of simple equalities
/// don't get rejected as "too complex".
pub(crate) fn count_expr_nodes(expr: &Expr) -> usize {
    let mut count = 0usize;
    let mut stack: Vec<&Expr> = vec![expr];

    while let Some(e) = stack.pop() {
        match e {
            Expr::And(a, b)
            | Expr::Or(a, b)
            | Expr::Eq(a, b)
            | Expr::Neq(a, b)
            | Expr::Lt(a, b)
            | Expr::Leq(a, b)
            | Expr::Gt(a, b)
            | Expr::Geq(a, b)
            | Expr::In(a, b)
            | Expr::NotIn(a, b)
            | Expr::Implies(a, b) => {
                count += 1;
                // Stop early if we've exceeded the limit
                if count > MAX_EXPR_NODES {
                    return count;
                }
                stack.push(&a.node);
                stack.push(&b.node);
            }
            Expr::Not(inner) => {
                count += 1;
                if count > MAX_EXPR_NODES {
                    return count;
                }
                stack.push(&inner.node);
            }
            Expr::Apply(func, args) => {
                count += 1;
                if count > MAX_EXPR_NODES {
                    return count;
                }
                stack.push(&func.node);
                for arg in args {
                    stack.push(&arg.node);
                }
            }
            _ => {}
        }
    }
    count
}
