// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! RECURSIVE fold detection and iterative evaluation (Part of #2955).
//!
//! Detects the standard fold idiom: `IF S={} THEN base ELSE LET x==CHOOSE x \in S : TRUE
//! IN g(x) ⊕ F(S\{x})` and evaluates iteratively, eliminating per-element overhead of
//! IF/CHOOSE/SetMinus/recursive dispatch (~39% call reduction for GameOfLife).

use super::super::{
    apply_builtin_binary_op, apply_named_binary_op, eval, EvalCtx, EvalError, EvalResult,
};
use super::closures::create_closure_from_arg;
use crate::cache::small_caches::SMALL_CACHES;
use crate::value::{intern_string, Value};
use std::sync::Arc;
use tla_core::ast::{Expr, OperatorDef};
use tla_core::{ExprVisitor, Span, Spanned};

// Part of #3962: FOLD_RESULT_CACHE consolidated into SMALL_CACHES.fold_result_cache.
// Previously a standalone thread_local! in this file; now shares a single TLS
// access with 12 other small caches. Clearing is now done inline in
// cache/lifecycle.rs clear_run_reset_impl() within the SMALL_CACHES.with block.

/// Binary operation type detected in fold accumulation pattern.
#[derive(Debug, Clone)]
enum FoldBinOp {
    Add,
    Sub,
    Mul,
    Union,
    /// Named binary operator (e.g., `DyadicRationals.Add(x, y)`).
    /// Stores the operator name for resolution at fold time.
    /// Part of #3041.
    Named(String),
}

/// Components of a detected fold pattern, referencing the operator's AST.
struct FoldPattern<'a> {
    /// Index of the set parameter being folded over.
    set_param_idx: usize,
    /// The base case expression (IF S = {} THEN <base>).
    base_expr: &'a Spanned<Expr>,
    /// Name of the element variable (CHOOSE x \in S : TRUE).
    elem_var_name: &'a str,
    /// The per-element expression (the non-recursive side of the binary op).
    elem_expr: &'a Spanned<Expr>,
    /// The accumulation binary operation.
    binop: FoldBinOp,
    /// True if the recursive call is on the LEFT side of the binary op.
    /// Determines fold associativity: left=true → acc ⊕ elem, left=false → elem ⊕ acc.
    recursive_on_left: bool,
}

/// Try to evaluate a RECURSIVE operator as an iterative fold.
///
/// Returns `Ok(Some(value))` if fold optimization applied successfully.
/// Returns `Ok(None)` to fall through to standard recursive evaluation.
/// Returns `Err` only on actual evaluation errors during the fold.
pub(crate) fn try_eval_recursive_fold(
    ctx: &EvalCtx,
    def: &Arc<OperatorDef>,
    args: &[Spanned<Expr>],
    span: Option<Span>,
) -> EvalResult<Option<Value>> {
    // Only single-recursion folds (double-recursion needs memoization, not folding)
    if def.self_call_count != 1 || def.params.len() < 2 {
        return Ok(None);
    }

    let pattern = match detect_fold_pattern(def) {
        Some(p) => p,
        None => return Ok(None),
    };

    // Fold result memoization: for pure folds (all params arity 0), cache
    // (operator_ptr, evaluated_args) → result. Avoids recomputing the same
    // fold repeatedly in specs like CarTalkPuzzle M3 where Sum(B, S) is
    // called with the same B and cycling through the same 32 subsets.
    let all_arity_zero = def.params.iter().all(|p| p.arity == 0);
    let def_ptr = Arc::as_ptr(def) as usize;

    let cache_key = if all_arity_zero {
        let mut evaluated_args = Vec::with_capacity(args.len());
        for arg in args.iter() {
            evaluated_args.push(eval(ctx, arg)?);
        }
        // Check cache
        let cached = SMALL_CACHES.with(|sc| {
            sc.borrow().fold_result_cache.get(&(def_ptr, evaluated_args.clone())).cloned()
        });
        if let Some(result) = cached {
            return Ok(Some(result));
        }
        Some(evaluated_args)
    } else {
        None
    };

    // Force-evaluate the set argument to get a concrete sorted set.
    let set_val = if let Some(ref key) = cache_key {
        key[pattern.set_param_idx].clone()
    } else {
        eval(ctx, &args[pattern.set_param_idx])?
    };
    let sorted_set = match set_val.to_sorted_set() {
        Some(ss) => ss,
        None => return Ok(None), // Not materializable, fall back to recursive eval
    };

    // Bind pass-through parameters (arity > 0 → closures, arity 0 → eager eval).
    let mut fold_ctx = ctx.clone();
    for (i, (param, arg)) in def.params.iter().zip(args.iter()).enumerate() {
        if i == pattern.set_param_idx {
            continue;
        }
        let val = if param.arity > 0 {
            create_closure_from_arg(ctx, arg, &param.name.node, param.arity, span)?
        } else if let Some(ref key) = cache_key {
            key[i].clone()
        } else {
            eval(ctx, arg)?
        };
        fold_ctx = fold_ctx.into_bind_local(intern_string(&param.name.node), val);
    }

    // Evaluate base case
    let mut acc = eval(&fold_ctx, pattern.base_expr)?;

    if sorted_set.is_empty() {
        if let Some(key) = cache_key {
            SMALL_CACHES.with(|sc| {
                let mut sc = sc.borrow_mut();
                if sc.fold_result_cache.len() > 100_000 {
                    sc.fold_result_cache.clear();
                }
                sc.fold_result_cache.insert((def_ptr, key), acc.clone());
            });
        }
        return Ok(Some(acc));
    }

    // Reverse iteration for right-fold: g(x1) ⊕ (g(x2) ⊕ (g(x3) ⊕ base))
    let elements: Vec<&Value> = sorted_set.iter().collect();

    // Fast path: when elem_expr is `f[x]` (function param applied to element var),
    // pre-resolve the function value once and do direct lookups per element.
    // Eliminates per-element: EvalCtx clone, eval dispatch, context chain walks.
    if let Some(func_val) =
        try_resolve_func_apply_param(&fold_ctx, pattern.elem_expr, pattern.elem_var_name)
    {
        for elem in elements.iter().rev() {
            let elem_val = apply_resolved_func(&func_val, elem, span)?;
            acc = if pattern.recursive_on_left {
                apply_fold_binop(&pattern.binop, &fold_ctx, acc, elem_val, span)?
            } else {
                apply_fold_binop(&pattern.binop, &fold_ctx, elem_val, acc, span)?
            };
        }
    } else {
        // General path: full eval per element (handles arbitrary elem_expr)
        let elem_name_arc: Arc<str> = intern_string(pattern.elem_var_name);
        for elem in elements.iter().rev() {
            let elem_ctx = fold_ctx.bind(Arc::clone(&elem_name_arc), (*elem).clone());
            let elem_val = eval(&elem_ctx, pattern.elem_expr)?;
            acc = if pattern.recursive_on_left {
                apply_fold_binop(&pattern.binop, &fold_ctx, acc, elem_val, span)?
            } else {
                apply_fold_binop(&pattern.binop, &fold_ctx, elem_val, acc, span)?
            };
        }
    }

    // Store result in fold cache
    if let Some(key) = cache_key {
        SMALL_CACHES.with(|sc| {
            let mut sc = sc.borrow_mut();
            if sc.fold_result_cache.len() > 100_000 {
                sc.fold_result_cache.clear();
            }
            sc.fold_result_cache.insert((def_ptr, key), acc.clone());
        });
    }

    Ok(Some(acc))
}

/// Detect a fold pattern in a RECURSIVE operator's body AST.
///
/// Returns `Some(FoldPattern)` if the body matches the standard fold idiom,
/// `None` otherwise (triggering fallback to standard recursive eval).
fn detect_fold_pattern(def: &OperatorDef) -> Option<FoldPattern<'_>> {
    if !def.is_recursive || def.params.len() < 2 {
        return None;
    }
    let (cond, base_expr, else_branch) = match &def.body.node {
        Expr::If(c, t, e) => (c.as_ref(), t.as_ref(), e.as_ref()),
        _ => return None,
    };
    let set_param_name = match_emptiness_check(cond)?;
    let set_param_idx = def
        .params
        .iter()
        .position(|p| p.name.node == set_param_name && p.arity == 0)?;

    // ELSE branch must be: LET <elem> == CHOOSE <elem> \in <set_param> : TRUE IN <body>
    let (elem_var_name, let_body) = match_choose_elem_binding(else_branch, set_param_name)?;
    let op_name = &def.name.node;
    let (binop, left, right) = match_binary_op(let_body)?;

    let left_is_self_call = is_recursive_self_call(
        left,
        op_name,
        def,
        set_param_idx,
        set_param_name,
        elem_var_name,
    );
    let right_is_self_call = is_recursive_self_call(
        right,
        op_name,
        def,
        set_param_idx,
        set_param_name,
        elem_var_name,
    );

    // Exactly one side must be the recursive self-call
    if left_is_self_call == right_is_self_call {
        return None;
    }

    let (elem_expr, recursive_on_left) = if left_is_self_call {
        (right, true)
    } else {
        (left, false)
    };

    // CORRECTNESS SAFETY CHECK: elem_expr must NOT reference the set parameter.
    // If it does, the fold would evaluate it with the wrong set (full set instead
    // of the progressively shrinking set), producing incorrect results.
    if expr_references_name(&elem_expr.node, set_param_name) {
        return None;
    }

    // Also check base_expr doesn't reference set param (it should be a constant
    // like 0, {}, TRUE — if it references S, we'd need to bind S = {} which
    // adds complexity for a rare edge case).
    if expr_references_name(&base_expr.node, set_param_name) {
        return None;
    }

    Some(FoldPattern {
        set_param_idx,
        base_expr,
        elem_var_name,
        elem_expr,
        binop,
        recursive_on_left,
    })
}

/// Match an expression as a supported binary operation for fold accumulation.
///
/// Handles both built-in infix operators (Add, Sub, Mul, Union) and named
/// binary function calls like `Add(x, y)` which appear as
/// `Expr::Apply(Ident("Add"), [left, right])`. Part of #3041.
fn match_binary_op(expr: &Spanned<Expr>) -> Option<(FoldBinOp, &Spanned<Expr>, &Spanned<Expr>)> {
    match &expr.node {
        Expr::Add(l, r) => Some((FoldBinOp::Add, l.as_ref(), r.as_ref())),
        Expr::Sub(l, r) => Some((FoldBinOp::Sub, l.as_ref(), r.as_ref())),
        Expr::Mul(l, r) => Some((FoldBinOp::Mul, l.as_ref(), r.as_ref())),
        Expr::Union(l, r) => Some((FoldBinOp::Union, l.as_ref(), r.as_ref())),
        Expr::Apply(op, args) if args.len() == 2 => {
            if let Expr::Ident(name, _) = &op.node {
                Some((FoldBinOp::Named(name.clone()), &args[0], &args[1]))
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Match the set emptiness check: `<name> = {}` or `{} = <name>`.
fn match_emptiness_check(cond: &Spanned<Expr>) -> Option<&str> {
    match &cond.node {
        Expr::Eq(left, right) => match (&left.node, &right.node) {
            (Expr::Ident(name, _), Expr::SetEnum(elems)) if elems.is_empty() => Some(name),
            (Expr::SetEnum(elems), Expr::Ident(name, _)) if elems.is_empty() => Some(name),
            _ => None,
        },
        _ => None,
    }
}

/// Match the LET/CHOOSE element binding pattern in the ELSE branch.
///
/// Expects: `LET x == CHOOSE x \in S : TRUE IN <body>` and returns
/// the element variable name and the LET body expression.
fn match_choose_elem_binding<'a>(
    else_branch: &'a Spanned<Expr>,
    set_param_name: &str,
) -> Option<(&'a str, &'a Spanned<Expr>)> {
    let (let_defs, let_body) = match &else_branch.node {
        Expr::Let(defs, body) => (defs.as_slice(), body.as_ref()),
        _ => return None,
    };
    if let_defs.len() != 1 || !let_defs[0].params.is_empty() {
        return None;
    }
    let let_def = &let_defs[0];
    match &let_def.body.node {
        Expr::Choose(bound, pred) => {
            if !matches!(&pred.node, Expr::Bool(true)) {
                return None;
            }
            let domain = bound.domain.as_ref()?;
            if !matches!(&domain.node, Expr::Ident(n, _) if n == set_param_name) {
                return None;
            }
            if bound.pattern.is_some() || let_def.name.node != bound.name.node {
                return None;
            }
            Some((bound.name.node.as_str(), let_body))
        }
        _ => None,
    }
}

/// Check if an expression is a recursive self-call with proper pass-through args.
///
/// Verifies:
/// 1. Call target matches the RECURSIVE operator name
/// 2. Arity matches
/// 3. Set argument is `<set_param> \ {<elem_var>}`
/// 4. All other arguments are passed through unchanged as `Ident(param_name)`
fn is_recursive_self_call(
    expr: &Spanned<Expr>,
    op_name: &str,
    def: &OperatorDef,
    set_param_idx: usize,
    set_param_name: &str,
    elem_var_name: &str,
) -> bool {
    let (call_op, call_args) = match &expr.node {
        Expr::Apply(op, args) => (op.as_ref(), args.as_slice()),
        _ => return false,
    };

    // Operator must be the same RECURSIVE operator
    if !matches!(&call_op.node, Expr::Ident(n, _) if n == op_name) {
        return false;
    }

    // Arity must match
    if call_args.len() != def.params.len() {
        return false;
    }

    // Set argument must be: <set_param> \ {<elem_var>}
    if !matches!(&call_args[set_param_idx].node,
        Expr::SetMinus(s, t) if {
            matches!(&s.node, Expr::Ident(n, _) if n == set_param_name)
            && matches!(&t.node, Expr::SetEnum(elems) if
                elems.len() == 1
                && matches!(&elems[0].node, Expr::Ident(n, _) if n == elem_var_name)
            )
        }
    ) {
        return false;
    }

    // All non-set params must be passed through unchanged
    for (i, (param, arg)) in def.params.iter().zip(call_args.iter()).enumerate() {
        if i == set_param_idx {
            continue;
        }
        if !matches!(&arg.node, Expr::Ident(n, _) if n == &param.name.node) {
            return false;
        }
    }

    true
}

/// Check if an expression contains any reference to an identifier with the given name.
/// Uses ExprVisitor for complete AST traversal.
fn expr_references_name(expr: &Expr, name: &str) -> bool {
    struct NameFinder<'a> {
        name: &'a str,
        found: bool,
    }
    impl ExprVisitor for NameFinder<'_> {
        type Output = ();
        fn visit_node(&mut self, expr: &Expr) -> Option<()> {
            if self.found {
                return Some(()); // already found, skip remaining children
            }
            match expr {
                Expr::Ident(n, _) | Expr::StateVar(n, _, _) if n == self.name => {
                    self.found = true;
                    Some(())
                }
                _ => None,
            }
        }
    }
    let mut finder = NameFinder { name, found: false };
    finder.walk_expr(expr);
    finder.found
}

/// Try to detect `FuncApply(Ident(param), Ident(elem_var))` and pre-resolve the function.
///
/// Returns `Some(func_value)` if elem_expr is `param[elem_var]` and `param` evaluates
/// to a concrete function value (Func or IntFunc). Returns None for any other pattern,
/// falling through to the general eval path.
fn try_resolve_func_apply_param(
    ctx: &EvalCtx,
    elem_expr: &Spanned<Expr>,
    elem_var_name: &str,
) -> Option<Value> {
    let (func_expr, arg_expr) = match &elem_expr.node {
        Expr::FuncApply(f, a) => (f.as_ref(), a.as_ref()),
        _ => return None,
    };
    // arg must be the element variable
    if !matches!(&arg_expr.node, Expr::Ident(n, _) if n == elem_var_name) {
        return None;
    }
    // func must be a simple identifier (a parameter name)
    if !matches!(&func_expr.node, Expr::Ident(_, _)) {
        return None;
    }
    // Evaluate the function parameter in the fold context
    let func_val = eval(ctx, func_expr).ok()?;
    // Only use fast path for concrete function types (Func/IntFunc/Seq), not LazyFunc
    match &func_val {
        Value::Func(_) | Value::IntFunc(_) | Value::Seq(_) => Some(func_val),
        _ => None,
    }
}

/// Apply a pre-resolved function value to an argument, bypassing eval dispatch.
#[inline]
fn apply_resolved_func(func_val: &Value, arg: &Value, span: Option<Span>) -> EvalResult<Value> {
    match func_val {
        Value::Func(f) => f.apply(arg).cloned().ok_or_else(|| EvalError::NotInDomain {
            arg: format!("{arg}"),
            func_display: Some(format!("{func_val}")),
            span,
        }),
        Value::IntFunc(f) => f.apply(arg).cloned().ok_or_else(|| EvalError::NotInDomain {
            arg: format!("{arg}"),
            func_display: Some(format!("{func_val}")),
            span,
        }),
        Value::Seq(s) => {
            // Seq is 1-indexed: convert to 0-based index for direct lookup
            let idx = arg.as_i64().ok_or_else(|| EvalError::NotInDomain {
                arg: format!("{arg}"),
                func_display: Some(format!("{func_val}")),
                span,
            })?;
            if idx < 1 || idx as usize > s.len() {
                return Err(EvalError::NotInDomain {
                    arg: format!("{arg}"),
                    func_display: Some(format!("{func_val}")),
                    span,
                });
            }
            Ok(s[(idx - 1) as usize].clone())
        }
        _ => unreachable!("try_resolve_func_apply_param only returns Func/IntFunc/Seq"),
    }
}

/// Apply a binary operation on two evaluated values for fold accumulation.
///
/// For `Named` operators (Part of #3041), reuse the shared named-op helper so
/// recursive folds get the same stdlib fast paths as `FoldFunction`.
fn apply_fold_binop(
    op: &FoldBinOp,
    ctx: &EvalCtx,
    left: Value,
    right: Value,
    span: Option<Span>,
) -> EvalResult<Value> {
    match op {
        FoldBinOp::Add => apply_builtin_binary_op("+", left, right, span),
        FoldBinOp::Sub => apply_builtin_binary_op("-", left, right, span),
        FoldBinOp::Mul => apply_builtin_binary_op("*", left, right, span),
        FoldBinOp::Union => apply_builtin_binary_op("\\cup", left, right, span),
        FoldBinOp::Named(name) => apply_named_binary_op(ctx, name, left, right, span),
    }
}

#[cfg(test)]
#[path = "recursive_fold_tests.rs"]
mod tests;
