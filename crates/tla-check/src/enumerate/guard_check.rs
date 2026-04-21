// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Guard checking for state enumeration.
//!
//! This module handles:
//! - `check_and_guards`: Recursively evaluate guard expressions within And trees
//!
//! Related modules (split from this file, Part of #3427):
//! - `action_validation`: Post-enumeration validation of successor states
//! - `unchanged_extraction`: Extract variable names from UNCHANGED expressions

use std::sync::Arc;

use tla_core::ast::Expr;
use tla_core::Spanned;

use crate::error::EvalError;
use crate::eval::{EvalCtx, OpEnv};
use crate::Value;
use tla_eval::tir::TirProgram;

use super::tir_leaf::eval_leaf;

use super::expr_analysis::{
    expr_contains_prime, expr_contains_prime_ctx, expr_is_action_level, is_guard_expression,
    is_operator_reference_guard_unsafe,
};
use super::{case_guard_error, is_action_level_error};
#[cfg(debug_assertions)]
use super::{debug_guards, debug_stage};
/// Log a debug message when a stage guard expression is evaluated.
/// Part of #1106: Debug stage guard evaluation. Extracted to reduce nesting depth.
#[cfg(debug_assertions)]
fn debug_log_stage_guard(expr: &Expr, message: &str) {
    debug_block!(debug_stage(), {
        if let Expr::Eq(lhs, rhs) = expr {
            if let (Expr::Ident(name, _) | Expr::StateVar(name, _, _), Expr::String(val)) =
                (&lhs.node, &rhs.node)
            {
                if name == "stage" {
                    eprintln!("[DEBUG STAGE] stage = {:?} {}", val, message);
                }
            }
        }
    });
}

/// Recursively check all guard expressions within an And tree.
/// Returns false if any guard evaluates to false, true otherwise.
/// This handles cases like And(And(guard, assignment), assignment) where
/// the guard is nested within the And tree.
pub(super) fn check_and_guards(
    ctx: &EvalCtx,
    expr: &Spanned<Expr>,
    debug: bool,
    tir: Option<&TirProgram<'_>>,
) -> Result<bool, EvalError> {
    // Use stack_safe to grow stack on demand for deeply nested And trees
    crate::eval::stack_safe(|| check_and_guards_inner(ctx, expr, debug, tir))
}

/// Evaluate a guard expression and interpret the result as a boolean guard check.
///
/// Returns `Ok(false)` if the guard is definitely false, `Ok(true)` if true or
/// if an action-level error was suppressed. Propagates `ExitRequested` and
/// non-action-level errors.
///
/// Part of #3260: extracted from 3 duplicated match blocks in `check_and_guards_inner`.
#[inline]
fn eval_guard_leaf(
    ctx: &EvalCtx,
    expr: &Spanned<Expr>,
    debug: bool,
    tir: Option<&TirProgram<'_>>,
) -> Result<bool, EvalError> {
    // `debug` is used by debug_eprintln! which compiles to nothing in release builds
    let _ = &debug;
    match eval_leaf(ctx, expr, tir) {
        Ok(Value::Bool(b)) => {
            debug_eprintln!(
                debug && !b,
                "check_and_guards: guard={:?} evaluated to false",
                expr.node
            );
            Ok(b)
        }
        Ok(other) => Err(EvalError::TypeError {
            expected: "BOOLEAN",
            got: other.type_name(),
            span: Some(expr.span),
        }),
        Err(e) if matches!(e, EvalError::ExitRequested { .. }) => Err(e),
        Err(e) if is_action_level_error(&e) => {
            crate::guard_error_stats::record_suppressed_action_level_error();
            Ok(true)
        }
        Err(e) => Err(e),
    }
}

fn check_and_guards_inner(
    ctx: &EvalCtx,
    expr: &Spanned<Expr>,
    debug: bool,
    tir: Option<&TirProgram<'_>>,
) -> Result<bool, EvalError> {
    // Part of #575: Add entry debug to trace what expressions are being checked
    debug_eprintln!(
        debug_guards(),
        "[DEBUG GUARDS] check_and_guards_inner: expr type={:?}",
        std::mem::discriminant(&expr.node)
    );
    // Part of #1106: Debug stage guard checking
    #[cfg(debug_assertions)]
    debug_log_stage_guard(&expr.node, "found guard");
    match &expr.node {
        // Label: transparent wrapper — unwrap and recurse into body.
        Expr::Label(label) => return check_and_guards(ctx, &label.body, debug, tir),

        Expr::And(a, b) => {
            // Part of #1106: Debug And tree traversal
            debug_eprintln!(
                debug_stage(),
                "[DEBUG STAGE] And: checking left={:?}, right={:?}",
                std::mem::discriminant(&a.node),
                std::mem::discriminant(&b.node)
            );
            // Check both sides of the And
            if !check_and_guards(ctx, a, debug, tir)? {
                debug_eprintln!(
                    debug_stage(),
                    "[DEBUG STAGE] And: left side returned false, short-circuiting"
                );
                return Ok(false);
            }
            debug_eprintln!(
                debug_stage(),
                "[DEBUG STAGE] And: left side returned true, checking right side"
            );
            check_and_guards(ctx, b, debug, tir)
        }
        // LET expressions: bind definitions and recurse into body
        // This is essential for patterns like:
        //   LET newThis == ... IN /\ IsSafe(newThis) /\ x' = ...
        // The IsSafe guards need to be checked with newThis bound.
        Expr::Let(defs, body) => {
            // Guard checking must respect TLA+'s substitution semantics for LET:
            // bindings are only evaluated when referenced. Eager evaluation of all
            // zero-arg LET defs can incorrectly disable actions when some defs are
            // unused on the taken path (e.g., btree's WhichToSplit: ParentOf(root)).
            //
            // Fix #804: Zero-arg LET defs must be bound on local_stack (as lazy
            // thunks) so they properly shadow same-named outer bindings (e.g.,
            // EXISTS-bound variables). Previously only adding to local_ops caused
            // local_stack lookups to find the outer binding first, since local_stack
            // has higher priority than local_ops in eval's Ident resolution.
            // This matches eval's LET handler (core.rs:5627-5645).
            let mut new_ctx = ctx.clone();
            let mut local_ops: OpEnv = match new_ctx.local_ops() {
                Some(ops) => (**ops).clone(),
                None => OpEnv::default(),
            };
            for def in defs {
                if def.params.is_empty() && !matches!(&def.body.node, Expr::InstanceExpr(_, _)) {
                    // Zero-arg non-instance def: bind as lazy thunk on local_stack.
                    // This ensures the LET def shadows any outer binding of the same name.
                    // Part of #2895: Use create_closure for O(1) chain capture.
                    let thunk = Value::Closure(std::sync::Arc::new(new_ctx.create_closure(
                        vec![], // No params = lazy thunk marker
                        def.body.clone(),
                        new_ctx.local_ops().clone(),
                    )));
                    // Part of #1383: new_ctx is owned and reassigned — use into_bind_local
                    new_ctx = new_ctx.into_bind_local(def.name.node.clone(), thunk);
                }
                // Always add to local_ops too (for parameterized defs, and as fallback)
                local_ops.insert(def.name.node.clone(), Arc::new(def.clone()));
            }
            *new_ctx.local_ops_mut() = Some(Arc::new(local_ops));
            check_and_guards(&new_ctx, body, debug, tir)
        }
        // Or expressions: do NOT evaluate guards inside Or branches.
        // Each Or branch has its own guards that should be checked AFTER distribution.
        // Walking into Or branches and checking guards like `cnt # 0` would incorrectly
        // reject the entire action when only some branches have that guard.
        Expr::Or(_, _) => Ok(true),
        // Part of #342: EXISTS needs careful handling:
        // - EXISTS WITH primes → nondeterministic choice, must be enumerated (return true)
        // - EXISTS WITHOUT primes → pure guard, must be evaluated
        // Example: `\E n \in Node : ReadLog(n, idx) /= NoNode` is a pure guard
        // Example: `\E x \in S : x' = f(x)` is nondeterministic choice
        Expr::Exists(_bindings, body) => {
            // Check if the EXISTS body contains primes (action expressions)
            let body_has_primes = expr_contains_prime_ctx(ctx, &body.node);
            if body_has_primes {
                // Nondeterministic choice - must be enumerated, not evaluated as guard
                // Part of #86: PaxosCommit under-exploration fix.
                if debug {
                    eprintln!(
                        "check_and_guards: EXISTS with primes, treating as nondeterministic choice"
                    );
                }
                Ok(true)
            } else {
                // Pure guard - evaluate and return the boolean result
                if debug {
                    eprintln!("check_and_guards: EXISTS without primes, evaluating as guard");
                }
                match eval_leaf(ctx, expr, tir) {
                    Ok(Value::Bool(result)) => {
                        if debug {
                            eprintln!("check_and_guards: EXISTS guard evaluated to {}", result);
                        }
                        Ok(result)
                    }
                    Ok(other) => {
                        // TLC treats quantified predicates as boolean-only.
                        // Non-boolean results are fatal type errors.
                        if debug {
                            eprintln!(
                                "check_and_guards: EXISTS guard returned non-boolean: {}",
                                other.type_name()
                            );
                        }
                        Err(EvalError::TypeError {
                            expected: "BOOLEAN",
                            got: other.type_name(),
                            span: Some(expr.span),
                        })
                    }
                    Err(e) => {
                        if matches!(e, EvalError::ExitRequested { .. }) {
                            return Err(e);
                        }
                        if is_action_level_error(&e) {
                            crate::guard_error_stats::record_suppressed_action_level_error();
                            return Ok(true);
                        }
                        // TLC propagates non-action-level guard evaluation errors.
                        if debug {
                            eprintln!("check_and_guards: EXISTS guard evaluation error: {:?}", e);
                        }
                        Err(e)
                    }
                }
            }
        }
        // Part of #342: CASE expressions need guard checking in arm bodies.
        // When CASE is used in actions (e.g., `LET pair = ... IN CASE pair[1] = "write" -> Write(actor)`),
        // the arm body (Write(actor)) may contain guards that must be validated.
        Expr::Case(arms, other) => {
            if debug {
                eprintln!("check_and_guards: CASE with {} arms", arms.len());
            }
            // Evaluate each guard to find the matching arm
            for (i, arm) in arms.iter().enumerate() {
                match eval_leaf(ctx, &arm.guard, tir) {
                    Ok(Value::Bool(true)) => {
                        // Found matching arm - recurse into its body to check guards there
                        if debug {
                            eprintln!(
                                "check_and_guards: CASE arm {} matched, checking body guards",
                                i
                            );
                        }
                        return check_and_guards(ctx, &arm.body, debug, tir);
                    }
                    Ok(Value::Bool(false)) => {
                        if debug {
                            eprintln!("check_and_guards: CASE arm {} guard=false, continuing", i);
                        }
                    }
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
                    // Part of #1425: Propagate eval errors from CASE guards.
                    // TLC: EvalException propagates fatally from guard evaluation.
                    Err(e) => return Err(case_guard_error(e, arm.guard.span)),
                }
            }
            // No arm matched - check OTHER if present
            if let Some(other_body) = other {
                if debug {
                    eprintln!("check_and_guards: CASE no arm matched, checking OTHER");
                }
                return check_and_guards(ctx, other_body, debug, tir);
            }
            // No arm matched and no OTHER - action is disabled (no valid branch)
            if debug {
                eprintln!("check_and_guards: CASE no arm matched, no OTHER, action disabled");
            }
            Ok(false)
        }
        // Part of #342: Zero-param action operator references (Expr::Ident) need guard checking
        // in the operator body. When the CASE arm body is DoWrite (not DoWrite()), we need to
        // recurse into DoWrite's body to check guards like `active_read = FALSE`.
        Expr::Ident(name, _) => {
            let resolved = ctx.resolve_op_name(name.as_str());
            if let Some(def) = ctx.get_op(resolved) {
                // Check if this is an action operator (contains primes)
                let is_action_op = def.contains_prime || expr_contains_prime(&def.body.node);
                if is_action_op && def.params.is_empty() {
                    if debug {
                        eprintln!(
                            "check_and_guards: Ident '{}' is zero-param action, checking body guards",
                            name
                        );
                    }
                    // Recurse into operator body to check guards
                    return check_and_guards(ctx, &def.body, debug, tir);
                }
            }
            // Not an action operator or has params - use default handling
            if is_guard_expression(&expr.node)
                && !is_operator_reference_guard_unsafe(ctx, &expr.node)
            {
                eval_guard_leaf(ctx, expr, debug, tir)
            } else {
                Ok(true)
            }
        }
        // Part of #342: Apply expressions that reference action operators need guard checking
        // in the operator body. When the CASE arm body is Write(actor), we need to bind the
        // parameters and recurse into Write's body to check guards like `readers = {}`.
        Expr::Apply(op_expr, args) => {
            // Part of #357 (corrected): Check if ANY argument is action-level FIRST.
            // This applies to ALL operators, not just action operators.
            // Example: MCReply(p, d, oldMemInt, newMemInt) == newMemInt = <<p, d>>
            // MCReply's body has NO primes, but it's called as Reply(p, buf[p], memInt, memInt')
            // where memInt' is action-level. We cannot evaluate memInt' in current state.
            let args_are_action = args.iter().any(|a| expr_is_action_level(ctx, &a.node));
            if args_are_action {
                if debug {
                    eprintln!(
                        "check_and_guards: Apply with action-level args, skipping evaluation"
                    );
                }
                return Ok(true); // Can't evaluate args, let assignment extraction handle it
            }

            // Only process if operator contains primes (is an action operator)
            let is_action_op = match &op_expr.node {
                Expr::Ident(op_name, _) => {
                    let resolved = ctx.resolve_op_name(op_name.as_str());
                    ctx.get_op(resolved).is_some_and(|def| {
                        def.contains_prime || expr_contains_prime(&def.body.node)
                    })
                }
                _ => false,
            };

            if is_action_op {
                // This is an action operator - we need to check guards in its body
                if let Expr::Ident(op_name, _) = &op_expr.node {
                    let resolved = ctx.resolve_op_name(op_name.as_str());
                    if let Some(def) = ctx.get_op(resolved) {
                        if debug {
                            eprintln!("check_and_guards: Apply to action operator '{}' (resolved='{}'), checking body guards, body span={:?}, params={:?}",
                                op_name, resolved, def.body.span, def.params.iter().map(|p| &p.name.node).collect::<Vec<_>>());
                        }
                        // Bind parameters to arguments.
                        // TLC propagates eval errors — it does not treat them
                        // as "action disabled." Disabled-action errors (NotInDomain,
                        // etc.) are handled by the caller.
                        let mut new_ctx = ctx.clone();
                        for (param, arg) in def.params.iter().zip(args.iter()) {
                            let arg_val = eval_leaf(ctx, arg, tir)?;
                            new_ctx.push_binding(Arc::from(param.name.node.as_str()), arg_val);
                        }
                        // Recurse into operator body with parameters bound
                        return check_and_guards(&new_ctx, &def.body, debug, tir);
                    }
                }
            }
            // Not an action operator or couldn't resolve - continue to default handling
            if is_guard_expression(&expr.node)
                && !is_operator_reference_guard_unsafe(ctx, &expr.node)
            {
                eval_guard_leaf(ctx, expr, debug, tir)
            } else {
                Ok(true)
            }
        }
        _ => {
            // For non-And, non-Let, non-Or expressions, check if it's a guard and evaluate it
            let is_guard = is_guard_expression(&expr.node);
            let is_unsafe = is_operator_reference_guard_unsafe(ctx, &expr.node);
            if debug {
                eprintln!(
                    "check_and_guards: _ case expr type={:?}, is_guard={}, is_unsafe={}",
                    std::mem::discriminant(&expr.node),
                    is_guard,
                    is_unsafe
                );
            }
            // Part of #1106: Debug stage guard evaluation
            #[cfg(debug_assertions)]
            debug_log_stage_guard(
                &expr.node,
                &format!("evaluating, is_guard={}, is_unsafe={}", is_guard, is_unsafe),
            );
            // Part of #575: Debug guard expressions specifically
            if is_guard && !is_unsafe {
                let result = eval_guard_leaf(ctx, expr, debug, tir);
                #[cfg(debug_assertions)]
                match &result {
                    Ok(false) => debug_log_stage_guard(&expr.node, "evaluated to FALSE"),
                    Ok(true) => debug_log_stage_guard(&expr.node, "evaluated to TRUE"),
                    _ => {}
                }
                result
            } else {
                // Not a guard expression (contains primes), skip
                Ok(true)
            }
        }
    }
}
