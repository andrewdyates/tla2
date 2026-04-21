// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Optimized evaluation path for successor enumeration when all variables
//! are already assigned.
//!
//! When all state variables have been bound (detected via the assigned_mask
//! bitmap), remaining conjuncts must be boolean guards. This fast path
//! evaluates them directly without the full conjunct dispatch, avoiding
//! the overhead of assignment extraction and symbolic handling.
//!
//! Extracted from unified.rs as part of #2360.

use smallvec::SmallVec;
use tla_core::ast::Expr;
use tla_core::Spanned;

use crate::error::EvalError;
use crate::eval::EvalCtx;
use crate::Value;

use super::expr_analysis::flatten_and_spanned;
use super::tir_leaf::eval_leaf;
use super::unified::{enumerate_conjuncts, trace_expr_tag, Cont, EnumMut, EnumParams};
use super::unified_emit::{emit_successor, GuardFailed, GuardFailedEval};

/// allAssigned fast path: evaluate remaining conjuncts as boolean guards.
pub(super) fn all_assigned_fast_path(
    ctx: &mut EvalCtx,
    c: &Cont<'_>,
    pending: Option<&Spanned<Expr>>,
    p: &EnumParams<'_>,
    m: &mut EnumMut<'_>,
    debug: bool,
    trace: bool,
) -> Result<(), EvalError> {
    if debug {
        eprintln!(
            "enumerate_conjuncts: allAssigned fast path, remaining={} pending={}",
            c.conjuncts.len() - c.next_idx,
            pending.is_some()
        );
    }
    let _env = ctx.bind_next_state_env_guard(m.rec.working.env_ref());

    let mut loop_idx = c.next_idx;
    let mut loop_pending = pending;

    let result = 'outer: loop {
        let expr = match loop_pending.take() {
            Some(p_expr) => p_expr,
            None if loop_idx < c.conjuncts.len() => {
                let e = c.conjuncts[loop_idx];
                loop_idx += 1;
                e
            }
            None => break Ok(()),
        };

        // Flatten AND expressions inline
        if let Expr::And(_, _) = &expr.node {
            let mut flat = SmallVec::new();
            flatten_and_spanned(expr, &mut flat);
            for guard_expr in &flat {
                match eval_leaf(ctx, guard_expr, p.tir_leaf) {
                    Ok(Value::Bool(true)) => {
                        if trace {
                            eprintln!(
                                "[enum-trace] fast-guard level={} tag={} result=true",
                                ctx.get_tlc_level(),
                                trace_expr_tag(&guard_expr.node)
                            );
                        }
                    }
                    Ok(Value::Bool(false)) => {
                        if trace {
                            eprintln!(
                                "[enum-trace] fast-guard level={} tag={} result=false",
                                ctx.get_tlc_level(),
                                trace_expr_tag(&guard_expr.node)
                            );
                        }
                        break 'outer Err(GuardFailed);
                    }
                    Ok(other) => {
                        if trace {
                            eprintln!(
                                "[enum-trace] fast-guard level={} tag={} result=type-error got={}",
                                ctx.get_tlc_level(),
                                trace_expr_tag(&guard_expr.node),
                                other.type_name()
                            );
                        }
                        break 'outer Err(GuardFailedEval(EvalError::TypeError {
                            expected: "BOOLEAN",
                            got: other.type_name(),
                            span: Some(guard_expr.span),
                        }));
                    }
                    Err(e) => {
                        if trace {
                            eprintln!(
                                "[enum-trace] fast-guard level={} tag={} result=error err={:?}",
                                ctx.get_tlc_level(),
                                trace_expr_tag(&guard_expr.node),
                                e
                            );
                        }
                        break 'outer Err(GuardFailedEval(e));
                    }
                }
            }
            continue;
        }

        // Evaluate as boolean guard
        match eval_leaf(ctx, expr, p.tir_leaf) {
            Ok(Value::Bool(true)) => {
                if trace {
                    eprintln!(
                        "[enum-trace] fast-guard level={} tag={} result=true",
                        ctx.get_tlc_level(),
                        trace_expr_tag(&expr.node)
                    );
                }
            }
            Ok(Value::Bool(false)) => {
                if trace {
                    eprintln!(
                        "[enum-trace] fast-guard level={} tag={} result=false",
                        ctx.get_tlc_level(),
                        trace_expr_tag(&expr.node)
                    );
                }
                break Err(GuardFailed);
            }
            Ok(other) => {
                if trace {
                    eprintln!(
                        "[enum-trace] fast-guard level={} tag={} result=type-error got={}",
                        ctx.get_tlc_level(),
                        trace_expr_tag(&expr.node),
                        other.type_name()
                    );
                }
                break Err(GuardFailedEval(EvalError::TypeError {
                    expected: "BOOLEAN",
                    got: other.type_name(),
                    span: Some(expr.span),
                }));
            }
            Err(e) => {
                if trace {
                    eprintln!(
                        "[enum-trace] fast-guard level={} tag={} result=error err={:?}",
                        ctx.get_tlc_level(),
                        trace_expr_tag(&expr.node),
                        e
                    );
                }
                break Err(GuardFailedEval(e));
            }
        }
    };

    drop(_env);

    match result {
        Ok(()) => {}
        Err(GuardFailed) => return Ok(()),
        Err(GuardFailedEval(e)) => return Err(e),
    }

    // All guards passed — produce successor (or restore scope and continue)
    if let Some(ref sr) = c.scope_restore {
        // Pop LET/apply bindings and continue with parent continuation
        ctx.pop_to_mark(&sr.binding_mark);
        ctx.local_ops_mut().clone_from(&sr.saved_local_ops);
        ctx.set_skip_prime_validation(sr.saved_skip_prime);
        let parent = sr.restored_parent_cont();
        return enumerate_conjuncts(ctx, &parent, None, p, m);
    }
    emit_successor(
        ctx,
        m.accumulated,
        p,
        m.rec.working,
        m.rec.undo,
        m.rec.results,
        m.has_complex,
    )
}
