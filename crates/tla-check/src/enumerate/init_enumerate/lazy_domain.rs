// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Lazy-domain streaming helpers for init constraint enumeration.

use std::sync::Arc;

use tla_core::ast::{BoundPattern, BoundVar, Expr};
use tla_core::{Span, Spanned};

use crate::error::EvalError;
use crate::eval::{eval_entry, EvalCtx};
use crate::Value;

use super::bulk_sink::{
    emit_values_to_bulk, eval_filter_expr, plan_filter_constraints, BulkEnumSink,
};
use super::{BulkConstraintEnumerationError, Constraint, DeferredConstraint};

fn build_setpred_base_ctx(ctx: &EvalCtx, spv: &crate::eval::SetPredValue) -> EvalCtx {
    spv.env().iter().fold(ctx.clone(), |acc, (name, value)| {
        acc.into_bind_local(name.clone(), value.clone())
    })
}

fn push_bound_var_local(
    ctx: &mut EvalCtx,
    bound: &BoundVar,
    elem: &Value,
    span: Option<Span>,
) -> Result<(), EvalError> {
    match &bound.pattern {
        Some(BoundPattern::Tuple(vars)) => {
            let tuple = elem
                .to_tuple_like_elements()
                .ok_or_else(|| EvalError::type_error("Tuple", elem, span))?;
            if tuple.len() != vars.len() {
                return Err(EvalError::Internal {
                    message: format!(
                        "Tuple pattern has {} variables but element has {} components",
                        vars.len(),
                        tuple.len()
                    ),
                    span,
                });
            }
            for (var, value) in vars.iter().zip(tuple.iter()) {
                ctx.push_binding(Arc::from(var.node.as_str()), value.clone());
            }
            Ok(())
        }
        Some(BoundPattern::Var(var)) => {
            ctx.push_binding(Arc::from(var.node.as_str()), elem.clone());
            Ok(())
        }
        None => {
            ctx.push_binding(Arc::from(bound.name.node.as_str()), elem.clone());
            Ok(())
        }
    }
}

fn is_streamable_record_filter_domain(domain: &Value) -> bool {
    match domain {
        Value::SetPred(spv) => is_streamable_record_filter_domain(spv.source()),
        Value::RecordSet(_) => true,
        _ => false,
    }
}

fn stream_domain_values_in_order<E>(
    ctx: &EvalCtx,
    domain: &Value,
    consume: &mut dyn FnMut(Value) -> Result<(), BulkConstraintEnumerationError<E>>,
) -> Result<Option<()>, BulkConstraintEnumerationError<E>> {
    match domain {
        Value::SetPred(spv) => {
            let mut pred_ctx = build_setpred_base_ctx(ctx, spv);
            let Some(()) = stream_domain_values_in_order(ctx, spv.source(), &mut |elem| {
                let mark = pred_ctx.mark_stack();
                let outcome = (|| {
                    push_bound_var_local(&mut pred_ctx, spv.bound(), &elem, Some(spv.pred().span))?;
                    match eval_entry(&pred_ctx, spv.pred())? {
                        Value::Bool(true) => consume(elem),
                        Value::Bool(false) => Ok(()),
                        other => {
                            Err(
                                EvalError::type_error("BOOLEAN", &other, Some(spv.pred().span))
                                    .into(),
                            )
                        }
                    }
                })();
                pred_ctx.pop_to_mark(&mark);
                outcome
            })?
            else {
                return Ok(None);
            };
            Ok(Some(()))
        }
        other => {
            let Some(iter) = other.iter_set() else {
                return Ok(None);
            };
            for elem in iter {
                consume(elem)?;
            }
            Ok(Some(()))
        }
    }
}

pub(super) fn try_enumerate_single_lazy_domain_to_bulk<'a, F, E>(
    ctx: &mut EvalCtx,
    vars: &'a [Arc<str>],
    immediate: &[&Constraint],
    deferred: &[DeferredConstraint],
    filters: &[&Spanned<Expr>],
    sink: &mut BulkEnumSink<'a, F, E>,
) -> Result<bool, BulkConstraintEnumerationError<E>>
where
    F: FnMut(&[Value], &mut EvalCtx) -> Result<bool, E>,
{
    if vars.len() != 1 || !deferred.is_empty() {
        return Ok(false);
    }

    let [constraint] = immediate else {
        return Ok(false);
    };
    let Constraint::In(name, super::super::InitDomain::Enumerable(domain)) = constraint else {
        return Ok(false);
    };
    let var = &vars[0];
    if name != var.as_ref() || !is_streamable_record_filter_domain(domain) {
        return Ok(false);
    }

    let ordered_vars = vec![Arc::clone(var)];
    let filter_constraints = plan_filter_constraints(ctx, vars, &ordered_vars, filters);
    if filter_constraints
        .iter()
        .any(|filter| filter.requires_deferred)
    {
        return Ok(false);
    }

    sink.var_indices = rustc_hash::FxHashMap::from_iter([(var.as_ref(), 0usize)]);

    let mut values = vec![Value::Bool(false); vars.len()];
    let stream_ctx = (*ctx).clone();
    let Some(()) = stream_domain_values_in_order(&stream_ctx, domain, &mut |elem| {
        values[0] = elem.clone();
        ctx.bind_mut(Arc::clone(var), elem);

        let outcome: Result<(), BulkConstraintEnumerationError<E>> = (|| {
            for filter_constraint in &filter_constraints {
                if filter_constraint.trigger_idx != 0 {
                    continue;
                }
                if !eval_filter_expr(ctx, &filter_constraint.expr)? {
                    return Ok(());
                }
            }
            emit_values_to_bulk(ctx, &values, sink)
        })();

        ctx.unbind(var.as_ref());
        outcome
    })?
    else {
        return Ok(false);
    };

    Ok(true)
}
