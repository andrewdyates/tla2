// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bulk-output helpers for init constraint enumeration.

use rustc_hash::FxHashSet;
use std::sync::Arc;

use tla_core::ast::Expr;
use tla_core::Spanned;

use crate::error::EvalError;
use crate::eval::EvalCtx;
use crate::Value;

use super::{collect_state_var_refs, BulkConstraintEnumerationError};

/// A filter constraint with dependency info for early evaluation.
pub(super) struct FilterConstraint {
    /// Canonical AST filter expression evaluated once its dependencies are bound.
    pub(super) expr: Spanned<Expr>,
    /// Index at which this filter becomes applicable (max immediate dependency index).
    pub(super) trigger_idx: usize,
    /// True if this filter references any state var that is not an immediate variable.
    pub(super) requires_deferred: bool,
}

pub(super) fn plan_filter_constraints(
    ctx: &EvalCtx,
    vars: &[Arc<str>],
    immediate_vars: &[Arc<str>],
    filters: &[&Spanned<Expr>],
) -> Vec<FilterConstraint> {
    let immediate_positions: rustc_hash::FxHashMap<&str, usize> = immediate_vars
        .iter()
        .enumerate()
        .map(|(index, var)| (var.as_ref(), index))
        .collect();

    filters
        .iter()
        .map(|filter_expr| {
            let mut refs = FxHashSet::default();
            collect_state_var_refs(ctx, filter_expr, vars, &mut refs);

            let mut requires_deferred = immediate_vars.is_empty();
            let mut trigger_idx = 0usize;
            for reference in refs {
                if let Some(&position) = immediate_positions.get(reference.as_ref()) {
                    trigger_idx = trigger_idx.max(position);
                } else {
                    requires_deferred = true;
                }
            }

            FilterConstraint {
                expr: (*filter_expr).clone(),
                trigger_idx,
                requires_deferred,
            }
        })
        .collect()
}

pub(crate) fn eval_filter_expr(ctx: &EvalCtx, expr: &Spanned<Expr>) -> Result<bool, EvalError> {
    match crate::eval::eval_entry(ctx, expr)? {
        Value::Bool(value) => Ok(value),
        other => Err(EvalError::type_error("BOOLEAN", &other, Some(expr.span))),
    }
}

/// Mutable output sink for bulk enumeration: storage, dedup set, filter, count, and index map.
pub(super) struct BulkEnumSink<'a, F, E> {
    pub(super) storage: &'a mut crate::arena::BulkStateStorage,
    pub(super) seen: &'a mut FxHashSet<u64>,
    pub(super) filter: &'a mut F,
    pub(super) generated_count: &'a mut usize,
    pub(super) added_count: &'a mut usize,
    pub(super) var_indices: rustc_hash::FxHashMap<&'a str, usize>,
    pub(super) _filter_error: std::marker::PhantomData<E>,
}

pub(super) fn emit_values_to_bulk<F, E>(
    ctx: &mut EvalCtx,
    values: &[Value],
    sink: &mut BulkEnumSink<'_, F, E>,
) -> Result<(), BulkConstraintEnumerationError<E>>
where
    F: FnMut(&[Value], &mut EvalCtx) -> Result<bool, E>,
{
    if !(sink.filter)(values, ctx).map_err(BulkConstraintEnumerationError::Filter)? {
        return Ok(());
    }

    *sink.generated_count += 1;
    let fingerprint = compute_values_fingerprint(values);
    if !sink.seen.insert(fingerprint) {
        return Ok(());
    }

    sink.storage.push_from_values(values);
    *sink.added_count += 1;
    Ok(())
}

/// Compute a fingerprint for a value slice (for deduplication).
pub(super) fn compute_values_fingerprint(values: &[Value]) -> u64 {
    use std::hash::{Hash, Hasher};

    let mut hasher = rustc_hash::FxHasher::default();
    for value in values {
        value.hash(&mut hasher);
    }
    hasher.finish()
}
