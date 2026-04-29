// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Init predicate constraint enumeration.

use rustc_hash::FxHashSet;
use std::collections::BTreeSet;
use std::sync::Arc;

use tla_core::ast::Expr;
use tla_core::Spanned;

use crate::error::EvalError;
use crate::eval::EvalCtx;
use crate::Value;

use super::{
    classify_iter_error_for_speculative_path, collect_state_var_refs, find_values_for_var,
    Constraint, IterDomainAction,
};

mod bulk_sink;
mod lazy_domain;
mod state_enumeration;

use bulk_sink::{emit_values_to_bulk, plan_filter_constraints, BulkEnumSink, FilterConstraint};
use lazy_domain::try_enumerate_single_lazy_domain_to_bulk;
use state_enumeration::enumerate_states_from_constraints;

pub(crate) use bulk_sink::eval_filter_expr;

#[cfg(test)]
pub(super) fn compute_values_fingerprint(values: &[Value]) -> u64 {
    bulk_sink::compute_values_fingerprint(values)
}

/// Counts produced by bulk init enumeration before and after fingerprint deduplication.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BulkConstraintEnumerationStats {
    /// States that satisfied the extracted constraints/filter before deduplication.
    pub generated: usize,
    /// Distinct states inserted into the bulk sink after deduplication.
    pub added: usize,
}

/// Error raised while streaming init constraints into bulk storage.
#[derive(Debug)]
pub(crate) enum BulkConstraintEnumerationError<E> {
    Eval(EvalError),
    Filter(E),
}

impl<E> From<EvalError> for BulkConstraintEnumerationError<E> {
    fn from(error: EvalError) -> Self {
        Self::Eval(error)
    }
}

impl BulkConstraintEnumerationError<EvalError> {
    fn into_eval(self) -> EvalError {
        match self {
            Self::Eval(error) | Self::Filter(error) => error,
        }
    }
}

/// A deferred constraint pending evaluation.
enum DeferredConstraint<'a> {
    /// Deferred equality: var = expr (produces one value)
    Eq(&'a str, &'a Spanned<Expr>),
    /// Deferred membership: var \in expr (produces multiple values)
    In(&'a str, &'a Spanned<Expr>),
}

struct ClassifiedConstraints<'a> {
    immediate: Vec<&'a Constraint>,
    deferred: Vec<DeferredConstraint<'a>>,
    filters: Vec<&'a Spanned<Expr>>,
}

fn classify_constraints<'a>(constraints: &'a [Constraint]) -> ClassifiedConstraints<'a> {
    let mut classified = ClassifiedConstraints {
        immediate: Vec::new(),
        deferred: Vec::new(),
        filters: Vec::new(),
    };

    for constraint in constraints {
        match constraint {
            Constraint::Deferred(name, expr) => {
                classified
                    .deferred
                    .push(DeferredConstraint::Eq(name.as_str(), expr.as_ref()));
            }
            Constraint::DeferredIn(name, expr) => {
                classified
                    .deferred
                    .push(DeferredConstraint::In(name.as_str(), expr.as_ref()));
            }
            Constraint::Filter(expr) => classified.filters.push(expr.as_ref()),
            _ => classified.immediate.push(constraint),
        }
    }

    classified
}

fn build_immediate_var_values(
    ctx: Option<&EvalCtx>,
    vars: &[Arc<str>],
    immediate: &[&Constraint],
) -> Result<Option<Vec<(Arc<str>, Vec<Value>)>>, EvalError> {
    let constrained_names: FxHashSet<&str> = immediate
        .iter()
        .filter_map(|constraint| match constraint {
            Constraint::Eq(name, _) | Constraint::In(name, _) | Constraint::NotEq(name, _) => {
                Some(name.as_str())
            }
            _ => None,
        })
        .collect();
    let immediate_owned: Vec<Constraint> = immediate
        .iter()
        .map(|&constraint| constraint.clone())
        .collect();
    let mut var_values = Vec::new();

    for var in vars
        .iter()
        .filter(|var| constrained_names.contains(var.as_ref()))
    {
        let Some(values) = find_values_for_var(ctx, var, &immediate_owned)? else {
            return Ok(None);
        };
        var_values.push((Arc::clone(var), values));
    }

    Ok(Some(var_values))
}

// Allow mutable_key_type: State/Value have interior mutability for lazy evaluation memoization,
// but Ord/Eq implementations don't depend on the mutable state
#[allow(clippy::mutable_key_type)]
pub fn enumerate_states_from_constraint_branches(
    ctx: Option<&EvalCtx>,
    vars: &[Arc<str>],
    branches: &[Vec<Constraint>],
) -> Result<Option<Vec<crate::state::State>>, EvalError> {
    let mut all_states = BTreeSet::new();
    for branch in branches {
        match enumerate_states_from_constraints(ctx, vars, branch)? {
            Some(states) => {
                for state in states {
                    all_states.insert(state);
                }
            }
            None => return Ok(None),
        }
    }
    Ok(Some(all_states.into_iter().collect()))
}

/// Streaming enumeration directly to BulkStateStorage.
#[allow(clippy::mutable_key_type)]
pub(crate) fn enumerate_constraints_to_bulk_with_stats_filter_error<F, E>(
    ctx: &mut EvalCtx,
    vars: &[Arc<str>],
    branches: &[Vec<Constraint>],
    storage: &mut crate::arena::BulkStateStorage,
    mut filter: F,
) -> Result<Option<BulkConstraintEnumerationStats>, BulkConstraintEnumerationError<E>>
where
    F: FnMut(&[Value], &mut EvalCtx) -> Result<bool, E>,
{
    let mut seen_fingerprints: FxHashSet<u64> = FxHashSet::default();
    let mut generated_count = 0;
    let mut added_count = 0;

    for branch in branches {
        let classified = classify_constraints(branch);
        let mut sink = BulkEnumSink {
            storage,
            seen: &mut seen_fingerprints,
            filter: &mut filter,
            generated_count: &mut generated_count,
            added_count: &mut added_count,
            var_indices: rustc_hash::FxHashMap::default(),
            _filter_error: std::marker::PhantomData,
        };
        if try_enumerate_single_lazy_domain_to_bulk(
            ctx,
            vars,
            &classified.immediate,
            &classified.deferred,
            &classified.filters,
            &mut sink,
        )? {
            continue;
        }

        let Some(mut var_values) =
            build_immediate_var_values(Some(&*ctx), vars, &classified.immediate)?
        else {
            return Ok(None);
        };
        if var_values.iter().any(|(_, values)| values.is_empty()) {
            continue;
        }

        if !classified.filters.is_empty() && var_values.len() > 1 {
            let mut counts: rustc_hash::FxHashMap<Arc<str>, usize> =
                rustc_hash::FxHashMap::default();
            for filter_expr in &classified.filters {
                let mut refs = FxHashSet::default();
                collect_state_var_refs(ctx, filter_expr, vars, &mut refs);
                for reference in refs {
                    *counts.entry(reference).or_insert(0) += 1;
                }
            }

            let orig_pos: rustc_hash::FxHashMap<&str, usize> = vars
                .iter()
                .enumerate()
                .map(|(index, var)| (var.as_ref(), index))
                .collect();

            var_values.sort_by(|(lhs, _), (rhs, _)| {
                let lhs_count = counts.get(lhs).copied().unwrap_or(0);
                let rhs_count = counts.get(rhs).copied().unwrap_or(0);
                rhs_count.cmp(&lhs_count).then_with(|| {
                    let lhs_pos = orig_pos.get(lhs.as_ref()).copied().unwrap_or(usize::MAX);
                    let rhs_pos = orig_pos.get(rhs.as_ref()).copied().unwrap_or(usize::MAX);
                    lhs_pos.cmp(&rhs_pos)
                })
            });
        }

        let immediate_var_order: Vec<Arc<str>> =
            var_values.iter().map(|(var, _)| Arc::clone(var)).collect();
        let filter_constraints =
            plan_filter_constraints(ctx, vars, &immediate_var_order, &classified.filters);

        let Some(()) = enumerate_combinations_to_bulk(
            ctx,
            vars,
            &var_values,
            &classified.deferred,
            &filter_constraints,
            &mut sink,
        )?
        else {
            return Ok(None);
        };
    }

    Ok(Some(BulkConstraintEnumerationStats {
        generated: generated_count,
        added: added_count,
    }))
}

/// Streaming enumeration directly to BulkStateStorage.
#[allow(clippy::mutable_key_type)]
pub fn enumerate_constraints_to_bulk_with_stats<F>(
    ctx: &mut EvalCtx,
    vars: &[Arc<str>],
    branches: &[Vec<Constraint>],
    storage: &mut crate::arena::BulkStateStorage,
    filter: F,
) -> Result<Option<BulkConstraintEnumerationStats>, EvalError>
where
    F: FnMut(&[Value], &mut EvalCtx) -> Result<bool, crate::error::EvalError>,
{
    enumerate_constraints_to_bulk_with_stats_filter_error(ctx, vars, branches, storage, filter)
        .map_err(BulkConstraintEnumerationError::into_eval)
}

/// Compatibility wrapper returning only the distinct states inserted into storage.
#[allow(clippy::mutable_key_type)]
pub fn enumerate_constraints_to_bulk<F>(
    ctx: &mut EvalCtx,
    vars: &[Arc<str>],
    branches: &[Vec<Constraint>],
    storage: &mut crate::arena::BulkStateStorage,
    filter: F,
) -> Result<Option<usize>, EvalError>
where
    F: FnMut(&[Value], &mut EvalCtx) -> Result<bool, crate::error::EvalError>,
{
    enumerate_constraints_to_bulk_with_stats(ctx, vars, branches, storage, filter)
        .map(|stats| stats.map(|stats| stats.added))
}

#[allow(clippy::mutable_key_type)]
fn enumerate_combinations_to_bulk<'a, F, E>(
    ctx: &mut EvalCtx,
    all_vars: &'a [Arc<str>],
    var_values: &[(Arc<str>, Vec<Value>)],
    deferred: &[DeferredConstraint],
    filter_constraints: &[FilterConstraint],
    sink: &mut BulkEnumSink<'a, F, E>,
) -> Result<Option<()>, BulkConstraintEnumerationError<E>>
where
    F: FnMut(&[Value], &mut EvalCtx) -> Result<bool, E>,
{
    let mut values: Vec<Value> = vec![Value::Bool(false); all_vars.len()];
    sink.var_indices = all_vars
        .iter()
        .enumerate()
        .map(|(index, var)| (var.as_ref(), index))
        .collect();

    enumerate_combinations_to_bulk_rec(
        ctx,
        var_values,
        0,
        deferred,
        filter_constraints,
        &mut values,
        sink,
    )
}

/// Recursive helper for combination enumeration to bulk storage.
fn enumerate_combinations_to_bulk_rec<F, E>(
    ctx: &mut EvalCtx,
    var_values: &[(Arc<str>, Vec<Value>)],
    idx: usize,
    deferred: &[DeferredConstraint],
    filter_constraints: &[FilterConstraint],
    values: &mut [Value],
    sink: &mut BulkEnumSink<'_, F, E>,
) -> Result<Option<()>, BulkConstraintEnumerationError<E>>
where
    F: FnMut(&[Value], &mut EvalCtx) -> Result<bool, E>,
{
    if idx == var_values.len() {
        if deferred.is_empty() {
            if var_values.is_empty() && !filter_constraints.is_empty() {
                for filter_constraint in filter_constraints {
                    if !eval_filter_expr(ctx, &filter_constraint.expr)? {
                        return Ok(Some(()));
                    }
                }
            }
            emit_values_to_bulk(ctx, values, sink)?;
            return Ok(Some(()));
        }

        let _scope_guard = var_values.is_empty().then(|| ctx.scope_guard());
        return evaluate_deferred_to_bulk(
            ctx,
            deferred,
            values,
            filter_constraints,
            var_values.is_empty(),
            sink,
        );
    }

    let (var, possible_values) = &var_values[idx];
    let Some(&var_idx) = sink.var_indices.get(var.as_ref()) else {
        return Ok(None);
    };

    'value_loop: for value in possible_values {
        values[var_idx] = value.clone();
        ctx.bind_mut(Arc::clone(var), value.clone());

        if !filter_constraints.is_empty() {
            for filter_constraint in filter_constraints {
                if filter_constraint.requires_deferred || filter_constraint.trigger_idx != idx {
                    continue;
                }
                match eval_filter_expr(ctx, &filter_constraint.expr) {
                    Ok(true) => {}
                    Ok(false) => {
                        ctx.unbind(var.as_ref());
                        continue 'value_loop;
                    }
                    Err(error) => {
                        ctx.unbind(var.as_ref());
                        return Err(error.into());
                    }
                }
            }
        }

        let result = enumerate_combinations_to_bulk_rec(
            ctx,
            var_values,
            idx + 1,
            deferred,
            filter_constraints,
            values,
            sink,
        )?;
        ctx.unbind(var.as_ref());
        if result.is_none() {
            return Ok(None);
        }
    }

    Ok(Some(()))
}

/// Helper: Evaluate deferred constraints and push results to bulk storage.
#[allow(clippy::only_used_in_recursion)]
fn evaluate_deferred_to_bulk<F, E>(
    ctx: &mut EvalCtx,
    deferred: &[DeferredConstraint],
    values: &mut [Value],
    filter_constraints: &[FilterConstraint],
    eval_all_filters: bool,
    sink: &mut BulkEnumSink<'_, F, E>,
) -> Result<Option<()>, BulkConstraintEnumerationError<E>>
where
    F: FnMut(&[Value], &mut EvalCtx) -> Result<bool, E>,
{
    if deferred.is_empty() {
        if !filter_constraints.is_empty() {
            for filter_constraint in filter_constraints {
                if !eval_all_filters && !filter_constraint.requires_deferred {
                    continue;
                }
                if !eval_filter_expr(ctx, &filter_constraint.expr)? {
                    return Ok(Some(()));
                }
            }
        }
        emit_values_to_bulk(ctx, values, sink)?;
        return Ok(Some(()));
    }

    let constraint = &deferred[0];
    let remaining = &deferred[1..];

    match constraint {
        DeferredConstraint::Eq(name, expr) => {
            let value = crate::eval::eval_entry(ctx, expr)?;
            let Some(&var_idx) = sink.var_indices.get(*name) else {
                return Ok(None);
            };
            values[var_idx] = value.clone();
            ctx.bind_mut(Arc::from(*name), value);
            let result = evaluate_deferred_to_bulk(
                ctx,
                remaining,
                values,
                filter_constraints,
                eval_all_filters,
                sink,
            )?;
            ctx.unbind(name);
            Ok(result)
        }
        DeferredConstraint::In(name, expr) => {
            let set_value = crate::eval::eval_entry(ctx, expr)?;
            let elements = match &set_value {
                Value::Set(set) => set.iter().cloned().collect::<Vec<_>>(),
                Value::Interval(interval) => interval.iter_values().collect::<Vec<_>>(),
                value if value.is_set() => return Ok(None),
                value => return Err(EvalError::type_error("set", value, Some(expr.span)).into()),
            };

            let Some(&var_idx) = sink.var_indices.get(*name) else {
                return Ok(None);
            };
            let var_arc = Arc::from(*name);
            for element in elements {
                values[var_idx] = element.clone();
                ctx.bind_mut(Arc::clone(&var_arc), element);
                let result = evaluate_deferred_to_bulk(
                    ctx,
                    remaining,
                    values,
                    filter_constraints,
                    eval_all_filters,
                    sink,
                );
                ctx.unbind(name);
                let result = result?;
                if result.is_none() {
                    return Ok(None);
                }
            }
            Ok(Some(()))
        }
    }
}
