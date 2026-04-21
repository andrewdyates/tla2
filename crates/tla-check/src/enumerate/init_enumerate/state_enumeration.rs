// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! State-producing init constraint enumeration helpers.

use std::sync::Arc;

use crate::error::EvalError;
use crate::eval::{eval_entry, eval_iter_set_tlc_normalized, EvalCtx};
use crate::state::State;
use crate::Value;

use super::{
    build_immediate_var_values, classify_constraints, classify_iter_error_for_speculative_path,
    Constraint, DeferredConstraint, IterDomainAction,
};

pub(super) fn enumerate_states_from_constraints(
    ctx: Option<&EvalCtx>,
    vars: &[Arc<str>],
    constraints: &[Constraint],
) -> Result<Option<Vec<State>>, EvalError> {
    let classified = classify_constraints(constraints);
    let Some(var_values) = build_immediate_var_values(ctx, vars, &classified.immediate)? else {
        return Ok(None);
    };
    if var_values.iter().any(|(_, values)| values.is_empty()) {
        return Ok(Some(Vec::new()));
    }

    let mut partial_states = Vec::new();
    enumerate_combinations(&var_values, 0, &mut Vec::new(), &mut partial_states);

    if classified.deferred.is_empty() && classified.filters.is_empty() {
        return Ok(Some(partial_states));
    }

    let Some(ctx) = ctx else {
        return Ok(None);
    };

    let mut final_states = Vec::new();
    for partial_state in partial_states {
        let mut eval_ctx = ctx.clone();
        for (name, value) in partial_state.vars() {
            eval_ctx.bind_mut(Arc::clone(name), value.clone());
        }

        let mut current_states = vec![partial_state];
        for deferred in &classified.deferred {
            let mut next_states = Vec::new();

            for state in &current_states {
                for (name, value) in state.vars() {
                    eval_ctx.bind_mut(Arc::clone(name), value.clone());
                }

                match deferred {
                    DeferredConstraint::Eq(var_name, expr) => match eval_entry(&eval_ctx, expr) {
                        Ok(value) => next_states.push(state.clone().with_var(*var_name, value)),
                        Err(error) => return Err(error),
                    },
                    DeferredConstraint::In(var_name, expr) => match eval_entry(&eval_ctx, expr) {
                        Ok(set_val) => {
                            match eval_iter_set_tlc_normalized(&eval_ctx, &set_val, Some(expr.span))
                            {
                                Ok(iter) => {
                                    for elem in iter {
                                        next_states.push(state.clone().with_var(*var_name, elem));
                                    }
                                }
                                Err(error) => {
                                    match classify_iter_error_for_speculative_path(&error) {
                                        IterDomainAction::Defer => return Ok(None),
                                        IterDomainAction::Fatal => return Err(error),
                                    }
                                }
                            }
                        }
                        Err(error) => return Err(error),
                    },
                }
            }

            current_states = next_states;
            if current_states.is_empty() {
                break;
            }
        }

        final_states.extend(current_states);
    }

    if !classified.filters.is_empty() {
        let mut kept = Vec::new();
        for state in final_states {
            let mut filter_ctx = ctx.clone();
            for (name, value) in state.vars() {
                filter_ctx.bind_mut(Arc::clone(name), value.clone());
            }

            let mut keep = true;
            for filter_expr in &classified.filters {
                match eval_entry(&filter_ctx, filter_expr) {
                    Ok(Value::Bool(true)) => {}
                    Ok(Value::Bool(false)) => {
                        keep = false;
                        break;
                    }
                    Ok(value) => {
                        return Err(EvalError::type_error(
                            "BOOLEAN",
                            &value,
                            Some(filter_expr.span),
                        ));
                    }
                    Err(error) => return Err(error),
                }
            }

            if keep {
                kept.push(state);
            }
        }
        final_states = kept;
    }

    Ok(Some(final_states))
}

fn enumerate_combinations(
    var_values: &[(Arc<str>, Vec<Value>)],
    idx: usize,
    current: &mut Vec<(Arc<str>, Value)>,
    results: &mut Vec<State>,
) {
    if idx == var_values.len() {
        let state = State::from_pairs(
            current
                .iter()
                .map(|(name, value)| (Arc::clone(name), value.clone())),
        );
        results.push(state);
        return;
    }

    let (var, values) = &var_values[idx];
    for value in values {
        current.push((Arc::clone(var), value.clone()));
        enumerate_combinations(var_values, idx + 1, current, results);
        current.pop();
    }
}
