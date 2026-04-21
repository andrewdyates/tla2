// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::{ActionLabelMappingConfig, OperatorRef};
use crate::eval::{eval_entry, Env};
use crate::json_codec::{json_to_value, JsonValueDecodeError};
use crate::json_output::JsonValue;
use crate::state::State;
use crate::value::Value;
use crate::EvalCtx;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use tla_core::ast::Expr;

/// Error from validating an action label against a transition.
#[derive(Debug, thiserror::Error)]
pub enum ActionLabelValidationError {
    #[error("unknown action label: {label}")]
    UnknownLabel { label: String },
    #[error("action label {label} params mismatch: expected {expected:?}, got {got:?}")]
    ParamMismatch {
        label: String,
        expected: Vec<String>,
        got: Vec<String>,
    },
    #[error("param decode error for label {label}, param {param}: {source}")]
    ParamDecodeError {
        label: String,
        param: String,
        #[source]
        source: JsonValueDecodeError,
    },
    #[error("eval error for action label {label}: {message}")]
    EvalError { label: String, message: String },
    #[error("action label {label} evaluated to non-boolean value")]
    NotBoolean { label: String },
    #[error("action label {label} detected stutter transition but allow_stutter=false")]
    StutterNotAllowed { label: String },
}

/// Result of action label validation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ActionLabelValidationResult {
    /// The action label constraint was satisfied by the transition.
    Satisfied,
    /// The action label constraint was not satisfied (transition doesn't match the action).
    NotSatisfied,
}

/// Validate that a trace action label constraint holds for a transition (state -> next_state).
///
/// This evaluates the action operator with the trace-provided parameter bindings, checking
/// whether `Op(params...)` evaluates to TRUE in the context where unprimed variables refer
/// to `state` and primed variables refer to `next_state`.
///
/// # Arguments
///
/// * `ctx` - Evaluation context with the spec loaded
/// * `mapping` - Action label mapping configuration
/// * `state` - The current state (unprimed variable values)
/// * `next_state` - The next state (primed variable values)
/// * `label` - The action label name from the trace
/// * `params` - The action parameters from the trace (may be empty)
///
/// # Returns
///
/// * `Ok(Satisfied)` - The action constraint holds for this transition
/// * `Ok(NotSatisfied)` - The action constraint does not hold
/// * `Err(_)` - Validation error (unknown label, param mismatch, eval error)
pub fn validate_action_label(
    ctx: &mut EvalCtx,
    mapping: &ActionLabelMappingConfig,
    state: &State,
    next_state: &State,
    label: &str,
    params: &HashMap<String, JsonValue>,
) -> Result<ActionLabelValidationResult, ActionLabelValidationError> {
    let action_mapping =
        mapping
            .mapping(label)
            .ok_or_else(|| ActionLabelValidationError::UnknownLabel {
                label: label.to_string(),
            })?;

    if !action_mapping.allow_stutter && state.fingerprint() == next_state.fingerprint() {
        return Err(ActionLabelValidationError::StutterNotAllowed {
            label: label.to_string(),
        });
    }

    let expected: HashSet<&str> = action_mapping
        .params
        .iter()
        .map(std::string::String::as_str)
        .collect();
    let got: HashSet<&str> = params.keys().map(std::string::String::as_str).collect();
    if expected != got {
        let mut expected_vec: Vec<String> = action_mapping.params.clone();
        let mut got_vec: Vec<String> = params.keys().cloned().collect();
        expected_vec.sort();
        got_vec.sort();
        return Err(ActionLabelValidationError::ParamMismatch {
            label: label.to_string(),
            expected: expected_vec,
            got: got_vec,
        });
    }

    let mut decoded_params: Vec<(Arc<str>, Value)> =
        Vec::with_capacity(action_mapping.params.len());
    for param_name in &action_mapping.params {
        let json_val =
            params
                .get(param_name)
                .ok_or_else(|| ActionLabelValidationError::ParamMismatch {
                    label: label.to_string(),
                    expected: action_mapping.params.clone(),
                    got: params.keys().cloned().collect(),
                })?;
        let value = json_to_value(json_val).map_err(|source| {
            ActionLabelValidationError::ParamDecodeError {
                label: label.to_string(),
                param: param_name.clone(),
                source,
            }
        })?;
        decoded_params.push((Arc::from(param_name.as_str()), value));
    }

    let op_body = match &action_mapping.operator {
        OperatorRef::Unqualified { name } => {
            let def = ctx
                .get_op(name)
                .ok_or_else(|| ActionLabelValidationError::EvalError {
                    label: label.to_string(),
                    message: format!("operator {} not found", name),
                })?;
            def.body.clone()
        }
        OperatorRef::ModuleRef { target, name } => {
            let module_name = if let Some(info) = ctx.get_instance(target) {
                info.module_name.clone()
            } else if let Some(def) = ctx.get_op(target) {
                match &def.body.node {
                    Expr::InstanceExpr(module_name, _) => module_name.clone(),
                    _ => {
                        return Err(ActionLabelValidationError::EvalError {
                            label: label.to_string(),
                            message: format!("cannot resolve module for {}", target),
                        });
                    }
                }
            } else {
                return Err(ActionLabelValidationError::EvalError {
                    label: label.to_string(),
                    message: format!("instance {} not found", target),
                });
            };

            let def = ctx.get_instance_op(&module_name, name).ok_or_else(|| {
                ActionLabelValidationError::EvalError {
                    label: label.to_string(),
                    message: format!("operator {}!{} not found", target, name),
                }
            })?;
            def.body.clone()
        }
    };

    // RAII guard restores env + next_state on drop (Part of #2738)
    let _scope_guard = ctx.scope_guard_with_next_state();
    let mark = ctx.mark_stack();

    for (name, value) in state.vars() {
        ctx.bind_mut(Arc::clone(name), value.clone());
    }

    for (name, value) in decoded_params {
        ctx.push_binding(name, value);
    }

    let mut next_env = Env::new();
    for (name, value) in next_state.vars() {
        next_env.insert(Arc::clone(name), value.clone());
    }
    // Part of #3416: explicit next-state Env remains invisible to eval_entry's
    // pointer tracker, so the clone still needs the conservative eval-scope boundary.
    let eval_ctx = ctx.with_next_state_for_eval_scope(next_env);

    let result = eval_entry(&eval_ctx, &op_body);

    ctx.pop_to_mark(&mark);

    match result {
        Ok(Value::Bool(true)) => Ok(ActionLabelValidationResult::Satisfied),
        Ok(Value::Bool(false)) => Ok(ActionLabelValidationResult::NotSatisfied),
        Ok(_) => Err(ActionLabelValidationError::NotBoolean {
            label: label.to_string(),
        }),
        Err(e) => Err(ActionLabelValidationError::EvalError {
            label: label.to_string(),
            message: e.to_string(),
        }),
    }
}
