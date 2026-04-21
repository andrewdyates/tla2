// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared action label identification for trace reconstruction.
//!
//! Part of #2470 Step 3: extracted from `check/model_checker/trace_actions.rs`
//! so both the sequential and parallel checker paths can identify which action
//! produced each state transition in a counterexample trace.
//!
//! Both checker paths MUST use this function for action label identification
//! to prevent parity drift.

use crate::check::{format_span_location, format_span_location_from_source, ActionLabel};
use crate::coverage::{detect_actions, DetectedAction};
use crate::eval::{eval_entry, Env, EvalCtx};
use crate::state::{ArrayState, State};
use crate::Value;
use rustc_hash::FxHashMap;
use std::path::PathBuf;
use std::sync::Arc;
use tla_core::ast::OperatorDef;
use tla_core::FileId;

/// Context for action label identification.
///
/// Bundles the module-level information needed to resolve source locations
/// in action labels. The caller looks up the Next definition and passes it
/// directly, avoiding HashMap type mismatch between sequential (FxHashMap)
/// and parallel (std HashMap) checker paths.
pub(crate) struct ActionLabelCtx<'a> {
    /// Name of the Next operator (used as fallback label for monolithic Next).
    pub(crate) next_name: &'a str,
    /// The Next operator definition (caller resolves from their op_defs map).
    /// `None` if the Next definition is not found.
    pub(crate) next_def: Option<&'a OperatorDef>,
    /// Mapping from FileId to source path for TLC-style line/col location rendering.
    pub(crate) file_id_to_path: &'a FxHashMap<FileId, PathBuf>,
    /// Root module name (for TLC-style location rendering).
    pub(crate) module_name: &'a str,
}

/// Identify action labels for each state in a trace.
///
/// For state 0, returns `<Initial predicate>`. For subsequent states, evaluates
/// each action disjunct of the Next relation to determine which action produced
/// the transition from `states[i-1]` to `states[i]`.
///
/// Returns one `ActionLabel` per state. Falls back to `<Action>` placeholders
/// when the Next definition is unavailable or no action matches.
///
/// Both the sequential and parallel checkers MUST use this function for action
/// label identification. Inline implementations are forbidden to prevent drift.
pub(crate) fn identify_action_labels(
    ctx: &mut EvalCtx,
    label_ctx: &ActionLabelCtx<'_>,
    states: &[State],
) -> Vec<ActionLabel> {
    if states.is_empty() {
        return Vec::new();
    }

    let mut labels = Vec::with_capacity(states.len());

    // State 0 is always "Initial predicate"
    labels.push(ActionLabel {
        name: "Initial predicate".to_string(),
        source_location: None,
    });

    if states.len() < 2 {
        return labels;
    }

    // Look up the Next operator definition
    let actions = match label_ctx.next_def {
        Some(next_def) => detect_actions(next_def),
        None => {
            fill_placeholder_labels(&mut labels, states.len() - 1);
            return labels;
        }
    };

    if actions.is_empty() {
        // No actions detected (monolithic Next) — use Next name
        for _ in 1..states.len() {
            labels.push(ActionLabel {
                name: label_ctx.next_name.to_string(),
                source_location: None,
            });
        }
        return labels;
    }

    // When detect_actions returns exactly one action with a synthetic name
    // (e.g., "Action_1"), the Next definition is monolithic (not decomposed
    // into disjuncts). TLC uses the Next operator name in this case, not a
    // synthetic identifier. Part of #2470 Step 6.
    let is_monolithic = actions.len() == 1 && actions[0].name.starts_with("Action_");
    let actions = if is_monolithic {
        let original = actions.into_iter().next().expect("exactly one action");
        vec![DetectedAction {
            id: original.id,
            name: label_ctx.next_name.to_string(),
            expr: original.expr,
        }]
    } else {
        actions
    };

    let registry = ctx.var_registry().clone();

    // For each transition, evaluate each action to find which one fired
    for i in 1..states.len() {
        let current_arr = ArrayState::from_state(&states[i - 1], &registry);
        let next_arr = ArrayState::from_state(&states[i], &registry);

        let label = identify_action_for_transition(
            ctx,
            &actions,
            &current_arr,
            &next_arr,
            label_ctx.file_id_to_path,
            label_ctx.module_name,
        );
        labels.push(label);
    }

    labels
}

/// Identify which action produced a specific transition by evaluating each action
/// with the current and next state bound.
fn identify_action_for_transition(
    ctx: &mut EvalCtx,
    actions: &[DetectedAction],
    current: &ArrayState,
    next: &ArrayState,
    file_id_to_path: &FxHashMap<FileId, PathBuf>,
    module_name: &str,
) -> ActionLabel {
    let _state_guard = ctx.bind_state_env_guard(current.env_ref());
    let _next_guard = ctx.bind_next_state_env_guard(next.env_ref());
    let prev_next_state = ctx.next_state_mut().take();

    // Build next-state HashMap for UNCHANGED evaluation
    let mut next_env = Env::new();
    for (idx, name) in ctx.var_registry().iter() {
        next_env.insert(Arc::clone(name), next.get(idx));
    }
    *ctx.next_state_mut() = Some(Arc::new(next_env));

    let mut fired_name = None;
    let mut fired_span = None;
    let mut _eval_errors = 0usize;
    for action in actions {
        match eval_entry(ctx, &action.expr) {
            Ok(Value::Bool(true)) => {
                fired_name = Some(action.name.clone());
                fired_span = Some(action.expr.span);
                break; // First match (TLC semantics: actions are disjuncts)
            }
            Err(_e) => {
                // Part of #2793: Log eval failures during trace action matching.
                _eval_errors += 1;
                debug_eprintln!(
                    crate::check::debug::tla2_debug(),
                    "[trace-action] eval error for action '{}': {}",
                    action.name,
                    _e
                );
            }
            Ok(Value::Bool(false)) => {} // Action not enabled for this transition
            Ok(_other) => {
                // Part of #1433: warn on non-boolean action result.
                debug_eprintln!(
                    crate::check::debug::tla2_debug(),
                    "[trace-action] WARNING: action '{}' returned non-boolean value {:?}",
                    action.name,
                    _other
                );
            }
        }
    }
    debug_eprintln!(
        _eval_errors > 0 && fired_name.is_none() && crate::check::debug::tla2_debug(),
        "[trace-action] WARNING: no action matched and {} eval error(s) occurred — \
         action label may be incorrect",
        _eval_errors
    );

    *ctx.next_state_mut() = prev_next_state;
    // _next_guard and _state_guard restore array envs on drop

    match fired_name {
        Some(name) => {
            // Resolve through operator definition to get the body span (TLC behavior).
            // TLC reports the source location of the action definition body, not the
            // reference in the Next disjunction. For example, if Next == A \/ B and
            // A == x = 0 /\ x' = 1 is defined at line 10, TLC reports "line 10, ..."
            // not the location of "A" in the Next formula.
            let resolved_span = ctx.get_op(&name).map(|def| def.body.span).or(fired_span);
            let source_location = resolved_span.map(|span| {
                if let Some(path) = file_id_to_path.get(&span.file) {
                    if let Ok(source) = std::fs::read_to_string(path) {
                        return format_span_location_from_source(&span, module_name, &source);
                    }
                }
                format_span_location(&span, module_name)
            });
            ActionLabel {
                name,
                source_location,
            }
        }
        None => ActionLabel {
            name: "Action".to_string(),
            source_location: None,
        },
    }
}

/// Fill `count` placeholder `<Action>` labels into the labels vector.
fn fill_placeholder_labels(labels: &mut Vec<ActionLabel>, count: usize) {
    for _ in 0..count {
        labels.push(ActionLabel {
            name: "Action".to_string(),
            source_location: None,
        });
    }
}
