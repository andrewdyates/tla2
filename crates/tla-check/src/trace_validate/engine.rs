// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Core trace validation engine: ObservationConstraint and TraceValidationEngine.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use crate::coverage::detect_actions;
use crate::error::EvalError;
use crate::eval::{eval_entry, Env, EvalCtx};
use crate::json_codec::json_to_value;
use crate::state::State;
use crate::trace_input::TraceStep;
use crate::Value;

use tla_core::ast::{Expr, OperatorDef};
use tla_core::Spanned;

use super::{
    ActionLabelMode, ActionMatchResult, StepDiagnostic, TraceValidationError,
    TraceValidationResult, TraceValidationSuccess, TraceValidationWarning,
};

/// Observation constraint: maps trace step observation to spec state predicate.
///
/// For the MVP, this is a full-state snapshot observation: all spec variables
/// must match the trace observation exactly.
#[derive(Debug, Clone)]
pub(crate) struct ObservationConstraint {
    /// Variable name -> expected value (decoded from JSON).
    pub(super) values: HashMap<Arc<str>, Value>,
}

impl ObservationConstraint {
    /// Create an observation constraint from a trace step.
    ///
    /// Decodes all JSON values in the trace step to TLA+ values.
    pub(crate) fn from_trace_step(
        step: &TraceStep,
        step_idx: usize,
        spec_vars: &[Arc<str>],
    ) -> Result<Self, TraceValidationError> {
        let mut values = HashMap::new();

        // Build set for O(1) lookup instead of O(n) per trace variable
        let spec_var_set: HashSet<&str> =
            spec_vars.iter().map(std::convert::AsRef::as_ref).collect();

        // Validate that all trace variables are known spec variables
        for var_name in step.state.keys() {
            if !spec_var_set.contains(var_name.as_str()) {
                return Err(TraceValidationError::UnknownTraceVariable {
                    variable: var_name.clone(),
                });
            }
        }

        // For MVP, require all spec variables to be present in observation
        for spec_var in spec_vars {
            let json_value = step.state.get(spec_var.as_ref()).ok_or_else(|| {
                TraceValidationError::MissingSpecVariable {
                    step: step_idx,
                    variable: spec_var.to_string(),
                }
            })?;

            let value = json_to_value(json_value).map_err(|e| {
                TraceValidationError::ObservationDecodeError {
                    step: step_idx,
                    variable: spec_var.to_string(),
                    source: e,
                }
            })?;

            values.insert(Arc::clone(spec_var), value);
        }

        Ok(Self { values })
    }

    /// Check if a spec state matches this observation.
    #[cfg(test)]
    pub(crate) fn matches(&self, state: &State) -> bool {
        for (var, expected) in &self.values {
            match state.get(var) {
                Some(actual) if actual == expected => {}
                _ => return false,
            }
        }
        true
    }

    /// Convert this observation to a State.
    ///
    /// When the observation fully specifies all state variables (the MVP requires this),
    /// we can construct the State directly without enumerating candidates. This avoids
    /// the combinatorial explosion from enumerating all possible successor states.
    pub(crate) fn to_state(&self) -> State {
        use im::OrdMap;
        let vars: OrdMap<Arc<str>, Value> = self
            .values
            .iter()
            .map(|(k, v)| (Arc::clone(k), v.clone()))
            .collect();
        State::from_vars(vars)
    }
}

/// Trace validation engine using explicit-state enumeration.
///
/// Implements the <code>Candidates\[i\]</code> algorithm at the interpreter level.
pub struct TraceValidationEngine<'a> {
    ctx: &'a mut EvalCtx,
    init_def: &'a OperatorDef,
    next_def: &'a OperatorDef,
    vars: Vec<Arc<str>>,
    actions_by_name: HashMap<String, Vec<Spanned<Expr>>>,
    action_label_mode: ActionLabelMode,
}

impl<'a> TraceValidationEngine<'a> {
    /// Create a new trace validation engine.
    ///
    /// # Arguments
    /// * `ctx` - Evaluation context (must have constants bound)
    /// * `init_def` - Init predicate operator definition
    /// * `next_def` - Next relation operator definition
    /// * `vars` - Spec variable names
    pub fn new(
        ctx: &'a mut EvalCtx,
        init_def: &'a OperatorDef,
        next_def: &'a OperatorDef,
        vars: Vec<Arc<str>>,
    ) -> Self {
        let mut actions_by_name: HashMap<String, Vec<Spanned<Expr>>> = HashMap::new();
        for action in detect_actions(next_def) {
            actions_by_name
                .entry(action.name)
                .or_default()
                .push(action.expr);
        }

        Self {
            ctx,
            init_def,
            next_def,
            vars,
            actions_by_name,
            action_label_mode: ActionLabelMode::Error,
        }
    }

    /// Set the action label enforcement mode.
    pub fn with_action_label_mode(mut self, mode: ActionLabelMode) -> Self {
        self.action_label_mode = mode;
        self
    }

    /// Validate a trace against the spec.
    ///
    /// Uses predicate evaluation: for each trace step, constructs the state from
    /// the observation and evaluates Init/Next as predicates. This is O(n) in the
    /// number of trace steps, avoiding the combinatorial explosion of enumerating
    /// all possible successor states (Fix #2769).
    ///
    /// # Arguments
    /// * `steps` - Trace steps to validate (collected eagerly; must start with step 0)
    ///
    /// # Returns
    /// * `Ok(TraceValidationSuccess)` - All steps validated successfully
    /// * `Err(TraceValidationError)` - Validation failed at some step
    pub fn validate_trace<I>(&mut self, steps: I) -> TraceValidationResult
    where
        I: IntoIterator<Item = TraceStep>,
    {
        let steps: Vec<TraceStep> = steps.into_iter().collect();
        if steps.is_empty() {
            return Ok(TraceValidationSuccess {
                steps_validated: 0,
                candidates_per_step: vec![],
                total_candidates_enumerated: 0,
                warnings: vec![],
            });
        }

        let mut candidates_per_step = Vec::with_capacity(steps.len());
        let mut warnings: Vec<TraceValidationWarning> = Vec::new();
        let warn_mode = self.action_label_mode == ActionLabelMode::Warn;

        // Collect sorted action names once for diagnostic output
        let available_actions: Vec<String> = {
            let mut names: Vec<String> = self.actions_by_name.keys().cloned().collect();
            names.sort();
            names
        };

        // Step 0: construct state from observation, evaluate Init predicate
        let obs0 = ObservationConstraint::from_trace_step(&steps[0], 0, &self.vars)?;
        let state0 = obs0.to_state();

        let init_holds = self
            .init_holds_on_state(&state0)
            .map_err(TraceValidationError::InitEnumerationFailed)?;

        if !init_holds {
            return Err(TraceValidationError::NoMatchingStates {
                step: 0,
                diagnostic: StepDiagnostic {
                    successors_enumerated: 0,
                    observation_matches: 0,
                    action_results: vec![],
                    available_actions: available_actions.clone(),
                },
            });
        }
        candidates_per_step.push(1);

        // Track current state (predicate mode: exactly one candidate per step)
        let mut current_state = state0;

        // Steps 1..n: construct next state, evaluate Next predicate
        for (step_idx, step) in steps.iter().enumerate().skip(1) {
            let obs = ObservationConstraint::from_trace_step(step, step_idx, &self.vars)?;
            let next_state = obs.to_state();
            let action_name = step.action.as_ref().map(|action| action.name.clone());

            // Evaluate Next(current_state, next_state)
            let next_holds = self
                .next_holds_on_transition(&current_state, &next_state)
                .map_err(|e| TraceValidationError::SuccessorEnumerationFailed {
                    step: step_idx,
                    source: e,
                })?;

            if !next_holds {
                return Err(TraceValidationError::NoMatchingStates {
                    step: step_idx,
                    diagnostic: StepDiagnostic {
                        successors_enumerated: 0,
                        observation_matches: 0,
                        action_results: vec![],
                        available_actions: available_actions.clone(),
                    },
                });
            }

            // Validate action label if present
            if let Some(label) = action_name.as_deref() {
                match self.actions_by_name.get(label).cloned() {
                    Some(action_exprs) => {
                        let matched = self
                            .transition_matches_any_action(
                                &current_state,
                                &next_state,
                                &action_exprs,
                            )
                            .map_err(|e| TraceValidationError::ActionExprEvalFailed {
                                step: step_idx,
                                source: e,
                            })?;
                        if !matched {
                            if warn_mode {
                                warnings.push(TraceValidationWarning {
                                    step: step_idx,
                                    message: format!(
                                        "action label {label:?} did not match transition"
                                    ),
                                });
                            } else {
                                // Build action match diagnostics
                                let all_actions: Vec<(String, Vec<Spanned<Expr>>)> = self
                                    .actions_by_name
                                    .iter()
                                    .map(|(k, v)| (k.clone(), v.clone()))
                                    .collect();
                                let mut action_results: Vec<ActionMatchResult> = Vec::new();
                                for (act_name, act_exprs) in &all_actions {
                                    let act_matched = match self.transition_matches_any_action(
                                        &current_state,
                                        &next_state,
                                        act_exprs,
                                    ) {
                                        Ok(matched) => matched,
                                        Err(_e) => {
                                            // Part of #2793: Log eval errors in diagnostics
                                            // instead of silently treating as "not matched".
                                            debug_eprintln!(
                                                crate::check::debug::tla2_debug(),
                                                "[trace-validate] eval error for action '{}': {}",
                                                act_name,
                                                _e
                                            );
                                            false
                                        }
                                    };
                                    action_results.push(ActionMatchResult {
                                        name: act_name.clone(),
                                        matched: act_matched,
                                    });
                                }
                                action_results.sort_by(|a, b| a.name.cmp(&b.name));

                                return Err(TraceValidationError::ActionLabelNotSatisfied {
                                    step: step_idx,
                                    label: label.to_string(),
                                    diagnostic: StepDiagnostic {
                                        successors_enumerated: 0,
                                        observation_matches: 1,
                                        action_results,
                                        available_actions: available_actions.clone(),
                                    },
                                });
                            }
                        }
                    }
                    None => {
                        if warn_mode {
                            warnings.push(TraceValidationWarning {
                                step: step_idx,
                                message: format!(
                                    "unknown action label {label:?} (not in spec actions: {})",
                                    available_actions.join(", ")
                                ),
                            });
                        } else {
                            return Err(TraceValidationError::UnknownActionLabel {
                                step: step_idx,
                                label: label.to_string(),
                            });
                        }
                    }
                }
            }

            candidates_per_step.push(1);
            current_state = next_state;
        }

        Ok(TraceValidationSuccess {
            steps_validated: steps.len(),
            candidates_per_step,
            total_candidates_enumerated: 0,
            warnings,
        })
    }

    /// Enumerate all initial states satisfying Init.
    /// Check whether any detected action expression evaluates to TRUE on a transition.
    ///
    /// Returns `Ok(true)` if any action expression evaluates to TRUE,
    /// `Ok(false)` if all evaluate to FALSE, or `Err` if any raises an eval error.
    /// TLC propagates eval errors — it does not treat them as "action not enabled."
    fn transition_matches_any_action(
        &mut self,
        current: &State,
        next: &State,
        action_exprs: &[Spanned<Expr>],
    ) -> Result<bool, EvalError> {
        for expr in action_exprs {
            if self.action_expr_holds_on_transition(current, next, expr)? {
                return Ok(true);
            }
        }
        Ok(false)
    }

    /// Evaluate one action expression over a transition (state, next_state).
    ///
    /// Returns `Ok(true)` if the expression evaluates to TRUE, `Ok(false)` if FALSE,
    /// or propagates the eval error. TLC does not catch eval errors during action
    /// evaluation — they halt model checking with a trace.
    fn action_expr_holds_on_transition(
        &mut self,
        current: &State,
        next: &State,
        action_expr: &Spanned<Expr>,
    ) -> Result<bool, EvalError> {
        // RAII guard restores env + next_state on drop (Part of #2738)
        let _scope_guard = self.ctx.scope_guard_with_next_state();
        let _state_guard = self.ctx.take_state_env_guard();
        let _next_guard = self.ctx.take_next_state_env_guard();
        let mark = self.ctx.mark_stack();

        for (name, value) in current.vars() {
            self.ctx.bind_mut(Arc::clone(name), value.clone());
        }

        let mut next_env = Env::new();
        for (name, value) in next.vars() {
            next_env.insert(Arc::clone(name), value.clone());
        }

        // Part of #3416: conservative cache boundary for clone-next-state path
        let eval_ctx = self.ctx.with_next_state_for_eval_scope(next_env);
        let result = eval_entry(&eval_ctx, action_expr);

        self.ctx.pop_to_mark(&mark);
        // _scope_guard, _next_guard, _state_guard restore on drop

        match result {
            Ok(Value::Bool(b)) => Ok(b),
            Ok(other) => Err(crate::error::EvalError::TypeError {
                expected: "BOOLEAN",
                got: other.type_name(),
                span: Some(action_expr.span),
            }),
            Err(e) => Err(e),
        }
    }

    /// Evaluate Init predicate on a specific state.
    ///
    /// Fix #2769: Instead of enumerating all possible initial states (which can be
    /// combinatorially explosive for specs with large constant domains), directly
    /// evaluate whether the given state satisfies Init.
    fn init_holds_on_state(&mut self, state: &State) -> Result<bool, EvalError> {
        let mark = self.ctx.mark_stack();

        for (name, value) in state.vars() {
            self.ctx.bind_mut(Arc::clone(name), value.clone());
        }

        let result = eval_entry(self.ctx, &self.init_def.body);

        self.ctx.pop_to_mark(&mark);

        match result {
            Ok(Value::Bool(b)) => Ok(b),
            Ok(other) => Err(crate::error::EvalError::TypeError {
                expected: "BOOLEAN",
                got: other.type_name(),
                span: Some(self.init_def.body.span),
            }),
            Err(e) => Err(e),
        }
    }

    /// Evaluate Next relation on a specific (current, next) transition.
    ///
    /// Fix #2769: Instead of enumerating all possible successor states (which can be
    /// combinatorially explosive for specs with quantifiers over large domains like
    /// `x' \in 0..MaxValue`), directly evaluate whether the given transition satisfies
    /// the Next relation. This is O(1) per transition vs O(product of domain sizes).
    fn next_holds_on_transition(
        &mut self,
        current: &State,
        next_state: &State,
    ) -> Result<bool, EvalError> {
        // RAII guard restores env + next_state on drop (Part of #2738)
        let _scope_guard = self.ctx.scope_guard_with_next_state();
        let _state_guard = self.ctx.take_state_env_guard();
        let _next_guard = self.ctx.take_next_state_env_guard();
        let mark = self.ctx.mark_stack();

        for (name, value) in current.vars() {
            self.ctx.bind_mut(Arc::clone(name), value.clone());
        }

        let mut next_env = Env::new();
        for (name, value) in next_state.vars() {
            next_env.insert(Arc::clone(name), value.clone());
        }

        // Part of #3416: conservative cache boundary for clone-next-state path
        let eval_ctx = self.ctx.with_next_state_for_eval_scope(next_env);
        let result = eval_entry(&eval_ctx, &self.next_def.body);

        self.ctx.pop_to_mark(&mark);
        // _scope_guard, _next_guard, _state_guard restore on drop

        match result {
            Ok(Value::Bool(b)) => Ok(b),
            Ok(other) => Err(crate::error::EvalError::TypeError {
                expected: "BOOLEAN",
                got: other.type_name(),
                span: Some(self.next_def.body.span),
            }),
            Err(e) => Err(e),
        }
    }
}
