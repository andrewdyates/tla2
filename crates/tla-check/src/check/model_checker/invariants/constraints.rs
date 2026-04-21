// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Constraint and terminal-state evaluation.
//!
//! BFS filtering predicates: state constraints (`CONSTRAINT`), action constraints
//! (`ACTION_CONSTRAINT`), and terminal state detection. Extracted from `eval.rs`
//! as part of #3603 to keep each module under the 500-line threshold.
//!
//! TLC alignment: `Tool.isInModel()` (state constraint), `Tool.isInActions()`
//! (action constraint), terminal state handling.

use super::super::{ArrayState, CheckError, ModelChecker, TerminalSpec};

/// Check if an ArrayState is a terminal state (standalone version).
///
/// This is a free function usable by both the sequential and parallel model checkers.
/// Delegates to the canonical [`crate::checker_ops::check_terminal_array_state`].
///
/// Returns `false` if `terminal` is `None`. Part of #2092.
///
/// Part of #2484: now delegates to shared canonical implementation.
pub(crate) fn check_terminal_array(
    ctx: &mut tla_eval::EvalCtx,
    terminal: Option<&TerminalSpec>,
    var_registry: &crate::var_index::VarRegistry,
    array_state: &ArrayState,
) -> Result<bool, CheckError> {
    crate::checker_ops::check_terminal_array_state(ctx, terminal, var_registry, array_state)
}

impl<'a> ModelChecker<'a> {
    /// Check all state constraints for an ArrayState, returning true if ALL are satisfied.
    ///
    /// Usually delegates to the canonical
    /// [`crate::checker_ops::check_state_constraints_array`].
    ///
    /// Part of #3194: when TIR eval/parity is enabled for a selected constraint
    /// operator, this wrapper evaluates the named operator in-place so the
    /// sequential checker can exercise TIR without changing the shared
    /// `checker_ops` API.
    ///
    /// TLC semantics: eval/type errors in CONSTRAINT are reported as errors, not as unsatisfied.
    ///
    /// Part of #2565: sequential path now delegates to shared canonical implementation.
    pub(in crate::check::model_checker) fn check_state_constraints_array(
        &mut self,
        array_state: &ArrayState,
    ) -> Result<bool, CheckError> {
        let needs_tir_path = self.tir_parity.as_ref().is_some_and(|tir| {
            self.config
                .constraints
                .iter()
                .any(|name| tir.is_selected(name))
        });
        if needs_tir_path {
            let _state_guard = self.ctx.bind_state_env_guard(array_state.env_ref());
            for constraint_name in &self.config.constraints {
                // Scope tir borrow to compute result + parity flag, then release
                // before maybe_check_tir_parity_state which takes &mut self.
                let (result, needs_parity_check) = {
                    let tir = self
                        .tir_parity
                        .as_ref()
                        .expect("invariant: tir_parity is Some inside needs_tir_path block");
                    let needs_parity = tir.is_parity_mode() && tir.is_selected(constraint_name);
                    // Part of #3391: call eval_named_op directly — it already
                    // wraps in eval_entry_with internally. Removing the outer
                    // wrapper eliminates the double-wrapping that could
                    // interfere with cache lifecycle during BFS.
                    let result = if tir.is_eval_mode() && tir.is_selected(constraint_name) {
                        tir.eval_named_op(&self.ctx, constraint_name)
                    } else {
                        self.ctx.eval_op(constraint_name)
                    };
                    (result, needs_parity)
                };

                let satisfied = match result {
                    Ok(crate::Value::Bool(flag)) => flag,
                    Ok(_) => {
                        return Err(crate::EvalCheckError::ConstraintNotBoolean(
                            constraint_name.clone(),
                        )
                        .into())
                    }
                    Err(e) => return Err(crate::EvalCheckError::Eval(e).into()),
                };

                if needs_parity_check {
                    self.maybe_check_tir_parity_state(constraint_name, array_state)?;
                }

                if !satisfied {
                    return Ok(false);
                }
            }
            return Ok(true);
        }

        crate::checker_ops::check_state_constraints_array(
            &mut self.ctx,
            &self.config.constraints,
            array_state,
        )
    }

    /// Check all action constraints for a transition using ArrayState, returning true if ALL pass.
    ///
    /// Usually delegates to the canonical
    /// [`crate::checker_ops::check_action_constraints_array`], which uses RAII
    /// array guards for exception-safe state/next-state binding.
    ///
    /// Part of #3194: when TIR eval/parity is enabled for a selected
    /// ACTION_CONSTRAINT operator, this wrapper evaluates the named operator
    /// in-place so the sequential checker can exercise TIR without changing the
    /// shared `checker_ops` API.
    ///
    /// TLC semantics: eval/type errors in ACTION_CONSTRAINT are reported as errors.
    ///
    /// Part of #2484: ArrayState-only action constraint check.
    pub(in crate::check::model_checker) fn check_action_constraints_array(
        &mut self,
        current: &ArrayState,
        next: &ArrayState,
    ) -> Result<bool, CheckError> {
        let needs_tir_path = self.tir_parity.as_ref().is_some_and(|tir| {
            self.config
                .action_constraints
                .iter()
                .any(|name| tir.is_selected(name))
        });
        if needs_tir_path {
            let _state_guard = self.ctx.bind_state_env_guard(current.env_ref());
            let _next_guard = self.ctx.bind_next_state_env_guard(next.env_ref());
            for constraint_name in &self.config.action_constraints {
                let (result, needs_parity_check) = {
                    let tir = self
                        .tir_parity
                        .as_ref()
                        .expect("invariant: tir_parity is Some inside needs_tir_path block");
                    let needs_parity = tir.is_parity_mode() && tir.is_selected(constraint_name);
                    // Part of #3391: same fix — remove outer eval_entry_with.
                    let result = if tir.is_eval_mode() && tir.is_selected(constraint_name) {
                        tir.eval_named_op(&self.ctx, constraint_name)
                    } else {
                        self.ctx.eval_op(constraint_name)
                    };
                    (result, needs_parity)
                };

                let satisfied = match result {
                    Ok(crate::Value::Bool(flag)) => flag,
                    Ok(_) => {
                        return Err(crate::EvalCheckError::ConstraintNotBoolean(
                            constraint_name.clone(),
                        )
                        .into())
                    }
                    Err(e) => return Err(crate::EvalCheckError::Eval(e).into()),
                };

                if needs_parity_check {
                    self.maybe_check_tir_parity_transition(constraint_name, current, next)?;
                }

                if !satisfied {
                    return Ok(false);
                }
            }
            return Ok(true);
        }

        // Use optimized path with variable-change analysis when available.
        if let Some(ref analysis) = self.compiled.action_constraint_analysis {
            return crate::checker_ops::check_action_constraints_with_analysis(
                &mut self.ctx,
                &self.config.action_constraints,
                current,
                next,
                analysis,
            );
        }

        crate::checker_ops::check_action_constraints_array(
            &mut self.ctx,
            &self.config.action_constraints,
            current,
            next,
        )
    }

    /// Check if an ArrayState is a terminal state
    ///
    /// Usually delegates to the canonical
    /// [`crate::checker_ops::check_terminal_array_state`].
    ///
    /// Part of #3194: when TIR eval/parity is enabled for a selected
    /// operator-form TERMINAL predicate, this wrapper evaluates the operator
    /// in-place so the sequential checker can exercise TIR without changing the
    /// shared `checker_ops` API.
    ///
    /// TLC semantics: eval/type errors in TERMINAL operators are reported as errors.
    ///
    /// Part of #2484: sequential path now delegates to shared canonical implementation.
    pub(in crate::check::model_checker) fn is_terminal_state_array(
        &mut self,
        array_state: &ArrayState,
    ) -> Result<bool, CheckError> {
        if let Some(crate::TerminalSpec::Operator(op_name)) = self.config.terminal.as_ref() {
            let terminal_selected = self
                .tir_parity
                .as_ref()
                .is_some_and(|tir| tir.is_selected(op_name));
            if terminal_selected {
                let _state_guard = self.ctx.bind_state_env_guard(array_state.env_ref());
                let (result, needs_parity_check) = {
                    let tir = self
                        .tir_parity
                        .as_ref()
                        .expect("invariant: tir_parity is Some inside terminal_selected block");
                    let needs_parity = tir.is_parity_mode();
                    // Part of #3391: same fix — remove outer eval_entry_with.
                    let result = if tir.is_eval_mode() {
                        tir.eval_named_op(&self.ctx, op_name)
                    } else {
                        self.ctx.eval_op(op_name)
                    };
                    (result, needs_parity)
                };

                let is_terminal = match result {
                    Ok(crate::Value::Bool(flag)) => flag,
                    Ok(_) => {
                        return Err(
                            crate::EvalCheckError::ConstraintNotBoolean(op_name.clone()).into()
                        )
                    }
                    Err(e) => return Err(crate::EvalCheckError::Eval(e).into()),
                };

                if needs_parity_check {
                    self.maybe_check_tir_parity_state(op_name, array_state)?;
                }

                return Ok(is_terminal);
            }
        }

        let registry = self.ctx.var_registry().clone();
        crate::checker_ops::check_terminal_array_state(
            &mut self.ctx,
            self.config.terminal.as_ref(),
            &registry,
            array_state,
        )
    }
}
