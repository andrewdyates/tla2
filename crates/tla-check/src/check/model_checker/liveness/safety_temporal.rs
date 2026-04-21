// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Safety-temporal fast-path checks and related helpers.

#[cfg(debug_assertions)]
use super::super::debug_safety_temporal;
use super::super::{
    check_error_to_result, Arc, ArrayState, CheckResult, Expr, Fingerprint, ModelChecker,
    SafetyTemporalPropertyOutcome, Spanned, SuccessorWitnessMap, Value,
};
use crate::checker_ops::{classify_safety_temporal, SafetyTemporalClassification};
use crate::storage::SuccessorGraph;
use crate::{ConfigCheckError, EvalCheckError, LivenessCheckError};
#[cfg(test)]
use tla_core::ast::OperatorDef;

impl ModelChecker<'_> {
    fn eval_property_bool_term(
        &self,
        prop_name: &str,
        term: &Spanned<Expr>,
    ) -> Result<bool, CheckResult> {
        crate::checker_ops::eval_property_bool_term_to_result(
            &self.ctx,
            prop_name,
            term,
            &self.stats,
        )
    }

    fn missing_safety_temporal_state(
        &self,
        missing: &str,
        fp: Fingerprint,
        context: &str,
    ) -> SafetyTemporalPropertyOutcome {
        SafetyTemporalPropertyOutcome::Violated(Box::new(check_error_to_result(
            LivenessCheckError::RuntimeFailure(format!(
                "{missing} for fingerprint {fp} in seen storage ({context}, safety_temporal) \
                 — storage invariant violated"
            ))
            .into(),
            &self.stats,
        )))
    }

    fn check_safety_temporal_init_terms_for_states(
        &mut self,
        prop_name: &str,
        init_state_fps: &[Fingerprint],
        init_terms: &[Spanned<Expr>],
    ) -> Option<SafetyTemporalPropertyOutcome> {
        for fp in init_state_fps {
            let Some(cur_array) = self.state_storage.seen.get(fp) else {
                return Some(self.missing_safety_temporal_state(
                    "missing init state",
                    *fp,
                    "init path",
                ));
            };

            let saved_next = self.ctx.next_state().clone();
            let _init_next_guard = self.ctx.take_next_state_env_guard();
            let _init_state_guard = self.ctx.bind_state_env_guard(cur_array.env_ref());
            *self.ctx.next_state_mut() = None;
            // Part of #3465: Use array-bound eval boundary helper.
            crate::eval::clear_for_bound_state_eval_scope(&self.ctx);

            for term in init_terms {
                let matches_term = match self.eval_property_bool_term(prop_name, term) {
                    Ok(value) => value,
                    Err(result) => {
                        *self.ctx.next_state_mut() = saved_next;
                        return Some(SafetyTemporalPropertyOutcome::Violated(Box::new(result)));
                    }
                };

                if matches_term {
                    continue;
                }

                let trace = self.reconstruct_trace(*fp);
                *self.ctx.next_state_mut() = saved_next;
                return Some(SafetyTemporalPropertyOutcome::Violated(Box::new(
                    CheckResult::PropertyViolation {
                        property: prop_name.to_string(),
                        kind: crate::check::api::PropertyViolationKind::StateLevel,
                        trace,
                        stats: self.stats.clone(),
                    },
                )));
            }

            *self.ctx.next_state_mut() = saved_next;
        }

        None
    }

    fn check_safety_temporal_state_terms_on_seen(
        &mut self,
        prop_name: &str,
        always_state_terms: &[Spanned<Expr>],
    ) -> Option<SafetyTemporalPropertyOutcome> {
        // Collect entries to release the immutable borrow on self.state_storage.seen
        // before the loop body calls &mut self methods (eval_property_bool_term, etc.).
        let seen_entries: Vec<_> = self
            .state_storage
            .seen
            .iter()
            .map(|(fp, arr)| (*fp, arr.clone()))
            .collect();
        for (fp, cur_array) in &seen_entries {
            let saved_next = self.ctx.next_state().clone();
            let _as_next_guard = self.ctx.take_next_state_env_guard();
            let _as_state_guard = self.ctx.bind_state_env_guard(cur_array.env_ref());
            *self.ctx.next_state_mut() = None;
            // Part of #3465: Use array-bound eval boundary helper.
            crate::eval::clear_for_bound_state_eval_scope(&self.ctx);

            for term in always_state_terms {
                let matches_term = match self.eval_property_bool_term(prop_name, term) {
                    Ok(value) => value,
                    Err(result) => {
                        *self.ctx.next_state_mut() = saved_next;
                        return Some(SafetyTemporalPropertyOutcome::Violated(Box::new(result)));
                    }
                };

                if matches_term {
                    continue;
                }

                debug_eprintln!(
                    debug_safety_temporal(),
                    "[PROPERTY EVAL] State-level term violated on state fp={}",
                    fp
                );
                let trace = self.reconstruct_trace(*fp);
                *self.ctx.next_state_mut() = saved_next;
                return Some(SafetyTemporalPropertyOutcome::Violated(Box::new(
                    CheckResult::PropertyViolation {
                        property: prop_name.to_string(),
                        kind: crate::check::api::PropertyViolationKind::StateLevel,
                        trace,
                        stats: self.stats.clone(),
                    },
                )));
            }

            *self.ctx.next_state_mut() = saved_next;
        }

        None
    }

    fn check_safety_temporal_action_terms_with_witnesses(
        &mut self,
        prop_name: &str,
        always_action_terms: &[Spanned<Expr>],
        succ_witnesses: &Arc<SuccessorWitnessMap>,
    ) -> SafetyTemporalPropertyOutcome {
        let registry = self.ctx.var_registry().clone();

        for (fp, witness_list) in succ_witnesses.iter() {
            let Some(cur_array) = self.state_storage.seen.get(fp) else {
                return self.missing_safety_temporal_state(
                    "missing state",
                    *fp,
                    "symmetry action path",
                );
            };

            let saved_next = self.ctx.next_state().clone();
            let _outer_next_guard = self.ctx.take_next_state_env_guard();
            let _state_guard = self.ctx.bind_state_env_guard(cur_array.env_ref());
            *self.ctx.next_state_mut() = None;

            for (dest_canon_fp, succ_arr) in witness_list {
                #[cfg(not(debug_assertions))]
                let _ = dest_canon_fp;
                let _inner_next_guard = self.ctx.bind_next_state_env_guard(succ_arr.env_ref());

                crate::eval::clear_for_run_reset();

                for term in always_action_terms {
                    debug_block!(debug_safety_temporal(), {
                        eprintln!("[PROPERTY EVAL] Checking transition (symmetry path):");
                        eprintln!("  Current state (fp={}): array-backed from seen", fp);
                        eprintln!("  Next state (array): {:?}", succ_arr.values());
                    });

                    let matches_term = match self.eval_property_bool_term(prop_name, term) {
                        Ok(value) => value,
                        Err(result) => {
                            *self.ctx.next_state_mut() = saved_next;
                            return SafetyTemporalPropertyOutcome::Violated(Box::new(result));
                        }
                    };
                    debug_eprintln!(
                        debug_safety_temporal(),
                        "[PROPERTY EVAL] Term result (symmetry): {:?}",
                        matches_term
                    );

                    if matches_term {
                        continue;
                    }

                    #[cfg(debug_assertions)]
                    {
                        let cur_state = cur_array.to_state(&registry);
                        let succ_state_dbg = succ_arr.to_state(&registry);
                        super::debug_log_safety_temporal_violation(
                            *fp,
                            *dest_canon_fp,
                            &cur_state,
                            &succ_state_dbg,
                        );
                    }

                    let succ_state = succ_arr.to_state(&registry);
                    let succ_fp = match self.state_fingerprint(&succ_state) {
                        Ok(fp) => fp,
                        Err(error) => {
                            *self.ctx.next_state_mut() = saved_next;
                            return SafetyTemporalPropertyOutcome::Violated(Box::new(
                                check_error_to_result(
                                    EvalCheckError::Eval(crate::error::EvalError::Internal {
                                        message: format!(
                                            "VIEW fingerprint failed during safety-temporal \
                                             check (BFS precondition violated): {error}"
                                        ),
                                        span: None,
                                    })
                                    .into(),
                                    &self.stats,
                                ),
                            ));
                        }
                    };
                    let trace = self.reconstruct_trace(succ_fp);
                    *self.ctx.next_state_mut() = saved_next;
                    return SafetyTemporalPropertyOutcome::Violated(Box::new(
                        CheckResult::PropertyViolation {
                            property: prop_name.to_string(),
                            kind: crate::check::api::PropertyViolationKind::ActionLevel,
                            trace,
                            stats: self.stats.clone(),
                        },
                    ));
                }
            }

            *self.ctx.next_state_mut() = saved_next;
        }

        SafetyTemporalPropertyOutcome::Satisfied
    }

    fn check_safety_temporal_action_terms_from_successors(
        &mut self,
        prop_name: &str,
        always_action_terms: &[Spanned<Expr>],
        state_successors: &SuccessorGraph,
    ) -> SafetyTemporalPropertyOutcome {
        // This path iterates ALL entries — only feasible with in-memory backend.
        // Disk backend: fall through to SCC checker (caller guards on store_full_states,
        // which implies in-memory mode for states of this size).
        let Some(succs_map) = state_successors.as_inner_map() else {
            return SafetyTemporalPropertyOutcome::NotApplicable;
        };
        for (fp, succ_fps) in succs_map {
            let Some(cur_array) = self.state_storage.seen.get(fp) else {
                return self.missing_safety_temporal_state(
                    "missing state",
                    *fp,
                    "non-symmetry action path",
                );
            };

            let saved_next = self.ctx.next_state().clone();
            let _outer_next_guard = self.ctx.take_next_state_env_guard();
            let _state_guard = self.ctx.bind_state_env_guard(cur_array.env_ref());
            *self.ctx.next_state_mut() = None;

            for succ_fp in succ_fps {
                let Some(succ_array) = self.state_storage.seen.get(succ_fp) else {
                    *self.ctx.next_state_mut() = saved_next;
                    return self.missing_safety_temporal_state(
                        "missing successor state",
                        *succ_fp,
                        "non-symmetry action path",
                    );
                };

                let _inner_next_guard = self.ctx.bind_next_state_env_guard(succ_array.env_ref());

                crate::eval::clear_for_run_reset();

                for term in always_action_terms {
                    let matches_term = match self.eval_property_bool_term(prop_name, term) {
                        Ok(value) => value,
                        Err(result) => {
                            *self.ctx.next_state_mut() = saved_next;
                            return SafetyTemporalPropertyOutcome::Violated(Box::new(result));
                        }
                    };
                    debug_eprintln!(
                        debug_safety_temporal(),
                        "[PROPERTY EVAL] Term result: {:?}",
                        matches_term
                    );

                    if matches_term {
                        continue;
                    }

                    let trace = self.reconstruct_trace(*succ_fp);
                    *self.ctx.next_state_mut() = saved_next;
                    return SafetyTemporalPropertyOutcome::Violated(Box::new(
                        CheckResult::PropertyViolation {
                            property: prop_name.to_string(),
                            kind: crate::check::api::PropertyViolationKind::ActionLevel,
                            trace,
                            stats: self.stats.clone(),
                        },
                    ));
                }
            }

            *self.ctx.next_state_mut() = saved_next;
        }

        SafetyTemporalPropertyOutcome::Satisfied
    }

    #[cfg(test)]
    pub(super) fn wrap_with_let_defs(
        defs: &Option<Vec<OperatorDef>>,
        expr: Spanned<Expr>,
    ) -> Spanned<Expr> {
        match defs {
            Some(defs) => Spanned::new(Expr::Let(defs.clone(), Box::new(expr.clone())), expr.span),
            None => expr,
        }
    }

    /// Check init terms on initial states.
    pub(super) fn check_init_terms(
        &mut self,
        prop_name: &str,
        init_terms: &[Spanned<Expr>],
        init_states: &[(Fingerprint, ArrayState)],
    ) -> Option<CheckResult> {
        let registry = self.ctx.var_registry().clone();
        for (_, state) in init_states {
            let _scope_guard = self.ctx.scope_guard_with_next_state();
            let _next_guard = self.ctx.take_next_state_env_guard();
            let _state_guard = self.ctx.bind_state_env_guard(state.env_ref());
            *self.ctx.next_state_mut() = None;
            for term in init_terms {
                let v = match crate::eval::eval_entry(&self.ctx, term) {
                    Ok(v) => v,
                    Err(e) => {
                        return Some(check_error_to_result(
                            EvalCheckError::Eval(e).into(),
                            &self.stats,
                        ));
                    }
                };
                match v {
                    Value::Bool(true) => {}
                    Value::Bool(false) => {
                        let trace =
                            super::super::Trace::from_states(vec![state.to_state(&registry)]);
                        return Some(CheckResult::PropertyViolation {
                            property: prop_name.to_string(),
                            kind: crate::check::api::PropertyViolationKind::StateLevel,
                            trace,
                            stats: self.stats.clone(),
                        });
                    }
                    _ => {
                        return Some(check_error_to_result(
                            EvalCheckError::PropertyNotBoolean(prop_name.to_string()).into(),
                            &self.stats,
                        ));
                    }
                }
            }
        }
        None
    }

    pub(super) fn check_safety_temporal_property(
        &mut self,
        prop_name: &str,
        init_state_fps: &[Fingerprint],
        state_successors: &SuccessorGraph,
        succ_witnesses: Option<&Arc<SuccessorWitnessMap>>,
    ) -> SafetyTemporalPropertyOutcome {
        // Part of #3175: In fingerprint-only mode, the safety-temporal fast path
        // cannot iterate `seen` (it's empty). Fall through to the SCC checker
        // which works with inline bitmask data.
        if !self.state_storage.store_full_states {
            return SafetyTemporalPropertyOutcome::NotApplicable;
        }

        // Part of #295: Debug entry
        debug_eprintln!(
            debug_safety_temporal(),
            "[DEBUG SAFETY_TEMPORAL] Entered check_safety_temporal_property for '{}'",
            prop_name
        );

        if !self.module.op_defs.contains_key(prop_name) {
            return SafetyTemporalPropertyOutcome::Violated(Box::new(check_error_to_result(
                ConfigCheckError::MissingProperty(prop_name.to_string()).into(),
                &self.stats,
            )));
        }

        let (init_terms, always_state_terms, always_action_terms) =
            match classify_safety_temporal(&self.ctx, &self.module.op_defs, prop_name) {
                SafetyTemporalClassification::Applicable {
                    init_terms,
                    always_state_terms,
                    always_action_terms,
                } => (init_terms, always_state_terms, always_action_terms),
                SafetyTemporalClassification::NotApplicable => {
                    debug_eprintln!(
                        debug_safety_temporal(),
                        "[PROPERTY EVAL] Shared safety-temporal classifier returned NotApplicable"
                    );
                    return SafetyTemporalPropertyOutcome::NotApplicable;
                }
            };

        debug_eprintln!(
            debug_safety_temporal(),
            "[PROPERTY EVAL] Checking {} init_terms",
            init_terms.len()
        );
        if let Some(result) =
            self.check_safety_temporal_init_terms_for_states(prop_name, init_state_fps, &init_terms)
        {
            return result;
        }

        debug_eprintln!(
            debug_safety_temporal(),
            "[PROPERTY EVAL] Checking {} always_state_terms on {} states",
            always_state_terms.len(),
            self.state_storage.seen.len()
        );
        if let Some(result) =
            self.check_safety_temporal_state_terms_on_seen(prop_name, &always_state_terms)
        {
            return result;
        }

        debug_eprintln!(
            debug_safety_temporal(),
            "[PROPERTY EVAL] Checking {} always_action_terms",
            always_action_terms.len()
        );
        if always_action_terms.is_empty() {
            return SafetyTemporalPropertyOutcome::Satisfied;
        }
        debug_eprintln!(
            debug_safety_temporal(),
            "[PROPERTY EVAL] succ_witnesses is_some={}",
            succ_witnesses.is_some()
        );
        if let Some(witnesses) = succ_witnesses {
            return self.check_safety_temporal_action_terms_with_witnesses(
                prop_name,
                &always_action_terms,
                witnesses,
            );
        }

        self.check_safety_temporal_action_terms_from_successors(
            prop_name,
            &always_action_terms,
            state_successors,
        )
    }
}
