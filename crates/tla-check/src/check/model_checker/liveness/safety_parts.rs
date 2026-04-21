// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Safety-part checking for liveness properties.
//!
//! Evaluates init terms on initial states and always terms on transitions.
//! Both symmetry and non-symmetry paths use array-backed binding.
//!
//! Part of #2661: both paths read ArrayState directly from `seen` storage
//! and use array-backed binding, eliminating the dependency on the O(N)
//! `state_cache` HashMap. Under symmetry, successor witness values are
//! converted to value arrays for binding; State conversion is deferred
//! to the rare violation-trace path only.

#[cfg(debug_assertions)]
use super::super::debug_safety_parts;
use super::super::{
    check_error_to_result, Arc, ArrayState, CheckResult, Expr, Fingerprint, ModelChecker,
    PropertySafetyParts, Spanned, SuccessorWitnessMap, Trace,
};
use crate::storage::SuccessorGraph;
use crate::LivenessCheckError;
use rustc_hash::FxHashSet;
use std::collections::VecDeque;

impl<'a> ModelChecker<'a> {
    fn eval_safety_part_bool_term(
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

    fn missing_safety_parts_state(
        &self,
        missing: &str,
        fp: Fingerprint,
        context: &str,
    ) -> CheckResult {
        check_error_to_result(
            LivenessCheckError::RuntimeFailure(format!(
                "{missing} for fingerprint {fp} in seen storage ({context}, safety_parts) \
                 — storage invariant violated"
            ))
            .into(),
            &self.stats,
        )
    }

    fn action_level_property_violation(&self, prop_name: &str, trace: Trace) -> CheckResult {
        CheckResult::PropertyViolation {
            property: prop_name.to_string(),
            kind: crate::check::api::PropertyViolationKind::ActionLevel,
            trace,
            stats: self.stats.clone(),
        }
    }

    fn check_property_safety_parts_with_witnesses(
        &mut self,
        prop_name: &str,
        always_terms: &[Spanned<Expr>],
        succ_witnesses: &Arc<SuccessorWitnessMap>,
    ) -> Option<CheckResult> {
        let registry = self.ctx.var_registry().clone();

        for (from_fp, witness_list) in succ_witnesses.iter() {
            let from_arr = match self.state_storage.seen.get(from_fp) {
                Some(arr) => arr.clone(),
                None => {
                    return Some(self.missing_safety_parts_state(
                        "missing state",
                        *from_fp,
                        "symmetry path",
                    ));
                }
            };

            for (dest_canon_fp, to_arr) in witness_list {
                if from_fp == dest_canon_fp {
                    continue;
                }

                let _scope_guard = self.ctx.scope_guard_with_next_state();
                let _sym_state_guard = self.ctx.take_state_env_guard();
                let _sym_next_guard = self.ctx.take_next_state_env_guard();
                *self.ctx.next_state_mut() = None;

                let _state_bound_guard = self.ctx.bind_state_env_guard(from_arr.env_ref());
                let _next_bound_guard = self.ctx.bind_next_state_env_guard(to_arr.env_ref());

                crate::eval::clear_for_run_reset();

                for term in always_terms {
                    let matches_term = match self.eval_safety_part_bool_term(prop_name, term) {
                        Ok(value) => value,
                        Err(result) => return Some(result),
                    };

                    if matches_term {
                        continue;
                    }

                    let from_state = from_arr.to_state(&registry);
                    let to_state = to_arr.to_state(&registry);
                    let trace = Trace::from_states(vec![from_state, to_state]);
                    return Some(self.action_level_property_violation(prop_name, trace));
                }
            }
        }

        None
    }

    fn check_property_safety_parts_from_successors(
        &mut self,
        prop_name: &str,
        always_terms: &[Spanned<Expr>],
        cached_successors: &SuccessorGraph,
    ) -> Option<CheckResult> {
        let registry = self.ctx.var_registry().clone();

        // Iterates all entries — only feasible with in-memory backend.
        let succs_map = cached_successors.as_inner_map()?;
        for (from_fp, succ_fps) in succs_map {
            let from_arr = match self.state_storage.seen.get(from_fp) {
                Some(arr) => arr.clone(),
                None => {
                    return Some(self.missing_safety_parts_state(
                        "missing state",
                        *from_fp,
                        "non-symmetry path",
                    ));
                }
            };

            let saved_next = self.ctx.next_state().clone();
            let _outer_next_guard = self.ctx.take_next_state_env_guard();
            let _state_guard = self.ctx.bind_state_env_guard(from_arr.env_ref());
            *self.ctx.next_state_mut() = None;

            for succ_fp in succ_fps {
                let succ_arr = match self.state_storage.seen.get(succ_fp) {
                    Some(arr) => arr.clone(),
                    None => {
                        *self.ctx.next_state_mut() = saved_next;
                        return Some(self.missing_safety_parts_state(
                            "missing successor state",
                            *succ_fp,
                            "non-symmetry path",
                        ));
                    }
                };

                let _inner_next_guard = self.ctx.bind_next_state_env_guard(succ_arr.env_ref());
                crate::eval::clear_for_run_reset();

                for term in always_terms {
                    let matches_term = match self.eval_safety_part_bool_term(prop_name, term) {
                        Ok(value) => value,
                        Err(result) => {
                            *self.ctx.next_state_mut() = saved_next;
                            return Some(result);
                        }
                    };

                    if matches_term || from_fp == succ_fp {
                        continue;
                    }

                    let from_state = from_arr.to_state(&registry);
                    let to_state = succ_arr.to_state(&registry);
                    let trace = Trace::from_states(vec![from_state, to_state]);
                    *self.ctx.next_state_mut() = saved_next;
                    return Some(self.action_level_property_violation(prop_name, trace));
                }
            }

            *self.ctx.next_state_mut() = saved_next;
        }

        None
    }

    /// Check the safety parts of a property by regenerating successors on demand.
    ///
    /// This is the sequential on-the-fly fallback for mixed safety/liveness
    /// `PROPERTY` formulas. It avoids the cached successor graph entirely, but
    /// still checks init and action terms before the temporal SCC phase runs.
    pub(in super::super) fn check_property_safety_parts_on_the_fly(
        &mut self,
        prop_name: &str,
        parts: &PropertySafetyParts,
    ) -> Option<CheckResult> {
        let init_states = self.liveness_cache.init_states.clone();
        if let Some(result) = self.check_init_terms(prop_name, &parts.init_terms, &init_states) {
            return Some(result);
        }
        if parts.always_terms.is_empty() {
            return None;
        }

        let registry = self.ctx.var_registry().clone();
        let mut seen = FxHashSet::default();
        let mut queue = VecDeque::new();
        for state in self.build_on_the_fly_init_states() {
            let state_fp = match self.state_fingerprint(&state) {
                Ok(fp) => fp,
                Err(error) => return Some(check_error_to_result(error, &self.stats)),
            };
            if seen.insert(state_fp) {
                queue.push_back(state);
            }
        }

        while let Some(from_state) = queue.pop_front() {
            let from_fp = match self.state_fingerprint(&from_state) {
                Ok(fp) => fp,
                Err(error) => return Some(check_error_to_result(error, &self.stats)),
            };
            let successors = match self.generate_liveness_successors_on_the_fly(&from_state) {
                Ok(successors) => successors,
                Err(error) => return Some(check_error_to_result(error, &self.stats)),
            };

            let from_arr = ArrayState::from_state(&from_state, &registry);
            let saved_next = self.ctx.next_state().clone();
            let _outer_next_guard = self.ctx.take_next_state_env_guard();
            let _state_guard = self.ctx.bind_state_env_guard(from_arr.env_ref());
            *self.ctx.next_state_mut() = None;

            for succ_state in successors {
                let succ_fp = match self.state_fingerprint(&succ_state) {
                    Ok(fp) => fp,
                    Err(error) => return Some(check_error_to_result(error, &self.stats)),
                };
                let succ_arr = ArrayState::from_state(&succ_state, &registry);
                let _inner_next_guard = self.ctx.bind_next_state_env_guard(succ_arr.env_ref());
                crate::eval::clear_for_run_reset();

                for term in &parts.always_terms {
                    let matches_term = match self.eval_safety_part_bool_term(prop_name, term) {
                        Ok(value) => value,
                        Err(result) => {
                            *self.ctx.next_state_mut() = saved_next;
                            return Some(result);
                        }
                    };

                    if matches_term || from_fp == succ_fp {
                        continue;
                    }

                    let trace = Trace::from_states(vec![from_state.clone(), succ_state.clone()]);
                    *self.ctx.next_state_mut() = saved_next;
                    return Some(self.action_level_property_violation(prop_name, trace));
                }

                if seen.insert(succ_fp) {
                    queue.push_back(succ_state);
                }
            }

            *self.ctx.next_state_mut() = saved_next;
        }

        None
    }

    /// Check the safety parts of a property (init terms and always terms)
    ///
    /// Returns Some(CheckResult) if property is violated, None if satisfied.
    ///
    /// Under symmetry, `succ_witnesses` contains the actual concrete successors that were
    /// generated during exploration. This is important because successor states from `seen`
    /// are representative states, which may be different symmetric variants than
    /// the actual successors.
    pub(in super::super) fn check_property_safety_parts(
        &mut self,
        prop_name: &str,
        parts: &PropertySafetyParts,
        init_states: &[(Fingerprint, ArrayState)],
        cached_successors: &SuccessorGraph,
        succ_witnesses: Option<&Arc<SuccessorWitnessMap>>,
    ) -> Option<CheckResult> {
        if !self.state_storage.store_full_states {
            if let Some(result) = self.check_init_terms(prop_name, &parts.init_terms, init_states) {
                return Some(result);
            }
            return None;
        }

        let _state_guard = self.ctx.take_state_env_guard();
        let _next_guard = self.ctx.take_next_state_env_guard();

        debug_block!(debug_safety_parts(), {
            eprintln!("=== check_property_safety_parts called ===");
            eprintln!("  prop_name: {}", prop_name);
            eprintln!("  init_terms.len(): {}", parts.init_terms.len());
            eprintln!("  always_terms.len(): {}", parts.always_terms.len());
            eprintln!("  succ_witnesses.is_some(): {}", succ_witnesses.is_some());
        });
        if let Some(result) = self.check_init_terms(prop_name, &parts.init_terms, init_states) {
            return Some(result);
        }

        if parts.always_terms.is_empty() {
            return None;
        }

        if let Some(witnesses) = succ_witnesses {
            debug_block!(debug_safety_parts(), {
                eprintln!(
                    "=== check_property_safety_parts: using succ_witnesses (symmetry path) ==="
                );
                eprintln!("  witnesses.len() = {}", witnesses.len());
            });
            return self.check_property_safety_parts_with_witnesses(
                prop_name,
                &parts.always_terms,
                witnesses,
            );
        }

        debug_block!(debug_safety_parts(), {
            eprintln!(
                "=== check_property_safety_parts: using cached_successors (non-symmetry path) ==="
            );
            eprintln!("  cached_successors.len() = {}", cached_successors.len());
        });
        self.check_property_safety_parts_from_successors(
            prop_name,
            &parts.always_terms,
            cached_successors,
        )
    }
}
