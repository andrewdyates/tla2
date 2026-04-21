// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Result-mapping boundary for liveness checking.
//!
//! Owns the `LivenessResult -> CheckResult` conversion surface:
//! - `map_liveness_result(...)` — dispatches result variants
//! - `reconstruct_liveness_counterexample_from_fingerprints(...)` — replays
//!   fingerprint-based counterexamples into concrete state sequences
//! - `build_liveness_violation_result(...)` — formats trace pairs into
//!   `CheckResult::LivenessViolation`
//!
//! Extracted from `check_property.rs` and `fp_only.rs` per #3604.

use super::{check_error_to_result, CheckResult, Fingerprint, ModelChecker, State};
use crate::liveness::LivenessResult;
use crate::{EvalCheckError, LivenessCheckError, Trace};

impl ModelChecker<'_> {
    pub(in crate::check::model_checker::liveness) fn map_liveness_result(
        &mut self,
        prop_name: &str,
        result: LivenessResult,
    ) -> Option<CheckResult> {
        match result {
            LivenessResult::Satisfied => None,
            LivenessResult::Violated { prefix, cycle } => {
                let prefix_states: Vec<State> =
                    prefix.into_iter().map(|(state, _)| state).collect();
                let cycle_states: Vec<State> = cycle.into_iter().map(|(state, _)| state).collect();
                Some(self.build_liveness_violation_result(prop_name, prefix_states, cycle_states))
            }
            LivenessResult::ViolatedFingerprints { prefix, cycle } => {
                let (prefix_states, cycle_states) = match self
                    .reconstruct_liveness_counterexample_from_fingerprints(&prefix, &cycle)
                {
                    Ok(result) => result,
                    Err(check_result) => return Some(check_result),
                };
                Some(self.build_liveness_violation_result(prop_name, prefix_states, cycle_states))
            }
            LivenessResult::RuntimeFailure { reason } => Some(check_error_to_result(
                LivenessCheckError::RuntimeFailure(format!(
                    "Liveness runtime failure for '{prop_name}': {reason}"
                ))
                .into(),
                &self.stats,
            )),
            LivenessResult::EvalFailure { error } => Some(check_error_to_result(
                EvalCheckError::Eval(error).into(),
                &self.stats,
            )),
        }
    }

    pub(super) fn reconstruct_liveness_counterexample_from_fingerprints(
        &mut self,
        prefix: &[(Fingerprint, usize)],
        cycle: &[(Fingerprint, usize)],
    ) -> Result<(Vec<State>, Vec<State>), CheckResult> {
        let Some((cycle_start_fp, _)) = cycle.first() else {
            return Ok((Vec::new(), Vec::new()));
        };

        let mut prefix_path = prefix.iter().map(|(fp, _)| *fp).collect::<Vec<_>>();
        prefix_path.push(*cycle_start_fp);
        let mut prefix_with_cycle_start = self.replay_fingerprint_path(&prefix_path)?;
        let Some(mut current_state) = prefix_with_cycle_start.pop() else {
            return Err(check_error_to_result(
                LivenessCheckError::RuntimeFailure(format!(
                    "could not reconstruct counterexample start state for fingerprint {cycle_start_fp}"
                ))
                .into(),
                &self.stats,
            ));
        };
        let prefix_states = prefix_with_cycle_start;
        let next_name = self.trace.cached_next_name.clone().ok_or_else(|| {
            check_error_to_result(
                LivenessCheckError::RuntimeFailure(
                    "cached_next_name not set during liveness counterexample reconstruction".into(),
                )
                .into(),
                &self.stats,
            )
        })?;

        let mut cycle_states: Vec<State> = vec![current_state.clone()];
        for (target_fp, _) in cycle.iter().skip(1) {
            // Use canonical fingerprint (VIEW/symmetry-aware) for comparison,
            // not raw state.fingerprint(). When VIEW is active, the cycle's
            // fingerprints are VIEW-based (from BFS), so the self-loop check
            // must use the same scheme. Part of #3175 fp-only correctness.
            let current_canon_fp = self
                .state_fingerprint(&current_state)
                .map_err(|e| check_error_to_result(e, &self.stats))?;
            if *target_fp == current_canon_fp {
                cycle_states.push(current_state.clone());
                continue;
            }

            let successors = match self.solve_next_relation(&next_name, &current_state) {
                Ok(successors) => successors,
                Err(error) => {
                    return Err(check_error_to_result(error, &self.stats));
                }
            };

            let mut matched_state = None;
            for successor in successors {
                let successor_fp = match self.state_fingerprint(&successor) {
                    Ok(fp) => fp,
                    Err(error) => return Err(check_error_to_result(error, &self.stats)),
                };
                if successor_fp == *target_fp {
                    matched_state = Some(successor);
                    break;
                }
            }

            let Some(next_state) = matched_state else {
                return Err(check_error_to_result(
                    LivenessCheckError::RuntimeFailure(format!(
                        "counterexample replay could not find transition {} -> {}",
                        current_state.fingerprint(),
                        target_fp
                    ))
                    .into(),
                    &self.stats,
                ));
            };

            cycle_states.push(next_state.clone());
            current_state = next_state;
        }

        Ok((prefix_states, cycle_states))
    }

    pub(in crate::check::model_checker) fn build_liveness_violation_result(
        &mut self,
        prop_name: &str,
        prefix_states: Vec<State>,
        mut cycle_states: Vec<State>,
    ) -> CheckResult {
        if cycle_states.len() >= 2 {
            let back_edge_state = cycle_states[0].clone();
            cycle_states.push(back_edge_state);
        }

        let full_states: Vec<State> = prefix_states
            .iter()
            .chain(cycle_states.iter())
            .cloned()
            .collect();
        let full_labels = self.identify_action_labels(&full_states);

        let (prefix_labels, cycle_labels) = if full_labels.len() == full_states.len() {
            let (pl, cl) = full_labels.split_at(prefix_states.len());
            (pl.to_vec(), cl.to_vec())
        } else {
            (Vec::new(), Vec::new())
        };

        let prefix_trace = Trace::from_states_with_labels(prefix_states, prefix_labels);
        let cycle_trace = Trace::from_states_with_labels(cycle_states, cycle_labels);
        CheckResult::LivenessViolation {
            property: prop_name.to_string(),
            prefix: prefix_trace,
            cycle: cycle_trace,
            stats: self.stats.clone(),
        }
    }
}
