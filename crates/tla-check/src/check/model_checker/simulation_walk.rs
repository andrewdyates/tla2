// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Random walk loop helpers for simulation mode.
//!
//! Extracted from `simulation.rs` (Part of #3472) to consolidate duplicated
//! deadlock-check, invariant-check, and stats-finalization patterns.

use super::simulation_actions::{array_state_trace_record, trace_records_value};
use super::simulation_types::SimulationStats;
use super::{ArrayState, CheckError, Fingerprint, Instant, ModelChecker, State, Trace};
use crate::check::model_checker::simulation_types::SimulationResult;
use crate::checker_ops::InvariantOutcome;
use crate::var_index::VarRegistry;
use rustc_hash::FxHashSet;

/// Result of a deadlock check after no successor was found.
pub(super) enum DeadlockOutcome {
    /// State is terminal (acceptable) — end trace normally.
    Terminal,
    /// True deadlock detected — return violation.
    Deadlock,
    /// Error during terminal-state check.
    Error(CheckError),
}

/// Result of invariant checking on a state.
pub(super) enum InvariantStepOutcome {
    /// All invariants hold — continue trace.
    Ok,
    /// Invariant violated — return violation result.
    Violation { invariant: String },
    /// Error during invariant evaluation.
    Error(CheckError),
}

/// Finalize simulation stats before an early return.
///
/// Consolidates the ~15 repeated `stats.traces_generated = ...; stats.distinct_states = ...;
/// stats.elapsed_secs = ...` snippets throughout `simulate()`.
pub(super) fn finalize_simulation_stats(
    stats: &mut SimulationStats,
    start_time: Instant,
    seen: &FxHashSet<Fingerprint>,
    trace_num: usize,
) {
    stats.traces_generated = trace_num;
    stats.distinct_states = seen.len();
    stats.elapsed_secs = start_time.elapsed().as_secs_f64();
}

/// Build a state trace from ArrayState trace for error reporting.
pub(super) fn build_state_trace(trace: &[ArrayState], registry: &VarRegistry) -> Vec<State> {
    trace.iter().map(|a| a.to_state(registry)).collect()
}

impl ModelChecker<'_> {
    /// Check whether a state with no successors is a true deadlock or an acceptable terminal state.
    ///
    /// Consolidates the 3 identical deadlock-check blocks in `simulate()`.
    /// Only called when `self.exploration.check_deadlock` is true.
    pub(super) fn check_simulation_deadlock(
        &mut self,
        current_arr: &ArrayState,
    ) -> DeadlockOutcome {
        match self.is_terminal_state_array(current_arr) {
            Ok(true) => DeadlockOutcome::Terminal,
            Ok(false) => DeadlockOutcome::Deadlock,
            Err(e) => DeadlockOutcome::Error(e),
        }
    }

    /// Check invariants on a state during simulation.
    ///
    /// Consolidates the 3 identical invariant-check blocks in `simulate()`.
    /// Handles trace context setup/teardown around the canonical
    /// `check_invariants_for_successor` call.
    pub(super) fn check_simulation_invariants(
        &mut self,
        next_arr: &ArrayState,
        next_fp: Fingerprint,
        trace_length: usize,
        trace_records: &mut Option<Vec<crate::Value>>,
        registry: &VarRegistry,
    ) -> InvariantStepOutcome {
        let current_level = match crate::checker_ops::depth_to_tlc_level(trace_length) {
            Ok(level) => level,
            Err(error) => return InvariantStepOutcome::Error(error),
        };
        if let Some(records) = trace_records.as_mut() {
            records.push(array_state_trace_record(next_arr, registry));
            self.ctx
                .set_tlc_trace_value(Some(trace_records_value(records)));
        }
        let outcome = crate::checker_ops::check_invariants_for_successor(
            &mut self.ctx,
            &self.config.invariants,
            &self.compiled.eval_state_invariants,
            next_arr,
            next_fp,
            current_level,
        );
        self.clear_trace_context();
        match outcome {
            InvariantOutcome::Ok | InvariantOutcome::ViolationContinued => InvariantStepOutcome::Ok,
            InvariantOutcome::Violation { invariant, .. } => {
                InvariantStepOutcome::Violation { invariant }
            }
            InvariantOutcome::Error(e) => InvariantStepOutcome::Error(e),
        }
    }

    /// Build a SimulationResult for a deadlock during simulation.
    pub(super) fn simulation_deadlock_result(
        trace: &[ArrayState],
        registry: &VarRegistry,
        stats: SimulationStats,
    ) -> SimulationResult {
        let state_trace = build_state_trace(trace, registry);
        SimulationResult::Deadlock {
            trace: Trace::from_states(state_trace),
            stats,
        }
    }

    /// Build a SimulationResult for an invariant violation during simulation.
    pub(super) fn simulation_invariant_violation_result(
        invariant: String,
        trace: &[ArrayState],
        registry: &VarRegistry,
        stats: SimulationStats,
    ) -> SimulationResult {
        let state_trace = build_state_trace(trace, registry);
        SimulationResult::InvariantViolation {
            invariant,
            trace: Trace::from_states(state_trace),
            stats,
        }
    }
}
