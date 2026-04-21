// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::{ArrayState, Fingerprint, Instant, ModelChecker, State};
use rustc_hash::FxHashSet;

use super::simulation_actions::{SimulationActionPlan, SimulationIntFuncInterningGuard};
use super::simulation_rng::SimpleRng;
pub use super::simulation_types::{SimulationConfig, SimulationResult, SimulationStats};
use super::simulation_walk::{finalize_simulation_stats, DeadlockOutcome, InvariantStepOutcome};

/// Helper macro: finalize stats and return an error SimulationResult.
macro_rules! sim_error {
    ($stats:expr, $start_time:expr, $seen:expr, $trace_num:expr, $err:expr) => {{
        finalize_simulation_stats(&mut $stats, $start_time, &$seen, $trace_num);
        return SimulationResult::Error {
            error: $err,
            stats: $stats,
        };
    }};
}

impl ModelChecker<'_> {
    /// Handle no-successor deadlock check for simulation.
    /// Returns `Some(SimulationResult)` if this is a true deadlock that should
    /// be reported, `None` if the trace should just end normally.
    fn handle_simulation_deadlock(
        &mut self,
        trace: &[ArrayState],
        registry: &crate::var_index::VarRegistry,
        stats: &mut SimulationStats,
        start_time: Instant,
        seen: &FxHashSet<Fingerprint>,
        trace_num: usize,
    ) -> Option<SimulationResult> {
        if self.exploration.check_deadlock {
            let current_arr = trace.last().expect("trace has current state");
            match self.check_simulation_deadlock(current_arr) {
                DeadlockOutcome::Terminal => {}
                DeadlockOutcome::Deadlock => {
                    finalize_simulation_stats(stats, start_time, seen, trace_num);
                    return Some(ModelChecker::simulation_deadlock_result(
                        trace,
                        registry,
                        stats.clone(),
                    ));
                }
                DeadlockOutcome::Error(e) => {
                    finalize_simulation_stats(stats, start_time, seen, trace_num);
                    return Some(SimulationResult::Error {
                        error: e,
                        stats: stats.clone(),
                    });
                }
            }
        }
        None
    }

    /// Run simulation mode - generate random traces through the state space
    ///
    /// Simulation mode is useful for:
    /// - Quick exploration of large state spaces
    /// - Finding bugs that require deep traces
    /// - Probabilistic coverage when exhaustive checking is infeasible
    ///
    /// Unlike exhaustive model checking, simulation does not guarantee complete
    /// coverage but can explore much deeper into the state space.
    pub fn simulate(&mut self, sim_config: &SimulationConfig) -> SimulationResult {
        let start_time = Instant::now();

        if let Some(err) = self.module.setup_error.take() {
            return SimulationResult::Error {
                error: err,
                stats: SimulationStats::default(),
            };
        }

        let (initial_states, next_name) = match self.prepare_simulation(sim_config) {
            Ok(simulation_setup) => simulation_setup,
            Err(error) => {
                return SimulationResult::Error {
                    error,
                    stats: SimulationStats::default(),
                };
            }
        };
        let raw_next_name = self
            .config
            .next
            .as_ref()
            .expect("simulation setup validated NEXT")
            .clone();

        // Part of #3316: Detect split action instances so simulation can avoid
        // repeated full-Next recompilation and operate on per-action diffs.
        let simulation_actions = self.detect_simulation_actions(&next_name);
        let use_split_actions = simulation_actions.len() >= 2;

        // Part of #2484: clone registry for ArrayState conversions
        let registry = self.ctx.var_registry().clone();

        // Part of #3316: Pre-build per-action OperatorDefs ONCE.
        // Part of #3433: No longer pre-compiles CompiledAction.
        let action_plans: Vec<SimulationActionPlan> = if use_split_actions {
            self.build_action_plans(&next_name, simulation_actions)
        } else {
            Vec::new()
        };
        // Part of #3316: Skip IntIntervalFunc interning during simulation.
        let _int_func_interning_guard = SimulationIntFuncInterningGuard::new();

        // Initialize RNG and simulation runtime state
        let actual_seed = sim_config.seed.unwrap_or_else(SimpleRng::entropy_seed);
        self.ctx.set_simulation_random_seed(Some(actual_seed));
        self.ctx
            .set_tlc_runtime_stats(Some(crate::eval::TlcRuntimeStats::default()));
        let mut rng = SimpleRng::new(actual_seed);

        let mut stats = SimulationStats::default();
        let mut seen: FxHashSet<Fingerprint> = FxHashSet::default();
        let mut total_trace_length: usize = 0;

        // Part of #3316: precompute flags to skip unnecessary work in the hot loop.
        let needs_constraint_check =
            !self.config.constraints.is_empty() || !self.config.action_constraints.is_empty();
        let uses_trace = self.compiled.uses_trace;

        // Generate random traces
        for _trace_num in 0..sim_config.num_traces {
            let current_trace = _trace_num + 1;
            let init_idx = rng.next_usize(initial_states.len());
            let mut trace: Vec<ArrayState> =
                Vec::with_capacity(sim_config.max_trace_length.saturating_add(1));
            trace.push(ArrayState::from_state_with_fp(
                &initial_states[init_idx],
                &registry,
            ));
            let mut trace_records = uses_trace
                .then(|| Vec::with_capacity(sim_config.max_trace_length.saturating_add(1)));
            let mut current_state: Option<State> = if use_split_actions {
                None
            } else {
                Some(initial_states[init_idx].clone())
            };

            let fp = trace
                .last_mut()
                .expect("trace has initial state")
                .fingerprint(&registry);
            seen.insert(fp);
            stats.states_visited += 1;
            self.update_simulation_runtime_stats(&stats, seen.len(), current_trace);

            // Check invariants on initial state (depth 0 → TLC level 1)
            if sim_config.check_invariants {
                match self.check_simulation_invariants(
                    trace.last().expect("trace has current state"),
                    fp,
                    0,
                    &mut trace_records,
                    &registry,
                ) {
                    InvariantStepOutcome::Ok => {}
                    InvariantStepOutcome::Violation { invariant } => {
                        finalize_simulation_stats(&mut stats, start_time, &seen, _trace_num + 1);
                        return ModelChecker::simulation_invariant_violation_result(
                            invariant, &trace, &registry, stats,
                        );
                    }
                    InvariantStepOutcome::Error(e) => {
                        sim_error!(stats, start_time, seen, _trace_num + 1, e);
                    }
                }
            }

            // Random walk
            let mut trace_length = 0;
            loop {
                if trace_length >= sim_config.max_trace_length {
                    stats.truncated_traces += 1;
                    break;
                }

                // Part of #3316: TLC-style action-first random selection.
                if use_split_actions {
                    let action_count = action_plans.len();
                    let current_arr = trace.last().expect("trace has current state");
                    let mut next_arr_opt: Option<ArrayState> = None;

                    if !needs_constraint_check {
                        let start_action = rng.next_usize(action_count);
                        let prime = rng.next_prime();

                        for i in 0..action_count {
                            let action_idx = (start_action + i * prime) % action_count;
                            let action_plan = &action_plans[action_idx];
                            let mut diffs = match self.generate_diffs_for_action(
                                current_arr,
                                &raw_next_name,
                                &next_name,
                                &action_plan.action_def,
                                &action_plan.instance.bindings,
                            ) {
                                Ok(d) => d,
                                Err(e) => {
                                    sim_error!(stats, start_time, seen, _trace_num + 1, e);
                                }
                            };
                            if diffs.is_empty() {
                                continue;
                            }
                            let chosen_idx = rng.next_usize(diffs.len());
                            let diff = diffs.swap_remove(chosen_idx);
                            next_arr_opt = Some(diff.materialize(current_arr, &registry));
                            break;
                        }
                    } else {
                        let start_action = rng.next_usize(action_count);
                        let prime = rng.next_prime();

                        'action_search: for i in 0..action_count {
                            let action_idx = (start_action + i * prime) % action_count;
                            let action_plan = &action_plans[action_idx];
                            let diffs = match self.generate_diffs_for_action(
                                current_arr,
                                &raw_next_name,
                                &next_name,
                                &action_plan.action_def,
                                &action_plan.instance.bindings,
                            ) {
                                Ok(d) => d,
                                Err(e) => {
                                    sim_error!(stats, start_time, seen, _trace_num + 1, e);
                                }
                            };
                            if diffs.is_empty() {
                                continue;
                            }
                            let diff_count = diffs.len();
                            let start_diff = rng.next_usize(diff_count);

                            for offset in 0..diff_count {
                                let didx = (start_diff + offset) % diff_count;
                                let candidate = diffs[didx].materialize(current_arr, &registry);
                                match self.check_state_constraints_array(&candidate) {
                                    Ok(true) => {}
                                    Ok(false) => continue,
                                    Err(e) => {
                                        sim_error!(stats, start_time, seen, _trace_num + 1, e);
                                    }
                                }
                                match self.check_action_constraints_array(current_arr, &candidate) {
                                    Ok(true) => {}
                                    Ok(false) => continue,
                                    Err(e) => {
                                        sim_error!(stats, start_time, seen, _trace_num + 1, e);
                                    }
                                }
                                next_arr_opt = Some(candidate);
                                break 'action_search;
                            }
                        }
                    }

                    let Some(mut next_arr) = next_arr_opt else {
                        // No action produced a valid successor — check for deadlock.
                        if let Some(result) = self.handle_simulation_deadlock(
                            &trace,
                            &registry,
                            &mut stats,
                            start_time,
                            &seen,
                            _trace_num + 1,
                        ) {
                            return result;
                        }
                        stats.deadlocked_traces += 1;
                        break;
                    };

                    let next_fp = next_arr.fingerprint(&registry);
                    stats.transitions += 1;
                    trace_length += 1;
                    seen.insert(next_fp);
                    stats.states_visited += 1;

                    if sim_config.check_invariants {
                        match self.check_simulation_invariants(
                            &next_arr,
                            next_fp,
                            trace_length,
                            &mut trace_records,
                            &registry,
                        ) {
                            InvariantStepOutcome::Ok => {}
                            InvariantStepOutcome::Violation { invariant } => {
                                trace.push(next_arr);
                                finalize_simulation_stats(
                                    &mut stats,
                                    start_time,
                                    &seen,
                                    _trace_num + 1,
                                );
                                return ModelChecker::simulation_invariant_violation_result(
                                    invariant, &trace, &registry, stats,
                                );
                            }
                            InvariantStepOutcome::Error(e) => {
                                trace.push(next_arr);
                                sim_error!(stats, start_time, seen, _trace_num + 1, e);
                            }
                        }
                    }

                    trace.push(next_arr);
                } else {
                    // Fallback: evaluate entire Next relation (unsplit or
                    // non-decomposable specs). Preserves exact RNG compatibility.
                    let cur_state = current_state
                        .as_ref()
                        .expect("current_state maintained for fallback path");
                    let raw_successors = match self.generate_successors(&next_name, cur_state) {
                        Ok(succs) => succs,
                        Err(e) => {
                            sim_error!(stats, start_time, seen, _trace_num + 1, e);
                        }
                    };

                    if raw_successors.is_empty() {
                        if let Some(result) = self.handle_simulation_deadlock(
                            &trace,
                            &registry,
                            &mut stats,
                            start_time,
                            &seen,
                            _trace_num + 1,
                        ) {
                            return result;
                        }
                        stats.deadlocked_traces += 1;
                        break;
                    }

                    let succ_count = raw_successors.len();
                    let start_idx = rng.next_usize(succ_count);
                    let mut next_state_opt = None;
                    let current_arr = trace.last().expect("trace has current state");
                    for offset in 0..succ_count {
                        let idx = (start_idx + offset) % succ_count;
                        let candidate = &raw_successors[idx];
                        let succ_arr = ArrayState::from_state(candidate, &registry);
                        match self.check_state_constraints_array(&succ_arr) {
                            Ok(true) => {}
                            Ok(false) => continue,
                            Err(e) => {
                                sim_error!(stats, start_time, seen, _trace_num + 1, e);
                            }
                        }
                        match self.check_action_constraints_array(current_arr, &succ_arr) {
                            Ok(true) => {}
                            Ok(false) => continue,
                            Err(e) => {
                                sim_error!(stats, start_time, seen, _trace_num + 1, e);
                            }
                        }
                        next_state_opt = Some(
                            raw_successors
                                .into_iter()
                                .nth(idx)
                                .expect("invariant: idx < succ_count"),
                        );
                        break;
                    }
                    let Some(next_state) = next_state_opt else {
                        // Part of #3083: constraint-filtered deadlock in fallback path.
                        if let Some(result) = self.handle_simulation_deadlock(
                            &trace,
                            &registry,
                            &mut stats,
                            start_time,
                            &seen,
                            _trace_num + 1,
                        ) {
                            return result;
                        }
                        stats.deadlocked_traces += 1;
                        break;
                    };

                    stats.transitions += 1;
                    trace_length += 1;

                    let mut next_arr = ArrayState::from_state_with_fp(&next_state, &registry);
                    let next_fp = next_arr.fingerprint(&registry);
                    seen.insert(next_fp);
                    stats.states_visited += 1;

                    if sim_config.check_invariants {
                        match self.check_simulation_invariants(
                            &next_arr,
                            next_fp,
                            trace_length,
                            &mut trace_records,
                            &registry,
                        ) {
                            InvariantStepOutcome::Ok => {}
                            InvariantStepOutcome::Violation { invariant } => {
                                trace.push(next_arr);
                                finalize_simulation_stats(
                                    &mut stats,
                                    start_time,
                                    &seen,
                                    _trace_num + 1,
                                );
                                return ModelChecker::simulation_invariant_violation_result(
                                    invariant, &trace, &registry, stats,
                                );
                            }
                            InvariantStepOutcome::Error(e) => {
                                trace.push(next_arr);
                                sim_error!(stats, start_time, seen, _trace_num + 1, e);
                            }
                        }
                    }

                    trace.push(next_arr);
                    current_state = Some(next_state);
                }
            }

            total_trace_length += trace_length;
            stats.max_trace_length = stats.max_trace_length.max(trace_length);
            stats.traces_generated += 1;
        }

        stats.distinct_states = seen.len();
        stats.avg_trace_length = if stats.traces_generated > 0 {
            total_trace_length as f64 / stats.traces_generated as f64
        } else {
            0.0
        };
        stats.elapsed_secs = start_time.elapsed().as_secs_f64();
        self.update_simulation_runtime_stats(&stats, seen.len(), stats.traces_generated);

        // Check POSTCONDITION after simulation completes (matches TLC semantics).
        self.stats.max_depth = stats.max_trace_length;
        if let Some(result) = self.check_postcondition() {
            return match result {
                super::CheckResult::Error { error, .. } => SimulationResult::Error { error, stats },
                _ => SimulationResult::Success(stats),
            };
        }

        SimulationResult::Success(stats)
    }
}
