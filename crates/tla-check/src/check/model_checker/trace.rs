// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::{
    AstToLive, FairnessConstraint, Fingerprint, LiveExpr, ModelChecker, State, Trace,
    TraceLocationStorage,
};

// Part of #2740: Error types and conversion logic moved to checker_ops.rs
// to be shared between sequential and parallel checker paths.
pub(super) use crate::checker_ops::FairnessToLiveExprError;

impl<'a> ModelChecker<'a> {
    /// Reconstruct a trace from an initial state to the given state.
    ///
    /// Part of #3178: unified trace-file path for both full-state and fp-only modes.
    /// When `store_full_states` is true and trace file is available, gets the
    /// fingerprint path from the trace file and looks up full states in memory.
    /// When trace file is enabled (fp-only): reads fingerprint path from disk
    /// and regenerates states via Init/Next replay.
    /// Otherwise: returns an empty trace.
    pub(super) fn reconstruct_trace(&mut self, end_fp: Fingerprint) -> Trace {
        // Case 1: Trace file is available (both full-state and fp-only modes)
        if self.trace.trace_file.is_some() {
            let fingerprint_path = self.get_fingerprint_path_from_file(end_fp);
            if fingerprint_path.is_empty() {
                return Trace::new();
            }

            // In full-state mode, try to look up states from memory first.
            if self.state_storage.store_full_states {
                let registry = self.ctx.var_registry().clone();
                let states: Vec<State> = fingerprint_path
                    .iter()
                    .filter_map(|fp| {
                        self.state_storage
                            .seen
                            .get(fp)
                            .map(|arr| arr.to_state(&registry))
                    })
                    .collect();
                if states.len() == fingerprint_path.len() {
                    let labels = self.identify_action_labels(&states);
                    return Trace::from_states_with_labels(states, labels);
                }
            }

            // Fallback: replay from Init/Next using the fingerprint path.
            return self.reconstruct_trace_from_fingerprint_path(&fingerprint_path);
        }

        // Case 2: No trace file — return empty trace.
        Trace::new()
    }

    /// Get the fingerprint path from the trace file for a given end state.
    ///
    /// Part of #3178: extracted from `reconstruct_trace_from_file` to enable
    /// sharing between full-state and fp-only trace reconstruction.
    fn get_fingerprint_path_from_file(&mut self, end_fp: Fingerprint) -> Vec<Fingerprint> {
        // Build the trace index lazily if needed.
        self.trace.ensure_trace_index_built();

        let Some(end_loc) = self.trace.trace_locs.get(&end_fp) else {
            eprintln!(
                "WARNING: trace reconstruction failed: fingerprint {end_fp:?} not found in trace location index"
            );
            return Vec::new();
        };

        let Some(ref mut trace_file) = self.trace.trace_file else {
            eprintln!(
                "WARNING: trace reconstruction failed: trace file unexpectedly None (internal error)"
            );
            return Vec::new();
        };
        match trace_file.get_fingerprint_path(end_loc) {
            Ok(path) => path,
            Err(e) => {
                eprintln!(
                    "WARNING: trace reconstruction failed: could not read fingerprint path from trace file: {e}"
                );
                Vec::new()
            }
        }
    }

    /// Reconstruct a trace by replaying from the initial state, matching a known fingerprint path.
    ///
    /// This is used for trace-file mode and as a fallback for checkpoint/resume when full states
    /// are not available in memory.
    fn reconstruct_trace_from_fingerprint_path(
        &mut self,
        fingerprint_path: &[Fingerprint],
    ) -> Trace {
        if fingerprint_path.is_empty() {
            // Part of #1433: empty fingerprint path means parent chain is broken
            // or trace file returned no path. TLC treats this as fatal.
            eprintln!(
                "WARNING: trace reconstruction failed: empty fingerprint path (broken parent chain or corrupt trace file)"
            );
            return Trace::new();
        }

        // We need Init and Next names to regenerate states
        let (init_name, next_name) =
            match (&self.trace.cached_init_name, &self.trace.cached_next_name) {
                (Some(init), Some(next)) => (init.clone(), next.clone()),
                _ => {
                    // Part of #1433: Init/Next names not cached — setup path failed
                    // to store them. TLC treats this as a fatal configuration error.
                    eprintln!(
                        "WARNING: trace reconstruction failed: Init/Next operator names not cached"
                    );
                    return Trace::new();
                }
            };

        // Replay from initial state, matching by fingerprint
        let mut states = Vec::new();

        // Generate initial states and find the one matching the first fingerprint
        let target_init_fp = fingerprint_path[0];
        let initial_states = match self.generate_initial_states(&init_name) {
            Ok(s) => s,
            Err(e) => {
                eprintln!(
                    "WARNING: trace reconstruction failed: could not generate initial states: {e}"
                );
                return Trace::new();
            }
        };

        let Some(mut current_state) =
            initial_states
                .into_iter()
                .find(|s| match self.state_fingerprint(s) {
                    Ok(fp) => fp == target_init_fp,
                    Err(e) => {
                        eprintln!(
                            "WARNING: state fingerprint failed during trace reconstruction: {e}"
                        );
                        false
                    }
                })
        else {
            // Part of #1433: none of the generated initial states match the target
            // fingerprint. This indicates hash collision or non-determinism.
            // TLC treats this as a fatal internal error.
            eprintln!(
                "WARNING: trace reconstruction failed: no initial state matches target fingerprint {target_init_fp:?}"
            );
            return Trace::new();
        };

        states.push(current_state.clone());

        // For each subsequent fingerprint, generate successors and find the match
        for &target_fp in &fingerprint_path[1..] {
            let successors = match self.solve_next_relation(&next_name, &current_state) {
                Ok(s) => s,
                Err(e) => {
                    eprintln!(
                        "WARNING: trace reconstruction failed: could not generate successor states: {e}"
                    );
                    return Trace::from_states(states); // Partial trace
                }
            };

            let Some(next_state) =
                successors
                    .into_iter()
                    .find(|s| match self.state_fingerprint(s) {
                        Ok(fp) => fp == target_fp,
                        Err(e) => {
                            eprintln!(
                            "WARNING: state fingerprint failed during trace reconstruction: {e}"
                        );
                            false
                        }
                    })
            else {
                // Part of #1433: none of the successor states match the expected
                // fingerprint. Returning partial trace. TLC treats this as fatal.
                eprintln!(
                    "WARNING: trace reconstruction incomplete: no successor matches target fingerprint {target_fp:?} (returning partial trace with {} states)",
                    states.len()
                );
                return Trace::from_states(states); // Partial trace
            };

            states.push(next_state.clone());
            current_state = next_state;
        }

        // Part of #2696 Step 3: add action labels to fingerprint-path reconstructed traces.
        let labels = self.identify_action_labels(&states);
        Trace::from_states_with_labels(states, labels)
    }

    /// Convert a fairness constraint to a LiveExpr.
    ///
    /// Part of #2740: Delegates to `checker_ops::fairness_to_live_expr` — the single
    /// canonical implementation shared by both sequential and parallel checker paths.
    pub(super) fn fairness_to_live_expr(
        &self,
        constraint: &FairnessConstraint,
        converter: &AstToLive,
    ) -> Result<LiveExpr, FairnessToLiveExprError> {
        crate::checker_ops::fairness_to_live_expr(
            constraint,
            &self.module.op_defs,
            &self.ctx,
            converter,
        )
    }
}
