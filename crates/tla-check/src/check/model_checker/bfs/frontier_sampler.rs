// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Frontier sampling for Cooperative Dual-Engine Model Checking (CDEMC).
//!
//! At BFS level boundaries (when the exploration depth increases), samples
//! up to [`MAX_SAMPLES_PER_LEVEL`] concrete states and sends them to the
//! [`SharedCooperativeState`] for consumption by symbolic engines (BMC/PDR).
//!
//! States with scalar variables (Bool, Int) are always sampled. States
//! with compound-typed variables (Set, Sequence, Record, Func, Tuple,
//! Interval, String, ModelValue) are also sampled when they can be
//! converted to `BmcValue` via [`value_to_bmc_value`]. Only states
//! containing lazy/non-enumerable types (Subset, FuncSet, SetPred, etc.)
//! are skipped, since those cannot be concretely represented in SMT.
//!
//! Part of #3768.

use crate::check::wavefront::value_to_bmc_value;
use crate::cooperative_state::{FrontierSample, SharedCooperativeState};
use crate::state::ArrayState;
use crate::var_index::VarRegistry;
use std::sync::Arc;
use tla_z4::BmcValue;

/// Maximum number of frontier states to sample per BFS level transition.
const MAX_SAMPLES_PER_LEVEL: usize = 10;

/// Tracks BFS depth transitions and samples frontier states for CDEMC.
///
/// Created at the start of the BFS worker loop. On each dequeued state,
/// call [`on_state`] with the current depth and state. When the depth
/// increases (level boundary), the sampler collects up to
/// [`MAX_SAMPLES_PER_LEVEL`] BmcValue-convertible states and sends them
/// to the cooperative state hub. States with compound types (sets,
/// sequences, records, functions) are included when they can be
/// concretely converted to `BmcValue`.
pub(crate) struct FrontierSampler {
    cooperative: Arc<SharedCooperativeState>,
    registry: VarRegistry,
    /// Depth of the previous dequeued state (`None` before the first state).
    prev_depth: Option<usize>,
    /// Number of states sampled at the current depth level.
    samples_at_current_level: usize,
    /// Total states seen at the previous level boundary, used to compute
    /// `new_states` for `record_convergence`. Part of #3871.
    prev_total_states: u64,
}

impl FrontierSampler {
    /// Create a new frontier sampler.
    ///
    /// # Arguments
    /// * `cooperative` - Shared cooperative state hub for sending samples
    /// * `registry` - Variable registry for name resolution
    pub(crate) fn new(cooperative: Arc<SharedCooperativeState>, registry: VarRegistry) -> Self {
        Self {
            cooperative,
            registry,
            prev_depth: None,
            samples_at_current_level: 0,
            prev_total_states: 0,
        }
    }

    /// Observe a dequeued BFS state at the given depth.
    ///
    /// When a depth increase is detected (level boundary), resets the
    /// per-level sample counter, updates the BFS depth watermark, records
    /// convergence data, and begins sampling. Up to [`MAX_SAMPLES_PER_LEVEL`]
    /// scalar-only states are sent to the cooperative hub per level.
    ///
    /// `total_states` is the cumulative count of unique states discovered
    /// so far. Used to compute `new_states` at level boundaries for
    /// `record_convergence`. Part of #3871.
    pub(crate) fn on_state(&mut self, depth: usize, state: &ArrayState, total_states: u64) {
        let is_new_level = match self.prev_depth {
            Some(prev) => depth > prev,
            None => true, // First state is always a level boundary (depth 0)
        };

        if is_new_level {
            self.prev_depth = Some(depth);
            self.samples_at_current_level = 0;
            self.cooperative.update_bfs_depth(depth);

            // Update the frontier depth hint so BMC can prioritize seeds
            // from deeper BFS levels (closer to the exploration frontier).
            self.cooperative.update_bfs_frontier_depth_hint(depth);

            // Part of #3871: record convergence data at level boundaries so
            // the oracle can detect when BFS is converging rapidly and avoid
            // routing actions to the symbolic engine unnecessarily.
            let new_states = total_states.saturating_sub(self.prev_total_states);
            self.cooperative
                .record_convergence(depth, new_states, total_states);
            self.prev_total_states = total_states;

            // Part of #3785: re-evaluate oracle routing at level boundaries.
            // As BFS accumulates more branching-factor data, the oracle may
            // reclassify actions from Either to SymbolicOnly (or vice versa).
            self.cooperative.maybe_reroute_oracle(depth);
        }

        if self.samples_at_current_level >= MAX_SAMPLES_PER_LEVEL {
            return;
        }

        if let Some(sample) = self.try_convert_state(depth, state) {
            if self.cooperative.send_frontier_sample(sample) {
                self.samples_at_current_level += 1;
            }
        }
    }

    /// Try to convert an `ArrayState` into a `FrontierSample`.
    ///
    /// Returns `None` if any variable has a value that cannot be converted
    /// to `BmcValue` (e.g., lazy/non-enumerable types like Subset, FuncSet,
    /// SetPred). Scalar types (Bool, Int) use fast inline conversion;
    /// compound types (Set, Sequence, Record, Func, Tuple, String,
    /// ModelValue) are converted via [`value_to_bmc_value`].
    fn try_convert_state(&self, depth: usize, state: &ArrayState) -> Option<FrontierSample> {
        let values = state.values();
        let mut assignments = Vec::with_capacity(values.len());

        for (idx, name) in self.registry.iter() {
            let cv = &values[idx.as_usize()];
            if cv.is_bool() {
                // Fast inline path: no heap access needed.
                assignments.push((name.to_string(), BmcValue::Bool(cv.as_bool())));
            } else if cv.is_int() {
                // Fast inline path: no heap access needed.
                assignments.push((name.to_string(), BmcValue::Int(cv.as_int())));
            } else if cv.is_heap() {
                // Compound type on the heap: delegate to value_to_bmc_value
                // which handles Set, Sequence, Record, Func, IntFunc, Tuple,
                // Interval, String, ModelValue. Returns None for lazy types.
                let value = cv.as_heap_value();
                match value_to_bmc_value(value) {
                    Some(bmc_val) => assignments.push((name.to_string(), bmc_val)),
                    None => return None,
                }
            } else {
                // Interned string or model value stored inline.
                // These can't be converted without reverse-lookup of the
                // intern table, which value_to_bmc_value handles for the
                // Value::String/Value::ModelValue variants but not for
                // inline CompactValue. Skip these states conservatively.
                return None;
            }
        }

        Some(FrontierSample { depth, assignments })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Value;
    use std::sync::atomic::Ordering;

    fn test_registry() -> VarRegistry {
        VarRegistry::from_names(["x", "y"])
    }

    #[test]
    fn test_sampler_sends_scalar_state() {
        let coop = Arc::new(SharedCooperativeState::new(0));
        let registry = test_registry();
        let mut sampler = FrontierSampler::new(coop.clone(), registry);

        let state = ArrayState::from_values(vec![Value::int(42), Value::Bool(true)]);
        sampler.on_state(0, &state, 1);

        assert_eq!(coop.frontier_samples_sent.load(Ordering::Relaxed), 1);
        let received = coop
            .recv_frontier_sample(std::time::Duration::from_millis(100))
            .expect("should receive sample");
        assert_eq!(received.depth, 0);
        assert_eq!(received.assignments.len(), 2);
    }

    #[test]
    fn test_sampler_sends_compound_set_state() {
        let coop = Arc::new(SharedCooperativeState::new(0));
        let registry = test_registry();
        let mut sampler = FrontierSampler::new(coop.clone(), registry);

        // A state with a concrete finite set — should be sampled since
        // value_to_bmc_value handles Set(Vec<BmcValue>).
        let state = ArrayState::from_values(vec![
            Value::int(1),
            Value::set([Value::int(1), Value::int(2)]),
        ]);
        sampler.on_state(0, &state, 1);

        assert_eq!(
            coop.frontier_samples_sent.load(Ordering::Relaxed),
            1,
            "concrete set states should be sampled"
        );
        let received = coop
            .recv_frontier_sample(std::time::Duration::from_millis(100))
            .expect("should receive compound sample");
        assert_eq!(received.assignments.len(), 2);
        // Second variable should be a Set BmcValue
        match &received.assignments[1].1 {
            BmcValue::Set(members) => {
                assert_eq!(members.len(), 2, "set should have 2 members");
            }
            other => panic!("expected BmcValue::Set, got {other:?}"),
        }
    }

    #[test]
    fn test_sampler_skips_lazy_set_state() {
        use tla_value::value::SubsetValue;

        let coop = Arc::new(SharedCooperativeState::new(0));
        let registry = test_registry();
        let mut sampler = FrontierSampler::new(coop.clone(), registry);

        // A state with a lazy subset (SUBSET S) — cannot be concretely
        // converted, should be skipped.
        let base_set = Value::set([Value::int(1), Value::int(2)]);
        let lazy_subset = Value::Subset(SubsetValue::new(base_set));
        let state = ArrayState::from_values(vec![Value::int(1), lazy_subset]);
        sampler.on_state(0, &state, 1);

        assert_eq!(
            coop.frontier_samples_sent.load(Ordering::Relaxed),
            0,
            "lazy subset states should be skipped"
        );
    }

    #[test]
    fn test_sampler_respects_max_samples_per_level() {
        let coop = Arc::new(SharedCooperativeState::new(0));
        let registry = test_registry();
        let mut sampler = FrontierSampler::new(coop.clone(), registry);

        // Send MAX_SAMPLES_PER_LEVEL + 5 states at the same depth
        for i in 0..MAX_SAMPLES_PER_LEVEL + 5 {
            let state = ArrayState::from_values(vec![Value::int(i as i64), Value::Bool(false)]);
            sampler.on_state(0, &state, (i + 1) as u64);
        }

        assert_eq!(
            coop.frontier_samples_sent.load(Ordering::Relaxed),
            MAX_SAMPLES_PER_LEVEL as u64
        );
    }

    #[test]
    fn test_sampler_resets_on_level_boundary() {
        let coop = Arc::new(SharedCooperativeState::new(0));
        let registry = test_registry();
        let mut sampler = FrontierSampler::new(coop.clone(), registry);

        // Fill depth 0
        for i in 0..MAX_SAMPLES_PER_LEVEL {
            let state = ArrayState::from_values(vec![Value::int(i as i64), Value::Bool(false)]);
            sampler.on_state(0, &state, (i + 1) as u64);
        }
        assert_eq!(
            coop.frontier_samples_sent.load(Ordering::Relaxed),
            MAX_SAMPLES_PER_LEVEL as u64
        );

        // Transition to depth 1 — counter should reset
        let state = ArrayState::from_values(vec![Value::int(99), Value::Bool(true)]);
        sampler.on_state(1, &state, (MAX_SAMPLES_PER_LEVEL + 1) as u64);
        assert_eq!(
            coop.frontier_samples_sent.load(Ordering::Relaxed),
            (MAX_SAMPLES_PER_LEVEL + 1) as u64
        );
    }

    #[test]
    fn test_sampler_updates_depth_watermark() {
        let coop = Arc::new(SharedCooperativeState::new(0));
        let registry = test_registry();
        let mut sampler = FrontierSampler::new(coop.clone(), registry);

        let state = ArrayState::from_values(vec![Value::int(1), Value::Bool(false)]);
        sampler.on_state(0, &state, 1);
        assert_eq!(coop.bfs_depth_watermark.load(Ordering::Relaxed), 0);

        sampler.on_state(1, &state, 2);
        assert_eq!(coop.bfs_depth_watermark.load(Ordering::Relaxed), 1);

        sampler.on_state(3, &state, 5);
        assert_eq!(coop.bfs_depth_watermark.load(Ordering::Relaxed), 3);
    }

    #[test]
    fn test_sampler_records_convergence_at_level_boundary() {
        let coop = Arc::new(SharedCooperativeState::new(0));
        let registry = test_registry();
        let mut sampler = FrontierSampler::new(coop.clone(), registry);

        let state = ArrayState::from_values(vec![Value::int(1), Value::Bool(false)]);

        // First state at depth 0: total_states=2
        sampler.on_state(0, &state, 2);
        // Transition to depth 1: total_states=10, so new_states=10-2=8
        sampler.on_state(1, &state, 10);
        // Transition to depth 2: total_states=15, so new_states=15-10=5
        sampler.on_state(2, &state, 15);

        // Verify depth watermark was updated (convergence recording is
        // tested in cooperative_state.rs; here we confirm on_state calls
        // record_convergence without panicking at each level boundary).
        assert_eq!(coop.bfs_depth_watermark.load(Ordering::Relaxed), 2);
    }
}
