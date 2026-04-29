// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Runtime type profiling for speculative JIT specialization.
//!
//! This module samples the concrete `Value` shapes seen for each state
//! variable during BFS exploration. After a warmup period, the collected
//! profile can be frozen and handed to the JIT as a specialization hint.

use rustc_hash::FxHashSet;
use std::env;

const DEFAULT_WARMUP_THRESHOLD: u64 = 1_000;
const DEFAULT_SAMPLING_RATE: u32 = 1;
const TYPE_WARMUP_ENV: &str = "TLA2_JIT_TYPE_WARMUP";
const TYPE_SAMPLE_RATE_ENV: &str = "TLA2_JIT_TYPE_SAMPLE_RATE";

/// Re-export the canonical [`SpecType`] enum from `tla-jit-abi`.
///
/// The definition moved to `tla-jit-abi::tier_types` in Wave 11b-redo of
/// epic #4251 Stage 2d so that `tla-check` can hold profile-scratch fields
/// (`Vec<SpecType>`) without pulling `tla-jit` (and its Cranelift forks)
/// into the dep graph.
pub use tla_jit_abi::SpecType;

/// Per-variable observation state for runtime type profiling.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) struct VarTypeObservation {
    /// Distinct specialization classes observed for this variable.
    pub(crate) observed_types: FxHashSet<SpecType>,
    /// Number of sampled states contributing to this observation.
    pub(crate) sample_count: u64,
}

impl VarTypeObservation {
    /// Record one more type observation for this variable.
    pub(crate) fn record(&mut self, ty: SpecType) {
        self.sample_count = self.sample_count.saturating_add(1);
        self.observed_types.insert(ty);
    }

    /// Return `true` when exactly one type has been observed.
    #[must_use]
    pub(crate) fn is_monomorphic(&self) -> bool {
        self.sample_count > 0 && self.observed_types.len() == 1
    }

    /// Return the sole observed type when this variable is monomorphic.
    #[must_use]
    pub(crate) fn dominant_type(&self) -> Option<SpecType> {
        if self.is_monomorphic() {
            self.observed_types.iter().copied().next()
        } else {
            None
        }
    }
}

/// A complete runtime type profile for all state variables.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeProfile {
    /// One observation slot per state variable.
    pub(crate) var_profiles: Vec<VarTypeObservation>,
    /// Number of sampled states recorded into this profile.
    pub(crate) total_states_sampled: u64,
    /// Whether the profile has been frozen for specialization.
    pub(crate) is_stable: bool,
}

impl TypeProfile {
    /// Create an empty profile with space for `var_count` state variables.
    #[must_use]
    pub fn new(var_count: usize) -> Self {
        Self {
            var_profiles: vec![VarTypeObservation::default(); var_count],
            total_states_sampled: 0,
            is_stable: false,
        }
    }

    /// Record one sampled state worth of specialization classes.
    pub fn record_state(&mut self, values: &[SpecType]) {
        assert_eq!(
            values.len(),
            self.var_profiles.len(),
            "TypeProfile expected {} variables, got {}",
            self.var_profiles.len(),
            values.len()
        );

        for (observation, ty) in self.var_profiles.iter_mut().zip(values.iter().copied()) {
            observation.record(ty);
        }
        self.total_states_sampled = self.total_states_sampled.saturating_add(1);
    }

    /// Return `true` when every variable has exactly one observed type.
    #[must_use]
    pub fn is_fully_monomorphic(&self) -> bool {
        self.var_profiles
            .iter()
            .all(VarTypeObservation::is_monomorphic)
    }

    /// Return the monomorphic type for each variable when available.
    #[must_use]
    pub fn monomorphic_types(&self) -> Vec<Option<SpecType>> {
        self.var_profiles
            .iter()
            .map(VarTypeObservation::dominant_type)
            .collect()
    }

    /// Mark this profile as stable and ready for specialization.
    pub fn mark_stable(&mut self) {
        self.is_stable = true;
    }

    /// Return the number of profiled state variables.
    #[must_use]
    pub fn var_count(&self) -> usize {
        self.var_profiles.len()
    }

    /// Return the number of sampled states recorded in this profile.
    #[must_use]
    pub fn total_states(&self) -> u64 {
        self.total_states_sampled
    }
}

/// Stateful warmup driver for runtime type profiling.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeProfiler {
    /// The mutable type profile under construction.
    pub(crate) profile: TypeProfile,
    /// Number of sampled states required before freezing.
    pub(crate) warmup_threshold: u64,
    /// Sample one out of every `sampling_rate` encountered states.
    pub(crate) sampling_rate: u32,
    /// Total states encountered, including unsampled and post-freeze states.
    pub(crate) states_seen: u64,
    /// Stop recording once the profile becomes stable.
    pub(crate) frozen: bool,
}

impl TypeProfiler {
    /// Create a profiler using environment-derived configuration.
    ///
    /// Environment variables:
    /// - `TLA2_JIT_TYPE_WARMUP` -> warmup threshold (default `1000`)
    /// - `TLA2_JIT_TYPE_SAMPLE_RATE` -> sampling rate (default `1`)
    #[must_use]
    pub fn new(var_count: usize) -> Self {
        Self::with_config(
            var_count,
            warmup_threshold_from_env(),
            sampling_rate_from_env(),
        )
    }

    /// Create a profiler with explicit warmup and sampling parameters.
    ///
    /// A `sampling_rate` of `0` is normalized to `1`.
    #[must_use]
    pub fn with_config(var_count: usize, warmup_threshold: u64, sampling_rate: u32) -> Self {
        Self {
            profile: TypeProfile::new(var_count),
            warmup_threshold,
            sampling_rate: sampling_rate.max(1),
            states_seen: 0,
            frozen: false,
        }
    }

    /// Observe one state and return `true` iff this call stabilized the profile.
    pub fn observe_state(&mut self, values: &[SpecType]) -> bool {
        self.states_seen = self.states_seen.saturating_add(1);

        if self.frozen || !self.should_sample_current_state() {
            return false;
        }

        self.profile.record_state(values);
        if self.profile.total_states() >= self.warmup_threshold {
            self.profile.mark_stable();
            self.frozen = true;
            return true;
        }

        false
    }

    /// Return whether the profile has stabilized.
    #[must_use]
    pub fn is_stable(&self) -> bool {
        self.profile.is_stable
    }

    /// Borrow the current type profile snapshot.
    #[must_use]
    pub fn profile(&self) -> &TypeProfile {
        &self.profile
    }

    /// Consume the profiler and return the accumulated profile.
    #[must_use]
    pub fn take_profile(self) -> TypeProfile {
        self.profile
    }

    fn should_sample_current_state(&self) -> bool {
        let rate = u64::from(self.sampling_rate);
        (self.states_seen - 1) % rate == 0
    }
}

/// Re-export `classify_value` from the surviving `tla-jit-runtime` crate.
///
/// The canonical definition moved to `tla-jit-runtime::helpers` in Wave 11e of
/// epic #4251 Stage 2d so that `tla-check` can classify state-variable values
/// without pulling `tla-jit` (and its Cranelift forks) into its dep graph.
pub use tla_jit_runtime::classify_value;

#[must_use]
fn warmup_threshold_from_env() -> u64 {
    env::var(TYPE_WARMUP_ENV)
        .ok()
        .and_then(|value| value.parse::<u64>().ok())
        .unwrap_or(DEFAULT_WARMUP_THRESHOLD)
}

#[must_use]
fn sampling_rate_from_env() -> u32 {
    env::var(TYPE_SAMPLE_RATE_ENV)
        .ok()
        .and_then(|value| value.parse::<u32>().ok())
        .filter(|rate| *rate > 0)
        .unwrap_or(DEFAULT_SAMPLING_RATE)
}

#[cfg(test)]
mod tests {
    use super::{
        classify_value, SpecType, TypeProfile, TypeProfiler, VarTypeObservation,
        TYPE_SAMPLE_RATE_ENV, TYPE_WARMUP_ENV,
    };
    use num_bigint::BigInt;
    use std::{
        env,
        sync::{Arc, Mutex},
    };
    use tla_value::{FuncBuilder, IntIntervalFunc, IntervalValue, Value};

    static TYPE_PROFILE_ENV_LOCK: Mutex<()> = Mutex::new(());

    #[test]
    fn classify_value_maps_major_variants() {
        assert_eq!(classify_value(&Value::SmallInt(42)), SpecType::Int);
        assert_eq!(classify_value(&Value::Bool(true)), SpecType::Bool);
        assert_eq!(classify_value(&Value::string("hello")), SpecType::String);
        assert_eq!(
            classify_value(&Value::set([Value::SmallInt(1), Value::SmallInt(2)])),
            SpecType::FiniteSet
        );
        assert_eq!(
            classify_value(&Value::record([("field", Value::SmallInt(1))])),
            SpecType::Record
        );
        assert_eq!(
            classify_value(&Value::seq([Value::SmallInt(1), Value::SmallInt(2)])),
            SpecType::Seq
        );

        let mut func_builder = FuncBuilder::new();
        func_builder.insert(Value::SmallInt(1), Value::Bool(true));
        let func = Value::Func(Arc::new(func_builder.build()));
        assert_eq!(classify_value(&func), SpecType::Func);

        let int_func = Value::IntFunc(Arc::new(IntIntervalFunc::new(
            1,
            2,
            vec![Value::SmallInt(10), Value::SmallInt(20)],
        )));
        assert_eq!(classify_value(&int_func), SpecType::Func);

        assert_eq!(
            classify_value(&Value::tuple([Value::SmallInt(1), Value::Bool(false)])),
            SpecType::Tuple
        );

        let big_int = Value::Int(Arc::new(BigInt::from(i128::MAX)));
        assert_eq!(classify_value(&big_int), SpecType::Other);

        let interval = Value::Interval(Arc::new(IntervalValue::new(
            BigInt::from(1_u8),
            BigInt::from(3_u8),
        )));
        assert_eq!(classify_value(&interval), SpecType::Other);
    }

    #[test]
    fn var_type_observation_detects_monomorphic_values() {
        let mut observation = VarTypeObservation::default();
        assert!(!observation.is_monomorphic());
        assert_eq!(observation.dominant_type(), None);

        observation.record(SpecType::Int);
        observation.record(SpecType::Int);
        assert!(observation.is_monomorphic());
        assert_eq!(observation.dominant_type(), Some(SpecType::Int));
        assert_eq!(observation.sample_count, 2);

        observation.record(SpecType::Bool);
        assert!(!observation.is_monomorphic());
        assert_eq!(observation.dominant_type(), None);
        assert_eq!(observation.sample_count, 3);
    }

    #[test]
    fn type_profile_records_and_queries_monomorphism() {
        let mut profile = TypeProfile::new(2);
        profile.record_state(&[SpecType::Int, SpecType::Bool]);
        profile.record_state(&[SpecType::Int, SpecType::Bool]);

        assert_eq!(profile.var_count(), 2);
        assert_eq!(profile.total_states(), 2);
        assert!(profile.is_fully_monomorphic());
        assert_eq!(
            profile.monomorphic_types(),
            vec![Some(SpecType::Int), Some(SpecType::Bool)]
        );

        profile.record_state(&[SpecType::String, SpecType::Bool]);
        assert!(!profile.is_fully_monomorphic());
        assert_eq!(
            profile.monomorphic_types(),
            vec![None, Some(SpecType::Bool)]
        );

        profile.mark_stable();
        assert!(profile.is_stable);
    }

    #[test]
    fn type_profiler_warmup_and_stabilization_freeze_recording() {
        let mut profiler = TypeProfiler::with_config(2, 2, 1);

        assert!(!profiler.observe_state(&[SpecType::Int, SpecType::Bool]));
        assert!(!profiler.is_stable());
        assert_eq!(profiler.profile().total_states(), 1);

        assert!(profiler.observe_state(&[SpecType::Int, SpecType::Bool]));
        assert!(profiler.is_stable());
        assert_eq!(profiler.profile().total_states(), 2);

        assert!(!profiler.observe_state(&[SpecType::String, SpecType::Bool]));
        assert_eq!(profiler.states_seen, 3);
        assert_eq!(profiler.profile().total_states(), 2);
        assert!(profiler.frozen);

        let profile = profiler.take_profile();
        assert!(profile.is_stable);
        assert_eq!(
            profile.monomorphic_types(),
            vec![Some(SpecType::Int), Some(SpecType::Bool)]
        );
    }

    #[test]
    fn type_profiler_respects_sampling_rate() {
        let mut profiler = TypeProfiler::with_config(1, 2, 2);

        assert!(!profiler.observe_state(&[SpecType::Int]));
        assert_eq!(profiler.profile().total_states(), 1);

        assert!(!profiler.observe_state(&[SpecType::Bool]));
        assert_eq!(profiler.profile().total_states(), 1);

        assert!(profiler.observe_state(&[SpecType::Int]));
        assert!(profiler.is_stable());
        assert_eq!(profiler.profile().total_states(), 2);
        assert_eq!(profiler.states_seen, 3);
    }

    #[test]
    fn type_profiler_new_reads_environment_configuration() {
        let _guard = TYPE_PROFILE_ENV_LOCK
            .lock()
            .expect("type profile env test lock should not be poisoned");

        env::remove_var(TYPE_WARMUP_ENV);
        env::remove_var(TYPE_SAMPLE_RATE_ENV);

        env::set_var(TYPE_WARMUP_ENV, "7");
        env::set_var(TYPE_SAMPLE_RATE_ENV, "3");
        let profiler = TypeProfiler::new(1);

        assert_eq!(profiler.warmup_threshold, 7);
        assert_eq!(profiler.sampling_rate, 3);

        env::remove_var(TYPE_WARMUP_ENV);
        env::remove_var(TYPE_SAMPLE_RATE_ENV);
    }
}
