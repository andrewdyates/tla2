// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! TLC configuration accessors and SharedCtx field accessor methods.
//!
//! Part of #2739, #2764. Extracted from `eval_ctx_state.rs` as part of #3463.

use super::super::{EvalCtx, HashMap, TlcConfig, Value};
use crate::core::TlcRuntimeStats;
use rustc_hash::FxHashSet;
use std::sync::Arc;
use tla_core::name_intern::NameId;

impl EvalCtx {
    // ---- TLC Configuration Accessors ----

    /// Set the TLC configuration (for TLCGet("config"))
    pub fn set_tlc_config(&mut self, config: TlcConfig) {
        Arc::make_mut(&mut self.stable_mut().shared).tlc_config = config;
    }

    /// Set the current BFS exploration level (for TLCGet("level"))
    ///
    /// Part of #254: Animation specs like EWD840_anim use TLCGet("level") to
    /// display the current exploration depth in SVG output. Called by the model
    /// checker before evaluating states at each BFS depth.
    #[inline]
    pub fn set_tlc_level(&mut self, level: u32) {
        self.stable_mut().tlc_level = level;
    }

    /// Get the current TLC level (for debug diagnostics).
    #[inline]
    pub fn get_tlc_level(&self) -> u32 {
        self.tlc_level
    }

    /// Set dynamic TLC runtime statistics for TLCGet("stats") and TLCGet("diameter").
    pub fn set_tlc_runtime_stats(&self, stats: Option<TlcRuntimeStats>) {
        *self.runtime_state.tlc_runtime_stats.borrow_mut() = stats;
    }

    /// Get dynamic TLC runtime statistics, if any have been configured.
    pub fn tlc_runtime_stats(&self) -> Option<TlcRuntimeStats> {
        *self.runtime_state.tlc_runtime_stats.borrow()
    }

    /// Seed the simulation-only RNG used by TLC!/Randomization builtins.
    ///
    /// The stored state matches the LCG convention used by the model-checker
    /// simulation worker (`seed + 1`, then advance on every draw).
    pub fn set_simulation_random_seed(&self, seed: Option<u64>) {
        *self.runtime_state.simulation_rng_state.borrow_mut() =
            seed.map(|value| value.wrapping_add(1));
    }

    /// Return whether simulation randomness is currently enabled.
    pub fn simulation_random_active(&self) -> bool {
        self.runtime_state.simulation_rng_state.borrow().is_some()
    }

    /// Draw a simulation-only pseudo-random index using the shared evaluator RNG.
    /// Returns `None` when simulation RNG is not active (i.e., in BFS mode).
    pub fn next_simulation_random_index(&self, bound: usize) -> Option<usize> {
        let mut rng_state = self.runtime_state.simulation_rng_state.borrow_mut();
        let state = rng_state.as_mut()?;
        if bound == 0 {
            return Some(0);
        }
        *state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
        Some((*state % (bound as u64)) as usize)
    }

    /// Set a base directory for resolving relative file paths in IO builtins.
    ///
    /// This is typically the root spec's directory so operators like
    /// `JsonDeserialize` / `ndJsonDeserialize` behave like TLC when specs are run
    /// from a different working directory.
    pub fn set_input_base_dir(&self, dir: Option<std::path::PathBuf>) {
        *self.runtime_state.input_base_dir.borrow_mut() = dir;
    }

    /// Get the configured base directory for resolving relative input paths.
    pub fn input_base_dir(&self) -> Option<std::path::PathBuf> {
        self.runtime_state.input_base_dir.borrow().clone()
    }

    /// Set the pre-built TLCExt!Trace value for the current behavior prefix.
    ///
    /// Part of #1117: Animation/debugging specs use TLCExt!Trace to access the
    /// current trace. This should be called before evaluating invariants/actions
    /// when Trace is used in the spec.
    #[inline]
    pub fn set_tlc_trace_value(&mut self, value: Option<Value>) {
        self.stable_mut().tlc_trace_value = value.map(Arc::new);
    }

    /// Get the pre-built TLCExt!Trace value if set.
    ///
    /// Part of #1117: Returns the trace value that was set via set_tlc_trace_value,
    /// or None if not set (indicating Trace operator should error or return empty).
    #[inline]
    pub fn tlc_trace_value(&self) -> Option<&Value> {
        self.stable.tlc_trace_value.as_deref()
    }

    /// Get the index of a variable (if registered)
    #[inline]
    pub fn var_index(&self, name: &str) -> Option<crate::var_index::VarIndex> {
        self.stable.shared.var_registry.get(name)
    }

    /// Resolve a pre-lowered `StateVar` slot against the current registry.
    ///
    /// Most `StateVar` nodes are lowered against the same registry used at
    /// runtime, so the embedded `idx` remains valid. Some cross-module and
    /// transformed expressions can outlive the registry they were lowered
    /// against, leaving a stale slot while the variable name is still correct.
    /// In that case, prefer the current registry's slot for the same name.
    #[inline]
    pub(crate) fn resolve_state_var_slot(
        &self,
        name: &str,
        idx: u16,
        name_id: NameId,
    ) -> crate::var_index::VarIndex {
        let raw_idx = crate::var_index::VarIndex(idx);
        let registry = &self.shared.var_registry;
        // Part of #3063: use NameId (u32) comparison instead of string comparison.
        // This is the state-variable-access hot path — called millions of times.
        if raw_idx.as_usize() < registry.len()
            && name_id != NameId::INVALID
            && registry.name_id_at(raw_idx) == name_id
        {
            return raw_idx;
        }
        if name_id != NameId::INVALID {
            if let Some(actual) = registry.get_by_name_id(name_id) {
                return actual;
            }
        }
        registry.get(name).unwrap_or(raw_idx)
    }
}

// ---- SharedCtx field accessor methods (Part of #2739, #2764) ----

impl super::super::SharedCtx {
    /// Get the stable identifier for this shared context.
    #[inline]
    pub fn id(&self) -> u64 {
        self.id
    }

    /// Check if a name is a config-overridden constant.
    #[inline]
    pub fn is_config_constant(&self, name: &str) -> bool {
        self.config_constants.contains(name)
    }

    /// Check if a module name was imported via EXTENDS.
    #[inline]
    pub fn is_extended_module(&self, name: &str) -> bool {
        self.extended_module_names.contains(name)
    }

    /// Get a reference to the precomputed constants map.
    #[inline]
    pub fn precomputed_constants(&self) -> &HashMap<NameId, Value> {
        &self.precomputed_constants
    }

    /// Version for bytecode/cache invalidation when precomputed constants change.
    #[inline]
    pub fn precomputed_constants_version(&self) -> u64 {
        self.precomputed_constants_version
    }

    /// Get a mutable reference to the precomputed constants map.
    #[inline]
    pub fn precomputed_constants_mut(&mut self) -> &mut HashMap<NameId, Value> {
        self.precomputed_constants_version = self.precomputed_constants_version.saturating_add(1);
        &mut self.precomputed_constants
    }

    /// Check if an operator name came from a THEOREM/LEMMA declaration.
    /// Such operators are registered for reference resolution but should not
    /// be candidates for constant precomputation (TLC never evaluates theorem
    /// bodies during model checking). Part of #1105.
    #[inline]
    pub fn is_theorem_op(&self, name: &str) -> bool {
        self.theorem_op_names.contains(name)
    }

    /// Get the config constants set.
    #[inline]
    pub fn config_constants(&self) -> &FxHashSet<String> {
        &self.config_constants
    }

    /// Get a mutable reference to the config constants set.
    #[inline]
    pub fn config_constants_mut(&mut self) -> &mut FxHashSet<String> {
        &mut self.config_constants
    }

    /// Get the extended module names set.
    #[inline]
    pub fn extended_module_names(&self) -> &FxHashSet<String> {
        &self.extended_module_names
    }

    /// Get a mutable reference to the extended module names set.
    #[inline]
    pub fn extended_module_names_mut(&mut self) -> &mut FxHashSet<String> {
        &mut self.extended_module_names
    }
}
