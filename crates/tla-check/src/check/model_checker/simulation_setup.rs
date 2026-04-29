// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared setup helpers for simulation-mode execution.

use super::simulation_types::{SimulationConfig, SimulationStats};
use super::{
    bind_constants_from_config, build_ident_hints, precompute_constant_operators,
    promote_env_constants_to_precomputed, ArrayState, CheckError, CheckResult, ModelChecker, State,
};
use crate::eval::TlcRuntimeStats;
use crate::{ConfigCheckError, EvalCheckError};

impl ModelChecker<'_> {
    pub(super) fn update_simulation_runtime_stats(
        &self,
        stats: &SimulationStats,
        distinct_states: usize,
        current_trace: usize,
    ) {
        self.ctx.set_tlc_runtime_stats(Some(TlcRuntimeStats::new(
            stats.states_visited as i64,
            distinct_states as i64,
            0,
            current_trace as i64,
            current_trace as i64,
        )));
    }

    pub(super) fn prepare_simulation(
        &mut self,
        sim_config: &SimulationConfig,
    ) -> Result<(Vec<State>, String), CheckError> {
        self.sync_simulation_tlc_config(sim_config);
        self.prepare_simulation_constants()?;
        self.validate_simulation_model()?;
        let (init_name, next_name) = self.resolve_simulation_operator_names()?;
        self.ensure_simulation_assumes_hold()?;
        self.detect_simulation_trace_usage()?;
        let initial_states = self.generate_constrained_initial_states(&init_name)?;
        Ok((initial_states, next_name))
    }

    fn sync_simulation_tlc_config(&mut self, sim_config: &SimulationConfig) {
        // Sync TLC config for TLCGet("config") support - use "generate" mode for simulation
        self.sync_tlc_config("generate");
        // Part of #3076: propagate simulation-specific config to TLCGet("config")
        let mut tlc_config = self.ctx.shared().tlc_config.clone();
        tlc_config.traces = sim_config.num_traces as i64;
        tlc_config.seed = sim_config.seed.unwrap_or(0) as i64;
        self.ctx.set_tlc_config(tlc_config);
    }

    fn prepare_simulation_constants(&mut self) -> Result<(), CheckError> {
        // Bind constants from config before checking.
        bind_constants_from_config(&mut self.ctx, self.config)
            .map_err(|error| CheckError::from(EvalCheckError::Eval(error)))?;
        // Part of #3078: Must match prepare_bfs_common setup — without these,
        // eval_ident's fast path skips env.get() for interned names when state_env
        // is set, causing "Undefined variable" errors for constants like N.
        // See run_gen.rs:47-48 for the same pattern in the BFS pilot path.
        precompute_constant_operators(&mut self.ctx);
        promote_env_constants_to_precomputed(&mut self.ctx);
        build_ident_hints(&mut self.ctx);
        Ok(())
    }

    fn validate_simulation_model(&self) -> Result<(), CheckError> {
        if self.module.vars.is_empty() {
            return Err(ConfigCheckError::NoVariables.into());
        }
        for inv_name in &self.config.invariants {
            if !self.ctx.has_op(inv_name) {
                return Err(ConfigCheckError::MissingInvariant(inv_name.clone()).into());
            }
        }
        Ok(())
    }

    fn resolve_simulation_operator_names(&self) -> Result<(String, String), CheckError> {
        let init_name = self
            .config
            .init
            .as_ref()
            .ok_or(ConfigCheckError::MissingInit)?;
        // Part of #3078: Apply CONSTANT operator replacements (e.g., `Init <- SimInit`).
        // BFS does this at run_gen.rs:50; simulation was missing it, causing the original
        // operator body to be used instead of the replacement.
        let init_name = self.ctx.resolve_op_name(init_name).to_string();

        let next_name = self
            .config
            .next
            .as_ref()
            .ok_or(ConfigCheckError::MissingNext)?;
        let next_name = self.ctx.resolve_op_name(next_name).to_string();

        Ok((init_name, next_name))
    }

    fn ensure_simulation_assumes_hold(&self) -> Result<(), CheckError> {
        // Check ASSUME statements before state exploration (matches TLC semantics).
        // Part of #3076: simulation path was missing this check, causing assume_violation
        // errors to only appear when diagnose ran specs under `tla2 check` instead of simulate.
        match self.check_assumes() {
            Some(result) => Err(assume_failure_to_error(result)),
            None => Ok(()),
        }
    }

    fn detect_simulation_trace_usage(&mut self) -> Result<(), CheckError> {
        // Part of #1121: Shared conservative Trace detector across checker paths.
        self.compiled.uses_trace =
            super::trace_detect::compute_uses_trace(self.config, &self.module.op_defs)?;
        Ok(())
    }

    fn generate_constrained_initial_states(
        &mut self,
        init_name: &str,
    ) -> Result<Vec<State>, CheckError> {
        // Part of #3079: Use simulation-specific fallback that defaults unconstrained
        // variables to 0, matching TLC's -generate behavior for specs like
        // EWD998ChanID_export where MCInit leaves some variables unconstrained.
        let initial_states = self.generate_initial_states_simulation_fallback(init_name)?;
        let registry = self.ctx.var_registry().clone();
        let mut constrained_initial_states = Vec::with_capacity(initial_states.len());
        for state in initial_states {
            let arr = ArrayState::from_state(&state, &registry);
            if self.check_state_constraints_array(&arr)? {
                constrained_initial_states.push(state);
            }
        }
        if constrained_initial_states.is_empty() {
            return Err(ConfigCheckError::InitCannotEnumerate(
                "No valid initial states after constraint filtering".to_string(),
            )
            .into());
        }
        Ok(constrained_initial_states)
    }
}

fn assume_failure_to_error(result: CheckResult) -> CheckError {
    match result {
        CheckResult::Error { error, .. } => error,
        other => ConfigCheckError::Setup(format!(
            "ASSUME check returned unexpected result: {:?}",
            other.stats()
        ))
        .into(),
    }
}
