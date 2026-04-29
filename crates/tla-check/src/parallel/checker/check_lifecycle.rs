// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Check lifecycle helpers: shared state construction, model config building,
//! and trace reconstruction for the parallel checker.

use super::*;

impl ParallelChecker {
    /// Build the per-worker shared state (Arc clones of checker's atomic counters).
    pub(super) fn build_shared_state(
        &self,
        result_tx: &Sender<WorkerResult>,
        bootstrap_injector_budget: &Arc<AtomicUsize>,
        shared_frontier_tail_mode: &Arc<AtomicBool>,
    ) -> WorkerSharedState {
        WorkerSharedState {
            seen: Arc::clone(&self.seen),
            seen_fps: Arc::clone(&self.seen_fps),
            parent_log: Arc::clone(&self.parent_log),
            stop_flag: Arc::clone(&self.stop_flag),
            depth_limit_reached: Arc::clone(&self.depth_limit_reached),
            work_remaining: Arc::clone(&self.work_remaining),
            active_workers: Arc::clone(&self.active_workers),
            bootstrap_injector_budget: Arc::clone(bootstrap_injector_budget),
            shared_frontier_tail_mode: Arc::clone(shared_frontier_tail_mode),
            max_queue: Arc::clone(&self.max_queue_depth),
            max_depth_atomic: Arc::clone(&self.max_depth),
            total_transitions: Arc::clone(&self.total_transitions),
            result_tx: result_tx.clone(),
            first_violation: Arc::clone(&self.first_violation),
            first_action_property_violation: Arc::clone(&self.first_action_property_violation),
            states_at_stop: Arc::clone(&self.states_at_stop),
            admitted_states: Arc::clone(&self.admitted_states),
            collision_diagnostics: self.collision_diagnostics.as_ref().map(Arc::clone),
            successors: self.successors.as_ref().map(Arc::clone),
            successor_witnesses: self.successor_witnesses.as_ref().map(Arc::clone),
            barrier: Arc::clone(&self.barrier),
            depths: Arc::clone(&self.depths),
            tier_state: self.tier_state.get().map(Arc::clone),
        }
    }

    /// Build the per-worker model config from checker state.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn build_model_config(
        &self,
        next_name: &str,
        parallel_tir_next_selection: &Option<crate::tir_mode::ParallelNextTirEvalSelection>,
        expanded_op_defs: &FxHashMap<String, OperatorDef>,
        por_actions: &Arc<Vec<crate::coverage::DetectedAction>>,
        por_independence: &Option<Arc<crate::por::IndependenceMatrix>>,
        por_visibility: &Arc<crate::por::VisibilitySet>,
        var_registry: &Arc<VarRegistry>,
        eval_implied_actions: &Arc<Vec<(String, tla_core::Spanned<tla_core::ast::Expr>)>>,
        eval_state_invariants: &Arc<Vec<(String, tla_core::Spanned<tla_core::ast::Expr>)>>,
        cached_view_name: &Option<String>,
        mvperms: &Arc<Vec<crate::value::MVPerm>>,
        bytecode: &Option<Arc<tla_eval::bytecode_vm::CompiledBytecode>>,
        jit_cache: &Option<crate::parallel::SharedJitInvariantCache>,
        action_constraint_analysis: &Option<Arc<crate::checker_ops::ActionConstraintAnalysis>>,
    ) -> WorkerModelConfig {
        WorkerModelConfig {
            module: Arc::clone(&self.module),
            extended_modules: Arc::clone(&self.extended_modules),
            unqualified_modules: Arc::clone(&self.unqualified_modules),
            vars: self.vars.clone(),
            op_defs: expanded_op_defs.clone(),
            por_actions: Arc::clone(por_actions),
            por_independence: por_independence.clone(),
            por_visibility: Arc::clone(por_visibility),
            config: self.config.clone(),
            check_deadlock: self.check_deadlock,
            next_name: next_name.to_string(),
            parallel_tir_next_selection: parallel_tir_next_selection.clone(),
            num_workers: self.num_workers,
            max_states_limit: self.max_states_limit,
            max_depth_limit: self.max_depth_limit,
            store_full_states: self.store_full_states,
            uses_trace: self.uses_trace,
            var_registry: Arc::clone(var_registry),
            eval_implied_actions: Arc::clone(eval_implied_actions),
            eval_state_invariants: Arc::clone(eval_state_invariants),
            continue_on_error: self.continue_on_error,
            cached_view_name: cached_view_name.clone(),
            input_base_dir: self.input_base_dir.clone(),
            mvperms: Arc::clone(mvperms),
            // Part of #3233: track depths when checkpointing OR fp-only liveness needs them.
            track_depths: self.track_depths_enabled(),
            // Per-worker inline RSS check: critical threshold = limit × 0.95.
            critical_rss_bytes: self
                .memory_policy
                .as_ref()
                .map(|p| (p.limit_bytes() as f64 * 0.95) as usize),
            bytecode: bytecode.clone(),
            jit_cache: jit_cache.clone(),
            action_constraint_analysis: action_constraint_analysis.clone(),
            spec_may_produce_lazy: self.spec_may_produce_lazy,
        }
    }

    /// Reconstruct trace from initial state to given state.
    ///
    /// Part of #2749: widened from `pub(super)` to `pub(crate)` so the
    /// checkpoint resume path can reconstruct traces for saved violations.
    pub(crate) fn reconstruct_trace(&self, end_fp: Fingerprint) -> Trace {
        if !self.store_full_states {
            return Trace::new();
        }

        // Part of #3178: Build parent map from the append-only log (cold path).
        let parents = self.parent_log.build_map();

        let mut fps = Vec::new();
        let mut current = end_fp;

        // Walk back through parents
        while let Some(parent_fp) = parents.get(&current) {
            fps.push(current);
            current = *parent_fp;
        }
        fps.push(current); // Add initial state

        // Reverse to get initial -> end order
        fps.reverse();

        // Part of #1922: Use explicit loop instead of filter_map to detect and warn
        // about missing fingerprints in all build modes. Silent truncation of
        // counterexample traces is dangerous for a verification tool.
        let mut states: Vec<State> = Vec::with_capacity(fps.len());
        let mut missing_count: usize = 0;
        for fp in &fps {
            match self.seen.get(fp) {
                Some(entry) => states.push(entry.to_state(&self.var_registry)),
                None => missing_count += 1,
            }
        }
        if missing_count > 0 {
            // eprintln is intentional: tla-check has no tracing subscriber, so
            // tracing::warn! would be silently dropped. This warning MUST reach
            // users in release builds — it indicates a truncated counterexample.
            eprintln!(
                "Warning: reconstruct_trace: {missing_count}/{} fingerprints not found in \
                 seen set — counterexample trace may be incomplete",
                fps.len()
            );
        }

        Trace::from_states(states)
    }

    /// Reconstruct trace and identify action labels for each transition.
    ///
    /// Part of #2470: wraps `reconstruct_trace` with action label identification
    /// from the shared `checker_ops::identify_action_labels`, giving the parallel
    /// checker parity with the sequential checker's trace output.
    pub(super) fn reconstruct_trace_with_labels(
        &self,
        end_fp: Fingerprint,
        ctx: &mut EvalCtx,
    ) -> Trace {
        let trace = self.reconstruct_trace(end_fp);
        if trace.is_empty() {
            return trace;
        }

        let next_name = match &self.config.next {
            Some(name) => name.as_str(),
            None => return trace,
        };

        let label_ctx = crate::checker_ops::ActionLabelCtx {
            next_name,
            next_def: self.op_defs.get(next_name),
            file_id_to_path: &self.file_id_to_path,
            module_name: &self.module.name.node,
        };

        let labels = crate::checker_ops::identify_action_labels(ctx, &label_ctx, &trace.states);
        Trace::from_states_with_labels(trace.states, labels)
    }
}
