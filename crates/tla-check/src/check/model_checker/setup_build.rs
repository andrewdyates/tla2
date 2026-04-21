// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Constructor implementation for `ModelChecker`.
//!
//! Extracted from `setup.rs` as part of #2359 Phase 2 decomposition.
//! Uses the shared `checker_setup::setup_checker_modules` pipeline (#810)
//! to perform module resolution, cfg rewrites, and operator/variable collection.

#[cfg(debug_assertions)]
use super::debug::debug_lazy_values_in_state_log_limit;
use super::debug::{
    debug_internal_fp_collision, debug_internal_fp_collision_limit, debug_seen_tlc_fp_dedup,
    debug_seen_tlc_fp_dedup_collision_limit, skip_liveness,
};
use super::{
    CapacityStatus, CheckpointState, CompiledSpec, CoverageState, DebugDiagnostics, Duration,
    ExplorationControl, FxHashMap, LivenessCacheState, LivenessMode, ModelChecker, Module,
    ModuleState, PeriodicLivenessState, RuntimeHooksState, StateStorage, SymmetryState,
    TraceLocationsStorage, TraceState,
};
use crate::check::model_checker::tir_parity::TirParityState;
use crate::state::fp_hashmap;
use crate::checker_setup::{setup_checker_modules, CheckerSetup, SetupOptions};
use crate::storage::factory::{FingerprintSetFactory, StorageConfig};
use crate::storage::SuccessorGraph;
use crate::Config;

impl<'a> ModelChecker<'a> {
    pub(super) fn new_with_extends_impl(
        module: &'a Module,
        extended_modules: &[&Module],
        config: &'a Config,
    ) -> Self {
        // Use the shared setup pipeline (Part of #810).
        let CheckerSetup {
            mut ctx,
            main_module,
            rewritten_exts,
            unqualified_modules: _,
            vars,
            op_defs,
            assumes,
            setup_error,
        } = setup_checker_modules(
            module,
            extended_modules,
            config,
            &SetupOptions {
                load_instances: true,
            },
        );

        // MC-specific: resolve state variable references in operators already loaded
        // in the EvalCtx. The shared pipeline registers vars and resolves op_defs,
        // but ctx-internal ops need a separate resolution pass.
        ctx.resolve_state_vars_in_loaded_ops();

        // Part of #4053: Determine if the spec can produce lazy values at runtime.
        // When false, the per-successor `has_lazy_state_value` scan is skipped.
        let spec_may_produce_lazy =
            crate::materialize::spec_may_produce_lazy_values(module, extended_modules);

        // Symmetry permutations will be computed lazily after constants are bound
        let symmetry_perms = Vec::new();
        let symmetry_mvperms = Vec::new();

        // Map FileId -> module name for TLC-style location rendering.
        let root_module_name = module.name.node.clone();
        let mut file_id_to_module_name: FxHashMap<tla_core::FileId, String> = FxHashMap::default();
        file_id_to_module_name.insert(module.name.span.file, root_module_name.clone());
        for ext_mod in extended_modules {
            file_id_to_module_name
                .entry(ext_mod.name.span.file)
                .or_insert_with(|| ext_mod.name.node.clone());
        }

        ModelChecker {
            config,
            module: ModuleState {
                root_name: root_module_name,
                file_id_to_name: file_id_to_module_name,
                file_id_to_path: FxHashMap::default(),
                setup_error,
                assumes,
                vars,
                op_defs,
            },
            ctx,
            state_storage: StateStorage {
                seen: fp_hashmap(),
                seen_fps: FingerprintSetFactory::create(StorageConfig::default())
                    .expect("in-memory storage creation is infallible"),
                store_full_states: false,
            },
            trace: TraceState {
                depths: fp_hashmap(),
                auto_create_trace_file: true,
                trace_file: None,
                trace_locs: TraceLocationsStorage::in_memory(),
                trace_degraded: false,
                current_parent_trace_loc: None,
                last_inserted_trace_loc: 0,
                lazy_trace_index: false,
                cached_init_name: None,
                cached_next_name: None,
                cached_resolved_next_name: None,
            },
            compiled: CompiledSpec {
                split_action_meta: None,
                cached_view_name: None,
                uses_trace: false,
                promoted_property_invariants: Vec::new(),
                state_property_violation_names: Vec::new(),
                eval_implied_actions: Vec::new(),
                eval_state_invariants: Vec::new(),
                promoted_implied_action_properties: Vec::new(),
                property_init_predicates: Vec::new(),
                action_constraint_analysis: None,
                pc_dispatch: None,
                pc_var_idx: None,
                spec_may_produce_lazy,
            },
            exploration: ExplorationControl {
                check_deadlock: config.check_deadlock,
                stuttering_allowed: true,
                continue_on_error: false,
                first_violation: None,
                first_action_property_violation: None,
                max_states: None,
                max_depth: None,
                memory_policy: None,
                disk_limit_bytes: None,
            },
            stats: super::CheckStats::default(),
            hooks: RuntimeHooksState {
                init_progress_callback: None,
                progress_callback: None,
                progress_interval: 1000,
                last_capacity_status: CapacityStatus::Normal,
            },
            liveness_cache: LivenessCacheState {
                // Part of #3176: use disk-backed successor graph when env var is set.
                successors: if crate::liveness::debug::use_disk_successors() {
                    SuccessorGraph::disk().expect("disk successor graph creation failed")
                } else {
                    SuccessorGraph::default()
                },
                successor_witnesses: fp_hashmap(),
                fairness: Vec::new(),
                fairness_state_checks: Vec::new(),
                fairness_action_checks: Vec::new(),
                fairness_max_tag: 0,
                action_provenance_tags: Vec::new(),
                action_fast_path_provenance_tags: Vec::new(),
                enabled_action_groups: Vec::new(),
                enabled_provenance: Vec::new(),
                subscript_action_pairs: Vec::new(),
                // Part of #3177: use disk-backed bitmask maps when env var is set.
                inline_state_bitmasks: if crate::liveness::debug::use_disk_bitmasks() {
                    crate::storage::StateBitmaskMap::disk()
                        .expect("disk state bitmask map creation failed")
                } else {
                    crate::storage::StateBitmaskMap::default()
                },
                inline_action_bitmasks: if crate::liveness::debug::use_disk_bitmasks() {
                    crate::storage::ActionBitmaskMap::disk()
                        .expect("disk action bitmask map creation failed")
                } else {
                    crate::storage::ActionBitmaskMap::default()
                },
                inline_property_plans: Vec::new(),
                #[cfg(feature = "jit")]
                compiled_liveness_batch: None,
                // Part of #3709: on-the-fly liveness regenerates successors
                // after BFS and therefore does not need the cached system graph.
                cache_for_liveness: !config.properties.is_empty()
                    && !skip_liveness()
                    && !config.liveness_execution.uses_on_the_fly(),
                init_states: Vec::new(),
                fp_only_replay_cache: None,
            },
            liveness_mode: LivenessMode::compute(
                !config.properties.is_empty(),
                false,
                false,
                false,
            ),
            coverage: CoverageState {
                collect: false,
                actions: Vec::new(),
                coverage_guided: false,
                tracker: None,
                mix_ratio: 8,
            },
            symmetry: SymmetryState {
                perms: symmetry_perms,
                mvperms: symmetry_mvperms,
                fp_cache: FxHashMap::default(),
                fp_cache_hits: 0,
                fp_cache_misses: 0,
                states_folded: 0,
                group_names: Vec::new(),
                auto_detected: false,
            },
            tir_parity: TirParityState::from_env(main_module, rewritten_exts),
            // Part of #3578: bytecode VM compilation happens after setup in
            // compile_invariant_bytecode(). Initialized None, populated lazily.
            bytecode: None,
            #[cfg(feature = "jit")]
            action_bytecode: None,
            // Part of #3582: JIT compilation happens after bytecode compilation.
            #[cfg(feature = "jit")]
            jit_cache: None,
            #[cfg(feature = "jit")]
            jit_state_scratch: Vec::new(),
            #[cfg(feature = "jit")]
            jit_all_compiled: false,
            #[cfg(feature = "jit")]
            jit_resolved_fns: None,
            #[cfg(feature = "jit")]
            jit_hits: 0,
            #[cfg(feature = "jit")]
            jit_misses: 0,
            #[cfg(feature = "jit")]
            jit_hit: 0,
            #[cfg(feature = "jit")]
            jit_fallback: 0,
            #[cfg(feature = "jit")]
            jit_not_compiled: 0,
            #[cfg(feature = "jit")]
            total_invariant_evals: 0,
            jit_verify_checked: 0,
            jit_verify_mismatches: 0,
            // Part of #3850: tiered JIT manager initialized in prepare_bfs_common
            // after action splitting discovers the action count.
            #[cfg(feature = "jit")]
            tier_manager: None,
            #[cfg(feature = "jit")]
            action_eval_counts: Vec::new(),
            #[cfg(feature = "jit")]
            action_succ_totals: Vec::new(),
            #[cfg(feature = "jit")]
            tier_promotion_history: Vec::new(),
            #[cfg(feature = "jit")]
            type_profile_scratch: Vec::new(),
            #[cfg(feature = "jit")]
            jit_next_state_cache: None,
            #[cfg(feature = "jit")]
            next_state_dispatch: tla_jit::NextStateDispatchCounters::default(),
            #[cfg(feature = "jit")]
            jit_cache_build_stats: None,
            #[cfg(feature = "jit")]
            pending_jit_compilation: None,
            #[cfg(feature = "jit")]
            recompilation_controller: tla_jit::RecompilationController::new(),
            #[cfg(feature = "jit")]
            jit_state_layout: None,
            #[cfg(feature = "jit")]
            jit_monolithic_disabled: false,
            #[cfg(feature = "jit")]
            jit_all_next_state_compiled: false,
            #[cfg(feature = "jit")]
            jit_has_any_promoted: false,
            #[cfg(feature = "jit")]
            jit_state_all_scalar: false,
            #[cfg(feature = "jit")]
            jit_validation_remaining: 100,
            #[cfg(feature = "jit")]
            jit_action_lookup_keys: Vec::new(),
            #[cfg(feature = "jit")]
            jit_action_out_scratch: Vec::new(),
            #[cfg(feature = "jit")]
            jit_perf_monitor: (0, 0, 0),
            #[cfg(feature = "jit")]
            jit_diag_enabled: {
                static JIT_DIAG: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
                *JIT_DIAG.get_or_init(|| std::env::var("TLA2_JIT_DIAG").is_ok())
            },
            #[cfg(feature = "jit")]
            compiled_bfs_step: None,
            #[cfg(feature = "jit")]
            compiled_bfs_level: None,
            checkpoint: CheckpointState {
                dir: None,
                interval: Duration::from_secs(300),
                last_time: None,
                spec_path: None,
                config_path: None,
                spec_hash: None,
                config_hash: None,
            },
            debug: DebugDiagnostics {
                seen_tlc_fp_dedup: if debug_seen_tlc_fp_dedup() {
                    Some(FxHashMap::default())
                } else {
                    None
                },
                seen_tlc_fp_dedup_collisions: 0,
                seen_tlc_fp_dedup_collision_limit: debug_seen_tlc_fp_dedup_collision_limit(),
                #[cfg(debug_assertions)]
                lazy_values_in_state_states: 0,
                #[cfg(debug_assertions)]
                lazy_values_in_state_values: 0,
                #[cfg(debug_assertions)]
                lazy_values_in_state_log_limit: debug_lazy_values_in_state_log_limit(),
                internal_fp_collision: if debug_internal_fp_collision() {
                    Some(FxHashMap::default())
                } else {
                    None
                },
                internal_fp_collisions: 0,
                internal_fp_collision_limit: debug_internal_fp_collision_limit(),
            },

            // POR fields - initialized empty, populated in setup_bfs if por_enabled
            por: super::PorState {
                independence: None,
                visibility: crate::por::VisibilitySet::new(),
                stats: crate::por::PorStats::default(),
            },
            // Part of #2752: periodic liveness checking (TLC doPeriodicWork pattern)
            periodic_liveness: PeriodicLivenessState::default(),
            // Part of #3717: portfolio racing verdict (None = standalone, no portfolio)
            portfolio_verdict: None,
            // Part of #3767: cooperative dual-engine state (None = standalone, no fused mode)
            #[cfg(feature = "z4")]
            cooperative: None,
            collision_detector: None,
            // Part of #3986: FlatState layout inferred after init state solving.
            flat_state_layout: None,
            // Part of #3986: FlatBfsBridge created after layout inference.
            flat_bfs_bridge: None,
            // Part of #4126: FlatBfsAdapter created alongside bridge.
            flat_bfs_adapter: None,
        }
    }
}
