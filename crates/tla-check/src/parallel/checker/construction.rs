// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! ParallelChecker constructor methods.

use super::*;

impl ParallelChecker {
    /// Create a new parallel model checker
    ///
    /// # Arguments
    /// * `module` - The TLA+ module to check
    /// * `config` - Model checking configuration
    /// * `num_workers` - Number of worker threads (0 = use number of CPUs)
    pub fn new(module: &Module, config: &Config, num_workers: usize) -> Self {
        Self::new_with_extends(module, &[], config, num_workers)
    }

    /// Create a new parallel model checker with additional loaded modules.
    ///
    /// Despite the historical name, `extended_modules` is **not** "EXTENDS-only".
    /// It must be a *loaded-module superset* for the whole run:
    ///
    /// - Include every non-stdlib module that may be referenced, via `EXTENDS` or `INSTANCE`
    ///   (including transitive and nested instance dependencies).
    /// - Put the modules that contribute to the **unqualified** operator namespace first, in a
    ///   TLC-shaped deterministic order (the `EXTENDS` closure and standalone `INSTANCE` imports).
    ///   Remaining loaded modules may follow in any deterministic order.
    ///
    /// Missing referenced non-stdlib modules are treated as a setup error.
    ///
    /// # Arguments
    /// * `module` - The TLA+ module to check
    /// * `extended_modules` - Modules that the main module extends
    /// * `config` - Model checking configuration
    /// * `num_workers` - Number of worker threads (0 = use number of CPUs)
    pub fn new_with_extends(
        module: &Module,
        extended_modules: &[&Module],
        config: &Config,
        num_workers: usize,
    ) -> Self {
        let num_workers = if num_workers == 0 {
            // Part of #3170: With the CAS-based fingerprint set replacing the
            // RwLock-backed Sharded backend, lock contention no longer caps
            // parallel scaling. Use all available cores.
            #[allow(clippy::redundant_closure_for_method_calls)]
            thread::available_parallelism()
                .map(|n| n.get())
                .unwrap_or(4)
        } else {
            num_workers
        };

        // Part of #810: Use shared setup pipeline directly. CheckerSetup already
        // collects vars/op_defs/assumes and resolves state variable references,
        // eliminating the redundant collect + resolve that the previous ModuleSetup
        // wrapper required.
        let CheckerSetup {
            ctx: _ctx,
            main_module,
            rewritten_exts,
            unqualified_modules: unqualified_modules_owned,
            vars,
            op_defs,
            assumes,
            mut setup_error,
        } = setup_checker_modules(
            module,
            extended_modules,
            config,
            &SetupOptions {
                load_instances: false,
            },
        );

        // Create VarRegistry for ArrayState <-> State conversion
        let var_registry = Arc::new(VarRegistry::from_names(vars.iter().cloned()));

        // Part of #4053: Determine if the spec can produce lazy values at runtime.
        let spec_may_produce_lazy =
            crate::materialize::spec_may_produce_lazy_values(module, extended_modules);

        // Part of #1121: Shared conservative Trace detector across checker paths.
        // Parallel mode needs this up-front because `check()` takes `&self`.
        let uses_trace = match compute_uses_trace(config, &op_defs) {
            Ok(val) => val,
            Err(e) => {
                if setup_error.is_none() {
                    setup_error = Some(e);
                }
                false
            }
        };

        // Use 256 shards (2^8) for fingerprint set - reduces lock contention in no-trace mode
        // With 256 shards and 8 workers, collision probability is ~3.1%
        let shard_bits = 8;
        // Part of #2955: Align DashMap shard counts with fingerprint set (256 shards).
        // Default DashMap uses num_cpus*4 shards (~64), causing higher collision
        // probability (~25%) vs 256 shards (~6%) per operation.
        let dashmap_shards = 1 << shard_bits; // 256

        // Part of #3304: propagate env-var parse errors into setup_error
        // instead of panicking.
        let fpset_mode = match parallel_fpset_mode() {
            Ok(mode) => mode,
            Err(e) => {
                if setup_error.is_none() {
                    setup_error = Some(e);
                }
                StorageMode::ShardedCas
            }
        };

        // Part of #3285: Allow overriding FPSet capacity via env var for diagnostic
        // benchmarking of L3 cache effects at different table sizes.
        let fp_capacity = {
            static FP_CAP: std::sync::OnceLock<Option<usize>> = std::sync::OnceLock::new();
            *FP_CAP.get_or_init(|| {
                std::env::var("TLA2_FP_CAPACITY")
                    .ok()
                    .and_then(|s| s.parse::<usize>().ok())
            })
        }
        .or(matches!(&fpset_mode, StorageMode::ShardedCas)
            .then_some(default_parallel_fpset_capacity(num_workers)));

        ParallelChecker {
            num_workers,
            seen: Arc::new(DashMap::with_hasher_and_shard_amount(
                FxBuildHasher::default(),
                dashmap_shards,
            )),
            // Part of #3170/#3285: default to CAS backend unless overridden
            // by TLA2_PARALLEL_FPSET env var for diagnostic benchmarking.
            seen_fps: FingerprintSetFactory::create(StorageConfig {
                mode: fpset_mode,
                shard_bits,
                capacity: fp_capacity,
                ..Default::default()
            })
            .expect("FPSet storage creation is infallible"),
            // Part of #3178: Per-worker sharded append log replaces DashMap.
            parent_log: Arc::new(ParentLog::new(num_workers)),
            var_registry,
            store_full_states: false,
            stop_flag: Arc::new(AtomicBool::new(false)),
            depth_limit_reached: Arc::new(AtomicBool::new(false)),
            work_remaining: Arc::new(AtomicUsize::new(0)),
            active_workers: Arc::new(AtomicUsize::new(0)),
            max_queue_depth: Arc::new(AtomicUsize::new(0)),
            max_depth: Arc::new(AtomicUsize::new(0)),
            total_transitions: Arc::new(AtomicUsize::new(0)),
            vars,
            op_defs: op_defs.into_iter().collect(),
            config: config.clone(),
            setup_error,
            check_deadlock: config.check_deadlock,
            module: Arc::new(main_module),
            extended_modules: Arc::new(rewritten_exts),
            unqualified_modules: Arc::new(unqualified_modules_owned),
            max_states_limit: None,
            max_depth_limit: None,
            progress_callback: None,
            // Part of #3247: 10s matches TLC's default progress interval.
            progress_interval_ms: 10_000,
            continue_on_error: false,
            first_violation: Arc::new(OnceLock::new()),
            first_action_property_violation: Arc::new(OnceLock::new()),
            first_violation_trace: Arc::new(OnceLock::new()),
            states_at_stop: Arc::new(OnceLock::new()),
            admitted_states: Arc::new(AtomicUsize::new(0)),
            collision_diagnostics: ParallelCollisionDiagnostics::from_env(dashmap_shards),
            assumes,
            uses_trace,
            input_base_dir: None,
            has_run: AtomicBool::new(false),
            successors: if config.has_liveness_properties() {
                Some(Arc::new(DashMap::with_hasher_and_shard_amount(
                    FxBuildHasher::default(),
                    dashmap_shards,
                )))
            } else {
                None
            },
            liveness_init_states: Arc::new(DashMap::with_hasher_and_shard_amount(
                FxBuildHasher::default(),
                dashmap_shards,
            )),
            // Part of #3011: Only allocate when both symmetry AND liveness are active.
            successor_witnesses: if config.has_liveness_properties() && config.symmetry.is_some() {
                Some(Arc::new(DashMap::with_hasher_and_shard_amount(
                    FxBuildHasher::default(),
                    dashmap_shards,
                )))
            } else {
                None
            },
            fairness: Vec::new(),
            stuttering_allowed: true,
            auto_create_trace_file: true,
            file_id_to_path: FxHashMap::default(),
            barrier: Arc::new(WorkBarrier::new(num_workers)),
            depths: Arc::new(DashMap::with_hasher_and_shard_amount(
                FxBuildHasher::default(),
                dashmap_shards,
            )),
            checkpoint_dir: None,
            checkpoint_interval: Duration::from_secs(300),
            periodic_liveness: PeriodicLivenessState::default(),
            checkpoint_spec_path: None,
            checkpoint_config_path: None,
            promoted_property_invariants: OnceLock::new(),
            memory_policy: None,
            disk_limit_bytes: None,
            internal_memory_limit: None,
            tier_state: OnceLock::new(),
            spec_may_produce_lazy,
        }
    }
}
