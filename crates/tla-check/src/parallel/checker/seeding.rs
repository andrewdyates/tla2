// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Parallel checker initial-state seeding and worker spawn phase.
//!
//! Part of #2814: Uses `BfsWorkItem` trait to handle both HandleState and
//! ArrayState modes in a single generic function, eliminating ~220 lines of
//! duplication between the two branches.

use super::*;
use crate::parallel::worker::SharedFrontier;
use crate::ConfigCheckError;

impl ParallelChecker {
    #[allow(clippy::result_large_err)]
    pub(super) fn seed_and_spawn_workers(
        &self,
        prep: &mut CheckPreparation,
    ) -> Result<CheckRuntime, CheckResult> {
        let initial_states = prep.initial_states.take().ok_or_else(|| {
            CheckResult::from_error(
                crate::RuntimeCheckError::Internal("initial_states already consumed".into()).into(),
                CheckStats::default(),
            )
        })?;
        let (result_tx, result_rx) = bounded::<WorkerResult>(self.num_workers);

        let (handles, num_initial) = if use_handle_state() {
            // Part of #3212: create per-worker interner shards.
            let interner_bank = Arc::new(crate::intern::HandleStateInternerBank::new(
                self.num_workers,
            ));
            let mode = crate::parallel::worker::HandleStateMode { interner_bank };
            self.seed_and_spawn_typed::<HandleState>(prep, initial_states, &result_tx, mode)?
        } else {
            let mode = crate::parallel::worker::ArrayStateMode;
            self.seed_and_spawn_typed::<ArrayState>(prep, initial_states, &result_tx, mode)?
        };

        // Drop our sender so result_rx will close when all workers are done
        drop(result_tx);

        let jit_compiled_invariants = prep.jit_cache.as_ref().map_or(0, |cache| cache.len());

        Ok(CheckRuntime {
            result_rx,
            handles,
            num_initial,
            start_time: Instant::now(),
            jit_compiled_invariants,
        })
    }

    /// Generic seeding and worker spawning over `BfsWorkItem` types.
    ///
    /// Creates work-stealing queues of type `(T, depth)`, seeds initial states
    /// through the full pipeline (constraint → materialize → fingerprint → dedup
    /// → invariant), converts via `T::from_array_state()`, and spawns workers
    /// with `run_worker_unified`.
    #[allow(clippy::result_large_err)]
    fn seed_and_spawn_typed<T: BfsWorkItem>(
        &self,
        prep: &mut CheckPreparation,
        initial_states: InitialStates,
        result_tx: &Sender<WorkerResult>,
        mode: T::Mode,
    ) -> Result<(Vec<thread::JoinHandle<()>>, usize), CheckResult>
    where
        T::Mode: Clone,
    {
        // Split borrows on prep fields: immutable refs for spawning, mutable for ctx.
        let next_name = &prep.resolved_next_name;
        let parallel_tir_next_selection = &prep.parallel_tir_next_selection;
        let cached_view_name = &prep.cached_view_name;
        let por_actions = &prep.por_actions;
        let por_independence = &prep.por_independence;
        let por_visibility = &prep.por_visibility;

        let eval_implied_actions = &prep.eval_implied_actions;
        let eval_state_invariants = &prep.eval_state_invariants;
        let var_registry = &prep.var_registry;
        let expanded_op_defs = &prep.expanded_op_defs;
        let mvperms = &prep.mvperms;
        let bytecode = &prep.bytecode;
        let jit_cache = &prep.jit_cache;
        let action_constraint_analysis = &prep.action_constraint_analysis;
        let seed_ctx = SeedingCtx {
            var_registry,
            cached_view_name,
            property_init_predicates: &prep.property_init_predicates,
            mvperms,
            promoted_property_invariants: &prep.promoted_property_invariants,
        };
        let ctx = &mut prep.ctx;

        // Part of #3266: bounded multi-worker BFS needs a depth-layered
        // frontier so first discovery depth stays equal to minimum BFS depth.
        if self.max_depth_limit.is_some() && self.num_workers > 1 {
            let frontier = Arc::new(SharedFrontier::<T>::new_depth_layered(self.num_workers));
            return self.seed_and_spawn_shared_queue::<T>(
                ctx,
                initial_states,
                &seed_ctx,
                result_tx,
                frontier,
                mode,
                next_name,
                parallel_tir_next_selection,
                expanded_op_defs,
                por_actions,
                por_independence,
                por_visibility,
                var_registry,
                eval_implied_actions,
                eval_state_invariants,
                cached_view_name,
                mvperms,
                bytecode,
                jit_cache,
                action_constraint_analysis,
            );
        }

        // Part of #3258: branch on queue topology before creating queues.
        if use_shared_queue() {
            let frontier = Arc::new(SharedFrontier::<T>::new(self.num_workers));
            return self.seed_and_spawn_shared_queue::<T>(
                ctx,
                initial_states,
                &seed_ctx,
                result_tx,
                frontier,
                mode,
                next_name,
                parallel_tir_next_selection,
                expanded_op_defs,
                por_actions,
                por_independence,
                por_visibility,
                var_registry,
                eval_implied_actions,
                eval_state_invariants,
                cached_view_name,
                mvperms,
                bytecode,
                jit_cache,
                action_constraint_analysis,
            );
        }

        // Create work-stealing queues
        let injector: Arc<Injector<(T, usize)>> = Arc::new(Injector::new());
        let mut workers: Vec<Worker<(T, usize)>> = Vec::new();
        let mut stealers: Vec<Stealer<(T, usize)>> = Vec::new();

        for _ in 0..self.num_workers {
            let worker = Worker::new_fifo();
            stealers.push(worker.stealer());
            workers.push(worker);
        }

        let stealers = Arc::new(stealers);
        let frontier = Arc::new(SharedFrontier::<T>::new(self.num_workers));

        // Seed initial states into local queues (avoids injecting huge frontiers
        // into Injector). Each state goes through process_initial_state for the
        // full pipeline, then is converted to T via BfsWorkItem::from_array_state.
        let mut num_initial: usize = 0;

        match initial_states {
            InitialStates::Bulk(storage) => {
                let total = bulk_len_as_u32(&storage)?;
                for idx in 0..total {
                    let mut arr = ArrayState::from_values(storage.get_state(idx).to_vec());

                    match self.process_initial_state(ctx, &mut arr, None, &seed_ctx, num_initial)? {
                        Some(_fp) => {
                            // Part of #3212: compute worker_idx before conversion
                            // so HandleState knows its owner shard.
                            let worker_idx = num_initial % self.num_workers;
                            let item = T::from_array_state(arr, var_registry, &mode, worker_idx);
                            workers[worker_idx].push((item, 0));
                            num_initial += 1;
                        }
                        None => {}
                    }
                }
            }
            InitialStates::Vec(states) => {
                for state in states {
                    let mut arr = ArrayState::from_state(&state, var_registry);

                    match self.process_initial_state(
                        ctx,
                        &mut arr,
                        Some(&state),
                        &seed_ctx,
                        num_initial,
                    )? {
                        Some(_fp) => {
                            // Part of #3212: compute worker_idx before conversion
                            // so HandleState knows its owner shard.
                            let worker_idx = num_initial % self.num_workers;
                            let item = T::from_array_state(arr, var_registry, &mode, worker_idx);
                            workers[worker_idx].push((item, 0));
                            num_initial += 1;
                        }
                        None => {}
                    }
                }
            }
        }

        self.work_remaining.store(num_initial, Ordering::Release);
        let bootstrap_injector_budget = Arc::new(AtomicUsize::new(
            crate::parallel::worker::initial_bootstrap_injector_budget(
                num_initial,
                self.num_workers,
            ),
        ));
        let shared_frontier_tail_mode = Arc::new(AtomicBool::new(false));

        // Spawn worker threads
        let mut handles = Vec::new();

        for (worker_id, local_queue) in workers.into_iter().enumerate() {
            let shared = self.build_shared_state(
                result_tx,
                &bootstrap_injector_budget,
                &shared_frontier_tail_mode,
            );
            let model = self.build_model_config(
                next_name,
                parallel_tir_next_selection,
                expanded_op_defs,
                por_actions,
                por_independence,
                por_visibility,
                var_registry,
                eval_implied_actions,
                eval_state_invariants,
                cached_view_name,
                mvperms,
                bytecode,
                jit_cache,
                action_constraint_analysis,
            );
            let injector = Arc::clone(&injector);
            let stealers = Arc::clone(&stealers);
            let frontier = Arc::clone(&frontier);
            let worker_mode = mode.clone();

            let handle = thread::Builder::new()
                .stack_size(16 * 1024 * 1024)
                .spawn(move || {
                    crate::eval::set_enabled_hook(crate::enabled::eval_enabled_cp);
                    run_worker_unified(
                        worker_id,
                        local_queue,
                        injector,
                        stealers,
                        frontier,
                        shared,
                        model,
                        worker_mode,
                    );
                })
                .map_err(|e| {
                    CheckResult::from_error(
                        ConfigCheckError::Setup(format!(
                            "Failed to spawn worker thread {}: {}",
                            worker_id, e
                        ))
                        .into(),
                        CheckStats::default(),
                    )
                })?;
            handles.push(handle);
        }

        Ok((handles, num_initial))
    }

    /// Shared-queue seeding and worker spawning (Part of #3258).
    ///
    /// Seeds initial states into a single shared FIFO frontier and spawns
    /// workers with [`run_worker_shared_queue`] instead of work-stealing.
    #[allow(clippy::too_many_arguments, clippy::result_large_err)]
    fn seed_and_spawn_shared_queue<T: BfsWorkItem>(
        &self,
        ctx: &mut crate::eval::EvalCtx,
        initial_states: InitialStates,
        seed_ctx: &SeedingCtx<'_>,
        result_tx: &Sender<WorkerResult>,
        frontier: Arc<SharedFrontier<T>>,
        mode: T::Mode,
        next_name: &str,
        parallel_tir_next_selection: &Option<crate::tir_mode::ParallelNextTirEvalSelection>,
        expanded_op_defs: &FxHashMap<String, tla_core::ast::OperatorDef>,
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
    ) -> Result<(Vec<thread::JoinHandle<()>>, usize), CheckResult>
    where
        T::Mode: Clone,
    {
        let mut num_initial: usize = 0;

        // Seed initial states into the shared frontier (same pipeline as
        // work-stealing, but all items go to one global FIFO).
        match initial_states {
            InitialStates::Bulk(storage) => {
                let total = bulk_len_as_u32(&storage)?;
                for idx in 0..total {
                    let mut arr = ArrayState::from_values(storage.get_state(idx).to_vec());
                    match self.process_initial_state(ctx, &mut arr, None, seed_ctx, num_initial)? {
                        Some(_fp) => {
                            let worker_idx = num_initial % self.num_workers;
                            let item = T::from_array_state(arr, var_registry, &mode, worker_idx);
                            frontier.push_single(item, 0);
                            num_initial += 1;
                        }
                        None => {}
                    }
                }
            }
            InitialStates::Vec(states) => {
                for state in states {
                    let mut arr = ArrayState::from_state(&state, var_registry);
                    match self.process_initial_state(
                        ctx,
                        &mut arr,
                        Some(&state),
                        seed_ctx,
                        num_initial,
                    )? {
                        Some(_fp) => {
                            let worker_idx = num_initial % self.num_workers;
                            let item = T::from_array_state(arr, var_registry, &mode, worker_idx);
                            frontier.push_single(item, 0);
                            num_initial += 1;
                        }
                        None => {}
                    }
                }
            }
        }

        self.work_remaining.store(num_initial, Ordering::Release);
        // Shared-queue mode still needs a bootstrap_injector_budget for
        // build_shared_state, but it is unused by SharedQueueTransport.
        let bootstrap_injector_budget = Arc::new(AtomicUsize::new(0));
        let shared_frontier_tail_mode = Arc::new(AtomicBool::new(false));

        let mut handles = Vec::new();
        for worker_id in 0..self.num_workers {
            let shared = self.build_shared_state(
                result_tx,
                &bootstrap_injector_budget,
                &shared_frontier_tail_mode,
            );
            let model = self.build_model_config(
                next_name,
                parallel_tir_next_selection,
                expanded_op_defs,
                por_actions,
                por_independence,
                por_visibility,
                var_registry,
                eval_implied_actions,
                eval_state_invariants,
                cached_view_name,
                mvperms,
                bytecode,
                jit_cache,
                action_constraint_analysis,
            );
            let frontier = Arc::clone(&frontier);
            let worker_mode = mode.clone();

            let handle = thread::Builder::new()
                .stack_size(16 * 1024 * 1024)
                .spawn(move || {
                    crate::eval::set_enabled_hook(crate::enabled::eval_enabled_cp);
                    run_worker_shared_queue(worker_id, frontier, shared, model, worker_mode);
                })
                .map_err(|e| {
                    CheckResult::from_error(
                        ConfigCheckError::Setup(format!(
                            "Failed to spawn worker thread {}: {}",
                            worker_id, e
                        ))
                        .into(),
                        CheckStats::default(),
                    )
                })?;
            handles.push(handle);
        }

        Ok((handles, num_initial))
    }
}
