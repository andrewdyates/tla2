// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! No-trace (fingerprint-only) BFS mode: initial state generation and BFS exploration loop.
//!
//! This module handles the fingerprint-only path where states are not stored in a HashMap
//! and traces are reconstructed from a trace file when needed.

use super::bfs::{FingerprintOnlyStorage, NoTraceQueueEntry};
#[cfg(debug_assertions)]
use super::debug::debug_states;
use super::frontier::BfsFrontier;
use super::{
    check_error_to_result, ArrayState, BulkStateHandle, BulkStateStorage, CheckResult,
    ModelChecker, VecDeque,
};
use crate::ConfigCheckError;

impl<'a> ModelChecker<'a> {
    /// Generate initial states for no-trace (fingerprint-only) BFS mode.
    ///
    /// Tries streaming enumeration first (avoids Vec<State> OrdMap overhead),
    /// then falls back to the Vec<State> path. Returns (BulkStateStorage, initial queue)
    /// or an early CheckResult on error/violation.
    #[allow(clippy::result_large_err, clippy::type_complexity)]
    fn init_states_no_trace(
        &mut self,
        init_name: &str,
        registry: &crate::var_index::VarRegistry,
        bulk_scratch: &mut ArrayState,
    ) -> Result<(BulkStateStorage, VecDeque<(NoTraceQueueEntry, usize, u64)>), CheckResult> {
        // Part of #3305: streaming invariant scan — O(1) memory per state.
        // For specs like Einstein (~199M init states), this finds invariant
        // violations without materializing the full state space into BulkStateStorage.
        self.scan_init_invariants_streaming(init_name)?;

        let init_generated: usize;
        let result = if let Some(bulk_init) =
            self.solve_predicate_for_states_to_bulk_prechecked(init_name)?
        {
            let init_generated_count = bulk_init.enumeration.generated;
            let storage = bulk_init.storage;
            let mut queue: VecDeque<(NoTraceQueueEntry, usize, u64)> = VecDeque::new();
            queue.reserve(storage.len());

            let num_states = u32::try_from(storage.len()).map_err(|_| {
                CheckResult::from_error(
                    ConfigCheckError::Setup(format!(
                        "too many initial states ({}) for u32 BulkStateStorage index",
                        storage.len()
                    ))
                    .into(),
                    self.stats.clone(),
                )
            })?;

            for idx in 0..num_states {
                bulk_scratch.overwrite_from_slice(storage.get_state(idx));
                let fp = self.prepare_prechecked_initial_state(bulk_scratch)?;

                self.debug_record_seen_state_array(fp, bulk_scratch, 0);
                if !self.mark_state_seen_fp_only_checked(fp, None, 0)? {
                    debug_eprintln!(debug_states(), "DUP INIT STATE {}", fp);
                    continue;
                }
                if self.track_liveness_init_states() {
                    self.liveness_cache
                        .init_states
                        .push((fp, bulk_scratch.clone()));
                }
                let trace_loc = self.trace.last_inserted_trace_loc;
                #[cfg(debug_assertions)]
                if debug_states() {
                    let state = bulk_scratch.to_state(registry);
                    eprintln!("INIT STATE {} via Init: {:?}", fp, state);
                }
                queue.push_back((
                    NoTraceQueueEntry::Bulk(BulkStateHandle::with_fingerprint(idx, fp)),
                    0,
                    trace_loc,
                ));
            }

            init_generated = init_generated_count;
            self.stats.initial_states = self.states_count();
            (storage, queue)
        } else {
            match self.generate_initial_states_to_bulk(init_name) {
                Ok(Some(bulk_init)) => {
                    let init_generated_count = bulk_init.enumeration.generated;
                    let storage = bulk_init.storage;
                    // Streaming successful! Process states from BulkStateStorage directly.
                    let mut queue: VecDeque<(NoTraceQueueEntry, usize, u64)> = VecDeque::new();
                    queue.reserve(storage.len());

                    let num_states = u32::try_from(storage.len()).map_err(|_| {
                        CheckResult::from_error(
                            ConfigCheckError::Setup(format!(
                                "too many initial states ({}) for u32 BulkStateStorage index",
                                storage.len()
                            ))
                            .into(),
                            self.stats.clone(),
                        )
                    })?;

                    // Part of #254: Set TLC level for TLCGet("level") - TLC uses 1-based indexing
                    // Initial states are at level 1 in TLC
                    self.ctx.set_tlc_level(1);

                    for idx in 0..num_states {
                        // Load state into scratch buffer for constraint/invariant checking
                        bulk_scratch.overwrite_from_slice(storage.get_state(idx));

                        // Part of #2473: Use shared check_init_state helper
                        let (fp, violation) = match self.check_init_state(bulk_scratch, true)? {
                            Some(result) => result,
                            None => continue,
                        };

                        // Part of #2708: atomic test-and-set — skip if already present.
                        self.debug_record_seen_state_array(fp, bulk_scratch, 0);
                        if !self.mark_state_seen_fp_only_checked(fp, None, 0)? {
                            debug_eprintln!(debug_states(), "DUP INIT STATE {}", fp);
                            continue;
                        }
                        // Part of #3175: cache init states for post-BFS liveness
                        if self.track_liveness_init_states() {
                            self.liveness_cache
                                .init_states
                                .push((fp, bulk_scratch.clone()));
                        }
                        // Part of #2881 Step 3: capture trace_loc for queue entry.
                        let trace_loc = self.trace.last_inserted_trace_loc;
                        if let Some(violation) = violation {
                            self.handle_init_violation(violation, fp, || {
                                bulk_scratch.to_state(registry)
                            })?;
                        } else {
                            #[cfg(debug_assertions)]
                            if debug_states() {
                                let state = bulk_scratch.to_state(registry);
                                eprintln!("INIT STATE {} via Init: {:?}", fp, state);
                            }
                        }
                        queue.push_back((
                            NoTraceQueueEntry::Bulk(BulkStateHandle::with_fingerprint(idx, fp)),
                            0,
                            trace_loc,
                        ));
                    }

                    init_generated = init_generated_count;
                    self.stats.initial_states = self.states_count();
                    (storage, queue)
                }
                // Part of #1433: Propagate actual eval errors instead of silently falling back.
                // Part of #2789: Route through check_error_to_result so ExitRequested
                // maps to LimitReached(Exit) instead of being misreported as Error.
                Err(e) => {
                    return Err(check_error_to_result(e, &self.stats));
                }
                Ok(None) => {
                    // Streaming not possible - fall back to Vec<State> path
                    let initial_states = self.constrained_initial_states(init_name)?;
                    // Part of #2163: capture pre-dedup count for states_generated reporting
                    init_generated = initial_states.len();

                    // Part of #254: Set TLC level for TLCGet("level") - TLC uses 1-based indexing
                    // Initial states are at level 1 in TLC
                    self.ctx.set_tlc_level(1);

                    // Convert to BulkStateStorage and check invariants in a single pass
                    // Part of #595: Handle continue_on_error for initial states
                    let mut bulk_storage =
                        BulkStateStorage::new(registry.len(), initial_states.len());
                    let mut queue: VecDeque<(NoTraceQueueEntry, usize, u64)> = VecDeque::new();
                    queue.reserve(initial_states.len());

                    for state in initial_states {
                        // Part of #2473: Use shared check_init_state helper
                        // check_constraints=false: already filtered by constrained_initial_states
                        let mut arr = ArrayState::from_state(&state, registry);
                        let (fp, violation) = match self.check_init_state(&mut arr, false)? {
                            Some(result) => result,
                            None => continue,
                        };

                        // Part of #2708: atomic test-and-set — push state then check
                        // dedup via InsertOutcome (skip enqueue if already present).
                        let idx = bulk_storage.push_from_state(&state, registry);
                        self.maybe_debug_record_seen_state(fp, &state, 0);
                        if !self.mark_state_seen_fp_only_checked(fp, None, 0)? {
                            debug_eprintln!(debug_states(), "DUP INIT STATE {}", fp);
                            continue;
                        }
                        // Part of #3175: cache init states for post-BFS liveness
                        if self.track_liveness_init_states() {
                            self.liveness_cache.init_states.push((fp, arr.clone()));
                        }
                        // Part of #2881 Step 3: capture trace_loc for queue entry.
                        let trace_loc = self.trace.last_inserted_trace_loc;
                        if let Some(violation) = violation {
                            self.handle_init_violation(violation, fp, || state.clone())?;
                        } else {
                            debug_eprintln!(
                                debug_states(),
                                "INIT STATE {} via Init: {:?}",
                                fp,
                                state
                            );
                        }
                        queue.push_back((
                            NoTraceQueueEntry::Bulk(BulkStateHandle::with_fingerprint(idx, fp)),
                            0,
                            trace_loc,
                        ));
                    }

                    self.stats.initial_states = self.states_count();
                    (bulk_storage, queue)
                }
            }
        };

        // Initialize states_found with initial states count
        self.stats.states_found = self.states_count();
        // Part of #2163: report both pre-dedup generated count and post-dedup distinct count
        self.report_init_progress(init_generated, self.stats.states_found);
        Ok(result)
    }

    /// Run the no-trace BFS loop using the unified `run_bfs_loop` implementation.
    ///
    /// Part of #2133: Delegates to `run_bfs_loop<FingerprintOnlyStorage>` instead of
    /// maintaining a separate copy of the BFS loop body.
    pub(in crate::check) fn check_impl_no_trace_mode(&mut self, init_name: &str) -> CheckResult {
        let registry = self.ctx.var_registry().clone();
        self.initialize_checkpoint_timing();
        // Part of #3175: Prepare inline liveness cache before BFS so that
        // record_inline_liveness_results() records bitmask data during BFS.
        // Without this, the post-BFS bitmask fast path is unavailable and
        // populate_node_check_masks falls back to eval which needs full states
        // that aren't stored in fingerprint-only mode.
        self.prepare_inline_liveness_cache();

        // Scratch ArrayState used to process bulk-backed states without per-state allocation.
        let mut bulk_scratch = ArrayState::new(registry.len());

        // Part of #1801: route init-state violations through finalize_terminal_result
        // so storage-error precedence applies even to early invariant violations.
        let (bulk_initial, mut queue) =
            match self.init_states_no_trace(init_name, &registry, &mut bulk_scratch) {
                Ok(result) => result,
                Err(result) => return self.finalize_terminal_result_with_storage(result),
            };

        // Part of #3986: Infer flat i64 state layout from first initial state.
        // Uses bulk_scratch which holds the last processed init state — sufficient
        // for layout inference since all states share the same variable types.
        if !queue.is_empty() {
            self.infer_flat_state_layout(&bulk_scratch);
        }

        // Part of #3910: Upgrade JIT invariant cache with compound layout info
        // inferred from the first initial state. Uses bulk_scratch which holds
        // the last processed init state — sufficient for layout inference since
        // all states share the same variable types.
        #[cfg(feature = "jit")]
        if !queue.is_empty() {
            self.upgrade_jit_cache_with_layout(&bulk_scratch);
            // Part of #3986: Verify that the flat BFS layout and JIT layout agree
            // on buffer format. Log warning if incompatible.
            self.verify_layout_compatibility();
        }

        // Part of #4126: Determine whether flat BFS should be active.
        //
        // Auto-detection: when all state variables are scalar (i64-representable)
        // and the roundtrip verification passes, flat BFS activates automatically
        // without requiring TLA2_FLAT_BFS=1. The env var still works as a
        // force-enable for non-fully-flat layouts, and TLA2_NO_FLAT_BFS=1
        // can force-disable.
        let use_flat = self.should_use_flat_bfs();
        let force_env = crate::check::debug::flat_bfs_enabled();

        // Log activation status.
        if use_flat {
            if let Some(ref adapter) = self.flat_bfs_adapter {
                let source = if force_env {
                    "TLA2_FLAT_BFS=1"
                } else if self.config.use_flat_state == Some(true) {
                    "config.use_flat_state=true"
                } else {
                    "auto-detected (all vars scalar)"
                };
                eprintln!(
                    "[flat-bfs] active ({}): {} slots/state, {} bytes/state, fully_flat={}",
                    source,
                    adapter.num_slots(),
                    adapter.bytes_per_state(),
                    adapter.is_fully_flat(),
                );
            }
        } else if force_env {
            // User explicitly requested flat BFS but it couldn't activate.
            if let Some(ref adapter) = self.flat_bfs_adapter {
                if !adapter.roundtrip_verified() {
                    eprintln!(
                        "[flat-bfs] TLA2_FLAT_BFS=1 but roundtrip verification failed — falling back to Owned queue entries ({} slots/state)",
                        adapter.num_slots(),
                    );
                }
            } else {
                eprintln!("[flat-bfs] TLA2_FLAT_BFS=1 but adapter not initialized (layout inference may have failed)");
            }
        }

        let mut storage = FingerprintOnlyStorage::new(bulk_initial, registry.len());

        // Part of #2881 Step 3: enable lazy trace index for the BFS loop.
        // Initial states above populated trace_locs eagerly (small count).
        // The BFS expansion loop below processes potentially millions of states,
        // so skipping trace_locs.insert per state eliminates the last per-state
        // HashMap write. The index is built lazily from the trace file if/when
        // trace reconstruction is needed (invariant violation, liveness check).
        self.trace.lazy_trace_index = true;

        // Part of #4126: Use arena-backed FlatBfsFrontier when flat BFS is active.
        // This stores flat i64 state buffers contiguously in a FlatStateStore arena
        // instead of individual Box<[i64]> per NoTraceQueueEntry::Flat, eliminating
        // per-state heap allocation on the BFS hot path and providing cache-friendly
        // sequential access during frontier iteration.
        if use_flat {
            let layout = self
                .flat_bfs_adapter
                .as_ref()
                .expect("invariant: flat_bfs_adapter present when use_flat")
                .layout()
                .clone();
            let mut flat_queue = super::bfs::flat_frontier::FlatBfsFrontier::with_capacity(
                layout,
                queue.len(),
            );
            // Transfer initial states from VecDeque to FlatBfsFrontier.
            while let Some(entry) = queue.pop_front() {
                flat_queue.push(entry);
            }

            // Part of #3988 / #4171: When the compiled BFS level is available
            // AND enabled (opt-in via TLA2_COMPILED_BFS=1 or config), use the
            // compiled level loop that processes the frontier directly from the
            // contiguous arena. This bypasses the per-state transport loop overhead
            // and runs action dispatch + fingerprint + first-level dedup in native
            // Cranelift-compiled code.
            //
            // The `should_use_compiled_bfs()` check respects the env var hierarchy:
            //   1. config.use_compiled_bfs=false -> disabled
            //   2. TLA2_NO_COMPILED_BFS=1 -> disabled
            //   3. config.use_compiled_bfs=true -> enabled (if level ready)
            //   4. TLA2_COMPILED_BFS=1 -> enabled (if level ready)
            //   5. Otherwise -> disabled (opt-in only for now)
            #[cfg(feature = "jit")]
            {
                if self.should_use_compiled_bfs() {
                    let result = self.run_compiled_bfs_loop(&mut storage, &mut flat_queue);
                    flat_queue.report_stats();
                    return result;
                } else if self.compiled_bfs_step.is_some() {
                    // Compiled BFS step is available but not opted-in via env var.
                    // Log once so users know they can enable it.
                    eprintln!(
                        "[compiled-bfs] compiled BFS step available but not enabled. \
                         Set TLA2_COMPILED_BFS=1 to activate."
                    );
                }
            }

            let result = self.run_bfs_loop(&mut storage, &mut flat_queue);
            flat_queue.report_stats();
            result
        } else {
            self.run_bfs_loop(&mut storage, &mut queue)
        }
    }
}
