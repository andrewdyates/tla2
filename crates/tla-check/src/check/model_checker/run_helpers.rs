// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! BFS helper functions shared between full-state and no-trace modes.
//!
//! Contains invariant checking, deadlock detection, checkpoint management,
//! and profiling. Post-BFS finalization lives in `run_finalize.rs`.

use super::debug::profile_enum;
use super::{
    check_error_to_result, print_enum_profile_stats, print_eval_profile_stats, ArrayState,
    CheckResult, Fingerprint, Instant, LimitType, ModelChecker, State, VecDeque,
};
use crate::checker_ops::InvariantOutcome;
use crate::state::print_symmetry_stats;

// Part of #4114: Cache debug env var with OnceLock instead of calling
// std::env::var on every JIT fallback in the BFS loop.
feature_flag!(jit_stats_enabled, "TLA2_JIT_STATS");

/// Number of JIT-dispatched states to sample before making the warmup gate decision.
/// After this many states, cumulative JIT vs interpreter time is compared and JIT
/// is disabled if it's >20% slower.
///
/// Part of #4031: JIT warmup gate.
#[cfg(feature = "jit")]
pub(in crate::check) const JIT_WARMUP_THRESHOLD: u32 = 500;

/// Ratio threshold: if JIT time / interpreter time exceeds this, JIT is disabled.
/// 1.2 means JIT must be no more than 20% slower than the interpreter.
///
/// Part of #4031: JIT warmup gate.
#[cfg(feature = "jit")]
const JIT_SLOWDOWN_RATIO: f64 = 1.2;

/// A JIT-compiled successor stored as flat i64 buffers.
///
/// Defers the expensive `unflatten_i64_to_array_state_with_input` conversion
/// until after the BFS dedup check. Most successors are duplicates — by keeping
/// them flat, we avoid allocating Value objects and ArrayState for states that
/// will be immediately discarded.
///
/// Part of #4032: Eliminate per-action unflatten.
#[cfg(feature = "jit")]
pub(in crate::check) struct JitFlatSuccessor {
    /// The raw i64 output from the JIT-compiled action function.
    /// Each slot corresponds to a state variable (same layout as flatten).
    pub(in crate::check) jit_output: Vec<i64>,
    /// Snapshot of the JIT input buffer at the time this action was evaluated.
    /// Needed by `unflatten_i64_to_array_state_with_input` to deserialize
    /// compound values that were modified in-place by native FuncExcept.
    pub(in crate::check) jit_input: Vec<i64>,
    /// Number of state variables (may be less than buffer length for compact layouts).
    pub(in crate::check) state_var_count: usize,
}

#[cfg(feature = "jit")]
impl JitFlatSuccessor {
    /// Convert this flat successor to an ArrayState by unflattening.
    ///
    /// This is the cold-path materialization: only called for NEW states that
    /// pass the dedup check and need invariant checking + queue insertion.
    #[inline]
    pub(in crate::check) fn to_array_state(
        &self,
        parent: &ArrayState,
    ) -> ArrayState {
        super::invariants::unflatten_i64_to_array_state_with_input(
            parent,
            &self.jit_output,
            self.state_var_count,
            Some(&self.jit_input),
        )
    }

    /// Try to compute a fingerprint directly from the flat buffer.
    ///
    /// Returns `Some(Fingerprint)` for all-scalar states where the fingerprint
    /// can be computed without materializing Value objects. Returns `None` when
    /// compound variables were modified, requiring full unflatten.
    ///
    /// Part of #4032: Hot-path fingerprinting without ArrayState allocation.
    #[inline]
    pub(in crate::check) fn try_flat_fingerprint(
        &self,
        parent: &ArrayState,
        registry: &crate::var_index::VarRegistry,
    ) -> Option<Fingerprint> {
        super::invariants::fingerprint_jit_flat_successor(
            parent,
            &self.jit_output,
            self.state_var_count,
            Some(&self.jit_input),
            registry,
        )
        .map(|(fp, _xor)| fp)
    }
}

/// Bundled BFS profiling counters and accumulator.
///
/// Used both as the accumulator during the BFS loop and as the snapshot
/// passed to `output_bfs_profile`. The `accum_*` and `count_*` methods
/// are no-ops when `do_profile` is false, avoiding scattered `if` checks.
///
/// Part of #2677: consolidated from 8 local variables in `run_bfs_loop`.
#[derive(Clone)]
pub(in crate::check) struct BfsProfile {
    pub do_profile: bool,
    pub start_time: Instant,
    pub succ_gen_us: u64,
    pub fingerprint_us: u64,
    pub dedup_us: u64,
    pub invariant_us: u64,
    pub jit_hits: u64,
    pub jit_misses: u64,
    pub total_successors: u64,
    pub new_states: u64,
    /// Part of #3990: arena allocation count (cumulative across resets).
    pub arena_allocs: u64,
    /// Part of #3990: arena bytes allocated (cumulative across resets).
    pub arena_bytes: u64,
    /// Part of #3990: arena reset count (number of BFS level boundaries).
    pub arena_resets: u64,
}

impl BfsProfile {
    /// Create a new accumulator. All counters start at zero.
    pub(in crate::check) fn new(start_time: Instant) -> Self {
        Self {
            do_profile: profile_enum(),
            start_time,
            succ_gen_us: 0,
            fingerprint_us: 0,
            dedup_us: 0,
            invariant_us: 0,
            jit_hits: 0,
            jit_misses: 0,
            total_successors: 0,
            new_states: 0,
            arena_allocs: 0,
            arena_bytes: 0,
            arena_resets: 0,
        }
    }

    /// Capture the current instant when profiling is enabled, else reuse start_time.
    #[inline(always)]
    pub(in crate::check) fn now(&self) -> Instant {
        if self.do_profile {
            Instant::now()
        } else {
            self.start_time
        }
    }

    /// Accumulate successor generation time from a captured instant.
    #[inline(always)]
    pub(in crate::check) fn accum_succ_gen(&mut self, t0: Instant) {
        if self.do_profile {
            self.succ_gen_us += t0.elapsed().as_micros() as u64;
        }
    }

    /// Accumulate fingerprinting time from a captured instant.
    #[inline(always)]
    pub(in crate::check) fn accum_fingerprint(&mut self, t0: Instant) {
        if self.do_profile {
            self.fingerprint_us += t0.elapsed().as_micros() as u64;
        }
    }

    /// Accumulate dedup check time from a captured instant.
    #[inline(always)]
    pub(in crate::check) fn accum_dedup(&mut self, t0: Instant) {
        if self.do_profile {
            self.dedup_us += t0.elapsed().as_micros() as u64;
        }
    }

    /// Record successors generated for this state.
    #[inline(always)]
    pub(in crate::check) fn count_successors(&mut self, n: usize) {
        if self.do_profile {
            self.total_successors += n as u64;
        }
    }

    /// Record one new (unseen) state discovered.
    #[inline(always)]
    pub(in crate::check) fn count_new_state(&mut self) {
        if self.do_profile {
            self.new_states += 1;
        }
    }

    /// Snapshot arena stats from the thread-local worker arena into this profile.
    ///
    /// Called at the end of BFS exploration (before profile output) so the arena
    /// allocation count, bytes, and reset count appear in the profile.
    ///
    /// Part of #3990: arena allocation metrics in BFS profile.
    pub(in crate::check) fn snapshot_arena_stats(&mut self) {
        if !self.do_profile {
            return;
        }
        crate::arena::with_worker_arena(|arena| {
            self.arena_allocs = arena.allocation_count() as u64;
            self.arena_bytes = arena.allocated_bytes() as u64;
            self.arena_resets = arena.reset_count() as u64;
        });
    }
}

pub(in crate::check) fn bfs_profile_lines(total_us: u64, prof: &BfsProfile) -> Vec<String> {
    let other_us = total_us.saturating_sub(
        prof.succ_gen_us
            .saturating_add(prof.fingerprint_us)
            .saturating_add(prof.dedup_us)
            .saturating_add(prof.invariant_us),
    );
    let pct = |us: u64| -> f64 {
        if total_us > 0 {
            us as f64 / total_us as f64 * 100.0
        } else {
            0.0
        }
    };
    let mut lines = vec![
        "=== Enumeration Profile ===".to_string(),
        format!(
            "  Successor gen:   {:>8.3}s ({:>5.1}%)",
            prof.succ_gen_us as f64 / 1_000_000.0,
            pct(prof.succ_gen_us)
        ),
        format!(
            "  Fingerprinting:  {:>8.3}s ({:>5.1}%)",
            prof.fingerprint_us as f64 / 1_000_000.0,
            pct(prof.fingerprint_us)
        ),
        format!(
            "  Dedup check:     {:>8.3}s ({:>5.1}%)",
            prof.dedup_us as f64 / 1_000_000.0,
            pct(prof.dedup_us)
        ),
        format!(
            "  Invariant check: {:>8.3}s ({:>5.1}%)",
            prof.invariant_us as f64 / 1_000_000.0,
            pct(prof.invariant_us)
        ),
        format!(
            "  Other:           {:>8.3}s ({:>5.1}%)",
            other_us as f64 / 1_000_000.0,
            pct(other_us)
        ),
        "  ---".to_string(),
        format!("  Total:           {:>8.3}s", total_us as f64 / 1_000_000.0),
    ];
    if prof.new_states > 0 {
        lines.push(format!(
            "  Total successors: {} ({:.0}/state)",
            prof.total_successors,
            prof.total_successors as f64 / prof.new_states as f64
        ));
    } else {
        lines.push(format!(
            "  Total successors: {} (no new states)",
            prof.total_successors
        ));
    }
    lines.push(format!("  New states:       {}", prof.new_states));
    if prof.jit_hits > 0 || prof.jit_misses > 0 {
        lines.push(format!(
            "  JIT invariant:    hits={} misses={}",
            prof.jit_hits, prof.jit_misses
        ));
    }
    // Part of #3990: arena allocation stats.
    if prof.arena_allocs > 0 {
        lines.push(format!(
            "  Arena allocs:     {} ({:.1} MB, {} resets)",
            prof.arena_allocs,
            prof.arena_bytes as f64 / (1024.0 * 1024.0),
            prof.arena_resets,
        ));
    }
    lines
}

impl<'a> ModelChecker<'a> {
    #[cfg(feature = "jit")]
    pub(in crate::check) fn reset_jit_profile_counters(&mut self) {
        self.jit_hits = 0;
        self.jit_misses = 0;
    }

    #[cfg(not(feature = "jit"))]
    pub(in crate::check) fn reset_jit_profile_counters(&mut self) {}

    #[cfg(feature = "jit")]
    pub(in crate::check) fn take_jit_profile_counters(&mut self) -> (u64, u64) {
        let hits = self.jit_hits as u64;
        let misses = self.jit_misses as u64;
        self.jit_hits = 0;
        self.jit_misses = 0;
        (hits, misses)
    }

    #[cfg(not(feature = "jit"))]
    pub(in crate::check) fn take_jit_profile_counters(&mut self) -> (u64, u64) {
        (0, 0)
    }

    /// Initialize the tiered JIT manager based on discovered action count.
    ///
    /// Called from `prepare_bfs_common` after action splitting discovers the
    /// number of actions. Uses `split_action_meta` when available (split actions),
    /// otherwise defaults to 1 action (monolithic Next).
    ///
    /// Part of #3850: tiered JIT wiring into eval hot path.
    #[cfg(feature = "jit")]
    pub(super) fn initialize_tier_manager(&mut self) {
        let action_count = self
            .compiled
            .split_action_meta
            .as_ref()
            .map_or(1, |meta| meta.len());
        let mut manager = tla_jit::TierManager::new(action_count);

        // Mark all actions as JIT-eligible by default. The bytecode lowerer
        // will filter out actions that cannot be compiled when promotion fires.
        for i in 0..action_count {
            manager.set_eligible(i);
        }

        self.action_eval_counts = vec![0u64; action_count];
        self.action_succ_totals = vec![0u64; action_count];

        // Part of #3989: Enable type profiling for Tier 2 speculative specialization.
        // The profiler collects runtime types of state variables during BFS warmup
        // and produces a SpecializationPlan when the profile stabilizes.
        let var_count = self.module.vars.len();
        if var_count > 0 {
            manager.enable_type_profiling(var_count);
            self.type_profile_scratch = vec![tla_jit::SpecType::Other; var_count];
        }

        self.tier_manager = Some(manager);

        #[cfg(debug_assertions)]
        if super::debug::tla2_debug() {
            eprintln!(
                "[#3850] Tiered JIT manager initialized: {} actions, thresholds={:?}, type_profiling={}",
                action_count,
                tla_jit::TierConfig::from_env(),
                var_count > 0,
            );
        }
    }

    /// Record an action evaluation for tiered JIT promotion tracking.
    ///
    /// Called during successor generation for each action fired. Lightweight:
    /// just increments a `Vec<u64>` counter (no atomics needed for sequential mode).
    ///
    /// Part of #3850: tiered JIT wiring into eval hot path.
    #[cfg(feature = "jit")]
    #[inline]
    pub(in crate::check) fn record_action_eval_for_tier(
        &mut self,
        action_id: usize,
        successor_count: u64,
    ) {
        if let Some(count) = self.action_eval_counts.get_mut(action_id) {
            *count += 1;
        }
        if let Some(total) = self.action_succ_totals.get_mut(action_id) {
            *total += successor_count;
        }
    }

    /// No-op stub when JIT feature is disabled.
    #[cfg(not(feature = "jit"))]
    #[inline]
    pub(in crate::check) fn record_action_eval_for_tier(
        &mut self,
        _action_id: usize,
        _successor_count: u64,
    ) {
    }

    /// Profile the runtime types of state variable values for Tier 2 specialization.
    ///
    /// Called once per BFS state dequeue (before successor generation). Classifies
    /// each state variable value into a [`SpecType`] and feeds the observation to
    /// the `TierManager`'s type profiler. Once the warmup threshold is reached,
    /// the profiler freezes and subsequent calls are no-ops.
    ///
    /// Overhead: classification runs during warmup only (~1000 states, default).
    /// After freeze, `observe_state_types` returns immediately. The scratch buffer
    /// avoids per-state allocation.
    ///
    /// Part of #3989: speculative type specialization.
    #[cfg(feature = "jit")]
    #[inline]
    pub(in crate::check) fn profile_state_types(&mut self, state: &super::ArrayState) {
        let manager = match self.tier_manager.as_mut() {
            Some(m) => m,
            None => return,
        };
        // Skip if already frozen (fast path).
        if manager.type_profile_stable() {
            return;
        }
        // Classify each variable value into a SpecType.
        let var_count = self.type_profile_scratch.len();
        for i in 0..var_count {
            let value = state.get(crate::var_index::VarIndex::new(i));
            self.type_profile_scratch[i] = tla_jit::classify_value(&value);
        }
        let stabilized = manager.observe_state_types(&self.type_profile_scratch);
        if stabilized {
            let profile = manager.type_profile();
            let mono_types = profile.map(|p| p.monomorphic_types());
            eprintln!(
                "[jit] Type profile stabilized after {} states: {:?}",
                profile.map_or(0, |p| p.total_states()),
                mono_types,
            );
        }
    }

    /// No-op stub when JIT feature is disabled.
    #[cfg(not(feature = "jit"))]
    #[inline]
    pub(in crate::check) fn profile_state_types(&mut self, _state: &super::ArrayState) {}

    /// Record JIT next-state dispatch decision for monolithic Next (action_id=0).
    ///
    /// Called from the four monolithic successor paths (diff, diff_streaming,
    /// full_state, full_state_streaming) after each state's successors are
    /// generated. Records whether the monolithic action was promoted to JIT
    /// tier and whether a compiled cache was available, feeding the
    /// `--show-tiers` dispatch counter report.
    ///
    /// Part of #3959: Also polls for async JIT compilation completion. The
    /// streaming/diff paths never call `try_jit_monolithic_successors()`,
    /// which was the only prior call site for `poll_pending_jit_compilation()`.
    /// By polling here, every BFS state (regardless of which successor path
    /// processes it) probes for JIT readiness. Once the cache is installed,
    /// subsequent states see `jit_next_state_cache.is_some()` in
    /// `jit_monolithic_ready()` and route to the batch JIT path.
    ///
    /// Part of #3910: JIT dispatch tracking for sequential BFS.
    #[cfg(feature = "jit")]
    #[inline]
    pub(in crate::check) fn record_monolithic_next_state_dispatch(&mut self) {
        // Poll for async JIT compilation completion so the streaming/diff
        // paths can detect JIT readiness for the *next* state's routing.
        // This is a non-blocking try_recv — negligible overhead when
        // compilation is still in progress or not started.
        if self.jit_next_state_cache.is_none() && self.pending_jit_compilation.is_some() {
            self.poll_pending_jit_compilation();
        }

        // Part of #3989: Poll for Tier 2 recompilation completion.
        // When the background recompilation finishes, swap in the new cache.
        self.poll_tier2_recompilation();

        if let Some(ref manager) = self.tier_manager {
            let tier = manager.current_tier(0);
            if tier >= tla_jit::CompilationTier::Tier1 {
                self.next_state_dispatch.total += 1;
                // This state was processed by the interpreter (streaming/diff
                // path). Record as not_compiled. If the poll above installed
                // the JIT cache, the *next* state will route to the batch JIT
                // path via jit_monolithic_ready().
                self.next_state_dispatch.jit_not_compiled += 1;
            }
        }
    }

    /// No-op stub when JIT feature is disabled.
    #[cfg(not(feature = "jit"))]
    #[inline]
    pub(in crate::check) fn record_monolithic_next_state_dispatch(&mut self) {}

    /// Try JIT-compiled evaluation of split actions for the monolithic path.
    ///
    /// The monolithic BFS successor files (diff, diff_streaming, full_state,
    /// full_state_streaming) evaluate the entire Next relation at once via the
    /// interpreter. This method attempts to use JIT-compiled per-action dispatch
    /// instead, iterating through all split actions and collecting successors.
    ///
    /// ALL actions must succeed via JIT for this method to return results.
    /// If any action is not compiled, needs fallback, or has compound binding
    /// values that prevent specialization, the method returns `None` so the
    /// caller uses the proven monolithic enumerator.
    ///
    /// Part of #4011: the per-action interpreter fallback
    /// (`eval_action_via_interpreter`) was unsound — it produced incorrect
    /// successor sets. The fix eliminates it: any action needing interpreter
    /// fallback causes the entire hybrid path to bail out.
    ///
    /// When this method returns `Some`, the JIT result is cross-checked
    /// against the monolithic enumerator for the first N states
    /// (`jit_validation_remaining`) to detect JIT correctness bugs early.
    ///
    /// Returns:
    /// - `Some(successors)` — all actions evaluated via JIT
    /// - `None` — JIT infrastructure not available, not all actions compiled,
    ///   or JIT runtime error
    ///
    /// Try the compiled BFS step for a single parent state (zero-copy flat output).
    ///
    /// When `CompiledBfsStep` is available, this performs the entire BFS inner
    /// loop (action dispatch, inline fingerprinting, dedup via AtomicFpSet,
    /// invariant checking) in a single native Cranelift-compiled function call.
    ///
    /// Returns `FlatBfsStepOutput` which avoids per-successor Vec allocations.
    /// The caller iterates flat i64 slices and only unflattens new states.
    ///
    /// Returns `Some(FlatBfsStepOutput)` on success, `None` if the compiled step
    /// is not available or encounters an error (in which case the caller falls
    /// back to the per-action JIT or interpreter paths).
    ///
    /// Part of #3988: Zero-copy compiled BFS step with deferred unflatten.
    /// Part of #4034: Wire CompiledBfsStep into model checker BFS loop.
    #[cfg(feature = "jit")]
    pub(in crate::check) fn try_compiled_bfs_step(
        &mut self,
        current_array: &ArrayState,
    ) -> Option<tla_jit::FlatBfsStepOutput> {
        // Guard: compiled BFS step must be built and JIT not disabled.
        if self.jit_monolithic_disabled {
            return None;
        }
        let step = self.compiled_bfs_step.as_ref()?;

        // Flatten current state to i64 representation.
        let mut flat_state = vec![0i64; step.state_len()];
        if !super::invariants::flatten_state_to_i64_selective(
            current_array,
            &mut flat_state,
            &[], // empty = all vars
        ) {
            return None; // State has compound types that can't flatten
        }

        match step.step_flat(&flat_state) {
            Ok(output) => Some(output),
            Err(e) => {
                eprintln!("[jit] CompiledBfsStep error: {e} — disabling");
                self.jit_monolithic_disabled = true;
                self.compiled_bfs_step = None;
                self.compiled_bfs_level = None;
                None
            }
        }
    }

    /// Part of #3910: Wire JIT dispatch into monolithic BFS paths.
    /// Part of #3968: Per-action hybrid JIT/interpreter dispatch.
    /// Part of #4013: Returns `(JitFlatSuccessor, Option<usize>)` pairs where the
    /// second element is the split-action index for liveness provenance tracking.
    /// Part of #4011: Eliminate unsound interpreter fallback, add validation.
    /// Part of #4032: Returns flat i64 buffers instead of ArrayState. The caller
    /// defers unflatten to after the dedup check, avoiding Value allocation for
    /// duplicate states (~80-95% of all successors in typical BFS runs).
    #[cfg(feature = "jit")]
    pub(in crate::check) fn try_jit_monolithic_successors(
        &mut self,
        current_array: &ArrayState,
    ) -> Option<Vec<(JitFlatSuccessor, Option<usize>)>> {
        // Early exit: JIT permanently disabled due to a prior runtime error.
        if self.jit_monolithic_disabled {
            return None;
        }

        // Part of #4030: Use cached flags instead of per-state iteration.
        if !self.jit_all_next_state_compiled || !self.jit_has_any_promoted {
            return None;
        }

        // Need split action metadata.
        let meta = self.compiled.split_action_meta.as_ref()?;
        if meta.is_empty() {
            return None;
        }

        // Part of #4030: Use pre-computed lookup keys instead of per-state allocation.
        // Keys were computed once in poll_pending_jit_compilation().
        if self.jit_action_lookup_keys.len() != meta.len() {
            return None;
        }

        // Flatten state for JIT evaluation.
        if !self.prepare_jit_next_state(current_array) {
            return None;
        }

        // Part of #4030: Optional timing diagnostics (TLA2_JIT_DIAG=1).
        // Uses cached field to avoid per-state syscall.
        let diag_t0 = if self.jit_diag_enabled {
            Some(Instant::now())
        } else {
            None
        };

        // Part of #4030: Track JIT eval time separately for fair warmup gate comparison.
        let warmup_sampling = self.jit_perf_monitor.2 < JIT_WARMUP_THRESHOLD;
        let mut jit_eval_ns: u64 = 0;

        // ALL actions must succeed via JIT for this path to produce results (#4011).
        //
        // Part of #4030: The action loop is inlined rather than calling a method
        // because the pre-computed keys borrow self.jit_action_lookup_keys and
        // a method call would require &mut self (conflicting borrow).
        let num_actions = self.jit_action_lookup_keys.len();
        let mut successors = Vec::with_capacity(num_actions);

        // Extract state_var_count once before the loop.
        let state_var_count = match self.jit_next_state_cache.as_ref() {
            Some(c) => c.state_var_count(),
            None => return None,
        };

        // Ensure action output scratch buffer is sized correctly.
        if self.jit_action_out_scratch.len() < state_var_count {
            self.jit_action_out_scratch.resize(state_var_count, 0);
        }

        // Part of #4030: Cache whether state is all-scalar for compound scratch skip.
        let state_all_scalar = self.jit_state_all_scalar;

        for action_idx in 0..num_actions {
            // Check key validity (empty = can't be JIT-compiled).
            if self.jit_action_lookup_keys[action_idx].is_empty() {
                return None;
            }

            // Part of #4030: Skip compound scratch clearing for all-scalar states.
            if !state_all_scalar {
                tla_jit::abi::clear_compound_scratch();
            }

            self.next_state_dispatch.total += 1;

            // Part of #4030: Time only the JIT eval, not Vec clones or bookkeeping.
            let eval_t0 = if warmup_sampling {
                Some(Instant::now())
            } else {
                None
            };

            // Part of #4030: Use eval_action_into with the reusable scratch buffer.
            // Split borrow: cache + jit_state_scratch (immut) + jit_action_out_scratch (mut).
            let eval_result = {
                let cache = self.jit_next_state_cache.as_ref().expect("checked above");
                let key = &self.jit_action_lookup_keys[action_idx];
                cache.eval_action_into(
                    key,
                    &self.jit_state_scratch,
                    &mut self.jit_action_out_scratch,
                )
            };

            // Accumulate JIT eval time (excludes Vec clones and bookkeeping).
            if let Some(t0) = eval_t0 {
                jit_eval_ns += t0.elapsed().as_nanos() as u64;
            }

            match eval_result {
                Some(Ok(true)) => {
                    // Action enabled — capture flat buffers for deferred unflatten.
                    // Part of #4032: defer Value reconstruction to after dedup check.
                    self.next_state_dispatch.jit_hit += 1;
                    let flat_succ = JitFlatSuccessor {
                        jit_output: self.jit_action_out_scratch.clone(),
                        jit_input: self.jit_state_scratch.clone(),
                        state_var_count,
                    };
                    successors.push((flat_succ, Some(action_idx)));
                }
                Some(Ok(false)) => {
                    // Action disabled (guard=false) — no successor.
                    self.next_state_dispatch.jit_hit += 1;
                }
                Some(Err(_)) => {
                    self.next_state_dispatch.jit_error += 1;
                    self.jit_monolithic_disabled = true;
                    return None;
                }
                None => {
                    // Not compiled or FallbackNeeded — abandon hybrid.
                    let has_action = self
                        .jit_next_state_cache
                        .as_ref()
                        .map_or(false, |c| {
                            c.contains_action(&self.jit_action_lookup_keys[action_idx])
                        });
                    if has_action {
                        self.next_state_dispatch.jit_fallback += 1;
                    } else {
                        self.next_state_dispatch.jit_not_compiled += 1;
                    }
                    return None;
                }
            }
        }

        // Part of #4030: Record JIT time for adaptive performance monitoring.
        if let Some(t0) = diag_t0 {
            let jit_ns = t0.elapsed().as_nanos() as u64;
            static DIAG_COUNT: std::sync::atomic::AtomicU64 =
                std::sync::atomic::AtomicU64::new(0);
            let count = DIAG_COUNT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            if count < 10 || count % 100_000 == 0 {
                eprintln!(
                    "[jit-diag] state {}: JIT dispatch {:.1}us, {} successors",
                    count,
                    jit_ns as f64 / 1000.0,
                    successors.len(),
                );
            }
        }

        // Part of #4030: Record only JIT eval time (not Vec clones, bookkeeping)
        // for fair comparison with interpreter successor-generation timing.
        if warmup_sampling {
            self.jit_perf_monitor.0 += jit_eval_ns;
            self.jit_perf_monitor.2 += 1;
        }

        // Part of #4011: Cross-check JIT results against the monolithic enumerator
        // for the first N states to detect JIT correctness bugs early.
        // Part of #4031: Also time the interpreter during validation to collect
        // comparison data for the warmup gate decision.
        if self.jit_validation_remaining > 0 {
            self.jit_validation_remaining -= 1;
            let interp_t0 = if warmup_sampling {
                Some(Instant::now())
            } else {
                None
            };
            match self.generate_successors_array_raw(current_array) {
                Ok(interp_result) => {
                    // Part of #4031: Capture interpreter timing during validation.
                    if let Some(t0) = interp_t0 {
                        self.jit_perf_monitor.1 += t0.elapsed().as_nanos() as u64;
                    }
                    let jit_count = successors.len();
                    let interp_count = interp_result.successors.len();
                    if jit_count != interp_count {
                        eprintln!(
                            "[jit] P0 VALIDATION FAILURE (#4011): JIT produced {} successors \
                             but monolithic enumerator produced {} for state. \
                             Permanently disabling JIT.",
                            jit_count, interp_count,
                        );
                        self.jit_monolithic_disabled = true;
                        return None;
                    }
                }
                Err(_) => {
                    self.jit_monolithic_disabled = true;
                    return None;
                }
            }
        }

        // Part of #4031: Warmup gate decision.
        // After JIT_WARMUP_THRESHOLD states, compare cumulative JIT time vs
        // interpreter time (extrapolated from the validation sample) and decide
        // whether to keep JIT enabled.
        if self.jit_perf_monitor.2 == JIT_WARMUP_THRESHOLD {
            self.evaluate_jit_warmup_gate();
            if self.jit_monolithic_disabled {
                return None;
            }
        }

        Some(successors)
    }

    /// Evaluate the JIT warmup gate decision.
    ///
    /// Called once after `JIT_WARMUP_THRESHOLD` states have been processed via JIT.
    /// Compares cumulative JIT time against interpreter time collected during the
    /// validation cross-check period. If JIT is slower than the interpreter by
    /// more than `JIT_SLOWDOWN_RATIO`, permanently disables JIT dispatch.
    ///
    /// The interpreter timing comes from the first `jit_validation_remaining` states
    /// where both JIT and interpreter run (for correctness cross-checking). We use
    /// per-state averages to compare fairly since the JIT sample is larger.
    ///
    /// Part of #4031: JIT warmup gate.
    #[cfg(feature = "jit")]
    pub(in crate::check) fn evaluate_jit_warmup_gate(&mut self) {
        let (jit_ns, interp_ns, sampled) = self.jit_perf_monitor;

        if sampled == 0 {
            return;
        }

        // We need interpreter timing data to make a decision.
        // interp_ns is collected during the validation cross-check period
        // (first jit_validation_remaining states, default 100).
        if interp_ns == 0 {
            // No interpreter comparison data available. This happens if
            // jit_validation_remaining was 0 or validation completed before
            // JIT was ready. Keep JIT enabled — we can't make an informed
            // decision without comparison data.
            eprintln!(
                "[jit] warmup gate: no interpreter comparison data after {} states — keeping JIT enabled",
                sampled,
            );
            return;
        }

        // Compute per-state average times. The interpreter was only sampled
        // during the validation period (first N states), while JIT was sampled
        // for all JIT_WARMUP_THRESHOLD states. Use per-state averages for fair
        // comparison.
        //
        // validation_count = initial_validation_remaining (100) - current remaining.
        // Since we only collected interp_ns during validation, the validation
        // sample count is the initial count minus what's left.
        let initial_validation = 100u32; // matches jit_validation_remaining default
        let validation_states = initial_validation.saturating_sub(self.jit_validation_remaining);
        if validation_states == 0 {
            eprintln!(
                "[jit] warmup gate: validation produced 0 interpreter samples — keeping JIT enabled",
            );
            return;
        }

        let jit_avg_ns = jit_ns as f64 / sampled as f64;
        let interp_avg_ns = interp_ns as f64 / validation_states as f64;

        // Avoid division by zero.
        if interp_avg_ns < 1.0 {
            eprintln!(
                "[jit] warmup gate: interpreter time negligible ({:.0}ns total for {} states) — keeping JIT enabled",
                interp_ns as f64, validation_states,
            );
            return;
        }

        let ratio = jit_avg_ns / interp_avg_ns;

        if ratio > JIT_SLOWDOWN_RATIO {
            // JIT is slower than the interpreter — disable it.
            eprintln!(
                "[jit] warmup gate: JIT is {:.1}x slower than interpreter after {} states \
                 (JIT avg {:.1}us/state, interp avg {:.1}us/state) — disabling JIT dispatch",
                ratio,
                sampled,
                jit_avg_ns / 1000.0,
                interp_avg_ns / 1000.0,
            );
            self.jit_monolithic_disabled = true;
            self.jit_next_state_cache = None;
            self.compiled_bfs_step = None;
            self.compiled_bfs_level = None;
        } else {
            // JIT is competitive — keep it enabled and stop sampling.
            eprintln!(
                "[jit] warmup gate: JIT is {:.2}x vs interpreter after {} states \
                 (JIT avg {:.1}us/state, interp avg {:.1}us/state) — keeping JIT enabled",
                ratio,
                sampled,
                jit_avg_ns / 1000.0,
                interp_avg_ns / 1000.0,
            );
        }
    }

    /// Evaluate a single split action via the interpreter.
    ///
    /// **DEPRECATED (#4011):** This method is unsound — it produces incorrect
    /// successor sets because the per-action evaluator doesn't replicate the
    /// monolithic enumerator's UNCHANGED semantics, guard ordering, and binding
    /// scope. It is no longer called from the hot path. Retained for reference
    /// and potential future use once the root cause is fixed.
    ///
    /// Used as the per-action fallback when JIT compilation is not available
    /// for a specific action. Constructs a temporary `OperatorDef` from the
    /// action's expression body and enumerates successors.
    ///
    /// Returns `Some(successors)` on success, `None` if the expression body
    /// is unavailable or the Next definition can't be found.
    ///
    /// Part of #3968: per-action hybrid JIT/interpreter dispatch.
    /// Part of #3982: bind EXISTS-quantified variables from split-action expansion.
    #[cfg(feature = "jit")]
    #[allow(dead_code)]
    fn eval_action_via_interpreter(
        &mut self,
        action_name: &str,
        action_expr: Option<&tla_core::Spanned<tla_core::ast::Expr>>,
        bindings: &[(std::sync::Arc<str>, crate::Value)],
        current_array: &ArrayState,
    ) -> Option<Vec<ArrayState>> {
        let expr = action_expr?;

        // Get the Next operator definition for metadata (params, contains_prime, etc.).
        let next_name = self.trace.cached_next_name.as_deref()?;
        let resolved_next_name = self.ctx.resolve_op_name(next_name).to_string();
        let next_def = self.module.op_defs.get(&resolved_next_name)?;

        // Construct a temporary OperatorDef with this action's expression body.
        let action_def = tla_core::ast::OperatorDef {
            name: next_def.name.clone(),
            params: next_def.params.clone(),
            body: expr.clone(),
            local: next_def.local,
            contains_prime: true, // Action bodies always contain primed variables.
            guards_depend_on_prime: false,
            has_primed_param: next_def.has_primed_param,
            is_recursive: false,
            self_call_count: 0,
        };

        // Bind state variables for this evaluation.
        let _state_guard = self.ctx.bind_state_env_guard(current_array.env_ref());

        // Bind EXISTS-quantified variables from split-action expansion.
        // E.g., for `\E p \in Proc : Request(p)`, bind `p` to its concrete value.
        // Use mark/pop for scoped cleanup after evaluation.
        let mark = self.ctx.mark_stack();
        for (var_name, val) in bindings {
            self.ctx.push_binding(var_name.clone(), val.clone());
        }

        let result = match crate::enumerate::enumerate_successors_array_with_tir(
            &mut self.ctx,
            &action_def,
            current_array,
            &self.module.vars,
            None,
        ) {
            Ok(succs) => {
                if jit_stats_enabled() {
                    eprintln!(
                        "[jit] Interpreter fallback for action '{}': {} successor(s)",
                        action_name,
                        succs.len()
                    );
                }
                Some(succs)
            }
            Err(e) => {
                if jit_stats_enabled() {
                    eprintln!(
                        "[jit] Interpreter fallback failed for action '{}': {e}",
                        action_name
                    );
                }
                None
            }
        };

        // Restore bindings to pre-action state.
        self.ctx.pop_to_mark(&mark);

        result
    }

    /// No-op stub when JIT feature is disabled.
    ///
    /// Returns `Option<Vec<(ArrayState, Option<usize>)>>` for API compatibility.
    /// Always returns `None`, so the caller always takes the interpreter path.
    #[cfg(not(feature = "jit"))]
    #[inline]
    #[allow(dead_code)]
    pub(in crate::check) fn try_jit_monolithic_successors(
        &mut self,
        _current_array: &ArrayState,
    ) -> Option<Vec<(ArrayState, Option<usize>)>> {
        None
    }

    /// Check if JIT is ready for monolithic successor evaluation.
    ///
    /// Returns true if a JIT cache exists (or is pending) and at least one
    /// split action is promoted to Tier1+. Used by diff and streaming paths
    /// to short-circuit to the full-state batch path which has JIT dispatch
    /// wired.
    ///
    /// Part of #3910: JIT routing for monolithic BFS paths.
    /// Part of #3968: Per-action dispatch — route to batch path when
    /// ANY action is promoted. `try_jit_monolithic_successors` returns
    /// `Some` only when ALL actions succeed via JIT (#4011).
    /// Part of #4030: Uses cached `jit_has_any_promoted` flag instead of
    /// iterating all actions on every state.
    #[cfg(feature = "jit")]
    #[inline]
    pub(in crate::check) fn jit_monolithic_ready(&self) -> bool {
        // Part of #3968: skip JIT path entirely if a previous JIT runtime error
        // permanently disabled it.
        if self.jit_monolithic_disabled {
            return false;
        }
        // Use pre-computed flags: all actions compiled + at least one promoted.
        // Both are set once when the JIT cache is installed, avoiding per-state
        // iteration over all actions (#4030).
        self.jit_all_next_state_compiled && self.jit_has_any_promoted
    }

    /// No-op stub when JIT feature is disabled.
    #[cfg(not(feature = "jit"))]
    #[inline]
    pub(in crate::check) fn jit_monolithic_ready(&self) -> bool {
        false
    }

    /// Check for tiered JIT promotions and log any tier transitions.
    ///
    /// Called periodically (at progress intervals) rather than on every state
    /// to keep hot-path overhead near zero. Constructs `ActionProfile` snapshots
    /// from the accumulated counters and passes them to `TierManager::promotion_check`.
    ///
    /// Part of #3850: tiered JIT wiring into eval hot path.
    /// Part of #3910: record promotions for `--show-tiers` report.
    #[cfg(feature = "jit")]
    pub(in crate::check) fn check_tier_promotions(&mut self) {
        let manager = match self.tier_manager.as_mut() {
            Some(m) => m,
            None => return,
        };

        let action_count = manager.action_count();

        // Part of #3910: Detect monolithic counting mode.
        //
        // The four no-trace BFS successor paths (diff, diff_streaming,
        // full_state, full_state_streaming) all record evaluations under
        // action_id=0 ("Next" aggregate). Individual split actions (1..N)
        // stay at 0 evals and never promote via per-action threshold checks.
        //
        // Fix: when action_count > 1 and only action 0 has evals (monolithic
        // counting), use the aggregate "Next" count to drive batch promotion
        // of ALL sub-actions together via `promote_all_actions`.
        let aggregate_evals = self.action_eval_counts.first().copied().unwrap_or(0);
        let aggregate_succ = self.action_succ_totals.first().copied().unwrap_or(0);
        let is_monolithic_counting = action_count > 1
            && aggregate_evals > 0
            && self
                .action_eval_counts
                .get(1..action_count)
                .map_or(true, |rest| rest.iter().all(|&c| c == 0));

        let promotions = if is_monolithic_counting {
            // Monolithic path: promote all sub-actions based on aggregate
            // "Next" eval count.
            let config = manager.config().clone();
            let aggregate_bf = if aggregate_evals > 0 {
                aggregate_succ as f64 / aggregate_evals as f64
            } else {
                0.0
            };

            let target_tier = if aggregate_evals >= config.tier2_threshold {
                tla_jit::CompilationTier::Tier2
            } else if aggregate_evals >= config.tier1_threshold {
                tla_jit::CompilationTier::Tier1
            } else {
                return; // Below all thresholds, nothing to do.
            };

            manager.promote_all_actions(target_tier, aggregate_evals, aggregate_bf)
        } else {
            // Per-action counting path (split-action mode in
            // generate_successors_filtered): check each action individually.
            let profiles: Vec<tla_jit::ActionProfile> = (0..action_count)
                .map(|i| {
                    let evals = self.action_eval_counts.get(i).copied().unwrap_or(0);
                    let total_succ = self.action_succ_totals.get(i).copied().unwrap_or(0);
                    let bf = if evals > 0 {
                        total_succ as f64 / evals as f64
                    } else {
                        0.0
                    };
                    tla_jit::ActionProfile {
                        times_evaluated: evals,
                        branching_factor: bf,
                        jit_eligible: true,
                    }
                })
                .collect();

            manager.promotion_check(&profiles)
        };

        for promo in &promotions {
            // Resolve action name from split_action_meta when available.
            let action_label = self
                .compiled
                .split_action_meta
                .as_ref()
                .and_then(|meta| meta.get(promo.action_id))
                .and_then(|m| m.name.as_deref())
                .unwrap_or("Next");
            // Part of #3989: log specialization plan for Tier 2 promotions.
            if let Some(ref plan) = promo.specialization_plan {
                eprintln!(
                    "[jit] Action '{}': {} -> {} at {} evals (bf={:.1}) [specialized: {} vars, {}i/{}b, est. {:.2}x speedup]",
                    action_label,
                    promo.old_tier,
                    promo.new_tier,
                    promo.evaluations_at_promotion,
                    promo.branching_factor,
                    plan.specialized_var_count(),
                    plan.int_var_count(),
                    plan.bool_var_count(),
                    plan.expected_speedup_factor,
                );
            } else {
                eprintln!(
                    "[jit] Action '{}': {} -> {} at {} evals (bf={:.1})",
                    action_label,
                    promo.old_tier,
                    promo.new_tier,
                    promo.evaluations_at_promotion,
                    promo.branching_factor,
                );
            }
        }
        // Trigger JIT compilation on first Tier 1 promotion.
        // Build the next-state cache lazily to avoid compilation overhead for
        // small specs that never cross the threshold.
        let has_tier1_promotion = promotions
            .iter()
            .any(|p| p.new_tier == tla_jit::CompilationTier::Tier1);
        if has_tier1_promotion
            && self.jit_next_state_cache.is_none()
            && self.pending_jit_compilation.is_none()
        {
            self.compile_jit_next_state_on_promotion();
        }

        // Part of #3989: Trigger Tier 2 recompilation with type specialization.
        // When a Tier 2 promotion fires with a SpecializationPlan, spawn a
        // background recompilation of the JIT cache. The existing Tier 1 cache
        // continues to serve while Cranelift recompiles.
        let has_tier2_with_plan = promotions.iter().any(|p| {
            p.new_tier == tla_jit::CompilationTier::Tier2 && p.specialization_plan.is_some()
        });
        if has_tier2_with_plan && !self.recompilation_controller.already_attempted() {
            if let Some(plan) = promotions
                .iter()
                .filter_map(|p| p.specialization_plan.as_ref())
                .next()
                .cloned()
            {
                self.trigger_tier2_recompilation(plan);
            }
        }

        // Stash promotions for end-of-run `--show-tiers` report.
        if !promotions.is_empty() {
            self.tier_promotion_history.extend(promotions);
        }
    }

    /// Trigger Tier 2 recompilation with a specialization plan.
    ///
    /// Extracts the same compilation inputs as `compile_jit_next_state_on_promotion`
    /// and passes them to the `RecompilationController` which spawns a background
    /// thread. The BFS loop continues with the existing Tier 1 cache.
    ///
    /// Part of #3989: speculative type specialization.
    #[cfg(feature = "jit")]
    fn trigger_tier2_recompilation(&mut self, plan: tla_jit::SpecializationPlan) {
        if !crate::check::debug::jit_enabled() {
            return;
        }

        let bytecode = match self.action_bytecode.as_ref() {
            Some(bc) => bc,
            None => return,
        };

        let chunk = bytecode.chunk.clone();
        let op_indices = bytecode.op_indices.clone();
        let state_var_count = self.module.vars.len();
        let state_layout = self.jit_state_layout.clone();

        // Extract binding specializations (same logic as Tier 1 path).
        let specializations: Vec<tla_jit::BindingSpec> = self
            .compiled
            .split_action_meta
            .as_ref()
            .map(|meta| {
                meta.iter()
                    .filter_map(|m| {
                        let name = m.name.as_ref()?;
                        if m.bindings.is_empty() {
                            return None;
                        }
                        let binding_values = tla_jit::bindings_to_jit_i64(&m.bindings)?;
                        Some(tla_jit::BindingSpec {
                            action_name: name.clone(),
                            binding_values,
                        })
                    })
                    .collect()
            })
            .unwrap_or_default();

        eprintln!(
            "[jit] Tier 2 recompilation triggered: {} specialized vars ({} int, {} bool), est. {:.2}x speedup",
            plan.specialized_var_count(),
            plan.int_var_count(),
            plan.bool_var_count(),
            plan.expected_speedup_factor,
        );

        if let Err(e) = self.recompilation_controller.trigger_recompilation(
            plan,
            chunk,
            op_indices,
            state_var_count,
            state_layout,
            specializations,
        ) {
            eprintln!("[jit] Failed to trigger Tier 2 recompilation: {e}");
        }
    }

    /// Spawn async JIT compilation on a background thread.
    ///
    /// Called lazily from `check_tier_promotions()` when the first Tier 1
    /// promotion fires. Clones the bytecode chunk and op_indices, then
    /// spawns a background thread to build the `JitNextStateCache`. The
    /// BFS loop continues with the interpreter while Cranelift compiles.
    ///
    /// The compiled cache is sent back via a `std::sync::mpsc` channel.
    /// `poll_pending_jit_compilation` does a non-blocking `try_recv` on
    /// each BFS state to check for completion.
    ///
    /// Part of #3910: Async JIT compilation with interpreter warmup.
    /// Part of #3984: Wire binding specialization — extract BindingSpec entries
    /// from split_action_meta and use build_with_stats_and_specializations so
    /// EXISTS-bound actions (e.g., `\E p \in Proc : Action(p)`) get per-binding
    /// specialized native code instead of falling back to the interpreter.
    #[cfg(feature = "jit")]
    fn compile_jit_next_state_on_promotion(&mut self) {
        if !crate::check::debug::jit_enabled() {
            return;
        }

        // Part of #3910: Use action_bytecode (compiled from split-action operators)
        // instead of invariant bytecode. The JitNextStateCache needs action operators
        // (Send, Receive, etc.) that use StoreVar for primed variables, not invariants.
        let bytecode = match self.action_bytecode.as_ref() {
            Some(bc) => bc,
            None => {
                eprintln!("[jit] no action bytecode available — action operators may not have compiled");
                return;
            }
        };

        // Clone data for the background thread (BytecodeChunk + op_indices).
        let chunk = bytecode.chunk.clone();
        let op_indices = bytecode.op_indices.clone();
        let state_var_count = self.module.vars.len();
        // Part of #3958: pass state layout for native compound access
        let state_layout = self.jit_state_layout.clone();

        // Part of #3984: Extract BindingSpec entries from split_action_meta.
        // For each split action with non-empty bindings, create a BindingSpec
        // that requests a specialized JIT function with binding values baked in
        // as LoadImm constants. This enables JIT dispatch for EXISTS-bound actions
        // like `\E p \in Proc : SendMsg(p)` where `p` takes values {p1, p2, p3}.
        let specializations: Vec<tla_jit::BindingSpec> = self
            .compiled
            .split_action_meta
            .as_ref()
            .map(|meta| {
                meta.iter()
                    .filter_map(|m| {
                        let name = m.name.as_ref()?;
                        if m.bindings.is_empty() {
                            return None; // No bindings to specialize
                        }
                        let binding_values = tla_jit::bindings_to_jit_i64(&m.bindings)?;
                        Some(tla_jit::BindingSpec {
                            action_name: name.clone(),
                            binding_values,
                        })
                    })
                    .collect()
            })
            .unwrap_or_default();

        let spec_count = specializations.len();

        let (tx, rx) = std::sync::mpsc::sync_channel(1);

        eprintln!(
            "[jit] Spawning async compilation for {} actions, {} binding specializations (state_layout={})",
            op_indices.len(),
            spec_count,
            if state_layout.is_some() { "present" } else { "NONE" },
        );

        std::thread::Builder::new()
            .name("jit-compile".to_string())
            .spawn(move || {
                let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    if specializations.is_empty() {
                        // No specializations needed — use the simpler path.
                        tla_jit::JitNextStateCache::build_with_stats_and_layout(
                            &chunk,
                            &op_indices,
                            state_var_count,
                            state_layout.as_ref(),
                        )
                    } else {
                        // Part of #3984: Build with binding specializations.
                        tla_jit::JitNextStateCache::build_with_stats_and_specializations(
                            &chunk,
                            &op_indices,
                            state_var_count,
                            state_layout.as_ref(),
                            &specializations,
                        )
                    }
                }));

                match result {
                    Ok(Ok((cache, stats))) => {
                        // Log per-action compile times from the bg thread.
                        for action_stat in &stats.per_action {
                            eprintln!("{action_stat}");
                        }
                        eprintln!("{stats}");
                        let _ = tx.send((cache, stats));
                    }
                    Ok(Err(error)) => {
                        eprintln!("[jit] async compilation failed: {error}");
                        // Channel dropped — receiver gets Disconnected on try_recv
                    }
                    Err(panic_info) => {
                        // Part of #4018: Catch Cranelift panics instead of crashing.
                        // AssertUnwindSafe is correct here because we don't access
                        // any shared state after a panic — we just drop the sender.
                        let msg = panic_info
                            .downcast_ref::<String>()
                            .map(|s| s.as_str())
                            .or_else(|| panic_info.downcast_ref::<&str>().copied())
                            .unwrap_or("unknown panic");
                        eprintln!("[jit] PANIC in async compilation (caught): {msg}");
                        eprintln!("[jit] JIT disabled — falling back to interpreter");
                        // Channel dropped — receiver gets Disconnected, model checker
                        // continues with interpreter-only mode
                    }
                }
            })
            .expect("failed to spawn JIT compilation thread");

        self.pending_jit_compilation = Some(rx);
    }

    /// Poll for completion of the async JIT compilation.
    ///
    /// Called from `prepare_jit_next_state` on each BFS state. If the
    /// background thread has finished compilation, takes the cache from
    /// the channel and installs it. Subsequent states use native code.
    ///
    /// This is a non-blocking check (`try_recv`), so it adds negligible
    /// overhead to the hot path when compilation is still in progress.
    ///
    /// Part of #3910: Async JIT compilation with interpreter warmup.
    #[cfg(feature = "jit")]
    fn poll_pending_jit_compilation(&mut self) -> bool {
        if self.jit_next_state_cache.is_some() {
            return true;
        }

        let rx = match self.pending_jit_compilation.as_ref() {
            Some(rx) => rx,
            None => return false,
        };

        match rx.try_recv() {
            Ok((cache, stats)) => {
                if cache.is_empty() {
                    eprintln!("[jit] async compilation produced no eligible actions");
                    self.pending_jit_compilation = None;
                    return false;
                }
                eprintln!(
                    "[jit] Async compilation complete: {} actions ready",
                    cache.len(),
                );

                // Compute whether ALL split actions have JIT cache entries.
                // This is checked once here so the per-state hot path can skip
                // the O(N) coverage scan on every state.
                let all_covered = self.check_jit_next_state_coverage(&cache);
                self.jit_all_next_state_compiled = all_covered;
                // Part of #4030: Cache the "any promoted" check once instead of
                // iterating all actions on every state in jit_monolithic_ready().
                if let Some(manager) = self.tier_manager.as_ref() {
                    self.jit_has_any_promoted = (0..manager.action_count())
                        .any(|i| manager.current_tier(i) >= tla_jit::CompilationTier::Tier1);
                }
                if all_covered {
                    eprintln!("[jit] All actions covered by JIT — hybrid dispatch enabled");
                } else {
                    eprintln!("[jit] NOT all actions covered — JIT hybrid dispatch will not activate");
                }

                // Part of #4030: Pre-compute JIT cache lookup keys once to avoid
                // per-state String allocation in the hot path.
                self.jit_action_lookup_keys = self.precompute_jit_lookup_keys();

                // Part of #4030: Pre-allocate reusable output scratch buffer.
                let svc = cache.state_var_count();
                self.jit_action_out_scratch = vec![0i64; svc];

                // Part of #4030: Reset adaptive performance monitor.
                self.jit_perf_monitor = (0, 0, 0);

                self.jit_next_state_cache = Some(cache);
                self.jit_cache_build_stats = Some(stats);
                self.pending_jit_compilation = None;

                // Part of #4034: Try to build CompiledBfsStep now that we
                // have all actions compiled. This also requires all invariants
                // to be JIT-compiled and a state layout to be available.
                self.try_build_compiled_bfs_step();

                // Part of #4171: Try to upgrade to fused CompiledBfsLevel.
                // This builds a single native function that processes entire
                // BFS frontiers, eliminating per-parent Rust-to-JIT crossings.
                self.try_build_compiled_bfs_level();

                true
            }
            Err(std::sync::mpsc::TryRecvError::Empty) => {
                // Compilation still in progress — interpreter continues
                false
            }
            Err(std::sync::mpsc::TryRecvError::Disconnected) => {
                // Background thread panicked or failed without sending.
                // Part of #4018: Disable JIT so we don't keep polling a dead channel.
                eprintln!("[jit] async compilation thread disconnected without result");
                self.pending_jit_compilation = None;
                self.jit_monolithic_disabled = true;
                false
            }
        }
    }

    /// Poll for Tier 2 recompilation completion and swap in the new cache.
    ///
    /// Called from the BFS hot path (non-blocking `try_recv`). When the
    /// background Tier 2 recompilation completes successfully, the new cache
    /// replaces the existing one. Pre-computed lookup keys and scratch buffers
    /// are updated to match the new cache.
    ///
    /// Part of #3989: speculative type specialization.
    #[cfg(feature = "jit")]
    #[inline]
    fn poll_tier2_recompilation(&mut self) {
        if !self.recompilation_controller.has_pending() {
            return;
        }

        if let Some(result) = self.recompilation_controller.poll_completion() {
            match result {
                Ok(recomp) => {
                    if recomp.cache.is_empty() {
                        eprintln!("[jit] Tier 2 recompilation produced no eligible actions");
                        return;
                    }
                    eprintln!(
                        "[jit] Tier 2 recompilation complete in {:.1}ms: {} actions, {} specialized vars (est. {:.2}x speedup)",
                        recomp.total_time.as_secs_f64() * 1000.0,
                        recomp.cache.len(),
                        recomp.plan.specialized_var_count(),
                        recomp.plan.expected_speedup_factor,
                    );

                    // Log per-action compile times from the recompilation.
                    for action_stat in &recomp.stats.per_action {
                        eprintln!("[jit-tier2] {action_stat}");
                    }

                    // Update coverage check for the new cache.
                    let all_covered = self.check_jit_next_state_coverage(&recomp.cache);
                    self.jit_all_next_state_compiled = all_covered;
                    // Part of #4030: Refresh the cached "any promoted" flag.
                    if let Some(manager) = self.tier_manager.as_ref() {
                        self.jit_has_any_promoted = (0..manager.action_count())
                            .any(|i| manager.current_tier(i) >= tla_jit::CompilationTier::Tier1);
                    }

                    // Recompute lookup keys and scratch buffers.
                    self.jit_action_lookup_keys = self.precompute_jit_lookup_keys();
                    let svc = recomp.cache.state_var_count();
                    self.jit_action_out_scratch = vec![0i64; svc];

                    // Swap in the new cache.
                    self.jit_next_state_cache = Some(recomp.cache);
                    self.jit_cache_build_stats = Some(recomp.stats);
                }
                Err(msg) => {
                    eprintln!("[jit] Tier 2 recompilation failed: {msg}");
                }
            }
        }
    }

    /// Attempt to build a `CompiledBfsStep` from the current JIT caches.
    ///
    /// Prerequisites:
    /// - `jit_all_next_state_compiled` is true (all actions have JIT entries)
    /// - `jit_all_compiled` is true (all invariants have JIT entries)
    /// - `jit_state_layout` is available (state is fully flat)
    ///
    /// On success, stores the result in `self.compiled_bfs_step`.
    /// On failure, logs the reason and leaves `compiled_bfs_step` as `None`.
    ///
    /// Part of #4034: Wire CompiledBfsStep into model checker BFS loop.
    #[cfg(feature = "jit")]
    fn try_build_compiled_bfs_step(&mut self) {
        // Guard: already built.
        if self.compiled_bfs_step.is_some() {
            return;
        }

        // Guard: all actions must be JIT-compiled.
        if !self.jit_all_next_state_compiled {
            return;
        }

        // Guard: all invariants must be JIT-compiled.
        if !self.jit_all_compiled {
            return;
        }

        // Guard: need state layout for BfsStepSpec.
        let state_layout = match self.jit_state_layout.as_ref() {
            Some(l) => l.clone(),
            None => return,
        };

        // Guard: need split action metadata to build descriptors.
        let meta = match self.compiled.split_action_meta.as_ref() {
            Some(m) if !m.is_empty() => m,
            _ => return,
        };

        // Guard: need the JIT caches.
        let next_state_cache = match self.jit_next_state_cache.as_ref() {
            Some(c) => c,
            None => return,
        };
        let invariant_cache = match self.jit_cache.as_ref() {
            Some(c) => c,
            None => return,
        };

        let state_len = next_state_cache.state_var_count();

        // Build action lookup keys and descriptors.
        let mut action_names = Vec::with_capacity(meta.len());
        let mut action_descriptors = Vec::with_capacity(meta.len());
        for (idx, m) in meta.iter().enumerate() {
            let name = match &m.name {
                Some(n) => n.clone(),
                None => return, // Can't build without names for all actions
            };

            let lookup_key = if m.bindings.is_empty() {
                name.clone()
            } else {
                match tla_jit::bindings_to_jit_i64(&m.bindings) {
                    Some(vals) => tla_jit::specialized_key(&name, &vals),
                    None => return, // Compound bindings — can't build
                }
            };

            let binding_values = if m.bindings.is_empty() {
                Vec::new()
            } else {
                match tla_jit::bindings_to_jit_i64(&m.bindings) {
                    Some(vals) => vals,
                    None => return,
                }
            };

            // Get per-action metadata from the cache.
            let meta_entry = match next_state_cache.action_metadata(&lookup_key) {
                Some(m) => m,
                None => return, // Missing metadata — can't build
            };

            action_descriptors.push(tla_jit::ActionDescriptor {
                name: lookup_key.clone(),
                action_idx: idx as u32,
                binding_values,
                read_vars: meta_entry.read_vars.clone(),
                write_vars: meta_entry.write_vars.clone(),
            });
            action_names.push(lookup_key);
        }

        // Resolve action function pointers.
        let action_fn_ptrs = match next_state_cache.resolve_ordered(&action_names) {
            Some(fns) => fns,
            None => return, // Not all actions compiled
        };

        // Build CompiledActionFn wrappers.
        let compiled_actions: Vec<tla_jit::CompiledActionFn> = action_descriptors
            .into_iter()
            .zip(action_fn_ptrs)
            .map(|(desc, func)| tla_jit::CompiledActionFn::new(desc, func))
            .collect();

        // Build invariant descriptors and resolve function pointers.
        let invariant_names = &self.config.invariants;
        let invariant_fn_ptrs = match invariant_cache.resolve_ordered(invariant_names) {
            Some(fns) => fns,
            None => return, // Not all invariants compiled
        };

        let invariant_descriptors: Vec<tla_jit::InvariantDescriptor> = invariant_names
            .iter()
            .enumerate()
            .map(|(idx, name)| tla_jit::InvariantDescriptor {
                name: name.clone(),
                invariant_idx: idx as u32,
            })
            .collect();

        let compiled_invariants: Vec<tla_jit::CompiledInvariantFn> = invariant_descriptors
            .into_iter()
            .zip(invariant_fn_ptrs)
            .map(|(desc, func)| tla_jit::CompiledInvariantFn::new(desc, func))
            .collect();

        // Build BfsStepSpec.
        let spec = tla_jit::BfsStepSpec {
            state_len,
            state_layout,
            actions: compiled_actions
                .iter()
                .map(|a| a.descriptor.clone())
                .collect(),
            invariants: compiled_invariants
                .iter()
                .map(|i| i.descriptor.clone())
                .collect(),
        };

        // Estimate expected states for AtomicFpSet sizing.
        let expected_states = self.states_count().max(1024);

        match tla_jit::CompiledBfsStep::build(
            &spec,
            compiled_actions,
            compiled_invariants,
            expected_states,
        ) {
            Ok(step) => {
                eprintln!(
                    "[jit] CompiledBfsStep built: {} actions, {} invariants, state_len={}",
                    meta.len(),
                    invariant_names.len(),
                    state_len,
                );
                self.compiled_bfs_step = Some(step);
            }
            Err(e) => {
                eprintln!("[jit] CompiledBfsStep build failed: {e}");
            }
        }
    }

    /// Attempt to build a fused `CompiledBfsLevel` from the current JIT caches.
    ///
    /// This upgrades the per-parent `CompiledBfsStep` to a fused BFS level
    /// function that processes entire frontiers in a single native call.
    ///
    /// Prerequisites (same as `try_build_compiled_bfs_step` plus):
    /// - `compiled_bfs_step` is already built
    /// - Compiled BFS is not disabled via config or env var
    /// - The fused level function compiles successfully
    ///
    /// On success, stores the result in `self.compiled_bfs_level`.
    /// On failure, logs the reason — the per-parent `CompiledBfsStep` path
    /// remains available as a fallback.
    ///
    /// Part of #4171: End-to-end compiled BFS wiring.
    #[cfg(feature = "jit")]
    fn try_build_compiled_bfs_level(&mut self) {
        // Guard: already built.
        if self.compiled_bfs_level.is_some() {
            return;
        }

        // Guard: force-disabled via config.
        if self.config.use_compiled_bfs == Some(false) {
            return;
        }

        // Guard: force-disabled via env var.
        if crate::check::debug::compiled_bfs_disabled() {
            return;
        }

        // Guard: need CompiledBfsStep as the base requirement.
        if self.compiled_bfs_step.is_none() {
            return;
        }

        // Guard: all actions must be JIT-compiled.
        if !self.jit_all_next_state_compiled {
            return;
        }

        // Guard: all invariants must be JIT-compiled.
        if !self.jit_all_compiled {
            return;
        }

        // Guard: need state layout for BfsStepSpec.
        let state_layout = match self.jit_state_layout.as_ref() {
            Some(l) => l.clone(),
            None => return,
        };

        // Guard: need split action metadata to build descriptors.
        let meta = match self.compiled.split_action_meta.as_ref() {
            Some(m) if !m.is_empty() => m,
            _ => return,
        };

        // Guard: need the JIT caches.
        let next_state_cache = match self.jit_next_state_cache.as_ref() {
            Some(c) => c,
            None => return,
        };
        let invariant_cache = match self.jit_cache.as_ref() {
            Some(c) => c,
            None => return,
        };

        let state_len = next_state_cache.state_var_count();

        // Build action descriptors (same logic as try_build_compiled_bfs_step).
        let mut action_names = Vec::with_capacity(meta.len());
        let mut action_descriptors = Vec::with_capacity(meta.len());
        for (idx, m) in meta.iter().enumerate() {
            let name = match &m.name {
                Some(n) => n.clone(),
                None => return,
            };

            let lookup_key = if m.bindings.is_empty() {
                name.clone()
            } else {
                match tla_jit::bindings_to_jit_i64(&m.bindings) {
                    Some(vals) => tla_jit::specialized_key(&name, &vals),
                    None => return,
                }
            };

            let binding_values = if m.bindings.is_empty() {
                Vec::new()
            } else {
                match tla_jit::bindings_to_jit_i64(&m.bindings) {
                    Some(vals) => vals,
                    None => return,
                }
            };

            let meta_entry = match next_state_cache.action_metadata(&lookup_key) {
                Some(m) => m,
                None => return,
            };

            action_descriptors.push(tla_jit::ActionDescriptor {
                name: lookup_key.clone(),
                action_idx: idx as u32,
                binding_values,
                read_vars: meta_entry.read_vars.clone(),
                write_vars: meta_entry.write_vars.clone(),
            });
            action_names.push(lookup_key);
        }

        // Resolve action function pointers.
        let action_fn_ptrs = match next_state_cache.resolve_ordered(&action_names) {
            Some(fns) => fns,
            None => return,
        };

        let compiled_actions: Vec<tla_jit::CompiledActionFn> = action_descriptors
            .into_iter()
            .zip(action_fn_ptrs)
            .map(|(desc, func)| tla_jit::CompiledActionFn::new(desc, func))
            .collect();

        // Build invariant descriptors and resolve function pointers.
        let invariant_names = &self.config.invariants;
        let invariant_fn_ptrs = match invariant_cache.resolve_ordered(invariant_names) {
            Some(fns) => fns,
            None => return,
        };

        let invariant_descriptors: Vec<tla_jit::InvariantDescriptor> = invariant_names
            .iter()
            .enumerate()
            .map(|(idx, name)| tla_jit::InvariantDescriptor {
                name: name.clone(),
                invariant_idx: idx as u32,
            })
            .collect();

        let compiled_invariants: Vec<tla_jit::CompiledInvariantFn> = invariant_descriptors
            .into_iter()
            .zip(invariant_fn_ptrs)
            .map(|(desc, func)| tla_jit::CompiledInvariantFn::new(desc, func))
            .collect();

        // Build BfsStepSpec.
        let spec = tla_jit::BfsStepSpec {
            state_len,
            state_layout,
            actions: compiled_actions
                .iter()
                .map(|a| a.descriptor.clone())
                .collect(),
            invariants: compiled_invariants
                .iter()
                .map(|i| i.descriptor.clone())
                .collect(),
        };

        // Estimate expected states for AtomicFpSet sizing.
        let expected_states = self.states_count().max(1024);

        // Build the fused level function. Falls back gracefully on failure.
        match tla_jit::CompiledBfsLevel::build_fused(
            &spec,
            compiled_actions,
            compiled_invariants,
            expected_states,
        ) {
            Ok(level) => {
                let source = if self.config.use_compiled_bfs == Some(true) {
                    "config"
                } else if crate::check::debug::compiled_bfs_enabled() {
                    "TLA2_COMPILED_BFS=1"
                } else {
                    "auto-detected"
                };
                eprintln!(
                    "[compiled-bfs] fused level built ({}): {} actions, {} invariants, state_len={}",
                    source,
                    meta.len(),
                    invariant_names.len(),
                    state_len,
                );
                self.compiled_bfs_level = Some(level);
            }
            Err(e) => {
                eprintln!("[compiled-bfs] fused level build failed: {e} — using per-parent step");
            }
        }
    }

    /// Check whether the compiled BFS path should be used.
    ///
    /// This implements the decision hierarchy for the compiled BFS level loop:
    /// 1. `Config::use_compiled_bfs = Some(false)` -> disabled
    /// 2. `TLA2_NO_COMPILED_BFS=1` -> disabled
    /// 3. `Config::use_compiled_bfs = Some(true)` -> enabled if level ready
    /// 4. `TLA2_COMPILED_BFS=1` -> enabled if level ready
    /// 5. Otherwise -> disabled (opt-in only for now)
    ///
    /// The compiled BFS path is opt-in because it is a new code path that
    /// needs production hardening. Once proven correct across the full spec
    /// suite, step 5 can be changed to auto-detect.
    ///
    /// Part of #4171: End-to-end compiled BFS wiring.
    #[cfg(feature = "jit")]
    #[must_use]
    pub(in crate::check) fn should_use_compiled_bfs(&self) -> bool {
        // 1. Programmatic force-disable
        if self.config.use_compiled_bfs == Some(false) {
            return false;
        }
        // 2. Env var force-disable
        if crate::check::debug::compiled_bfs_disabled() {
            return false;
        }
        // 3. Programmatic force-enable (if level is ready)
        if self.config.use_compiled_bfs == Some(true) {
            return self.compiled_bfs_level.is_some();
        }
        // 4. Env var force-enable (if level is ready)
        if crate::check::debug::compiled_bfs_enabled() {
            return self.compiled_bfs_level.is_some();
        }
        // 5. Not explicitly enabled — opt-in only for now.
        // The compiled BFS level may be built (for benchmarking, etc.)
        // but won't be used unless explicitly requested.
        false
    }

    /// Flatten the current state for JIT next-state dispatch.
    ///
    /// Populates `jit_state_scratch` with the flattened i64 representation
    /// of the current state. Returns `true` if flattening succeeded,
    /// `false` if the state contains compound types that can't be serialized.
    ///
    /// Call this once per parent state, then use `try_jit_action` for each
    /// action in the split-action loop.
    ///
    /// Part of #3910: JIT next-state dispatch.
    /// Part of #3910: Polls async compilation on each state.
    #[cfg(feature = "jit")]
    #[inline]
    pub(in crate::check) fn prepare_jit_next_state(
        &mut self,
        current_array: &super::ArrayState,
    ) -> bool {
        // Poll for async compilation completion if no cache yet.
        if self.jit_next_state_cache.is_none() {
            if !self.poll_pending_jit_compilation() {
                return false;
            }
        }
        let ok = super::invariants::flatten_state_to_i64_selective(
            current_array,
            &mut self.jit_state_scratch,
            &[], // empty = all vars (next-state needs full state)
        );
        if ok {
            // Part of #4030: Cache whether the state is all-scalar so the fused
            // path can skip clear_compound_scratch() calls per action.
            self.jit_state_all_scalar = current_array
                .values()
                .iter()
                .all(|cv| cv.is_int() || cv.is_bool());
        }
        ok
    }

    /// Check whether ALL split actions have JIT cache entries.
    ///
    /// For each action in `split_action_meta`, computes the cache lookup key
    /// (base name for binding-free, specialized key for EXISTS-bound) and checks
    /// if it exists in the cache. Returns true only if every action is covered.
    ///
    /// Called once when the JIT cache is installed to set the
    /// `jit_all_next_state_compiled` flag. This avoids O(N) per-state checks.
    #[cfg(feature = "jit")]
    fn check_jit_next_state_coverage(
        &self,
        cache: &tla_jit::JitNextStateCache,
    ) -> bool {
        let meta = match self.compiled.split_action_meta.as_ref() {
            Some(m) if !m.is_empty() => m,
            _ => return false,
        };

        let mut all_covered = true;
        let mut covered_count = 0usize;
        let mut missing_count = 0usize;

        for m in meta {
            let name = match &m.name {
                Some(n) => n,
                None => {
                    all_covered = false;
                    missing_count += 1;
                    continue;
                }
            };

            let lookup_key = if m.bindings.is_empty() {
                name.clone()
            } else {
                match tla_jit::bindings_to_jit_i64(&m.bindings) {
                    Some(vals) => tla_jit::specialized_key(name, &vals),
                    None => {
                        // Compound binding values — can't specialize.
                        eprintln!(
                            "[jit] action '{}': compound binding values cannot be specialized",
                            name,
                        );
                        all_covered = false;
                        missing_count += 1;
                        continue;
                    }
                }
            };

            if cache.contains_action(&lookup_key) {
                covered_count += 1;
            } else {
                eprintln!(
                    "[jit] action '{}' (key='{}', bindings={}): NOT in JIT cache",
                    name,
                    lookup_key,
                    m.bindings.len(),
                );
                all_covered = false;
                missing_count += 1;
            }
        }

        eprintln!(
            "[jit] JIT cache coverage: {}/{} actions compiled ({} missing)",
            covered_count,
            meta.len(),
            missing_count,
        );

        all_covered
    }

    /// Pre-compute JIT cache lookup keys for all split actions.
    ///
    /// Called once when the JIT cache is installed. Returns a Vec of lookup keys
    /// matching the order of `split_action_meta`. For binding-free actions, the
    /// key is the action name. For EXISTS-bound actions, it's the specialized key.
    /// Empty string marks actions that can't be JIT-compiled.
    ///
    /// Part of #4030: Eliminate per-state String allocation in JIT hybrid dispatch.
    #[cfg(feature = "jit")]
    fn precompute_jit_lookup_keys(&self) -> Vec<String> {
        let meta = match self.compiled.split_action_meta.as_ref() {
            Some(m) => m,
            None => return Vec::new(),
        };
        meta.iter()
            .map(|m| {
                let name = match &m.name {
                    Some(n) => n,
                    None => return String::new(),
                };
                if m.bindings.is_empty() {
                    name.clone()
                } else {
                    tla_jit::bindings_to_jit_i64(&m.bindings)
                        .map(|vals| tla_jit::specialized_key(name, &vals))
                        .unwrap_or_default()
                }
            })
            .collect()
    }

    /// No-op stub when JIT feature is disabled.
    #[cfg(not(feature = "jit"))]
    #[inline]
    #[allow(dead_code)]
    pub(in crate::check) fn prepare_jit_next_state(
        &mut self,
        _current_array: &super::ArrayState,
    ) -> bool {
        false
    }

    /// Attempt JIT-compiled evaluation of a single split action.
    ///
    /// Requires `prepare_jit_next_state` to have been called first to populate
    /// the flattened state scratch buffer. Checks if `action_name` is in the
    /// JIT next-state cache and evaluates it.
    ///
    /// Returns:
    /// - `Some(Ok(Some(flat_successor)))` — action is enabled, JIT produced a flat successor
    /// - `Some(Ok(None))` — action is disabled (guard=false), no successor
    /// - `None` — action not compiled or needs interpreter fallback
    ///
    /// Part of #4032: Returns flat i64 buffers instead of ArrayState. The caller
    /// defers unflatten to after the dedup check to avoid materializing Value
    /// objects for duplicate states.
    ///
    /// Updates `next_state_dispatch` counters.
    ///
    /// Part of #3910: JIT next-state dispatch — per-action in split-action loop.
    #[cfg(feature = "jit")]
    #[inline]
    pub(in crate::check) fn try_jit_action(
        &mut self,
        action_name: &str,
        _current_array: &super::ArrayState,
    ) -> Option<Result<Option<JitFlatSuccessor>, ()>> {
        let cache = self.jit_next_state_cache.as_ref()?;
        let state_var_count = cache.state_var_count();
        let flat_state = &self.jit_state_scratch;

        self.next_state_dispatch.total += 1;

        // Clear the compound scratch buffer before each action evaluation.
        // JIT-compiled RecordNew writes serialized records here; unflatten
        // reads from it when it sees COMPOUND_SCRATCH_TAG in the output.
        // Part of #3909: native RecordNew lowering.
        tla_jit::abi::clear_compound_scratch();

        match cache.eval_action(action_name, flat_state) {
            Some(Ok(tla_jit::JitActionResult::Enabled { successor })) => {
                self.next_state_dispatch.jit_hit += 1;
                // Part of #4032: Return flat buffers instead of ArrayState.
                // Save a snapshot of the input buffer so unflatten (if needed later)
                // can deserialize compound values modified in-place by FuncExcept.
                let flat_succ = JitFlatSuccessor {
                    jit_output: successor,
                    jit_input: flat_state.clone(),
                    state_var_count,
                };
                Some(Ok(Some(flat_succ)))
            }
            Some(Ok(tla_jit::JitActionResult::Disabled)) => {
                self.next_state_dispatch.jit_hit += 1;
                Some(Ok(None)) // Action guard is false — no successor
            }
            Some(Err(_)) => {
                self.next_state_dispatch.jit_error += 1;
                None // Runtime error — fall back to interpreter
            }
            None => {
                // Not compiled or FallbackNeeded
                if cache.contains_action(action_name) {
                    self.next_state_dispatch.jit_fallback += 1;
                } else {
                    self.next_state_dispatch.jit_not_compiled += 1;
                }
                None
            }
        }
    }

    /// Evaluate a single split action via JIT using the reusable scratch buffer.
    ///
    /// Like `try_jit_action` but uses `eval_action_into` to write the successor
    /// into `jit_action_out_scratch` instead of allocating a new Vec<i64> per call.
    /// This eliminates the dominant per-action allocation on the JIT hot path.
    ///
    /// Returns:
    /// - `Some(Ok(Some(successor)))` — action is enabled, JIT produced a successor
    /// - `Some(Ok(None))` — action is disabled (guard=false), no successor
    /// - `Some(Err(()))` — JIT runtime error
    /// - `None` — action not compiled or needs interpreter fallback
    ///
    /// Part of #4030: Eliminate per-action Vec allocation in JIT dispatch.
    #[cfg(feature = "jit")]
    #[inline]
    pub(in crate::check) fn try_jit_action_into(
        &mut self,
        action_name: &str,
        current_array: &super::ArrayState,
    ) -> Option<Result<Option<super::ArrayState>, ()>> {
        use super::invariants::unflatten_i64_to_array_state_with_input;

        // Extract state_var_count first, then split borrows.
        let state_var_count = match self.jit_next_state_cache.as_ref() {
            Some(c) => c.state_var_count(),
            None => return None,
        };

        self.next_state_dispatch.total += 1;

        // Clear the compound scratch buffer before each action evaluation.
        tla_jit::abi::clear_compound_scratch();

        // Ensure scratch buffer is large enough.
        if self.jit_action_out_scratch.len() < state_var_count {
            self.jit_action_out_scratch.resize(state_var_count, 0);
        }

        // Part of #4030: Use eval_action_into with the reusable scratch buffer.
        // Split borrow: cache (immut) + jit_state_scratch (immut) + jit_action_out_scratch (mut).
        let eval_result = {
            let cache = self.jit_next_state_cache.as_ref().expect("checked above");
            cache.eval_action_into(
                action_name,
                &self.jit_state_scratch,
                &mut self.jit_action_out_scratch,
            )
        };

        match eval_result {
            Some(Ok(true)) => {
                // Action enabled — successor is in jit_action_out_scratch.
                self.next_state_dispatch.jit_hit += 1;
                let succ_array = unflatten_i64_to_array_state_with_input(
                    current_array,
                    &self.jit_action_out_scratch,
                    state_var_count,
                    Some(&self.jit_state_scratch),
                );
                Some(Ok(Some(succ_array)))
            }
            Some(Ok(false)) => {
                self.next_state_dispatch.jit_hit += 1;
                Some(Ok(None)) // Action guard is false — no successor
            }
            Some(Err(_)) => {
                self.next_state_dispatch.jit_error += 1;
                Some(Err(())) // Runtime error
            }
            None => {
                // Not compiled or FallbackNeeded
                let has_action = self
                    .jit_next_state_cache
                    .as_ref()
                    .map_or(false, |c| c.contains_action(action_name));
                if has_action {
                    self.next_state_dispatch.jit_fallback += 1;
                } else {
                    self.next_state_dispatch.jit_not_compiled += 1;
                }
                None
            }
        }
    }

    /// No-op stub when JIT feature is disabled.
    #[cfg(not(feature = "jit"))]
    #[inline]
    pub(in crate::check) fn check_tier_promotions(&mut self) {}

    /// Format a detailed per-action tier compilation report (sequential mode).
    ///
    /// Mirrors `SharedTierState::format_tier_report` for parallel mode.
    /// Called at end-of-run when `TLA2_SHOW_TIERS=1` is set.
    ///
    /// Part of #3910, #3932: `--show-tiers` CLI diagnostic for sequential BFS.
    #[cfg(feature = "jit")]
    pub(in crate::check) fn format_tier_report(&self) -> String {
        use std::fmt::Write as _;

        let manager = match self.tier_manager.as_ref() {
            Some(m) => m,
            None => return String::new(),
        };

        let action_count = manager.action_count();
        let summary = manager.tier_summary();

        // Count promotions per action.
        let mut per_action_promotions = vec![0usize; action_count];
        for promo in &self.tier_promotion_history {
            if promo.action_id < action_count {
                per_action_promotions[promo.action_id] += 1;
            }
        }

        let mut out = String::new();
        let _ = writeln!(out);
        let _ = writeln!(out, "=== Tier Compilation Report ===");
        let _ = writeln!(
            out,
            "{:<30} {:>18} {:>12} {:>10} {:>12}",
            "Action", "Tier", "Evals", "Avg BF", "Promotions"
        );
        let _ = writeln!(out, "{}", "-".repeat(86));

        for i in 0..action_count {
            let label = self
                .compiled
                .split_action_meta
                .as_ref()
                .and_then(|meta| meta.get(i))
                .and_then(|m| m.name.as_deref())
                .unwrap_or("Next");
            let tier = manager.current_tier(i);
            let evals = self.action_eval_counts.get(i).copied().unwrap_or(0);
            let total_succ = self.action_succ_totals.get(i).copied().unwrap_or(0);
            let bf = if evals > 0 {
                total_succ as f64 / evals as f64
            } else {
                0.0
            };
            let promos = per_action_promotions.get(i).copied().unwrap_or(0);
            // Truncate label to fit column.
            let display_label = if label.len() <= 30 {
                label.to_string()
            } else {
                format!("{}..", &label[..28])
            };
            let _ = writeln!(
                out,
                "{:<30} {:>18} {:>12} {:>10.1} {:>12}",
                display_label, tier, evals, bf, promos,
            );
        }

        // Promotion event log.
        if !self.tier_promotion_history.is_empty() {
            let _ = writeln!(out);
            let _ = writeln!(out, "Promotion events:");
            for promo in &self.tier_promotion_history {
                let label = self
                    .compiled
                    .split_action_meta
                    .as_ref()
                    .and_then(|meta| meta.get(promo.action_id))
                    .and_then(|m| m.name.as_deref())
                    .unwrap_or("Next");
                let _ = writeln!(
                    out,
                    "  '{}': {} -> {} at {} evals (bf={:.1})",
                    label,
                    promo.old_tier,
                    promo.new_tier,
                    promo.evaluations_at_promotion,
                    promo.branching_factor,
                );
            }
        }

        // JIT invariant dispatch counters.
        let _ = writeln!(out);
        let _ = writeln!(
            out,
            "JIT invariant dispatch: hits={}, fallbacks={}, not_compiled={}, total={}",
            self.jit_hit, self.jit_fallback, self.jit_not_compiled, self.total_invariant_evals,
        );

        // Next-state JIT dispatch counters.
        let ns = &self.next_state_dispatch;
        if ns.total > 0 {
            let _ = writeln!(
                out,
                "JIT next-state dispatch: hits={}, fallbacks={}, not_compiled={}, errors={}, total={}",
                ns.jit_hit, ns.jit_fallback, ns.jit_not_compiled, ns.jit_error, ns.total,
            );
        }

        // Compile latency (Part of #3910).
        if let Some(ref build_stats) = self.jit_cache_build_stats {
            let _ = writeln!(out);
            let _ = writeln!(
                out,
                "Compile latency: {:.1}ms total ({:.1}ms Cranelift, {:.1}ms overhead)",
                build_stats.total_build_time.as_secs_f64() * 1000.0,
                build_stats.total_compile_time().as_secs_f64() * 1000.0,
                (build_stats.total_build_time - build_stats.total_compile_time())
                    .as_secs_f64()
                    * 1000.0,
            );
            for stat in &build_stats.per_action {
                let _ = writeln!(
                    out,
                    "  {:30} {:.1}ms ({} opcodes) [{}]",
                    stat.action_name,
                    stat.compile_time.as_secs_f64() * 1000.0,
                    stat.opcode_count,
                    if stat.success { "ok" } else { "FAIL" },
                );
            }
        }

        // Part of #4031: Warmup gate status.
        {
            let (jit_ns, interp_ns, sampled) = self.jit_perf_monitor;
            if sampled > 0 {
                let _ = writeln!(out);
                let jit_avg = jit_ns as f64 / sampled as f64 / 1000.0;
                if interp_ns > 0 {
                    let initial_validation = 100u32;
                    let validation_states =
                        initial_validation.saturating_sub(self.jit_validation_remaining);
                    let interp_avg = if validation_states > 0 {
                        interp_ns as f64 / validation_states as f64 / 1000.0
                    } else {
                        0.0
                    };
                    let ratio = if interp_avg > 0.0 {
                        jit_avg / interp_avg
                    } else {
                        0.0
                    };
                    let _ = writeln!(
                        out,
                        "Warmup gate: sampled={}, JIT avg={:.1}us, interp avg={:.1}us, ratio={:.2}x, decision={}",
                        sampled, jit_avg, interp_avg, ratio,
                        if self.jit_monolithic_disabled { "DISABLED" } else { "enabled" },
                    );
                } else {
                    let _ = writeln!(
                        out,
                        "Warmup gate: sampled={}, JIT avg={:.1}us, no interp data, decision={}",
                        sampled, jit_avg,
                        if self.jit_monolithic_disabled { "DISABLED" } else { "enabled" },
                    );
                }
            }
        }

        // Summary.
        let all_total = self.total_invariant_evals + ns.total;
        let all_hits = self.jit_hit + ns.jit_hit;
        let hit_rate = if all_total > 0 {
            all_hits as f64 / all_total as f64 * 100.0
        } else {
            0.0
        };
        let _ = writeln!(
            out,
            "Summary: {} actions, {} eligible, tier0={}, tier1={}, tier2={} ({:.1}% JIT hit rate)",
            summary.total, summary.eligible, summary.interpreter, summary.tier1, summary.tier2,
            hit_rate,
        );
        let _ = writeln!(out);
        out
    }

    /// No-op stub when JIT feature is disabled.
    #[cfg(not(feature = "jit"))]
    #[inline]
    #[allow(dead_code)]
    pub(in crate::check) fn format_tier_report(&self) -> String {
        String::new()
    }

    /// Check if state exploration limit has been reached.
    /// Returns `Some(CheckResult)` if we should stop, `None` to continue.
    ///
    /// Part of #2133: Added `print_symmetry_stats()` to match the full-state
    /// inline implementation. Previously only full-state mode printed symmetry
    /// stats on state-limit return; no-trace mode (which uses this helper)
    /// silently omitted them.
    pub(in crate::check) fn check_state_limit(&mut self) -> Option<CheckResult> {
        if let Some(max_states) = self.exploration.max_states {
            if self.states_count() >= max_states {
                self.stats.states_found = self.states_count();
                self.update_coverage_totals();
                print_enum_profile_stats();
                print_eval_profile_stats();
                print_symmetry_stats();
                return Some(CheckResult::LimitReached {
                    limit_type: LimitType::States,
                    stats: self.stats.clone(),
                });
            }
        }
        None
    }

    /// Check a successor state for invariant violations.
    ///
    /// Sets trace context, evaluates successor invariants (JIT/bytecode/tree-walk
    /// or TIR), then clears trace context.
    ///
    /// Part of #3767: when cooperative mode is active and PDR has proved all
    /// invariants, per-state invariant evaluation is skipped entirely. This is
    /// the CDEMC fast path — once PDR returns `Safe`, the BFS lane only needs
    /// to explore for liveness, not re-verify safety at every state.
    ///
    /// Part of #3773: when PDR has proved some (but not all) invariants,
    /// only the unproved invariants are checked per-state. The proved
    /// invariant names are filtered out, avoiding redundant evaluation.
    pub(in crate::check) fn check_successor_invariant(
        &mut self,
        parent_fp: Fingerprint,
        succ: &ArrayState,
        succ_fp: Fingerprint,
        succ_level: u32,
    ) -> InvariantOutcome {
        // Part of #3767: cooperative invariant skip — if PDR has proved all
        // invariants, skip the per-state evaluation entirely.
        #[cfg(feature = "z4")]
        if let Some(ref coop) = self.cooperative {
            if coop.invariants_proved() {
                return InvariantOutcome::Ok;
            }
        }

        // Part of #3773: per-invariant partial skip — if PDR has proved
        // some invariants, check only the unproved ones.
        #[cfg(feature = "z4")]
        let partial_unproved: Option<Vec<String>> = self.cooperative_unproved_invariants();
        #[cfg(not(feature = "z4"))]
        let partial_unproved: Option<Vec<String>> = None;

        // Set trace context before invariant evaluation (Part of #1117).
        self.set_trace_context_for_successor(parent_fp, succ);

        // Part of #3773/#3810: per-invariant partial skip takes precedence over
        // other dispatch paths (TIR, JIT, bytecode). When PDR has proved some
        // invariants, we evaluate only the unproved subset via the canonical
        // `check_invariants_for_successor` path regardless of which eval backend
        // is active. This avoids the need to plumb partial-skip awareness into
        // every eval backend (TIR, JIT, bytecode).
        let outcome = if let Some(ref unproved) = partial_unproved {
            // Part of #3773: partial skip path — evaluate only unproved invariants.
            self.ctx.set_tlc_level(succ_level);
            crate::eval::clear_for_bound_state_eval_scope(&self.ctx);
            match crate::checker_ops::check_invariants_for_successor(
                &mut self.ctx,
                unproved,
                &self.compiled.eval_state_invariants,
                succ,
                succ_fp,
                succ_level,
            ) {
                InvariantOutcome::Ok => InvariantOutcome::Ok,
                other => other,
            }
        } else {
            // Route through check_invariants_array which has the
            // JIT/bytecode/TIR fast path (Part of #3700, #3950).
            // JIT native code takes priority over TIR eval when available;
            // check_invariants_array handles JIT dispatch + TIR/treewalk fallback.
            self.ctx.set_tlc_level(succ_level);
            crate::eval::clear_for_bound_state_eval_scope(&self.ctx);
            match self.check_invariants_array(succ) {
                Ok(None) => InvariantOutcome::Ok,
                Ok(Some(invariant)) => InvariantOutcome::Violation {
                    invariant,
                    state_fp: succ_fp,
                },
                Err(error) => InvariantOutcome::Error(error),
            }
        };
        self.clear_trace_context();
        outcome
    }

    /// Stage a terminal successor into seen/trace storage so trace
    /// reconstruction can include the violating state.
    ///
    /// The normal BFS path admits successors only after invariant/property
    /// checks pass. That keeps the hot path clone-free, but fatal violations
    /// need the successor recorded before reconstruction runs. This helper is
    /// intentionally used only on the terminal path; continue-on-error keeps
    /// the normal admit/enqueue flow so violating states still get explored.
    #[allow(clippy::result_large_err)]
    pub(in crate::check) fn stage_successor_for_terminal_trace(
        &mut self,
        parent_fp: Fingerprint,
        succ: &ArrayState,
        succ_fp: Fingerprint,
        succ_depth: usize,
    ) -> Result<(), CheckResult> {
        if self.exploration.continue_on_error {
            return Ok(());
        }

        if self.state_storage.store_full_states {
            let _ = self.mark_state_seen_owned_checked(
                succ_fp,
                succ.clone(),
                Some(parent_fp),
                succ_depth,
            )?;
        } else {
            let _ = self.mark_state_seen_checked(succ_fp, succ, Some(parent_fp), succ_depth)?;
        }
        Ok(())
    }

    /// Handle an invariant violation by marking the state seen, recording the
    /// violation, and returning the appropriate `CheckResult`.
    ///
    /// Returns `Some(CheckResult)` if the caller should return immediately
    /// (either fatal violation or error), `None` if `continue_on_error` is
    /// active and the caller should enqueue the violating state.
    ///
    /// Part of #1801: routes through `finalize_terminal_result` so storage-error
    /// precedence applies even to invariant violations found mid-BFS.
    ///
    /// Part of #2676/#3710: mixed properties may fail their state-level safety
    /// terms during BFS even when the property still has a temporal remainder.
    /// Use the dedicated attribution list instead of the full-promotion skip list.
    pub(in crate::check) fn handle_invariant_violation(
        &mut self,
        violation: String,
        succ_fp: Fingerprint,
        succ_depth: usize,
    ) -> Option<CheckResult> {
        self.stats.max_depth = self.stats.max_depth.max(succ_depth);
        self.stats.states_found = self.states_count();
        if self.record_invariant_violation(violation.clone(), succ_fp) {
            self.update_coverage_totals();
            let trace = self.reconstruct_trace(succ_fp);
            let candidate = if self
                .compiled
                .state_property_violation_names
                .contains(&violation)
            {
                // Part of #2676: This invariant was promoted from a PROPERTY entry.
                // Report as PropertyViolation to match TLC's error message format.
                CheckResult::PropertyViolation {
                    property: violation,
                    kind: crate::check::api::PropertyViolationKind::StateLevel,
                    trace,
                    stats: self.stats.clone(),
                }
            } else {
                CheckResult::InvariantViolation {
                    invariant: violation,
                    trace,
                    stats: self.stats.clone(),
                }
            };
            return Some(self.finalize_terminal_result(candidate));
        }
        // continue_on_error: violation recorded but exploration continues
        None
    }

    /// Check whether the current state is a deadlock (no successors and not terminal).
    ///
    /// Returns `Some(CheckResult::Deadlock { .. })` if deadlock detected, `None` otherwise.
    pub(in crate::check) fn check_deadlock(
        &mut self,
        fp: Fingerprint,
        current_array: &ArrayState,
        successors_empty: bool,
        had_raw_successors: bool,
    ) -> Option<CheckResult> {
        if self.exploration.check_deadlock && successors_empty && !had_raw_successors {
            let is_terminal = match self.is_terminal_state_array(current_array) {
                Ok(value) => value,
                Err(error) => {
                    self.update_coverage_totals();
                    return Some(check_error_to_result(error, &self.stats));
                }
            };
            if !is_terminal {
                self.stats.states_found = self.states_count();
                self.update_coverage_totals();
                let trace = self.reconstruct_trace(fp);
                return Some(CheckResult::Deadlock {
                    trace,
                    stats: self.stats.clone(),
                });
            }
        }
        None
    }

    /// Check whether the checkpoint interval has elapsed without building the frontier.
    pub(in crate::check) fn should_save_checkpoint(&self) -> bool {
        match (&self.checkpoint.dir, self.checkpoint.last_time) {
            (Some(_), Some(t)) => t.elapsed() >= self.checkpoint.interval,
            _ => false,
        }
    }

    /// Save a checkpoint now using a pre-built state frontier.
    ///
    /// Callers must check `should_save_checkpoint()` before building the frontier
    /// and calling this method to avoid unnecessary State conversions.
    pub(in crate::check) fn save_checkpoint_now(&mut self, state_frontier: &VecDeque<State>) {
        let checkpoint_dir = match &self.checkpoint.dir {
            Some(dir) => dir.clone(),
            None => return,
        };
        // Part of #3178: extract paths before mutable borrow in create_checkpoint.
        let spec_path = self.checkpoint.spec_path.clone();
        let config_path = self.checkpoint.config_path.clone();
        let checkpoint = match self.create_checkpoint(
            state_frontier,
            spec_path.as_deref(),
            config_path.as_deref(),
        ) {
            Ok(cp) => cp,
            Err(e) => {
                // Part of #1433: log the checkpoint creation error instead of discarding.
                // Coherence failure between trace.depths and seen_fps (#2353).
                // Skip this checkpoint attempt; the next one may succeed after
                // the bookkeeping converges.
                eprintln!("WARNING: checkpoint creation failed (will retry): {e}");
                self.checkpoint.last_time = Some(Instant::now());
                return;
            }
        };
        if let Err(e) = checkpoint.save(&checkpoint_dir) {
            eprintln!("Warning: Failed to save checkpoint: {}", e);
        } else {
            eprintln!(
                "Checkpoint saved: {} states, {} frontier",
                self.states_count(),
                state_frontier.len()
            );
        }
        self.checkpoint.last_time = Some(Instant::now());
    }

    /// Output BFS profiling results (no-trace mode).
    pub(in crate::check) fn output_bfs_profile(prof: &BfsProfile) {
        if !prof.do_profile {
            return;
        }
        let total_us = prof.start_time.elapsed().as_micros() as u64;
        for line in bfs_profile_lines(total_us, prof) {
            eprintln!("{line}");
        }
    }

    /// Retrieve the first initial state for JIT layout inference.
    ///
    /// Checks `liveness_cache.init_states` first (populated when liveness
    /// tracking is active), then falls back to `state_storage.seen` (populated
    /// in full-state mode). Returns `None` when no initial states have been
    /// stored yet (e.g., all filtered by constraints).
    ///
    /// Part of #3910: JIT invariant cache layout upgrade.
    #[cfg(feature = "jit")]
    pub(in crate::check) fn get_first_init_state_for_layout(&self) -> Option<ArrayState> {
        // Prefer liveness init cache (always populated when liveness is active).
        if let Some((_, arr)) = self.liveness_cache.init_states.first() {
            return Some(arr.clone());
        }
        // Fall back to the first entry in seen (full-state mode).
        if let Some((_, arr)) = self.state_storage.seen.iter().next() {
            return Some(arr.clone());
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::{bfs_profile_lines, BfsProfile, Instant};

    #[test]
    fn bfs_profile_lines_zero_total_us_stays_finite_and_keeps_summary_lines() {
        let prof = BfsProfile {
            do_profile: true,
            start_time: Instant::now(),
            succ_gen_us: 0,
            fingerprint_us: 0,
            dedup_us: 0,
            invariant_us: 0,
            jit_hits: 0,
            jit_misses: 0,
            total_successors: 0,
            new_states: 0,
            arena_allocs: 0,
            arena_bytes: 0,
            arena_resets: 0,
        };
        let lines = bfs_profile_lines(0, &prof);
        let rendered = lines.join("\n");
        let lowered = rendered.to_ascii_lowercase();

        assert!(rendered.contains("=== Enumeration Profile ==="));
        assert!(rendered.contains("Total successors: 0 (no new states)"));
        assert!(rendered.contains("New states:       0"));
        assert!(!lowered.contains("nan"));
        assert!(!lowered.contains("inf"));
    }

    #[test]
    fn bfs_profile_lines_include_jit_stats_when_nonzero() {
        let prof = BfsProfile {
            do_profile: true,
            start_time: Instant::now(),
            succ_gen_us: 0,
            fingerprint_us: 0,
            dedup_us: 0,
            invariant_us: 0,
            jit_hits: 7,
            jit_misses: 3,
            total_successors: 10,
            new_states: 5,
            arena_allocs: 0,
            arena_bytes: 0,
            arena_resets: 0,
        };

        let rendered = bfs_profile_lines(1, &prof).join("\n");
        assert!(rendered.contains("JIT invariant:    hits=7 misses=3"));
    }

    /// Part of #4031: Verify warmup gate constants are sensible.
    #[cfg(feature = "jit")]
    #[test]
    fn jit_warmup_gate_constants_are_sensible() {
        use super::{JIT_SLOWDOWN_RATIO, JIT_WARMUP_THRESHOLD};

        // Threshold should be in the 100-1000 range to collect enough data
        // without delaying the decision too long.
        assert!(
            JIT_WARMUP_THRESHOLD >= 100,
            "warmup threshold too low: {}",
            JIT_WARMUP_THRESHOLD
        );
        assert!(
            JIT_WARMUP_THRESHOLD <= 1000,
            "warmup threshold too high: {}",
            JIT_WARMUP_THRESHOLD
        );

        // Slowdown ratio should allow some overhead (>1.0) but not too much.
        assert!(
            JIT_SLOWDOWN_RATIO > 1.0,
            "slowdown ratio must be > 1.0: {}",
            JIT_SLOWDOWN_RATIO
        );
        assert!(
            JIT_SLOWDOWN_RATIO < 2.0,
            "slowdown ratio too permissive: {}",
            JIT_SLOWDOWN_RATIO
        );
    }

    /// Part of #4031: Verify the warmup gate decision math.
    #[cfg(feature = "jit")]
    #[test]
    fn jit_warmup_gate_ratio_math() {
        use super::JIT_SLOWDOWN_RATIO;

        // Scenario 1: JIT is 1.5x slower -> should disable.
        let jit_avg_ns: f64 = 1500.0;
        let interp_avg_ns: f64 = 1000.0;
        let ratio = jit_avg_ns / interp_avg_ns;
        assert!(ratio > JIT_SLOWDOWN_RATIO, "1.5x should exceed threshold");

        // Scenario 2: JIT is 1.1x slower -> should keep.
        let jit_avg_ns: f64 = 1100.0;
        let interp_avg_ns: f64 = 1000.0;
        let ratio = jit_avg_ns / interp_avg_ns;
        assert!(ratio < JIT_SLOWDOWN_RATIO, "1.1x should be within threshold");

        // Scenario 3: JIT is faster -> should definitely keep.
        let jit_avg_ns: f64 = 800.0;
        let interp_avg_ns: f64 = 1000.0;
        let ratio = jit_avg_ns / interp_avg_ns;
        assert!(ratio < JIT_SLOWDOWN_RATIO, "0.8x should be within threshold");

        // Scenario 4: JIT is exactly at the boundary (1.2x).
        let jit_avg_ns: f64 = 1200.0;
        let interp_avg_ns: f64 = 1000.0;
        let ratio = jit_avg_ns / interp_avg_ns;
        // At exactly 1.2, it should NOT disable (ratio must be strictly > threshold).
        assert!(
            !(ratio > JIT_SLOWDOWN_RATIO),
            "exactly at threshold should not disable"
        );
    }
}
