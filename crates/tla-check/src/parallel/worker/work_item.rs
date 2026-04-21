// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `BfsWorkItem` trait: abstraction over ArrayState and HandleState work items.
//!
//! This trait enables a single generic worker loop ([`super::run_unified::run_worker_unified`])
//! that handles both queue types, converging toward TLC's single `Worker.run()`.
//!
//! Part of #2356/#1931: eliminates the duplicated BFS loops in `run_array.rs`
//! and `run_handle.rs`.

use crate::config::Config;
use crate::enumerate::{
    enumerate_successors_array_as_diffs, enumerate_successors_array_as_diffs_into,
    enumerate_successors_array_as_diffs_into_with_current_values,
    enumerate_successors_array_as_diffs_with_current_values, DiffSink,
};
use crate::error::EvalError;
use crate::eval::EvalCtx;
use crate::intern::HandleState;
use crate::state::{ArrayState, DiffSuccessor, Fingerprint};
use crate::var_index::VarRegistry;
use std::sync::Arc;
use tla_core::ast::OperatorDef;
use tla_eval::tir::TirProgram;

use super::worker_value_lane::maybe_worker_current_state;

/// Part of #1150: Mode for ArrayState BFS workers.
///
/// ArrayState workers no longer carry a second compiled-action evaluator.
#[derive(Clone)]
pub struct ArrayStateMode;

/// Result of resolving a queued work item into an ArrayState for evaluation.
pub(in crate::parallel) enum ResolvedArrayState {
    /// The work item already owned its ArrayState and moved it out directly.
    Owned(ArrayState),
    /// The work item populated the caller-provided scratch buffer in place.
    UsedScratch,
}

/// Abstraction over work item types in the BFS queue.
///
/// Both `ArrayState` and `HandleState` serve as BFS queue elements but differ in:
/// - **Fingerprinting**: ArrayState computes on demand; HandleState stores pre-computed.
/// - **Materialization**: ArrayState is already materialized; HandleState needs interner lookup.
/// - **Enqueueing**: ArrayState is pushed directly; HandleState requires conversion back.
/// - **Diff enumeration**: Both ArrayState and HandleState support incremental fingerprinting via diffs.
///
/// This trait captures those 4 differences, allowing a single generic BFS loop.
///
/// Part of #2356: matches TLC's single `Worker.run()` pattern where the loop body
/// is identical regardless of state representation.
pub(in crate::parallel) trait BfsWorkItem: Send + Sized + 'static {
    /// Mode-specific data needed for materialization and enqueueing.
    ///
    /// - `ArrayState`: [`ArrayStateMode`]
    /// - `HandleState`: [`HandleStateMode`] (owner-local interner bank)
    type Mode: Send + 'static;

    /// Compute the base fingerprint (before VIEW transformation).
    ///
    /// - `ArrayState`: computes from variable values (caches result).
    /// - `HandleState`: returns pre-computed interned fingerprint (zero-cost).
    fn base_fingerprint(&mut self, var_registry: &VarRegistry) -> Fingerprint;

    /// Whether this work-item type needs a caller-owned decode scratch slot.
    fn requires_decode_scratch() -> bool {
        false
    }

    /// Consume self and resolve it into an `ArrayState` for successor enumeration.
    ///
    /// - `ArrayState`: identity (zero-cost move via `ResolvedArrayState::Owned`).
    /// - `HandleState`: materializes values into the caller's scratch buffer.
    ///
    /// Must be called AFTER `base_fingerprint` (which borrows `&mut self`).
    fn resolve_array_state(
        self,
        scratch: Option<&mut ArrayState>,
        var_registry: &VarRegistry,
        mode: &Self::Mode,
    ) -> ResolvedArrayState;

    /// Convert an `ArrayState` back to `Self` for enqueueing into the work-stealing queue.
    ///
    /// - `ArrayState`: identity (ignores `producer_worker`).
    /// - `HandleState`: interns values into the producer's shard.
    ///
    /// Part of #3212: `producer_worker` identifies which worker created this
    /// successor, enabling owner-local interner sharding.
    fn from_array_state(
        arr: ArrayState,
        var_registry: &VarRegistry,
        mode: &Self::Mode,
        producer_worker: usize,
    ) -> Self;

    /// Whether this mode supports diff-based enumeration given the current config.
    ///
    /// Diff enumeration requires: no VIEW, no state constraints, no action constraints.
    /// Both `ArrayState` and `HandleState` override this when config allows diffs.
    fn supports_diffs(_config: &Config) -> bool {
        false
    }

    /// Whether this queue representation can carry complete `value_fps`
    /// across enqueue/dequeue boundaries.
    fn preserves_complete_fp_cache() -> bool {
        false
    }

    /// Attempt diff-based enumeration for the current state.
    ///
    /// Returns `Ok(Some((diffs, base_array)))` if diffs were produced, where `base_array`
    /// has its fp_cache populated for incremental fingerprinting.
    /// Returns `Ok(None)` if diffs are not available (fallback to State-based).
    ///
    /// Default: always returns `Ok(None)`.
    fn try_diff_enumerate(
        _current_array: &ArrayState,
        _ctx: &mut EvalCtx,
        _def: &OperatorDef,
        _vars: &[Arc<str>],
        _var_registry: &VarRegistry,
        _mode: &Self::Mode,
        _tir_leaf: Option<&TirProgram<'_>>,
    ) -> Result<Option<(Vec<DiffSuccessor>, ArrayState, bool)>, EvalError> {
        Ok(None)
    }

    /// Streaming variant of `try_diff_enumerate` that pushes successors
    /// through a `DiffSink` instead of collecting into a `Vec`.
    ///
    /// Part of #3027 Phase 4: enables parallel workers to use the streaming
    /// functor pattern with inline dedup via `ClosureSink`. Callers capture
    /// `&dyn FingerprintSet` in the sink closure for O(1) duplicate rejection
    /// during enumeration, avoiding the intermediate `Vec<DiffSuccessor>`.
    ///
    /// Returns `Ok(Some((base_array, rebuilt, base_cache_ns)))` if streaming succeeded.
    /// `base_cache_ns` is the nanoseconds spent in base-state fp cache preparation
    /// (Part of #3285 Enumeration sub-bucket attribution).
    /// Returns `Ok(None)` if streaming is not available (fallback to batch).
    ///
    /// Default: always returns `Ok(None)`.
    fn try_streaming_diff_enumerate(
        _current_array: &ArrayState,
        _ctx: &mut EvalCtx,
        _def: &OperatorDef,
        _vars: &[Arc<str>],
        _var_registry: &VarRegistry,
        _mode: &Self::Mode,
        _tir_leaf: Option<&TirProgram<'_>>,
        _sink: &mut dyn DiffSink,
    ) -> Result<Option<(ArrayState, bool, u64)>, EvalError> {
        Ok(None)
    }
}

// --- ArrayState implementation ---

impl BfsWorkItem for ArrayState {
    type Mode = ArrayStateMode;

    #[inline]
    fn base_fingerprint(&mut self, var_registry: &VarRegistry) -> Fingerprint {
        self.fingerprint(var_registry)
    }

    #[inline]
    fn resolve_array_state(
        self,
        _scratch: Option<&mut ArrayState>,
        _var_registry: &VarRegistry,
        _mode: &Self::Mode,
    ) -> ResolvedArrayState {
        ResolvedArrayState::Owned(self)
    }

    #[inline]
    fn from_array_state(
        arr: ArrayState,
        _var_registry: &VarRegistry,
        _mode: &Self::Mode,
        _producer_worker: usize,
    ) -> Self {
        arr
    }

    fn supports_diffs(config: &Config) -> bool {
        config.view.is_none()
            && config.symmetry.is_none()
            && config.constraints.is_empty()
            && config.action_constraints.is_empty()
    }

    fn preserves_complete_fp_cache() -> bool {
        true
    }

    fn try_diff_enumerate(
        current_array: &ArrayState,
        ctx: &mut EvalCtx,
        def: &OperatorDef,
        vars: &[Arc<str>],
        var_registry: &VarRegistry,
        _mode: &Self::Mode,
        tir_leaf: Option<&TirProgram<'_>>,
    ) -> Result<Option<(Vec<DiffSuccessor>, ArrayState, bool)>, EvalError> {
        let mut base_array = if super::super::parallel_preserve_value_fps() {
            current_array.clone_with_complete_fp_cache()
        } else {
            current_array.clone()
        };
        let rebuilt_base_fp_cache = !base_array.has_complete_fp_cache();
        base_array.ensure_fp_cache_with_value_fps(var_registry);

        let worker_state = maybe_worker_current_state(&base_array);
        let result = if let Some(ws) = worker_state.as_ref() {
            // Worker-local unshared values path (TLA2_WORKER_UNSHARE)
            enumerate_successors_array_as_diffs_with_current_values(
                ctx,
                def,
                &base_array,
                ws.values(),
                vars,
                tir_leaf,
            )
        } else {
            // Compact state binding path (default hot path)
            enumerate_successors_array_as_diffs(ctx, def, &base_array, vars, tir_leaf)
        };

        match result {
            Ok(Some(diffs)) => Ok(Some((diffs, base_array, rebuilt_base_fp_cache))),
            Ok(None) => Ok(None),
            Err(e) => Err(e),
        }
    }

    fn try_streaming_diff_enumerate(
        current_array: &ArrayState,
        ctx: &mut EvalCtx,
        def: &OperatorDef,
        vars: &[Arc<str>],
        var_registry: &VarRegistry,
        _mode: &Self::Mode,
        tir_leaf: Option<&TirProgram<'_>>,
        sink: &mut dyn DiffSink,
    ) -> Result<Option<(ArrayState, bool, u64)>, EvalError> {
        // Part of #3285: time base-state fp cache preparation separately.
        let t_base = super::super::timing_start();
        let mut base_array = if super::super::parallel_preserve_value_fps() {
            current_array.clone_with_complete_fp_cache()
        } else {
            current_array.clone()
        };
        let rebuilt_base_fp_cache = !base_array.has_complete_fp_cache();
        base_array.ensure_fp_cache_with_value_fps(var_registry);
        let base_cache_ns = t_base.map(|t| t.elapsed().as_nanos() as u64).unwrap_or(0);

        let worker_state = maybe_worker_current_state(&base_array);
        if let Some(ws) = worker_state.as_ref() {
            enumerate_successors_array_as_diffs_into_with_current_values(
                ctx,
                def,
                &base_array,
                ws.values(),
                vars,
                sink,
                tir_leaf,
            )?;
        } else {
            enumerate_successors_array_as_diffs_into(ctx, def, &base_array, vars, sink, tir_leaf)?;
        }
        Ok(Some((base_array, rebuilt_base_fp_cache, base_cache_ns)))
    }
}

// --- HandleState implementation ---

/// Part of #1459, #3212: Mode for HandleState BFS workers.
///
/// Carries an interner bank with per-worker shards so HandleState workers can
/// use owner-local interning with the unified diff-based path.
#[derive(Clone)]
pub struct HandleStateMode {
    /// Part of #3212: Per-worker interner shards for owner-local access.
    pub interner_bank: Arc<crate::intern::HandleStateInternerBank>,
}

impl BfsWorkItem for HandleState {
    type Mode = HandleStateMode;

    #[inline]
    fn base_fingerprint(&mut self, _var_registry: &VarRegistry) -> Fingerprint {
        HandleState::fingerprint(self)
    }

    #[inline]
    fn requires_decode_scratch() -> bool {
        true
    }

    #[inline]
    fn resolve_array_state(
        self,
        scratch: Option<&mut ArrayState>,
        _var_registry: &VarRegistry,
        mode: &Self::Mode,
    ) -> ResolvedArrayState {
        let scratch =
            scratch.expect("HandleState parallel decode requires a transport-owned scratch slot");
        self.materialize_into_bank(scratch, &mode.interner_bank)
            .expect("HandleState owner shard must contain all interned values during BFS");
        ResolvedArrayState::UsedScratch
    }

    #[inline]
    fn from_array_state(
        arr: ArrayState,
        var_registry: &VarRegistry,
        mode: &Self::Mode,
        producer_worker: usize,
    ) -> Self {
        // Part of #3579: intern directly from CompactValue slice, avoiding
        // materialize_values() Vec allocation.
        HandleState::from_array_state_sharded(
            &arr,
            var_registry,
            &mode.interner_bank,
            producer_worker,
        )
    }

    fn supports_diffs(config: &Config) -> bool {
        config.view.is_none()
            && config.symmetry.is_none()
            && config.constraints.is_empty()
            && config.action_constraints.is_empty()
    }

    fn try_diff_enumerate(
        current_array: &ArrayState,
        ctx: &mut EvalCtx,
        def: &OperatorDef,
        vars: &[Arc<str>],
        var_registry: &VarRegistry,
        _mode: &Self::Mode,
        tir_leaf: Option<&TirProgram<'_>>,
    ) -> Result<Option<(Vec<DiffSuccessor>, ArrayState, bool)>, EvalError> {
        let mut base_array = current_array.clone();
        base_array.ensure_fp_cache_with_value_fps(var_registry);

        let _state_guard = ctx.bind_state_env_guard(base_array.env_ref());

        let result = enumerate_successors_array_as_diffs(ctx, def, &base_array, vars, tir_leaf);

        match result {
            Ok(Some(diffs)) => Ok(Some((diffs, base_array, false))),
            Ok(None) => Ok(None),
            Err(e) => Err(e),
        }
    }

    fn try_streaming_diff_enumerate(
        current_array: &ArrayState,
        ctx: &mut EvalCtx,
        def: &OperatorDef,
        vars: &[Arc<str>],
        var_registry: &VarRegistry,
        _mode: &Self::Mode,
        tir_leaf: Option<&TirProgram<'_>>,
        sink: &mut dyn DiffSink,
    ) -> Result<Option<(ArrayState, bool, u64)>, EvalError> {
        // Part of #3285: time base-state fp cache preparation separately.
        let t_base = super::super::timing_start();
        let mut base_array = current_array.clone();
        base_array.ensure_fp_cache_with_value_fps(var_registry);
        let base_cache_ns = t_base.map(|t| t.elapsed().as_nanos() as u64).unwrap_or(0);

        let _state_guard = ctx.bind_state_env_guard(base_array.env_ref());

        enumerate_successors_array_as_diffs_into(ctx, def, &base_array, vars, sink, tir_leaf)?;
        Ok(Some((base_array, false, base_cache_ns)))
    }
}
