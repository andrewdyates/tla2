// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Compiled BFS level function — Phase 5 of the JIT V2 SPIN-class plan.
//!
//! Generates a single Cranelift function that processes an **entire BFS
//! frontier** in native code. The parent-iteration loop itself runs in the
//! JIT'd function, eliminating per-parent Rust-to-JIT call overhead.
//!
//! # Architecture
//!
//! ```text
//! bfs_level(
//!     parents_ptr: *const i64,   // contiguous arena of parent states
//!     parent_count: u32,         // number of parents in arena
//!     succ_out: *mut i64,        // output buffer for new successors
//!     succ_capacity: u32,        // max successors that fit
//!     result_out: *mut BfsLevelLoopResult,
//! ) -> u32                       // total new successors written
//!
//!   for parent_idx in 0..parent_count:
//!     parent_ptr = parents_ptr + parent_idx * state_len * 8
//!     for each (action, binding) pair:
//!       call action_fn(out, parent_ptr, temp, state_len)
//!       if disabled: skip
//!       fingerprint temp via xxh3
//!       probe fp_set: if seen, skip
//!       check invariants on temp
//!       copy temp to succ_out[new_count]
//!       new_count++
//!   write result
//!   return new_count
//! ```
//!
//! This is the SPIN-equivalent transformation: the entire BFS inner loop
//! runs as a single native function with register allocation across the
//! full step.
//!
//! Part of #3988: JIT V2 Phase 5 compiled BFS step.

use crate::bfs_step::{
    status, BfsStepCompiler, BfsStepResult, BfsStepSpec, CompiledActionFn, CompiledInvariantFn,
};
use crate::compiled_bfs::{state_fingerprint, BfsStepError, BfsStepScratch, FlatBfsStepOutputRef};
use crate::error::JitError;
use std::sync::Arc;

use crate::atomic_fp_set::{AtomicFpSet, InsertResult, ResizableAtomicFpSet};

/// Output struct for a compiled BFS level loop function.
///
/// Written by the JIT-compiled `bfs_level` function to communicate
/// aggregate level statistics back to the Rust caller.
#[repr(C)]
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct BfsLevelLoopResult {
    /// Number of parents fully processed.
    pub parents_processed: u32,
    /// Total successors generated across all parents (before dedup).
    pub total_generated: u32,
    /// Total new successors after dedup.
    pub total_new: u32,
    /// Whether all invariants passed (1 = ok, 0 = violation).
    pub invariant_ok: u32,
    /// Index of the first invariant that failed (if any).
    pub failed_invariant_idx: u32,
    /// Parent index where invariant violation occurred.
    pub failed_parent_idx: u32,
    /// Successor index (within that parent) that violated the invariant.
    pub failed_successor_idx: u32,
    /// Status code (0 = ok, 1 = runtime error, 2 = buffer overflow).
    pub status: u32,
}

/// Function pointer type for a compiled BFS level loop function.
///
/// # Parameters
///
/// - `parents_ptr`: pointer to contiguous arena of parent states
/// - `parent_count`: number of parent states in the arena
/// - `succ_out`: pointer to output buffer for new successor states
/// - `succ_capacity`: maximum number of successors that fit in succ_out
/// - `result_out`: pointer to a `BfsLevelLoopResult` struct
///
/// # Returns
///
/// Total number of new successors written to `succ_out`.
///
/// # Safety
///
/// `parents_ptr` must point to `parent_count * state_len` valid i64 values.
/// `succ_out` must have room for `succ_capacity * state_len` i64 values.
/// `result_out` must be a valid `BfsLevelLoopResult`.
pub type JitBfsLevelFn = unsafe extern "C" fn(
    parents_ptr: *const i64,
    parent_count: u32,
    succ_out: *mut i64,
    succ_capacity: u32,
    result_out: *mut BfsLevelLoopResult,
) -> u32;

/// High-level wrapper around a compiled BFS level loop function.
///
/// Unlike `CompiledBfsStep` which processes one parent at a time (with
/// the parent loop in Rust), this compiles the entire parent loop into
/// the JIT function. The result is a single native function that
/// processes an entire BFS frontier with zero Rust-to-JIT call overhead
/// per parent.
///
/// Part of #3988: JIT V2 Phase 5 compiled BFS level loop.
pub struct CompiledBfsLevel {
    /// Pre-compiled per-parent step function (for fallback / shared-FP path).
    step_fn: crate::bfs_step::JitBfsStepFn,
    /// Fingerprint set for dedup.
    fp_set: Arc<AtomicFpSet>,
    /// Optional shared/resizable fingerprint set for multi-level BFS.
    shared_fp_set: Option<Arc<ResizableAtomicFpSet>>,
    /// Compiled invariant functions for wrapper-side checking.
    invariant_fns: Arc<[CompiledInvariantFn]>,
    /// Compiled action functions, retained for debug-only fused provenance
    /// derivation and direct helper tests.
    action_fns: Arc<[CompiledActionFn]>,
    /// Number of i64 slots per state.
    state_len: usize,
    /// Maximum successors per parent.
    succ_capacity: usize,
    /// Retains ownership of the BFS step compiler whose JIT modules back
    /// `step_fn`'s code pages. Without this, dropping the compiler would free
    /// the mmap'd code pages, making `step_fn` a dangling pointer (#4082).
    _compiler: BfsStepCompiler,
    /// Optional fused level function that processes the entire frontier in
    /// a single native call. When present, `run_level_fused_arena` uses this
    /// instead of the per-parent step loop.
    ///
    /// Part of #3988: Phase 5 fused BFS level function.
    fused_level_fn: Option<JitBfsLevelFn>,
}

/// Result of processing one BFS level via the compiled level loop.
///
/// Part of #3988: Phase 5 compiled BFS level loop result.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompiledLevelResult {
    /// New successor states discovered in this level, packed as
    /// `successor_count * state_len` i64 slots.
    pub successor_arena: Vec<i64>,
    /// Originating parent index for each packed successor, when available.
    pub successor_parent_indices: Option<Vec<usize>>,
    /// Number of packed successor states in `successor_arena`.
    pub successor_count: usize,
    /// Number of i64 slots per successor state.
    pub state_len: usize,
    /// Number of parent states fully processed.
    pub parents_processed: usize,
    /// Total successors generated (before dedup).
    pub total_generated: u64,
    /// Total new successors (after dedup).
    pub total_new: u64,
    /// Whether all invariants passed.
    pub invariant_ok: bool,
    /// Index of parent where invariant violation occurred.
    pub failed_parent_idx: Option<usize>,
    /// Index of the invariant that failed.
    pub failed_invariant_idx: Option<u32>,
    /// The failing successor state.
    pub failed_successor: Option<Vec<i64>>,
    /// Whether the backend checked every regular invariant before returning
    /// these successors.
    pub regular_invariants_checked_by_backend: bool,
}

impl CompiledLevelResult {
    fn empty(state_len: usize, parents_processed: usize) -> Self {
        Self {
            successor_arena: Vec::new(),
            successor_parent_indices: None,
            successor_count: 0,
            state_len,
            parents_processed,
            total_generated: 0,
            total_new: 0,
            invariant_ok: true,
            failed_parent_idx: None,
            failed_invariant_idx: None,
            failed_successor: None,
            regular_invariants_checked_by_backend: false,
        }
    }

    /// Number of new successors packed in this result.
    #[must_use]
    pub fn successor_count(&self) -> usize {
        self.successor_count
    }

    /// Iterate over flat successor slices.
    pub fn iter_successors(&self) -> impl Iterator<Item = &[i64]> + '_ {
        if self.state_len == 0 {
            return CompiledLevelSuccessorIter::Empty(self.successor_count);
        }

        let slots = self
            .successor_count
            .checked_mul(self.state_len)
            .expect("successor_count * state_len overflow");
        assert!(
            self.successor_arena.len() >= slots,
            "successor arena shorter than successor_count * state_len",
        );
        CompiledLevelSuccessorIter::Chunked(
            self.successor_arena[..slots].chunks_exact(self.state_len),
        )
    }
}

enum CompiledLevelSuccessorIter<'a> {
    Chunked(std::slice::ChunksExact<'a, i64>),
    Empty(usize),
}

impl<'a> Iterator for CompiledLevelSuccessorIter<'a> {
    type Item = &'a [i64];

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            CompiledLevelSuccessorIter::Chunked(chunks) => chunks.next(),
            CompiledLevelSuccessorIter::Empty(remaining) => {
                if *remaining == 0 {
                    None
                } else {
                    *remaining -= 1;
                    Some(&[])
                }
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match self {
            CompiledLevelSuccessorIter::Chunked(chunks) => chunks.size_hint(),
            CompiledLevelSuccessorIter::Empty(remaining) => (*remaining, Some(*remaining)),
        }
    }
}

impl<'a> ExactSizeIterator for CompiledLevelSuccessorIter<'a> {}

/// Result of multi-level BFS exploration via the compiled level loop.
///
/// Part of #3988: Phase 5 compiled BFS multi-level exploration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompiledMultiLevelResult {
    /// Number of BFS levels fully completed.
    pub depths_completed: usize,
    /// Total distinct states seen (including initial states).
    pub total_states_seen: u64,
    /// Total successors generated across all levels.
    pub total_generated: u64,
    /// Whether all invariants passed.
    pub invariant_ok: bool,
    /// Index of the invariant that failed (if any).
    pub failed_invariant_idx: Option<u32>,
    /// BFS depth at which violation occurred.
    pub failed_depth: Option<usize>,
    /// The failing successor state.
    pub failed_successor: Option<Vec<i64>>,
}

const FUSED_PARENT_PROVENANCE_REPLAY_ENV: &str = "TLA2_DEBUG_FUSED_PARENT_PROVENANCE";

/// Debug-only switch for fused parent provenance reconstruction.
///
/// Derivation replays Rust action functions against every parent, so it must
/// stay out of the normal packed-BFS hot path.
fn fused_parent_provenance_replay_enabled() -> bool {
    match std::env::var(FUSED_PARENT_PROVENANCE_REPLAY_ENV) {
        Ok(value) => matches!(
            value.as_str(),
            "1" | "true" | "TRUE" | "yes" | "YES" | "on" | "ON"
        ),
        Err(_) => false,
    }
}

impl CompiledBfsLevel {
    /// Build a compiled BFS level loop that uses the fused JIT-compiled level
    /// function for the hot path.
    ///
    /// The fused function loops over all parents in a single native call,
    /// eliminating per-parent Rust-to-JIT boundary crossings. Falls back to
    /// the per-parent step path for the shared-FP-set filtering.
    ///
    /// Part of #3988: Phase 5 fused BFS level function.
    pub fn build_fused(
        spec: &BfsStepSpec,
        action_fns: Vec<CompiledActionFn>,
        invariant_fns: Vec<CompiledInvariantFn>,
        expected_states: usize,
    ) -> Result<Self, JitError> {
        let succ_capacity = spec.actions.len().saturating_mul(2).max(64);
        if succ_capacity > u32::MAX as usize {
            return Err(JitError::CompileError(
                "compiled BFS level successor capacity exceeds u32::MAX".to_string(),
            ));
        }
        let fp_set = Arc::new(AtomicFpSet::new(expected_states.saturating_mul(2).max(1)));
        let fp_set_ptr = Arc::as_ptr(&fp_set).cast::<u8>();

        let action_fns: Arc<[CompiledActionFn]> = Arc::from(action_fns);
        let mut compiler = BfsStepCompiler::new()?;

        // Compile the fused level function.
        let fused_fn =
            compiler.compile_fused_level(spec, &action_fns, &invariant_fns, Some(fp_set_ptr))?;

        // Also compile the per-parent step function for fallback.
        let step_fn =
            compiler.compile_with_actions(spec, &action_fns, &invariant_fns, Some(fp_set_ptr))?;

        Ok(Self {
            step_fn,
            fp_set,
            shared_fp_set: None,
            invariant_fns: Arc::from(invariant_fns),
            action_fns,
            state_len: spec.state_len,
            succ_capacity,
            _compiler: compiler,
            fused_level_fn: Some(fused_fn),
        })
    }

    /// Build a compiled BFS level loop from pre-compiled action and invariant functions.
    ///
    /// The resulting wrapper processes entire frontiers in native code. Each
    /// parent is processed through the compiled BFS step function, with dedup
    /// handled by the fingerprint set and invariant checking by compiled
    /// invariant functions.
    pub fn build(
        spec: &BfsStepSpec,
        action_fns: Vec<CompiledActionFn>,
        invariant_fns: Vec<CompiledInvariantFn>,
        expected_states: usize,
    ) -> Result<Self, JitError> {
        let succ_capacity = spec.actions.len().saturating_mul(2).max(64);
        if succ_capacity > u32::MAX as usize {
            return Err(JitError::CompileError(
                "compiled BFS level successor capacity exceeds u32::MAX".to_string(),
            ));
        }
        let fp_set = Arc::new(AtomicFpSet::new(expected_states.saturating_mul(2).max(1)));
        let fp_set_ptr = Arc::as_ptr(&fp_set).cast::<u8>();

        let action_fns: Arc<[CompiledActionFn]> = Arc::from(action_fns);
        let mut compiler = BfsStepCompiler::new()?;
        let step_fn =
            compiler.compile_with_actions(spec, &action_fns, &invariant_fns, Some(fp_set_ptr))?;

        Ok(Self {
            step_fn,
            fp_set,
            shared_fp_set: None,
            invariant_fns: Arc::from(invariant_fns),
            action_fns,
            state_len: spec.state_len,
            succ_capacity,
            _compiler: compiler,
            fused_level_fn: None,
        })
    }

    /// Build a compiled BFS level loop that deduplicates against a shared set.
    ///
    /// Uses the shared fingerprint set for cross-level dedup. Actions are
    /// compiled without inline fingerprinting; dedup happens in the Rust
    /// wrapper against the shared set.
    pub fn build_with_shared_fp_set(
        spec: &BfsStepSpec,
        action_fns: Vec<CompiledActionFn>,
        invariant_fns: Vec<CompiledInvariantFn>,
        shared_fp_set: Arc<ResizableAtomicFpSet>,
    ) -> Result<Self, JitError> {
        let succ_capacity = spec.actions.len().saturating_mul(2).max(64);
        let action_only_spec = BfsStepSpec {
            state_len: spec.state_len,
            state_layout: spec.state_layout.clone(),
            actions: spec.actions.clone(),
            invariants: Vec::new(),
        };

        let action_fns: Arc<[CompiledActionFn]> = Arc::from(action_fns);
        let mut compiler = BfsStepCompiler::new()?;
        let step_fn = compiler.compile_with_actions(&action_only_spec, &action_fns, &[], None)?;

        Ok(Self {
            step_fn,
            fp_set: Arc::new(AtomicFpSet::new(shared_fp_set.capacity())),
            shared_fp_set: Some(shared_fp_set),
            invariant_fns: Arc::from(invariant_fns),
            action_fns,
            state_len: spec.state_len,
            succ_capacity,
            _compiler: compiler,
            fused_level_fn: None,
        })
    }

    /// Process an entire BFS frontier from a contiguous arena of parent states.
    ///
    /// Takes a flat `&[i64]` arena where each parent occupies `state_len`
    /// consecutive i64 slots. This is the Phase 5 compiled BFS level loop:
    /// one scratch buffer is reused across all parents, and the per-parent
    /// step function runs in native code.
    ///
    /// This method accepts a contiguous arena (as from `FlatStateStore`)
    /// instead of `&[Vec<i64>]`, avoiding per-parent pointer chasing.
    ///
    /// Part of #3988: Phase 5 compiled BFS level loop.
    pub fn run_level_arena(
        &self,
        arena: &[i64],
        parent_count: usize,
    ) -> Result<CompiledLevelResult, BfsStepError> {
        if self.state_len == 0 {
            return Ok(CompiledLevelResult::empty(self.state_len, parent_count));
        }

        let expected_slots = parent_count
            .checked_mul(self.state_len)
            .ok_or(BfsStepError::RuntimeError)?;
        if arena.len() < expected_slots {
            return Err(BfsStepError::RuntimeError);
        }

        let mut scratch = BfsStepScratch::new(self.state_len, self.succ_capacity);
        let mut result = CompiledLevelResult {
            successor_arena: Vec::new(),
            successor_parent_indices: Some(Vec::new()),
            successor_count: 0,
            state_len: self.state_len,
            parents_processed: 0,
            total_generated: 0,
            total_new: 0,
            invariant_ok: true,
            failed_parent_idx: None,
            failed_invariant_idx: None,
            failed_successor: None,
            regular_invariants_checked_by_backend: true,
        };

        for parent_idx in 0..parent_count {
            let start = parent_idx * self.state_len;
            let end = start + self.state_len;
            let parent = &arena[start..end];

            let output = self.step_flat_into(parent, &mut scratch)?;
            result.parents_processed += 1;
            result.total_generated = result
                .total_generated
                .checked_add(u64::from(output.generated_count))
                .ok_or(BfsStepError::RuntimeError)?;
            result.total_new = result
                .total_new
                .checked_add(
                    u64::try_from(output.successor_count())
                        .map_err(|_| BfsStepError::RuntimeError)?,
                )
                .ok_or(BfsStepError::RuntimeError)?;

            let failed_successor = output
                .failed_successor_idx
                .and_then(|idx| usize::try_from(idx).ok())
                .and_then(|idx| output.iter_successors().nth(idx).map(|s| s.to_vec()));

            let successor_count_before = result.successor_count;
            output.iter_successors().try_for_each(|successor| {
                if successor.len() != self.state_len {
                    return Err(BfsStepError::RuntimeError);
                }
                result.successor_arena.extend_from_slice(successor);
                if let Some(parent_indices) = result.successor_parent_indices.as_mut() {
                    parent_indices.push(parent_idx);
                }
                result.successor_count = result
                    .successor_count
                    .checked_add(1)
                    .ok_or(BfsStepError::RuntimeError)?;
                Ok(())
            })?;

            if result.invariant_ok && !output.invariant_ok {
                result.invariant_ok = false;
                result.failed_parent_idx = Some(parent_idx);
                result.failed_invariant_idx = output.failed_invariant_idx;
                result.failed_successor = failed_successor;
                debug_assert_eq!(
                    result.successor_count,
                    successor_count_before + output.successor_count(),
                    "violation path should preserve generated new successors"
                );
                break;
            }
        }

        Ok(result)
    }

    /// Process an entire BFS frontier using the fused JIT-compiled level function.
    ///
    /// This is the Phase 5 fully-fused path: a single native function call
    /// processes all parents, dispatches all actions, fingerprints, deduplicates,
    /// checks invariants, and writes new successors. Zero Rust-to-JIT boundary
    /// crossings per parent.
    ///
    /// Returns `None` if no fused function is available (use `run_level_arena`
    /// as fallback). Only available when built via `build_fused`.
    /// Non-empty successor parent provenance is omitted by default because
    /// deriving it requires replaying action functions; set
    /// `TLA2_DEBUG_FUSED_PARENT_PROVENANCE=1` to enable debug reconstruction.
    ///
    /// Part of #3988: Phase 5 fused BFS level function.
    pub fn run_level_fused_arena(
        &self,
        arena: &[i64],
        parent_count: usize,
    ) -> Option<Result<CompiledLevelResult, BfsStepError>> {
        let fused_fn = self.fused_level_fn?;

        if self.state_len == 0 {
            return Some(Ok(CompiledLevelResult::empty(self.state_len, parent_count)));
        }

        let expected_slots = match parent_count.checked_mul(self.state_len) {
            Some(s) => s,
            None => return Some(Err(BfsStepError::RuntimeError)),
        };
        if arena.len() < expected_slots {
            return Some(Err(BfsStepError::RuntimeError));
        }

        // Allocate output buffer for successors.
        // Use a generous capacity: succ_capacity * parent_count, capped to avoid OOM.
        let total_succ_capacity = self
            .succ_capacity
            .saturating_mul(parent_count)
            .min(1_000_000);
        let succ_buf_len = total_succ_capacity.saturating_mul(self.state_len);
        let mut succ_buf = vec![0i64; succ_buf_len];
        let mut level_result = BfsLevelLoopResult::default();

        let parent_count_u32 = match u32::try_from(parent_count) {
            Ok(c) => c,
            Err(_) => return Some(Err(BfsStepError::RuntimeError)),
        };
        let total_succ_cap_u32 = match u32::try_from(total_succ_capacity) {
            Ok(c) => c,
            Err(_) => return Some(Err(BfsStepError::RuntimeError)),
        };

        let total_new = unsafe {
            // SAFETY: `arena` contains `parent_count * state_len` valid i64 slots.
            // `succ_buf` has room for `total_succ_capacity * state_len` i64 slots.
            // `level_result` is a valid `BfsLevelLoopResult`.
            fused_fn(
                arena.as_ptr(),
                parent_count_u32,
                succ_buf.as_mut_ptr(),
                total_succ_cap_u32,
                &mut level_result,
            )
        };

        let total_new_usize = total_new as usize;

        // Check status.
        match level_result.status {
            0 => {} // OK
            1 => return Some(Err(BfsStepError::RuntimeError)),
            2 => {
                return Some(Err(BfsStepError::BufferOverflow {
                    partial_count: total_new,
                }))
            }
            _ => return Some(Err(BfsStepError::RuntimeError)),
        }
        if level_result.total_new != total_new {
            return Some(Err(BfsStepError::RuntimeError));
        }

        let slots = match total_new_usize.checked_mul(self.state_len) {
            Some(slots) => slots,
            None => return Some(Err(BfsStepError::RuntimeError)),
        };
        if slots > succ_buf.len() {
            return Some(Err(BfsStepError::RuntimeError));
        }
        succ_buf.truncate(slots);

        let invariant_ok = level_result.invariant_ok != 0;
        let failed_successor = if invariant_ok {
            None
        } else {
            let failed_successor_idx = level_result.failed_successor_idx as usize;
            if failed_successor_idx >= total_new_usize {
                return Some(Err(BfsStepError::RuntimeError));
            }
            let start = match failed_successor_idx.checked_mul(self.state_len) {
                Some(start) => start,
                None => return Some(Err(BfsStepError::RuntimeError)),
            };
            let end = match start.checked_add(self.state_len) {
                Some(end) => end,
                None => return Some(Err(BfsStepError::RuntimeError)),
            };
            match succ_buf.get(start..end) {
                Some(successor) => Some(successor.to_vec()),
                None => return Some(Err(BfsStepError::RuntimeError)),
            }
        };

        let successor_parent_indices = if total_new_usize == 0 {
            Some(Vec::new())
        } else if fused_parent_provenance_replay_enabled() {
            self.derive_fused_successor_parent_indices(
                arena,
                parent_count,
                &succ_buf,
                total_new_usize,
            )
        } else {
            None
        };

        Some(Ok(CompiledLevelResult {
            successor_arena: succ_buf,
            successor_parent_indices,
            successor_count: total_new_usize,
            state_len: self.state_len,
            parents_processed: level_result.parents_processed as usize,
            total_generated: u64::from(level_result.total_generated),
            total_new: u64::from(level_result.total_new),
            invariant_ok,
            failed_parent_idx: if !invariant_ok {
                Some(level_result.failed_parent_idx as usize)
            } else {
                None
            },
            failed_invariant_idx: if !invariant_ok {
                Some(level_result.failed_invariant_idx)
            } else {
                None
            },
            failed_successor,
            regular_invariants_checked_by_backend: true,
        }))
    }

    fn derive_fused_successor_parent_indices(
        &self,
        arena: &[i64],
        parent_count: usize,
        successor_arena: &[i64],
        successor_count: usize,
    ) -> Option<Vec<usize>> {
        if successor_count == 0 {
            return Some(Vec::new());
        }

        let expected_slots = parent_count.checked_mul(self.state_len)?;
        if arena.len() < expected_slots {
            return None;
        }

        let successor_slots = successor_count.checked_mul(self.state_len)?;
        if successor_arena.len() < successor_slots {
            return None;
        }

        let state_len_u32 = u32::try_from(self.state_len).ok()?;
        let mut successor_slots_by_state: std::collections::HashMap<&[i64], Vec<usize>> =
            std::collections::HashMap::with_capacity(successor_count);
        for (successor_idx, successor) in successor_arena[..successor_slots]
            .chunks_exact(self.state_len)
            .enumerate()
        {
            successor_slots_by_state
                .entry(successor)
                .or_default()
                .push(successor_idx);
        }

        let mut temp_state = vec![0i64; self.state_len];
        let mut parent_indices = vec![None; successor_count];
        let mut matched_successors = 0usize;

        'parents: for parent_idx in 0..parent_count {
            let parent_start = parent_idx.checked_mul(self.state_len)?;
            let parent_end = parent_start.checked_add(self.state_len)?;
            let parent = arena.get(parent_start..parent_end)?;

            for action in self.action_fns.iter() {
                let mut out = crate::abi::JitCallOut::default();
                temp_state.copy_from_slice(parent);
                unsafe {
                    // SAFETY: `parent` and `temp_state` both contain exactly
                    // `state_len` i64 slots, and `out` is a valid call result.
                    (action.func)(
                        &mut out,
                        parent.as_ptr(),
                        temp_state.as_mut_ptr(),
                        state_len_u32,
                    );
                }

                if out.status != crate::abi::JitStatus::Ok {
                    return None;
                }
                if out.value == 0 {
                    continue;
                }

                if let Some(successor_idx) = successor_slots_by_state
                    .get(temp_state.as_slice())
                    .and_then(|successor_indices| {
                        successor_indices
                            .iter()
                            .copied()
                            .find(|idx| parent_indices[*idx].is_none())
                    })
                {
                    parent_indices[successor_idx] = Some(parent_idx);
                    matched_successors += 1;

                    if matched_successors == successor_count {
                        break 'parents;
                    }
                }
            }
        }

        parent_indices.into_iter().collect()
    }

    /// Whether this level has a fused JIT function available.
    #[must_use]
    pub fn has_fused_level(&self) -> bool {
        self.fused_level_fn.is_some()
    }

    /// Process a frontier given as a slice of owned state vectors.
    ///
    /// Convenience wrapper around `run_level_arena` that first packs the
    /// states into a contiguous arena.
    pub fn run_level<S>(&self, parents: &[S]) -> Result<CompiledLevelResult, BfsStepError>
    where
        S: AsRef<[i64]>,
    {
        if parents.is_empty() || self.state_len == 0 {
            return Ok(CompiledLevelResult::empty(self.state_len, parents.len()));
        }

        // Pack into contiguous arena for cache-friendly iteration.
        let mut arena = Vec::with_capacity(parents.len() * self.state_len);
        for parent in parents {
            let p = parent.as_ref();
            if p.len() != self.state_len {
                return Err(BfsStepError::RuntimeError);
            }
            arena.extend_from_slice(p);
        }

        self.run_level_arena(&arena, parents.len())
    }

    /// Run multi-level BFS exploration from initial states.
    ///
    /// Starting from `init_states`, executes BFS level-by-level using the
    /// compiled level loop until either:
    /// - `max_depth` levels have been processed,
    /// - the frontier is empty, or
    /// - an invariant violation is found.
    ///
    /// Each level's new successors become the next level's parents, packed
    /// into a contiguous arena for cache-friendly access. The fingerprint
    /// set is shared across all levels for cross-level dedup.
    ///
    /// Part of #3988: Phase 5 compiled BFS multi-level exploration.
    pub fn run_multi_level(
        &self,
        init_states: &[Vec<i64>],
        max_depth: usize,
    ) -> Result<CompiledMultiLevelResult, BfsStepError> {
        let mut result = CompiledMultiLevelResult {
            depths_completed: 0,
            total_states_seen: 0,
            total_generated: 0,
            invariant_ok: true,
            failed_invariant_idx: None,
            failed_depth: None,
            failed_successor: None,
        };

        // Seed the fingerprint set with initial states.
        for init in init_states {
            let fp = state_fingerprint(init);
            let _ = self.fp_set.insert_if_absent(fp);
        }
        result.total_states_seen = init_states.len() as u64;

        // Pack initial frontier into contiguous arena.
        let mut frontier_arena: Vec<i64> = Vec::with_capacity(init_states.len() * self.state_len);
        for init in init_states {
            frontier_arena.extend_from_slice(init);
        }
        let mut frontier_count = init_states.len();

        for depth in 0..max_depth {
            if frontier_count == 0 {
                break;
            }

            let level = self.run_level_arena(&frontier_arena, frontier_count)?;

            result.total_generated = result
                .total_generated
                .checked_add(level.total_generated)
                .ok_or(BfsStepError::RuntimeError)?;
            result.total_states_seen = result
                .total_states_seen
                .checked_add(level.total_new)
                .ok_or(BfsStepError::RuntimeError)?;

            if !level.invariant_ok {
                result.invariant_ok = false;
                result.failed_invariant_idx = level.failed_invariant_idx;
                result.failed_depth = Some(depth);
                result.failed_successor = level.failed_successor;
                result.depths_completed = depth;
                return Ok(result);
            }

            result.depths_completed = depth + 1;

            // Pack next frontier into arena for cache-friendly access.
            frontier_arena.clear();
            let next_slots = level
                .successor_count
                .checked_mul(self.state_len)
                .ok_or(BfsStepError::RuntimeError)?;
            if next_slots > level.successor_arena.len() {
                return Err(BfsStepError::RuntimeError);
            }
            frontier_arena.extend_from_slice(&level.successor_arena[..next_slots]);
            frontier_count = level.successor_count;
        }

        Ok(result)
    }

    /// Number of i64 slots in each state.
    #[must_use]
    pub fn state_len(&self) -> usize {
        self.state_len
    }

    /// Number of distinct states recorded in the fingerprint set.
    #[must_use]
    pub fn states_seen(&self) -> usize {
        match self.shared_fp_set.as_ref() {
            Some(shared) => shared.len(),
            None => self.fp_set.len(),
        }
    }

    /// Access the fingerprint set.
    #[must_use]
    pub fn fp_set(&self) -> &AtomicFpSet {
        self.fp_set.as_ref()
    }

    /// Execute one step using the caller-provided scratch buffer.
    fn step_flat_into<'a>(
        &self,
        state: &[i64],
        scratch: &'a mut BfsStepScratch,
    ) -> Result<FlatBfsStepOutputRef<'a>, BfsStepError> {
        if state.len() != self.state_len {
            return Err(BfsStepError::RuntimeError);
        }

        let mut step_result = BfsStepResult::default();
        let written = unsafe {
            // SAFETY: `state` has `state_len` slots; `scratch` has room for
            // `succ_capacity * state_len` slots; `step_result` is valid.
            (self.step_fn)(
                state.as_ptr(),
                scratch.as_mut_ptr(),
                self.succ_capacity as u32,
                &mut step_result,
            )
        };

        if written != step_result.successors_new {
            return Err(BfsStepError::RuntimeError);
        }

        match step_result.status {
            status::OK => {}
            status::BUFFER_OVERFLOW => {
                return Err(BfsStepError::BufferOverflow {
                    partial_count: step_result.successors_new,
                })
            }
            status::RUNTIME_ERROR => return Err(BfsStepError::RuntimeError),
            _ => return Err(BfsStepError::RuntimeError),
        }

        let successor_count =
            usize::try_from(step_result.successors_new).map_err(|_| BfsStepError::RuntimeError)?;
        if successor_count > self.succ_capacity {
            return Err(BfsStepError::RuntimeError);
        }

        // Handle shared fingerprint set filtering.
        if let Some(ref shared) = self.shared_fp_set {
            let mut new_count = 0usize;
            let mut invariant_ok = true;
            let mut failed_invariant_idx = None;
            let mut failed_successor_idx = None;

            for chunk_idx in 0..successor_count {
                let start = chunk_idx
                    .checked_mul(self.state_len)
                    .ok_or(BfsStepError::RuntimeError)?;
                let end = start
                    .checked_add(self.state_len)
                    .ok_or(BfsStepError::RuntimeError)?;

                let fingerprint = {
                    let succ_slice = &scratch.successor_slice(successor_count)[start..end];
                    state_fingerprint(succ_slice)
                };

                let is_new = match shared.insert_if_absent(fingerprint) {
                    InsertResult::Inserted => true,
                    InsertResult::AlreadyPresent => false,
                    InsertResult::TableFull => return Err(BfsStepError::RuntimeError),
                };

                // Mirror into local set.
                match self.fp_set.insert_if_absent(fingerprint) {
                    InsertResult::Inserted
                    | InsertResult::AlreadyPresent
                    | InsertResult::TableFull => {}
                }

                if !is_new {
                    continue;
                }

                // Check invariants on new successor.
                if let Some(inv_idx) = {
                    let succ_slice = &scratch.successor_slice(successor_count)[start..end];
                    self.first_failed_invariant(succ_slice)?
                } {
                    if invariant_ok {
                        invariant_ok = false;
                        failed_invariant_idx = Some(inv_idx);
                        failed_successor_idx =
                            Some(u32::try_from(new_count).map_err(|_| BfsStepError::RuntimeError)?);
                    }
                }

                // Compact in place.
                if self.state_len != 0 && new_count != chunk_idx {
                    let dst_start = new_count
                        .checked_mul(self.state_len)
                        .ok_or(BfsStepError::RuntimeError)?;
                    scratch.compact_in_place(start, end, dst_start);
                }

                new_count += 1;
            }

            return Ok(FlatBfsStepOutputRef::from_parts(
                scratch.successor_slice(new_count),
                self.state_len,
                new_count,
                step_result.successors_generated,
                invariant_ok,
                failed_invariant_idx,
                failed_successor_idx,
            ));
        }

        Ok(FlatBfsStepOutputRef::from_parts(
            scratch.successor_slice(successor_count),
            self.state_len,
            successor_count,
            step_result.successors_generated,
            step_result.invariant_ok != 0,
            (step_result.invariant_ok == 0).then_some(step_result.failed_invariant_idx),
            (step_result.invariant_ok == 0).then_some(step_result.failed_successor_idx),
        ))
    }

    fn first_failed_invariant(&self, state: &[i64]) -> Result<Option<u32>, BfsStepError> {
        let state_len = u32::try_from(self.state_len).map_err(|_| BfsStepError::RuntimeError)?;

        for invariant in self.invariant_fns.iter() {
            let mut out = crate::abi::JitCallOut::default();
            unsafe {
                // SAFETY: `state` has `state_len` slots; `out` is valid.
                (invariant.func)(&mut out, state.as_ptr(), state_len);
            }

            if out.status != crate::abi::JitStatus::Ok {
                return Err(BfsStepError::RuntimeError);
            }
            if out.value == 0 {
                return Ok(Some(invariant.descriptor.invariant_idx));
            }
        }

        Ok(None)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::abi::JitCallOut;
    use crate::bfs_step::{ActionDescriptor, InvariantDescriptor};
    use crate::compiled_bfs::state_fingerprint;
    use crate::compound_layout::{StateLayout, VarLayout};
    use std::sync::atomic::{AtomicI64, Ordering};
    use std::sync::{Mutex, MutexGuard};

    static NONDETERMINISTIC_ACTION_COUNTER: AtomicI64 = AtomicI64::new(0);
    static FUSED_PARENT_PROVENANCE_ENV_LOCK: Mutex<()> = Mutex::new(());

    struct FusedParentProvenanceEnvGuard {
        _guard: MutexGuard<'static, ()>,
        previous: Option<String>,
    }

    impl FusedParentProvenanceEnvGuard {
        fn set(value: Option<&str>) -> Self {
            let guard = FUSED_PARENT_PROVENANCE_ENV_LOCK
                .lock()
                .expect("fused provenance env lock poisoned");
            let previous = std::env::var(FUSED_PARENT_PROVENANCE_REPLAY_ENV).ok();
            match value {
                Some(value) => std::env::set_var(FUSED_PARENT_PROVENANCE_REPLAY_ENV, value),
                None => std::env::remove_var(FUSED_PARENT_PROVENANCE_REPLAY_ENV),
            }
            Self {
                _guard: guard,
                previous,
            }
        }
    }

    impl Drop for FusedParentProvenanceEnvGuard {
        fn drop(&mut self) {
            match &self.previous {
                Some(value) => std::env::set_var(FUSED_PARENT_PROVENANCE_REPLAY_ENV, value),
                None => std::env::remove_var(FUSED_PARENT_PROVENANCE_REPLAY_ENV),
            }
        }
    }

    unsafe extern "C" fn increment_slot0(
        out: *mut JitCallOut,
        state_in: *const i64,
        state_out: *mut i64,
        state_len: u32,
    ) {
        let len = state_len as usize;
        let src = unsafe { std::slice::from_raw_parts(state_in, len) };
        let dst = unsafe { std::slice::from_raw_parts_mut(state_out, len) };
        dst.copy_from_slice(src);
        if let Some(first) = dst.first_mut() {
            *first += 1;
        }
        unsafe { *out = JitCallOut::ok(1) };
    }

    unsafe extern "C" fn increment_slot0_by_2(
        out: *mut JitCallOut,
        state_in: *const i64,
        state_out: *mut i64,
        state_len: u32,
    ) {
        unsafe { increment_slot0(out, state_in, state_out, state_len) };
        let len = state_len as usize;
        let dst = unsafe { std::slice::from_raw_parts_mut(state_out, len) };
        if let Some(first) = dst.first_mut() {
            *first += 1;
        }
    }

    unsafe extern "C" fn set_slot0_to_42(
        out: *mut JitCallOut,
        _state_in: *const i64,
        state_out: *mut i64,
        state_len: u32,
    ) {
        let len = state_len as usize;
        let dst = unsafe { std::slice::from_raw_parts_mut(state_out, len) };
        dst.fill(0);
        if let Some(first) = dst.first_mut() {
            *first = 42;
        }
        unsafe { *out = JitCallOut::ok(1) };
    }

    unsafe extern "C" fn increment_slot0_partial_write(
        out: *mut JitCallOut,
        state_in: *const i64,
        state_out: *mut i64,
        state_len: u32,
    ) {
        let len = state_len as usize;
        let src = unsafe { std::slice::from_raw_parts(state_in, len) };
        let dst = unsafe { std::slice::from_raw_parts_mut(state_out, len) };
        if let (Some(src_first), Some(dst_first)) = (src.first(), dst.first_mut()) {
            *dst_first = src_first + 1;
        }
        unsafe { *out = JitCallOut::ok(1) };
    }

    unsafe extern "C" fn monotonic_counter_successor(
        out: *mut JitCallOut,
        _state_in: *const i64,
        state_out: *mut i64,
        state_len: u32,
    ) {
        let len = state_len as usize;
        let dst = unsafe { std::slice::from_raw_parts_mut(state_out, len) };
        dst.fill(0);
        if let Some(first) = dst.first_mut() {
            *first = NONDETERMINISTIC_ACTION_COUNTER.fetch_add(1, Ordering::SeqCst) + 1;
        }
        unsafe { *out = JitCallOut::ok(1) };
    }

    unsafe extern "C" fn slot0_lt_100(out: *mut JitCallOut, state: *const i64, state_len: u32) {
        let state = unsafe { std::slice::from_raw_parts(state, state_len as usize) };
        let passed = state.first().copied().unwrap_or(0) < 100;
        unsafe { *out = JitCallOut::ok(passed as i64) };
    }

    fn make_spec(
        state_len: usize,
        actions: Vec<ActionDescriptor>,
        invariants: Vec<InvariantDescriptor>,
    ) -> BfsStepSpec {
        BfsStepSpec {
            state_len,
            state_layout: StateLayout::new(vec![VarLayout::ScalarInt; state_len]),
            actions,
            invariants,
        }
    }

    fn increment_action() -> ActionDescriptor {
        ActionDescriptor {
            name: "IncSlot0".to_string(),
            action_idx: 0,
            binding_values: vec![],
            formal_values: vec![],
            read_vars: vec![0],
            write_vars: vec![0],
        }
    }

    fn set_42_action() -> ActionDescriptor {
        ActionDescriptor {
            name: "SetSlot0To42".to_string(),
            action_idx: 0,
            binding_values: vec![],
            formal_values: vec![],
            read_vars: vec![],
            write_vars: vec![0],
        }
    }

    fn slot0_lt_100_invariant() -> InvariantDescriptor {
        InvariantDescriptor {
            name: "Slot0Lt100".to_string(),
            invariant_idx: 0,
        }
    }

    fn collect_successors(result: &CompiledLevelResult) -> Vec<&[i64]> {
        result.iter_successors().collect()
    }

    // ---- Arena-based level tests ----

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_compiled_level_arena_basic() {
        let actions = vec![increment_action()];
        let spec = make_spec(2, actions.clone(), vec![]);
        let compiled_actions = vec![CompiledActionFn::new(actions[0].clone(), increment_slot0)];

        let level = CompiledBfsLevel::build(&spec, compiled_actions, vec![], 32).expect("build");

        // Three parents in contiguous arena: [0,10], [1,10], [2,10]
        let arena = vec![0i64, 10, 1, 10, 2, 10];
        let result = level.run_level_arena(&arena, 3).expect("run_level_arena");

        assert_eq!(
            collect_successors(&result),
            vec![&[1, 10][..], &[2, 10][..], &[3, 10][..]]
        );
        assert_eq!(result.successor_arena, vec![1, 10, 2, 10, 3, 10]);
        assert_eq!(result.successor_parent_indices, Some(vec![0, 1, 2]));
        assert_eq!(result.successor_count(), 3);
        assert!(result.regular_invariants_checked_by_backend);
        assert_eq!(result.parents_processed, 3);
        assert_eq!(result.total_generated, 3);
        assert_eq!(result.total_new, 3);
        assert!(result.invariant_ok);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_compiled_level_arena_dedup() {
        // Two parents that produce the same successor -> only one new.
        let actions = vec![set_42_action()];
        let spec = make_spec(1, actions.clone(), vec![]);
        let shared_fp = Arc::new(ResizableAtomicFpSet::new(32));

        let level = CompiledBfsLevel::build_with_shared_fp_set(
            &spec,
            vec![CompiledActionFn::new(actions[0].clone(), set_slot0_to_42)],
            vec![],
            Arc::clone(&shared_fp),
        )
        .expect("build");

        let arena = vec![1i64, 2, 3]; // 3 parents of state_len=1
        let result = level.run_level_arena(&arena, 3).expect("run_level_arena");

        assert_eq!(collect_successors(&result), vec![&[42][..]]);
        assert_eq!(result.parents_processed, 3);
        assert_eq!(result.total_generated, 3);
        assert_eq!(result.total_new, 1);
        assert!(result.invariant_ok);
        assert_eq!(shared_fp.len(), 1);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_compiled_level_arena_invariant_violation() {
        let actions = vec![increment_action()];
        let invariants = vec![slot0_lt_100_invariant()];
        let spec = make_spec(1, actions.clone(), invariants.clone());
        let compiled_actions = vec![CompiledActionFn::new(actions[0].clone(), increment_slot0)];
        let compiled_invariants = vec![CompiledInvariantFn::new(
            invariants[0].clone(),
            slot0_lt_100,
        )];

        let level = CompiledBfsLevel::build(&spec, compiled_actions, compiled_invariants, 1000)
            .expect("build");

        // Parents: [0], [99], [1]. Invariant fails at parent [99] -> [100].
        let arena = vec![0i64, 99, 1];
        let result = level.run_level_arena(&arena, 3).expect("run_level_arena");

        assert_eq!(collect_successors(&result), vec![&[1][..], &[100][..]]);
        assert_eq!(result.parents_processed, 2);
        assert!(!result.invariant_ok);
        assert_eq!(result.failed_parent_idx, Some(1));
        assert_eq!(result.failed_invariant_idx, Some(0));
        assert_eq!(result.failed_successor, Some(vec![100]));
    }

    // ---- Convenience run_level tests (matching CompiledBfsStep::run_bfs_level) ----

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_compiled_level_run_level_matches_arena() {
        let actions = vec![increment_action()];
        let spec = make_spec(2, actions.clone(), vec![]);

        let arena_level = CompiledBfsLevel::build(
            &spec,
            vec![CompiledActionFn::new(actions[0].clone(), increment_slot0)],
            vec![],
            32,
        )
        .expect("build arena");

        let vec_level = CompiledBfsLevel::build(
            &spec,
            vec![CompiledActionFn::new(actions[0].clone(), increment_slot0)],
            vec![],
            32,
        )
        .expect("build vec");

        let parents = vec![vec![0i64, 10], vec![1, 10], vec![2, 10]];
        let arena = vec![0i64, 10, 1, 10, 2, 10];

        let arena_result = arena_level
            .run_level_arena(&arena, 3)
            .expect("run_level_arena");
        let vec_result = vec_level.run_level(&parents).expect("run_level");

        assert_eq!(
            collect_successors(&arena_result),
            collect_successors(&vec_result)
        );
        assert_eq!(arena_result.parents_processed, vec_result.parents_processed);
        assert_eq!(arena_result.total_generated, vec_result.total_generated);
        assert_eq!(arena_result.total_new, vec_result.total_new);
        assert_eq!(arena_result.invariant_ok, vec_result.invariant_ok);
    }

    // ---- Multi-level tests ----

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_compiled_level_multi_level_basic() {
        let actions = vec![increment_action()];
        let spec = make_spec(2, actions.clone(), vec![]);
        let shared_fp = Arc::new(ResizableAtomicFpSet::new(64));

        let level = CompiledBfsLevel::build_with_shared_fp_set(
            &spec,
            vec![CompiledActionFn::new(actions[0].clone(), increment_slot0)],
            vec![],
            Arc::clone(&shared_fp),
        )
        .expect("build");

        let result = level
            .run_multi_level(&[vec![0, 0]], 5)
            .expect("multi-level");

        assert_eq!(result.depths_completed, 5);
        assert!(result.invariant_ok);
        // Init + 5 new states = 6 total.
        assert_eq!(result.total_states_seen, 6);
        assert_eq!(result.total_generated, 5);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_compiled_level_multi_level_empty_frontier() {
        let actions = vec![set_42_action()];
        let spec = make_spec(1, actions.clone(), vec![]);
        let shared_fp = Arc::new(ResizableAtomicFpSet::new(32));

        let level = CompiledBfsLevel::build_with_shared_fp_set(
            &spec,
            vec![CompiledActionFn::new(actions[0].clone(), set_slot0_to_42)],
            vec![],
            Arc::clone(&shared_fp),
        )
        .expect("build");

        let result = level.run_multi_level(&[vec![0]], 100).expect("multi-level");

        // Depth 0: [0] -> [42] (new). Depth 1: [42] -> [42] (dup, empty).
        assert!(result.depths_completed <= 2);
        assert!(result.invariant_ok);
        assert_eq!(result.total_states_seen, 2);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_compiled_level_multi_level_invariant_violation() {
        let actions = vec![increment_action()];
        let invariants = vec![slot0_lt_100_invariant()];
        let spec = make_spec(2, actions.clone(), invariants.clone());
        let shared_fp = Arc::new(ResizableAtomicFpSet::new(64));

        let level = CompiledBfsLevel::build_with_shared_fp_set(
            &spec,
            vec![CompiledActionFn::new(actions[0].clone(), increment_slot0)],
            vec![CompiledInvariantFn::new(
                invariants[0].clone(),
                slot0_lt_100,
            )],
            Arc::clone(&shared_fp),
        )
        .expect("build");

        let result = level
            .run_multi_level(&[vec![98, 0]], 10)
            .expect("multi-level");

        assert!(!result.invariant_ok);
        assert_eq!(result.failed_invariant_idx, Some(0));
        assert_eq!(result.failed_depth, Some(1));
        assert_eq!(result.failed_successor, Some(vec![100, 0]));
    }

    // ---- Throughput benchmark ----

    #[cfg_attr(test, ntest::timeout(30000))]
    #[test]
    fn test_compiled_level_arena_throughput() {
        use std::time::Instant;

        let mut second_action = increment_action();
        second_action.name = "IncSlot0By2".to_string();
        second_action.action_idx = 1;

        let actions = vec![increment_action(), second_action];
        let spec = make_spec(4, actions.clone(), vec![]);

        for frontier_size in [100usize, 1_000, 10_000] {
            // Build contiguous arena.
            let mut arena = Vec::with_capacity(frontier_size * 4);
            for i in 0..frontier_size {
                arena.extend_from_slice(&[i as i64, 10, 20, 30]);
            }

            let level = CompiledBfsLevel::build(
                &spec,
                vec![
                    CompiledActionFn::new(actions[0].clone(), increment_slot0),
                    CompiledActionFn::new(actions[1].clone(), increment_slot0_by_2),
                ],
                vec![],
                frontier_size.saturating_mul(2),
            )
            .expect("build");

            let start = Instant::now();
            let result = level
                .run_level_arena(&arena, frontier_size)
                .expect("run_level_arena");
            let elapsed = start.elapsed();
            let elapsed_secs = elapsed.as_secs_f64().max(f64::EPSILON);

            assert_eq!(result.parents_processed, frontier_size);
            assert_eq!(result.total_generated, (frontier_size as u64) * 2);
            assert_eq!(result.total_new, (frontier_size as u64) + 1);
            assert!(result.invariant_ok);

            let states_per_sec = frontier_size as f64 / elapsed_secs;
            let generated_per_sec = result.total_generated as f64 / elapsed_secs;
            eprintln!(
                "CompiledBfsLevel throughput: frontier={frontier_size}, elapsed={:.3}ms, states/sec={:.0}, generated/sec={:.0}",
                elapsed_secs * 1000.0,
                states_per_sec,
                generated_per_sec,
            );
        }
    }

    // ---- Cross-validation: CompiledBfsLevel vs CompiledBfsStep ----

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_compiled_level_matches_compiled_bfs_step_level() {
        use crate::compiled_bfs::CompiledBfsStep;

        let actions = vec![increment_action()];
        let spec = make_spec(2, actions.clone(), vec![]);
        let parents = vec![vec![7i64, 11], vec![7, 11], vec![8, 11]];

        // CompiledBfsStep path
        let step = CompiledBfsStep::build(
            &spec,
            vec![CompiledActionFn::new(actions[0].clone(), increment_slot0)],
            vec![],
            64,
        )
        .expect("build step");
        let step_result = step.run_bfs_level(&parents).expect("run_bfs_level");

        // CompiledBfsLevel path
        let level = CompiledBfsLevel::build(
            &spec,
            vec![CompiledActionFn::new(actions[0].clone(), increment_slot0)],
            vec![],
            64,
        )
        .expect("build level");
        let level_result = level.run_level(&parents).expect("run_level");

        assert_eq!(
            step_result
                .new_successors
                .iter()
                .map(Vec::as_slice)
                .collect::<Vec<_>>(),
            collect_successors(&level_result)
        );
        assert_eq!(
            step_result.parents_processed,
            level_result.parents_processed
        );
        assert_eq!(step_result.total_generated, level_result.total_generated);
        assert_eq!(step_result.total_new, level_result.total_new);
        assert_eq!(step_result.invariant_ok, level_result.invariant_ok);
    }

    // ==== Fused BFS level tests (Phase 5 fused function) ====

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_fused_level_basic() {
        let _env = FusedParentProvenanceEnvGuard::set(None);
        let actions = vec![increment_action()];
        let spec = make_spec(2, actions.clone(), vec![]);
        let compiled_actions = vec![CompiledActionFn::new(actions[0].clone(), increment_slot0)];

        let level = CompiledBfsLevel::build_fused(&spec, compiled_actions, vec![], 32)
            .expect("build_fused");

        assert!(
            level.has_fused_level(),
            "build_fused should enable fused path"
        );

        let arena = vec![0i64, 10, 1, 10, 2, 10];
        let result = level
            .run_level_fused_arena(&arena, 3)
            .expect("fused path should be available")
            .expect("run_level_fused_arena");

        assert_eq!(
            collect_successors(&result),
            vec![&[1, 10][..], &[2, 10][..], &[3, 10][..]]
        );
        assert_eq!(result.successor_arena, vec![1, 10, 2, 10, 3, 10]);
        assert_eq!(result.successor_parent_indices, None);
        assert_eq!(result.successor_count(), 3);
        assert_eq!(result.parents_processed, 3);
        assert_eq!(result.total_generated, 3);
        assert_eq!(result.total_new, 3);
        assert!(result.invariant_ok);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_fused_level_dedup() {
        let _env = FusedParentProvenanceEnvGuard::set(None);
        // Two parents producing the same successor -> only one new.
        let actions = vec![set_42_action()];
        let spec = make_spec(1, actions.clone(), vec![]);
        let compiled_actions = vec![CompiledActionFn::new(actions[0].clone(), set_slot0_to_42)];

        let level = CompiledBfsLevel::build_fused(&spec, compiled_actions, vec![], 32)
            .expect("build_fused");

        let arena = vec![1i64, 2, 3]; // 3 parents of state_len=1
        let result = level
            .run_level_fused_arena(&arena, 3)
            .expect("fused available")
            .expect("run");

        assert_eq!(collect_successors(&result), vec![&[42][..]]);
        assert_eq!(result.successor_parent_indices, None);
        assert_eq!(result.parents_processed, 3);
        assert_eq!(result.total_generated, 3);
        assert_eq!(result.total_new, 1);
        assert!(result.invariant_ok);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_fused_level_invariant_violation() {
        let _env = FusedParentProvenanceEnvGuard::set(None);
        let actions = vec![increment_action()];
        let invariants = vec![slot0_lt_100_invariant()];
        let spec = make_spec(1, actions.clone(), invariants.clone());
        let compiled_actions = vec![CompiledActionFn::new(actions[0].clone(), increment_slot0)];
        let compiled_invariants = vec![CompiledInvariantFn::new(
            invariants[0].clone(),
            slot0_lt_100,
        )];

        let level =
            CompiledBfsLevel::build_fused(&spec, compiled_actions, compiled_invariants, 1000)
                .expect("build_fused");

        // Parents: [0], [99], [1]. Invariant fails at parent [99] -> [100].
        let arena = vec![0i64, 99, 1];
        let result = level
            .run_level_fused_arena(&arena, 3)
            .expect("fused available")
            .expect("run");

        // The fused path processes all parents (no early break on invariant failure).
        assert!(!result.invariant_ok);
        assert_eq!(result.failed_invariant_idx, Some(0));
        assert_eq!(result.failed_parent_idx, Some(1));
        assert_eq!(result.failed_successor, Some(vec![100]));
        assert_eq!(result.successor_parent_indices, None);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_fused_parent_provenance_derivation_matches_successors_by_value() {
        let actions = vec![increment_action()];
        let spec = make_spec(1, actions.clone(), vec![]);
        let compiled_actions = vec![CompiledActionFn::new(actions[0].clone(), increment_slot0)];

        let level = CompiledBfsLevel::build_fused(&spec, compiled_actions, vec![], 32)
            .expect("build_fused");

        let parent_arena = vec![0i64, 10];
        let reordered_successor_arena = vec![11i64, 1];
        let parent_indices = level
            .derive_fused_successor_parent_indices(&parent_arena, 2, &reordered_successor_arena, 2)
            .expect("semantic successor matching should recover reordered provenance");

        assert_eq!(parent_indices, vec![1, 0]);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_fused_parent_provenance_derivation_seeds_partial_write_output() {
        let actions = vec![increment_action()];
        let spec = make_spec(2, actions.clone(), vec![]);
        let compiled_actions = vec![CompiledActionFn::new(
            actions[0].clone(),
            increment_slot0_partial_write,
        )];

        let level = CompiledBfsLevel::build_fused(&spec, compiled_actions, vec![], 32)
            .expect("build_fused");

        let parent_arena = vec![0i64, 7, 10, 9];
        let reordered_successor_arena = vec![11i64, 9, 1, 7];
        let parent_indices = level
            .derive_fused_successor_parent_indices(&parent_arena, 2, &reordered_successor_arena, 2)
            .expect("partial-write provenance should inherit unchanged parent slots");

        assert_eq!(parent_indices, vec![1, 0]);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_fused_parent_provenance_replay_is_off_by_default() {
        let _env = FusedParentProvenanceEnvGuard::set(None);
        NONDETERMINISTIC_ACTION_COUNTER.store(0, Ordering::SeqCst);

        let actions = vec![set_42_action()];
        let spec = make_spec(1, actions.clone(), vec![]);
        let compiled_actions = vec![CompiledActionFn::new(
            actions[0].clone(),
            monotonic_counter_successor,
        )];

        let level = CompiledBfsLevel::build_fused(&spec, compiled_actions, vec![], 32)
            .expect("build_fused");

        let arena = vec![0i64, 1];
        let result = level
            .run_level_fused_arena(&arena, 2)
            .expect("fused available")
            .expect("run");

        assert_eq!(collect_successors(&result), vec![&[1][..], &[2][..]]);
        assert_eq!(result.successor_parent_indices, None);
        assert_eq!(result.successor_count(), 2);
        assert!(result.regular_invariants_checked_by_backend);
        assert_eq!(
            NONDETERMINISTIC_ACTION_COUNTER.load(Ordering::SeqCst),
            2,
            "default fused execution must not replay action functions for provenance"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_fused_parent_provenance_replay_env_enables_debug_derivation() {
        let _env = FusedParentProvenanceEnvGuard::set(Some("1"));

        let actions = vec![increment_action()];
        let spec = make_spec(1, actions.clone(), vec![]);
        let compiled_actions = vec![CompiledActionFn::new(actions[0].clone(), increment_slot0)];

        let level = CompiledBfsLevel::build_fused(&spec, compiled_actions, vec![], 32)
            .expect("build_fused");

        let arena = vec![0i64, 10];
        let result = level
            .run_level_fused_arena(&arena, 2)
            .expect("fused available")
            .expect("run");

        assert_eq!(collect_successors(&result), vec![&[1][..], &[11][..]]);
        assert_eq!(result.successor_parent_indices, Some(vec![0, 1]));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_fused_level_matches_unfused() {
        let _env = FusedParentProvenanceEnvGuard::set(None);
        // Cross-validate: fused and unfused must produce identical results.
        let actions = vec![increment_action()];
        let spec = make_spec(2, actions.clone(), vec![]);
        let parents = vec![vec![7i64, 11], vec![7, 11], vec![8, 11]];
        let arena = vec![7i64, 11, 7, 11, 8, 11];

        // Unfused path
        let unfused = CompiledBfsLevel::build(
            &spec,
            vec![CompiledActionFn::new(actions[0].clone(), increment_slot0)],
            vec![],
            64,
        )
        .expect("build unfused");
        let unfused_result = unfused.run_level(&parents).expect("run_level");

        // Fused path
        let fused = CompiledBfsLevel::build_fused(
            &spec,
            vec![CompiledActionFn::new(actions[0].clone(), increment_slot0)],
            vec![],
            64,
        )
        .expect("build_fused");
        let fused_result = fused
            .run_level_fused_arena(&arena, 3)
            .expect("fused available")
            .expect("run fused");

        assert_eq!(
            collect_successors(&unfused_result),
            collect_successors(&fused_result)
        );
        assert_eq!(
            unfused_result.parents_processed,
            fused_result.parents_processed
        );
        assert_eq!(unfused_result.total_generated, fused_result.total_generated);
        assert_eq!(unfused_result.total_new, fused_result.total_new);
        assert_eq!(unfused_result.invariant_ok, fused_result.invariant_ok);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_fused_level_empty_frontier() {
        let actions = vec![increment_action()];
        let spec = make_spec(2, actions.clone(), vec![]);

        let level = CompiledBfsLevel::build_fused(
            &spec,
            vec![CompiledActionFn::new(actions[0].clone(), increment_slot0)],
            vec![],
            32,
        )
        .expect("build_fused");

        let arena: Vec<i64> = vec![];
        let result = level
            .run_level_fused_arena(&arena, 0)
            .expect("fused available")
            .expect("run");

        assert_eq!(result.successor_count(), 0);
        assert_eq!(result.successor_parent_indices, Some(Vec::new()));
        assert_eq!(result.parents_processed, 0);
        assert_eq!(result.total_generated, 0);
        assert_eq!(result.total_new, 0);
        assert!(result.invariant_ok);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_fused_level_not_available_on_unfused_build() {
        let actions = vec![increment_action()];
        let spec = make_spec(2, actions.clone(), vec![]);

        let level = CompiledBfsLevel::build(
            &spec,
            vec![CompiledActionFn::new(actions[0].clone(), increment_slot0)],
            vec![],
            32,
        )
        .expect("build");

        assert!(!level.has_fused_level());
        let arena = vec![0i64, 10];
        assert!(level.run_level_fused_arena(&arena, 1).is_none());
    }

    #[cfg_attr(test, ntest::timeout(30000))]
    #[test]
    fn test_fused_level_throughput() {
        use std::time::Instant;

        let mut second_action = increment_action();
        second_action.name = "IncSlot0By2".to_string();
        second_action.action_idx = 1;

        let actions = vec![increment_action(), second_action];
        let spec = make_spec(4, actions.clone(), vec![]);

        for frontier_size in [100usize, 1_000, 10_000] {
            let mut arena = Vec::with_capacity(frontier_size * 4);
            for i in 0..frontier_size {
                arena.extend_from_slice(&[i as i64, 10, 20, 30]);
            }

            let level = CompiledBfsLevel::build_fused(
                &spec,
                vec![
                    CompiledActionFn::new(actions[0].clone(), increment_slot0),
                    CompiledActionFn::new(actions[1].clone(), increment_slot0_by_2),
                ],
                vec![],
                frontier_size.saturating_mul(2),
            )
            .expect("build_fused");

            let start = Instant::now();
            let result = level
                .run_level_fused_arena(&arena, frontier_size)
                .expect("fused available")
                .expect("run");
            let elapsed = start.elapsed();
            let elapsed_secs = elapsed.as_secs_f64().max(f64::EPSILON);

            assert_eq!(result.parents_processed, frontier_size);
            assert_eq!(result.total_generated, (frontier_size as u64) * 2);
            assert_eq!(result.total_new, (frontier_size as u64) + 1);
            assert!(result.invariant_ok);

            let states_per_sec = frontier_size as f64 / elapsed_secs;
            let generated_per_sec = result.total_generated as f64 / elapsed_secs;
            eprintln!(
                "FUSED BFS level: frontier={frontier_size}, elapsed={:.3}ms, states/sec={:.0}, generated/sec={:.0}",
                elapsed_secs * 1000.0,
                states_per_sec,
                generated_per_sec,
            );
        }
    }
}
