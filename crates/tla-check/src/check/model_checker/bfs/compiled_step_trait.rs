// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Backend-agnostic abstraction over compiled BFS step + fused BFS level.
//!
//! `compiled_bfs_loop.rs` is the single-thread supremacy path: it runs the
//! BFS level loop against a contiguous `FlatBfsFrontier` arena using a
//! compiled action dispatcher + invariant checker + fingerprinter. Today the
//! only implementer is the Cranelift-backed `tla_jit::CompiledBfsStep` /
//! `CompiledBfsLevel`. When Stage 2d of epic #4251 (#4267) deletes `tla-jit`,
//! the LLVM2 backend (`tla-llvm2`) will provide its own implementer.
//!
//! The loop is coded against these traits rather than the concrete Cranelift
//! types so that:
//!
//! 1. The loop survives the deletion of `tla-jit` in Stage 2d.
//! 2. The LLVM2 backend can plug in its own compiled BFS step and level
//!    implementations without rewriting the level loop.
//! 3. Future backends (e.g., AOT `.dylib`) implement one trait surface
//!    instead of reimplementing the BFS integration logic.
//!
//! Part of #4171 (end-to-end compiled BFS wiring) and #4267 (Stage 2d
//! deletion of `tla-jit`). This file is the seam between the level loop
//! and whichever backend generated the compiled action/invariant functions.

use tla_jit_runtime::{BfsStepError, FlatBfsStepOutput};

/// Result of processing one BFS frontier level via a compiled, fused level
/// function.
///
/// This mirrors the Cranelift-backed `tla_jit::CompiledLevelResult` so that
/// the level loop can consume level outputs without a direct dependency on
/// the Cranelift JIT. The LLVM2 backend and any future backend populate the
/// same shape.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(in crate::check::model_checker) struct CompiledLevelResult {
    /// New successor states discovered in this level, as owned flat i64 vecs
    /// of length `state_len`.
    pub new_successors: Vec<Vec<i64>>,
    /// Number of parent states fully processed before early exit (or the
    /// full frontier count if the level completed without violation).
    pub parents_processed: usize,
    /// Total successors generated across the whole level (before dedup).
    pub total_generated: u64,
    /// Total new successors after the backend's first-level dedup.
    pub total_new: u64,
    /// `true` if every compiled invariant passed on every generated
    /// successor; `false` if any invariant failed.
    pub invariant_ok: bool,
    /// Index of the parent that produced the first invariant violation
    /// (only set when `invariant_ok == false`).
    pub failed_parent_idx: Option<usize>,
    /// Index of the invariant that failed (only set when
    /// `invariant_ok == false`).
    pub failed_invariant_idx: Option<u32>,
    /// The failing successor state (optional; backends are not required to
    /// populate this — the level loop falls back to the parent state for
    /// error reporting when `None`).
    pub failed_successor: Option<Vec<i64>>,
}

/// Per-parent compiled BFS step.
///
/// Implementers take a parent flat-i64 state and return a `FlatBfsStepOutput`
/// describing the new successors, invariant status, and any violation.
/// Action dispatch, invariant checking, fingerprinting, and first-level
/// (backend-local) dedup all run in compiled code inside `step_flat`.
///
/// Currently implemented by:
/// - `tla_jit::CompiledBfsStep` (Cranelift backend, deleted in #4267)
/// - TBD: `tla_llvm2::CompiledBfsStep` (Stream 3 of epic #4251)
pub(in crate::check::model_checker) trait CompiledBfsStep: Send {
    /// Number of i64 slots per flat state.
    fn state_len(&self) -> usize;

    /// Execute one compiled BFS step and return flat successor slices.
    fn step_flat(&self, state: &[i64]) -> Result<FlatBfsStepOutput, BfsStepError>;
}

/// Fused compiled BFS level.
///
/// When available (`has_fused_level() == true`), processes an entire frontier
/// in a single native call by walking the arena in compiled code — no
/// per-parent Rust-to-native boundary crossing. The level loop prefers this
/// path when available and falls back to the per-parent `CompiledBfsStep`
/// otherwise.
///
/// Currently implemented by:
/// - `tla_jit::CompiledBfsLevel` (Cranelift backend, deleted in #4267)
/// - TBD: `tla_llvm2::CompiledBfsLevel` (Stream 3 of epic #4251)
pub(in crate::check::model_checker) trait CompiledBfsLevel: Send {
    /// Whether the fused native level function is actually available.
    /// Implementers may return `false` when only the per-parent path was
    /// compiled.
    fn has_fused_level(&self) -> bool;

    /// Process one frontier level in native code.
    ///
    /// Returns `None` when the fused function is unavailable (the level loop
    /// falls back to the per-parent `CompiledBfsStep` path). Returns
    /// `Some(Err(_))` on a runtime error (the level loop falls back and logs
    /// the error). Returns `Some(Ok(_))` with the level result otherwise.
    ///
    /// `arena` holds `parent_count * state_len` i64 slots, laid out as
    /// `parent_count` contiguous parent states in row-major order.
    fn run_level_fused_arena(
        &self,
        arena: &[i64],
        parent_count: usize,
    ) -> Option<Result<CompiledLevelResult, BfsStepError>>;
}

// ---------------------------------------------------------------------------
// Cranelift backend blanket impls.
//
// These adapt `tla_jit::CompiledBfsStep` / `CompiledBfsLevel` to the
// backend-agnostic traits above. They are unconditional today; Stage 2d of
// epic #4251 (#4267) deletes `tla-jit` and removes these impls along with
// the rest of the crate. After that, the LLVM2 backend will provide its own
// implementations in the `llvm2_dispatch` module.
// ---------------------------------------------------------------------------

impl CompiledBfsStep for tla_jit::CompiledBfsStep {
    fn state_len(&self) -> usize {
        tla_jit::CompiledBfsStep::state_len(self)
    }

    fn step_flat(&self, state: &[i64]) -> Result<FlatBfsStepOutput, BfsStepError> {
        tla_jit::CompiledBfsStep::step_flat(self, state)
    }
}

impl CompiledBfsLevel for tla_jit::CompiledBfsLevel {
    fn has_fused_level(&self) -> bool {
        tla_jit::CompiledBfsLevel::has_fused_level(self)
    }

    fn run_level_fused_arena(
        &self,
        arena: &[i64],
        parent_count: usize,
    ) -> Option<Result<CompiledLevelResult, BfsStepError>> {
        tla_jit::CompiledBfsLevel::run_level_fused_arena(self, arena, parent_count).map(|result| {
            result.map(|r| CompiledLevelResult {
                new_successors: r.new_successors,
                parents_processed: r.parents_processed,
                total_generated: r.total_generated,
                total_new: r.total_new,
                invariant_ok: r.invariant_ok,
                failed_parent_idx: r.failed_parent_idx,
                failed_invariant_idx: r.failed_invariant_idx,
                failed_successor: r.failed_successor,
            })
        })
    }
}
