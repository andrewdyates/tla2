// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Pure-data output types for the compiled BFS step pipeline.
//!
//! Consumers of `CompiledBfsStep::step` / `step_flat` see these shapes but do
//! not require the Cranelift backend that produced them. Moving the types
//! here in `tla-jit-runtime` lets `tla-check` handle BFS step results through
//! an imports path that is independent of the Cranelift JIT pipeline — a key
//! step toward deleting `tla-jit` entirely (epic #4251 Stage 2d Gate 1).
//!
//! Moved from `tla_jit::compiled_bfs` as part of #4267 Wave 12. Back-compat
//! re-exports remain in `tla-jit::compiled_bfs` so existing Cranelift callers
//! continue to compile unchanged.

use thiserror::Error;

/// Owned result of executing one compiled BFS step.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BfsStepOutput {
    pub successors: Vec<Vec<i64>>,
    pub generated_count: u32,
    pub invariant_ok: bool,
    pub failed_invariant_idx: Option<u32>,
    pub failed_successor_idx: Option<u32>,
    pub failed_successor: Option<Vec<i64>>,
}

/// Zero-copy result of executing one compiled BFS step.
///
/// Unlike [`BfsStepOutput`], this avoids per-successor `Vec<i64>` allocations.
/// Successors are stored contiguously in `succ_buf` as slices of `state_len`
/// i64 values. Use [`FlatBfsStepOutput::iter_successors`] to iterate over them.
///
/// Part of #3988: Zero-copy compiled BFS step output.
#[derive(Debug, Clone)]
pub struct FlatBfsStepOutput {
    succ_buf: Vec<i64>,
    state_len: usize,
    successor_count: usize,
    pub generated_count: u32,
    pub invariant_ok: bool,
    pub failed_invariant_idx: Option<u32>,
    pub failed_successor_idx: Option<u32>,
}

impl FlatBfsStepOutput {
    /// Construct a `FlatBfsStepOutput` from its constituent parts.
    ///
    /// Intended for use by the JIT backend when emitting a compiled BFS step
    /// result. `succ_buf` must contain at least `successor_count * state_len`
    /// i64 entries; any slack is ignored by [`Self::iter_successors`].
    #[must_use]
    #[allow(clippy::too_many_arguments)]
    pub fn from_parts(
        succ_buf: Vec<i64>,
        state_len: usize,
        successor_count: usize,
        generated_count: u32,
        invariant_ok: bool,
        failed_invariant_idx: Option<u32>,
        failed_successor_idx: Option<u32>,
    ) -> Self {
        Self {
            succ_buf,
            state_len,
            successor_count,
            generated_count,
            invariant_ok,
            failed_invariant_idx,
            failed_successor_idx,
        }
    }

    /// Number of new successors in this output.
    #[must_use]
    pub fn successor_count(&self) -> usize {
        self.successor_count
    }

    /// i64 slots per successor in this output.
    #[must_use]
    pub fn state_len(&self) -> usize {
        self.state_len
    }

    /// Iterate over the flat successor slices.
    ///
    /// Each item is a `&[i64]` of length `state_len` representing one
    /// successor state in the flat i64 representation.
    pub fn iter_successors(&self) -> impl Iterator<Item = &[i64]> + '_ {
        let len = self.state_len;
        if len == 0 {
            // Avoid division by zero; yield `successor_count` empty slices.
            return FlatSuccessorIter::Empty(self.successor_count);
        }
        FlatSuccessorIter::Chunked(self.succ_buf[..self.successor_count * len].chunks_exact(len))
    }
}

/// Borrowed zero-copy view over a compiled BFS step result.
///
/// Similar to [`FlatBfsStepOutput`] but borrows `succ_buf` from the caller's
/// scratch. Lifetime tied to the scratch buffer.
#[derive(Debug, Clone, Copy)]
pub struct FlatBfsStepOutputRef<'a> {
    succ_buf: &'a [i64],
    state_len: usize,
    successor_count: usize,
    pub generated_count: u32,
    pub invariant_ok: bool,
    pub failed_invariant_idx: Option<u32>,
    pub failed_successor_idx: Option<u32>,
}

impl<'a> FlatBfsStepOutputRef<'a> {
    /// Construct a `FlatBfsStepOutputRef` from its constituent parts.
    ///
    /// Used by `CompiledBfsLevel` to build results from scratch buffer
    /// slices without exposing the internal struct layout.
    ///
    /// Part of #3988: Phase 5 compiled BFS level loop.
    #[must_use]
    pub fn from_parts(
        succ_buf: &'a [i64],
        state_len: usize,
        successor_count: usize,
        generated_count: u32,
        invariant_ok: bool,
        failed_invariant_idx: Option<u32>,
        failed_successor_idx: Option<u32>,
    ) -> Self {
        Self {
            succ_buf,
            state_len,
            successor_count,
            generated_count,
            invariant_ok,
            failed_invariant_idx,
            failed_successor_idx,
        }
    }

    /// Number of new successors in this output.
    #[must_use]
    pub fn successor_count(&self) -> usize {
        self.successor_count
    }

    /// Iterate over the flat successor slices.
    #[must_use]
    pub fn iter_successors(&self) -> impl Iterator<Item = &[i64]> + '_ {
        if self.state_len == 0 {
            return FlatSuccessorIter::Empty(self.successor_count);
        }
        FlatSuccessorIter::Chunked(self.succ_buf.chunks_exact(self.state_len))
    }

    /// Pointer to the underlying successor buffer.
    ///
    /// Exposed for tests that assert the output aliases a caller-provided
    /// scratch buffer (e.g., `CompiledBfsLevel` scratch reuse invariants).
    /// The scratch field itself remains private.
    #[must_use]
    pub fn succ_buf_as_ptr(&self) -> *const i64 {
        self.succ_buf.as_ptr()
    }
}

/// Internal iterator shared by [`FlatBfsStepOutput`] and [`FlatBfsStepOutputRef`].
enum FlatSuccessorIter<'a> {
    Chunked(std::slice::ChunksExact<'a, i64>),
    Empty(usize),
}

impl<'a> Iterator for FlatSuccessorIter<'a> {
    type Item = &'a [i64];

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            FlatSuccessorIter::Chunked(chunks) => chunks.next(),
            FlatSuccessorIter::Empty(remaining) => {
                if *remaining > 0 {
                    *remaining -= 1;
                    Some(&[])
                } else {
                    None
                }
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match self {
            FlatSuccessorIter::Chunked(chunks) => chunks.size_hint(),
            FlatSuccessorIter::Empty(remaining) => (*remaining, Some(*remaining)),
        }
    }
}

impl<'a> ExactSizeIterator for FlatSuccessorIter<'a> {}

/// Aggregate result of executing a compiled BFS step over a batch of parent states.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BfsBatchResult {
    pub successors: Vec<Vec<i64>>,
    pub parents_processed: usize,
    pub generated_count: u64,
    pub new_count: u64,
    pub invariant_ok: bool,
    pub failed_parent_idx: Option<usize>,
    pub failed_invariant_idx: Option<u32>,
    pub failed_successor_idx: Option<u32>,
    pub failed_successor: Option<Vec<i64>>,
}

/// Execution errors from a compiled BFS step.
#[derive(Debug, Error, Clone, Copy, PartialEq, Eq)]
pub enum BfsStepError {
    #[error("compiled BFS step runtime error")]
    RuntimeError,
    #[error("compiled BFS step successor buffer overflow after {partial_count} successors")]
    BufferOverflow { partial_count: u32 },
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_flat_bfs_step_output_empty_state_len() {
        let out = FlatBfsStepOutput::from_parts(vec![], 0, 3, 3, true, None, None);
        assert_eq!(out.successor_count(), 3);
        assert_eq!(out.state_len(), 0);
        let slices: Vec<&[i64]> = out.iter_successors().collect();
        assert_eq!(slices.len(), 3);
        assert!(slices.iter().all(|s| s.is_empty()));
    }

    #[test]
    fn test_flat_bfs_step_output_chunked() {
        let buf = vec![1, 2, 3, 4, 5, 6];
        let out = FlatBfsStepOutput::from_parts(buf, 2, 3, 3, true, None, None);
        let slices: Vec<&[i64]> = out.iter_successors().collect();
        assert_eq!(slices, vec![&[1, 2][..], &[3, 4][..], &[5, 6][..]]);
    }

    #[test]
    fn test_flat_bfs_step_output_ref_chunked() {
        let buf = [10, 20, 30, 40];
        let out = FlatBfsStepOutputRef::from_parts(&buf, 2, 2, 2, true, None, None);
        let slices: Vec<&[i64]> = out.iter_successors().collect();
        assert_eq!(slices, vec![&[10, 20][..], &[30, 40][..]]);
    }

    #[test]
    fn test_bfs_step_error_display() {
        let e = BfsStepError::BufferOverflow { partial_count: 7 };
        assert!(format!("{e}").contains("7"));
    }
}
