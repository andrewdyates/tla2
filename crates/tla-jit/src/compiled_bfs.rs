// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! High-level compiled BFS step wrapper for the model checker.

use crate::abi::{JitCallOut, JitStatus};
use crate::atomic_fp_set::{atomic_fp_set_probe, AtomicFpSet, InsertResult, ResizableAtomicFpSet};
use crate::bfs_step::*;
use crate::error::JitError;
use std::sync::Arc;

// `FlatBfsStepOutput`, `FlatBfsStepOutputRef`, `BfsStepOutput`, `BfsBatchResult`,
// and `BfsStepError` moved to `tla-jit-runtime` in Wave 12 (#4267) so `tla-check`
// can describe BFS step results without a direct dependency on Cranelift.
// Re-exported for back-compat with existing Cranelift call sites.
pub use tla_jit_runtime::{
    BfsBatchResult, BfsStepError, BfsStepOutput, FlatBfsStepOutput, FlatBfsStepOutputRef,
};

const _ATOMIC_FP_SET_PROBE: extern "C" fn(*const u8, u64) -> u32 = atomic_fp_set_probe;

/// High-level wrapper around a compiled BFS step function.
pub struct CompiledBfsStep {
    step_fn: JitBfsStepFn,
    fp_set: Arc<AtomicFpSet>,
    shared_fp_set: Option<Arc<ResizableAtomicFpSet>>,
    invariant_fns: Arc<[CompiledInvariantFn]>,
    state_len: usize,
    succ_capacity: usize,
    /// Retains ownership of the BFS step compiler whose JIT modules back
    /// `step_fn`'s code pages. Without this, dropping the compiler would free
    /// the mmap'd code pages, making `step_fn` a dangling pointer (#4082).
    _compiler: BfsStepCompiler,
}

impl CompiledBfsStep {
    /// Build a compiled BFS step from pre-compiled action and invariant functions.
    pub fn build(
        spec: &BfsStepSpec,
        action_fns: Vec<CompiledActionFn>,
        invariant_fns: Vec<CompiledInvariantFn>,
        expected_states: usize,
    ) -> Result<Self, JitError> {
        let succ_capacity = Self::successor_capacity(spec)?;
        let fp_set = Arc::new(AtomicFpSet::new(expected_states.saturating_mul(2).max(1)));
        let fp_set_ptr = Arc::as_ptr(&fp_set).cast::<u8>();

        let mut compiler = BfsStepCompiler::new()?;
        let step_fn =
            compiler.compile_with_actions(spec, &action_fns, &invariant_fns, Some(fp_set_ptr))?;

        Ok(Self {
            step_fn,
            fp_set,
            shared_fp_set: None,
            invariant_fns: Arc::from(invariant_fns),
            state_len: spec.state_len,
            succ_capacity,
            _compiler: compiler,
        })
    }

    /// Build a compiled BFS step that deduplicates against an existing shared set.
    ///
    /// The generated native step still performs action dispatch and successor
    /// materialization, while this wrapper applies shared-set deduplication and
    /// invariant checks against `shared_fp_set`.
    pub fn build_with_shared_fp_set(
        spec: &BfsStepSpec,
        action_fns: Vec<CompiledActionFn>,
        invariant_fns: Vec<CompiledInvariantFn>,
        shared_fp_set: Arc<ResizableAtomicFpSet>,
    ) -> Result<Self, JitError> {
        let succ_capacity = Self::successor_capacity(spec)?;
        let action_only_spec = BfsStepSpec {
            state_len: spec.state_len,
            state_layout: spec.state_layout.clone(),
            actions: spec.actions.clone(),
            invariants: Vec::new(),
        };

        let mut compiler = BfsStepCompiler::new()?;
        let step_fn = compiler.compile_with_actions(&action_only_spec, &action_fns, &[], None)?;

        Ok(Self {
            step_fn,
            fp_set: Arc::new(AtomicFpSet::new(shared_fp_set.capacity())),
            shared_fp_set: Some(shared_fp_set),
            invariant_fns: Arc::from(invariant_fns),
            state_len: spec.state_len,
            succ_capacity,
            _compiler: compiler,
        })
    }

    /// Execute one compiled BFS step and return the new successors.
    pub fn step(&self, state: &[i64]) -> Result<BfsStepOutput, BfsStepError> {
        if state.len() != self.state_len {
            return Err(BfsStepError::RuntimeError);
        }

        let (succ_buf, result) = self.execute_raw_step(state)?;
        if self.shared_fp_set.is_some() {
            self.build_output_with_shared_fp_set(succ_buf, result)
        } else {
            self.build_output(succ_buf, result)
        }
    }

    /// Execute one compiled BFS step and return successors as flat buffer slices.
    ///
    /// Unlike [`step`], this avoids allocating per-successor `Vec<i64>` by
    /// returning a `FlatBfsStepOutput` that borrows from the successor buffer.
    /// The caller iterates flat slices of `state_len` i64 values. This is the
    /// preferred path when the caller will process successors one at a time
    /// (e.g., fingerprint + dedup inline) rather than collecting them all.
    ///
    /// Part of #3988: Zero-copy compiled BFS step output.
    pub fn step_flat(&self, state: &[i64]) -> Result<FlatBfsStepOutput, BfsStepError> {
        if state.len() != self.state_len {
            return Err(BfsStepError::RuntimeError);
        }

        let (succ_buf, result) = self.execute_raw_step(state)?;

        let successor_count =
            usize::try_from(result.successors_new).map_err(|_| BfsStepError::RuntimeError)?;
        if successor_count > self.succ_capacity {
            return Err(BfsStepError::RuntimeError);
        }

        let expected_slots = successor_count
            .checked_mul(self.state_len)
            .ok_or(BfsStepError::RuntimeError)?;
        if expected_slots > succ_buf.len() {
            return Err(BfsStepError::RuntimeError);
        }

        // For the shared_fp_set path, we need to filter through the shared set.
        // Only return genuinely new successors.
        if let Some(ref shared) = self.shared_fp_set {
            let mut filtered_buf = Vec::with_capacity(expected_slots);
            let mut new_count = 0u32;
            let mut invariant_ok = true;
            let mut failed_invariant_idx = None;
            let mut failed_successor_idx = None;

            for chunk_idx in 0..successor_count {
                let start = chunk_idx * self.state_len;
                let end = start + self.state_len;
                let succ_slice = &succ_buf[start..end];
                let fingerprint = state_fingerprint(succ_slice);

                let is_new = match shared.insert_if_absent(fingerprint) {
                    InsertResult::Inserted => true,
                    InsertResult::AlreadyPresent => false,
                    InsertResult::TableFull => return Err(BfsStepError::RuntimeError),
                };

                // Mirror into local set regardless.
                match self.fp_set.insert_if_absent(fingerprint) {
                    InsertResult::Inserted
                    | InsertResult::AlreadyPresent
                    | InsertResult::TableFull => {}
                }

                if !is_new {
                    continue;
                }

                // Check invariants on the new successor.
                if let Some(inv_idx) = self.first_failed_invariant(succ_slice)? {
                    if invariant_ok {
                        invariant_ok = false;
                        failed_invariant_idx = Some(inv_idx);
                        failed_successor_idx = Some(new_count);
                    }
                }

                filtered_buf.extend_from_slice(succ_slice);
                new_count += 1;
            }

            return Ok(FlatBfsStepOutput::from_parts(
                filtered_buf,
                self.state_len,
                new_count as usize,
                result.successors_generated,
                invariant_ok,
                failed_invariant_idx,
                failed_successor_idx,
            ));
        }

        Ok(FlatBfsStepOutput::from_parts(
            succ_buf,
            self.state_len,
            successor_count,
            result.successors_generated,
            result.invariant_ok != 0,
            (result.invariant_ok == 0).then_some(result.failed_invariant_idx),
            (result.invariant_ok == 0).then_some(result.failed_successor_idx),
        ))
    }

    /// Execute a batch of parent states and collect every new successor.
    pub fn run_bfs_batch<S>(&self, parents: &[S]) -> Result<BfsBatchResult, BfsStepError>
    where
        S: AsRef<[i64]>,
    {
        let mut batch_result = BfsBatchResult {
            successors: Vec::new(),
            parents_processed: parents.len(),
            generated_count: 0,
            new_count: 0,
            invariant_ok: true,
            failed_parent_idx: None,
            failed_invariant_idx: None,
            failed_successor_idx: None,
            failed_successor: None,
        };

        for (parent_idx, parent) in parents.iter().enumerate() {
            let output = self.step(parent.as_ref())?;
            let BfsStepOutput {
                successors,
                generated_count,
                invariant_ok,
                failed_invariant_idx,
                failed_successor_idx,
                failed_successor,
            } = output;

            batch_result.generated_count = batch_result
                .generated_count
                .checked_add(u64::from(generated_count))
                .ok_or(BfsStepError::RuntimeError)?;
            batch_result.new_count = batch_result
                .new_count
                .checked_add(
                    u64::try_from(successors.len()).map_err(|_| BfsStepError::RuntimeError)?,
                )
                .ok_or(BfsStepError::RuntimeError)?;

            if batch_result.invariant_ok && !invariant_ok {
                batch_result.invariant_ok = false;
                batch_result.failed_parent_idx = Some(parent_idx);
                batch_result.failed_invariant_idx = failed_invariant_idx;
                batch_result.failed_successor_idx = failed_successor_idx;
                batch_result.failed_successor = failed_successor;
            }

            batch_result.successors.extend(successors);
        }

        Ok(batch_result)
    }

    /// Access the shared fingerprint set.
    ///
    /// For instances built with [`Self::build_with_shared_fp_set`], this returns
    /// the local compatibility mirror rather than the external shared set.
    #[must_use]
    pub fn fp_set(&self) -> &AtomicFpSet {
        self.fp_set.as_ref()
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
            Some(shared_fp_set) => shared_fp_set.len(),
            None => self.fp_set.len(),
        }
    }

    fn successor_capacity(spec: &BfsStepSpec) -> Result<usize, JitError> {
        let succ_capacity = spec.actions.len().saturating_mul(2).max(64);
        if succ_capacity > u32::MAX as usize {
            return Err(JitError::CompileError(
                "compiled BFS successor capacity exceeds u32::MAX".to_string(),
            ));
        }
        Ok(succ_capacity)
    }

    fn execute_raw_step(&self, state: &[i64]) -> Result<(Vec<i64>, BfsStepResult), BfsStepError> {
        let succ_buf_len = self
            .succ_capacity
            .checked_mul(self.state_len)
            .ok_or(BfsStepError::RuntimeError)?;
        let mut succ_buf = vec![0; succ_buf_len];
        let mut result = BfsStepResult::default();

        let written = unsafe {
            // SAFETY: `state` matches `state_len`; `succ_buf` has room for
            // `succ_capacity * state_len` i64 slots; `result` is a valid
            // out-parameter.
            (self.step_fn)(
                state.as_ptr(),
                succ_buf.as_mut_ptr(),
                self.succ_capacity as u32,
                &mut result,
            )
        };

        if written != result.successors_new {
            return Err(BfsStepError::RuntimeError);
        }

        match result.status {
            status::OK => Ok((succ_buf, result)),
            status::BUFFER_OVERFLOW => Err(BfsStepError::BufferOverflow {
                partial_count: result.successors_new,
            }),
            status::RUNTIME_ERROR => Err(BfsStepError::RuntimeError),
            _ => Err(BfsStepError::RuntimeError),
        }
    }

    fn build_output(
        &self,
        succ_buf: Vec<i64>,
        result: BfsStepResult,
    ) -> Result<BfsStepOutput, BfsStepError> {
        let successors = self.collect_successors_from_buf(&succ_buf, result.successors_new)?;

        let invariant_ok = result.invariant_ok != 0;
        let failed_invariant_idx = (!invariant_ok).then_some(result.failed_invariant_idx);
        let failed_successor_idx = (!invariant_ok).then_some(result.failed_successor_idx);
        let failed_successor = failed_successor_idx
            .and_then(|idx| usize::try_from(idx).ok())
            .and_then(|idx| successors.get(idx).cloned());

        Ok(BfsStepOutput {
            successors,
            generated_count: result.successors_generated,
            invariant_ok,
            failed_invariant_idx,
            failed_successor_idx,
            failed_successor,
        })
    }

    fn build_output_with_shared_fp_set(
        &self,
        succ_buf: Vec<i64>,
        result: BfsStepResult,
    ) -> Result<BfsStepOutput, BfsStepError> {
        let generated_successors =
            self.collect_successors_from_buf(&succ_buf, result.successors_new)?;

        let mut successors = Vec::with_capacity(generated_successors.len());
        let mut invariant_ok = true;
        let mut failed_invariant_idx = None;
        let mut failed_successor_idx = None;
        let mut failed_successor = None;

        for successor in generated_successors {
            if !self.insert_shared_fingerprint(state_fingerprint(&successor))? {
                continue;
            }

            let successor_idx =
                u32::try_from(successors.len()).map_err(|_| BfsStepError::RuntimeError)?;
            if let Some(invariant_idx) = self.first_failed_invariant(&successor)? {
                if invariant_ok {
                    invariant_ok = false;
                    failed_invariant_idx = Some(invariant_idx);
                    failed_successor_idx = Some(successor_idx);
                    failed_successor = Some(successor.clone());
                }
            }

            successors.push(successor);
        }

        Ok(BfsStepOutput {
            generated_count: result.successors_generated,
            successors,
            invariant_ok,
            failed_invariant_idx,
            failed_successor_idx,
            failed_successor,
        })
    }

    fn collect_successors_from_buf(
        &self,
        succ_buf: &[i64],
        successor_count: u32,
    ) -> Result<Vec<Vec<i64>>, BfsStepError> {
        let successor_count =
            usize::try_from(successor_count).map_err(|_| BfsStepError::RuntimeError)?;
        if successor_count > self.succ_capacity {
            return Err(BfsStepError::RuntimeError);
        }

        let expected_slots = successor_count
            .checked_mul(self.state_len)
            .ok_or(BfsStepError::RuntimeError)?;
        if expected_slots > succ_buf.len() {
            return Err(BfsStepError::RuntimeError);
        }

        if self.state_len == 0 {
            return Ok(vec![Vec::new(); successor_count]);
        }

        Ok(succ_buf[..expected_slots]
            .chunks_exact(self.state_len)
            .map(|succ| succ.to_vec())
            .collect())
    }

    fn insert_shared_fingerprint(&self, fingerprint: u64) -> Result<bool, BfsStepError> {
        let shared_fp_set = self
            .shared_fp_set
            .as_ref()
            .ok_or(BfsStepError::RuntimeError)?;

        let inserted = match shared_fp_set.insert_if_absent(fingerprint) {
            InsertResult::Inserted => true,
            InsertResult::AlreadyPresent => false,
            InsertResult::TableFull => return Err(BfsStepError::RuntimeError),
        };

        match self.fp_set.insert_if_absent(fingerprint) {
            InsertResult::Inserted | InsertResult::AlreadyPresent | InsertResult::TableFull => {}
        }

        Ok(inserted)
    }

    fn first_failed_invariant(&self, state: &[i64]) -> Result<Option<u32>, BfsStepError> {
        let state_len = u32::try_from(self.state_len).map_err(|_| BfsStepError::RuntimeError)?;

        for invariant in self.invariant_fns.iter() {
            let mut out = JitCallOut::default();
            unsafe {
                // SAFETY: `state` has exactly `state_len` slots and `out` is a
                // valid out-parameter for the compiled invariant ABI.
                (invariant.func)(&mut out, state.as_ptr(), state_len);
            }

            if out.status != JitStatus::Ok {
                return Err(BfsStepError::RuntimeError);
            }
            if out.value == 0 {
                return Ok(Some(invariant.descriptor.invariant_idx));
            }
        }

        Ok(None)
    }
}

/// Compute a 64-bit fingerprint of a flat i64 state buffer using xxh3.
///
/// Uses the same xxh3 algorithm as the JIT-compiled fingerprint path
/// ([`crate::bfs_step::jit_xxh3_fingerprint_64`]), ensuring that fingerprints
/// computed by JIT code and Rust code are identical for the same state.
///
/// Part of #3987: JIT V2 Phase 4 compiled fingerprinting.
pub(crate) fn state_fingerprint(state: &[i64]) -> u64 {
    crate::bfs_step::jit_xxh3_fingerprint_64(state.as_ptr(), state.len() as u32)
}

/// Reusable scratch buffers for zero-allocation BFS stepping.
///
/// Pre-allocates the successor output buffer once and reuses it across
/// multiple [`CompiledBfsStep::step_flat_into`] calls. For a BFS level with
/// many parents, this removes one successor-buffer allocation per parent.
///
/// Part of #3988: Phase 5 zero-alloc compiled BFS inner loop.
#[derive(Debug, Clone)]
pub struct BfsStepScratch {
    /// Pre-allocated successor output buffer.
    succ_buf: Vec<i64>,
    /// Capacity in number of successors (not slots).
    succ_capacity: usize,
    /// State length (i64 slots per state).
    state_len: usize,
}

impl BfsStepScratch {
    /// Allocate reusable scratch space for compiled BFS stepping.
    #[must_use]
    pub fn new(state_len: usize, succ_capacity: usize) -> Self {
        let succ_buf_len = match succ_capacity.checked_mul(state_len) {
            Some(len) => len,
            None => panic!(
                "BfsStepScratch buffer overflow for succ_capacity={succ_capacity}, state_len={state_len}"
            ),
        };

        Self {
            succ_buf: vec![0; succ_buf_len],
            succ_capacity,
            state_len,
        }
    }

    /// Return the raw successor buffer pointer for the JIT call.
    #[must_use]
    pub fn as_mut_ptr(&mut self) -> *mut i64 {
        self.succ_buf.as_mut_ptr()
    }

    /// Return the flat slice of written successor slots.
    #[must_use]
    pub fn successor_slice(&self, count: usize) -> &[i64] {
        assert!(
            count <= self.succ_capacity,
            "successor count {count} exceeds scratch capacity {}",
            self.succ_capacity
        );

        let slots = match count.checked_mul(self.state_len) {
            Some(slots) => slots,
            None => panic!(
                "BfsStepScratch slice overflow for count={count}, state_len={}",
                self.state_len
            ),
        };

        &self.succ_buf[..slots]
    }

    /// Iterate successors as `&[i64]` chunks of length `state_len`.
    #[must_use]
    pub fn iter_successors(&self, count: usize) -> impl Iterator<Item = &[i64]> + '_ {
        let succ_slice = self.successor_slice(count);
        if self.state_len == 0 {
            return ScratchSuccessorIter::Empty(count);
        }
        ScratchSuccessorIter::Chunked(succ_slice.chunks_exact(self.state_len))
    }

    /// Copy a range of the successor buffer to a different (non-overlapping) start.
    ///
    /// Used by `CompiledBfsLevel` to compact successors in place after shared-
    /// fingerprint-set filtering removes duplicates.
    ///
    /// Part of #3988: Phase 5 compiled BFS level loop.
    pub fn compact_in_place(&mut self, src_start: usize, src_end: usize, dst_start: usize) {
        self.succ_buf.copy_within(src_start..src_end, dst_start);
    }
}

/// Internal iterator for [`BfsStepScratch::iter_successors`].
///
/// Mirrors the iterator inside `tla_jit_runtime::bfs_output` but lives here
/// because `BfsStepScratch` borrows from a caller-provided buffer with a
/// different lifetime convention than [`FlatBfsStepOutput`] / [`FlatBfsStepOutputRef`].
enum ScratchSuccessorIter<'a> {
    Chunked(std::slice::ChunksExact<'a, i64>),
    Empty(usize),
}

impl<'a> Iterator for ScratchSuccessorIter<'a> {
    type Item = &'a [i64];

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            ScratchSuccessorIter::Chunked(chunks) => chunks.next(),
            ScratchSuccessorIter::Empty(remaining) => {
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
            ScratchSuccessorIter::Chunked(chunks) => chunks.size_hint(),
            ScratchSuccessorIter::Empty(remaining) => (*remaining, Some(*remaining)),
        }
    }
}

impl<'a> ExactSizeIterator for ScratchSuccessorIter<'a> {}

/// Result of a multi-level BFS exploration.
///
/// Aggregates statistics across all levels processed by
/// [`CompiledBfsStep::run_bfs_multi_level`].
///
/// Part of #3988: Phase 5 compiled BFS multi-level exploration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BfsMultiLevelResult {
    /// Number of BFS levels fully completed.
    pub depths_completed: usize,
    /// Total distinct states seen (including initial states).
    pub total_states_seen: u64,
    /// Total successors generated across all levels (before dedup).
    pub total_generated: u64,
    /// Whether all invariants passed across all levels.
    pub invariant_ok: bool,
    /// Index of the invariant that failed (if any).
    pub failed_invariant_idx: Option<u32>,
    /// BFS depth at which the invariant violation occurred (if any).
    pub failed_depth: Option<usize>,
    /// The failing successor state (if any).
    pub failed_successor: Option<Vec<i64>>,
}

/// Result of processing one BFS frontier level.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BfsLevelResult {
    /// New successor states discovered in this level (flat i64 slices).
    pub new_successors: Vec<Vec<i64>>,
    /// Total number of parent states processed.
    pub parents_processed: usize,
    /// Total successors generated (before dedup).
    pub total_generated: u64,
    /// Total new successors (after dedup).
    pub total_new: u64,
    /// Whether all invariants passed.
    pub invariant_ok: bool,
    /// Index of parent that produced the first invariant violation.
    pub failed_parent_idx: Option<usize>,
    /// Index of the invariant that failed.
    pub failed_invariant_idx: Option<u32>,
    /// The failing successor state.
    pub failed_successor: Option<Vec<i64>>,
}

impl CompiledBfsStep {
    /// Execute one compiled BFS step using a caller-provided scratch buffer.
    ///
    /// Unlike [`Self::step_flat`], this does not allocate a new `Vec` per call.
    /// The successors are written into `scratch.succ_buf` and the returned
    /// [`FlatBfsStepOutputRef`] borrows from it.
    ///
    /// For the shared fingerprint-set path, filtering still happens but results
    /// are compacted back into the same scratch buffer in place.
    pub fn step_flat_into<'a>(
        &self,
        state: &[i64],
        scratch: &'a mut BfsStepScratch,
    ) -> Result<FlatBfsStepOutputRef<'a>, BfsStepError> {
        if state.len() != self.state_len {
            return Err(BfsStepError::RuntimeError);
        }

        let result = self.execute_raw_step_into_scratch(state, scratch)?;
        let successor_count =
            usize::try_from(result.successors_new).map_err(|_| BfsStepError::RuntimeError)?;
        if successor_count > self.succ_capacity || successor_count > scratch.succ_capacity {
            return Err(BfsStepError::RuntimeError);
        }

        let expected_slots = successor_count
            .checked_mul(self.state_len)
            .ok_or(BfsStepError::RuntimeError)?;
        if expected_slots > scratch.succ_buf.len() {
            return Err(BfsStepError::RuntimeError);
        }

        if self.shared_fp_set.is_some() {
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
                    let succ_slice = &scratch.succ_buf[start..end];
                    state_fingerprint(succ_slice)
                };
                if !self.insert_shared_fingerprint(fingerprint)? {
                    continue;
                }

                if let Some(inv_idx) = {
                    let succ_slice = &scratch.succ_buf[start..end];
                    self.first_failed_invariant(succ_slice)?
                } {
                    if invariant_ok {
                        invariant_ok = false;
                        failed_invariant_idx = Some(inv_idx);
                        failed_successor_idx =
                            Some(u32::try_from(new_count).map_err(|_| BfsStepError::RuntimeError)?);
                    }
                }

                if self.state_len != 0 && new_count != chunk_idx {
                    let dst_start = new_count
                        .checked_mul(self.state_len)
                        .ok_or(BfsStepError::RuntimeError)?;
                    scratch.succ_buf.copy_within(start..end, dst_start);
                }

                new_count += 1;
            }

            return Ok(FlatBfsStepOutputRef::from_parts(
                scratch.successor_slice(new_count),
                self.state_len,
                new_count,
                result.successors_generated,
                invariant_ok,
                failed_invariant_idx,
                failed_successor_idx,
            ));
        }

        Ok(FlatBfsStepOutputRef::from_parts(
            scratch.successor_slice(successor_count),
            self.state_len,
            successor_count,
            result.successors_generated,
            result.invariant_ok != 0,
            (result.invariant_ok == 0).then_some(result.failed_invariant_idx),
            (result.invariant_ok == 0).then_some(result.failed_successor_idx),
        ))
    }

    /// Process an entire BFS frontier level with zero per-parent allocation.
    ///
    /// Takes a slice of parent states and processes each through the compiled
    /// step function using a single pre-allocated scratch buffer. New
    /// successors are collected and returned as owned states.
    ///
    /// This is the Phase 5 compiled BFS inner loop: the entire sequence of
    /// parent dequeue, action dispatch, fingerprinting, deduplication,
    /// invariant checking, and enqueue preparation runs with minimal
    /// allocation overhead.
    ///
    /// Part of #3988: Phase 5 compiled BFS level processing.
    pub fn run_bfs_level<S>(&self, parents: &[S]) -> Result<BfsLevelResult, BfsStepError>
    where
        S: AsRef<[i64]>,
    {
        let mut scratch = BfsStepScratch::new(self.state_len, self.succ_capacity);
        let mut result = BfsLevelResult {
            new_successors: Vec::new(),
            parents_processed: 0,
            total_generated: 0,
            total_new: 0,
            invariant_ok: true,
            failed_parent_idx: None,
            failed_invariant_idx: None,
            failed_successor: None,
        };

        for (parent_idx, parent) in parents.iter().enumerate() {
            let output = self.step_flat_into(parent.as_ref(), &mut scratch)?;
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
                .and_then(|idx| output.iter_successors().nth(idx).map(|succ| succ.to_vec()));

            result
                .new_successors
                .extend(output.iter_successors().map(|succ| succ.to_vec()));

            if result.invariant_ok && !output.invariant_ok {
                result.invariant_ok = false;
                result.failed_parent_idx = Some(parent_idx);
                result.failed_invariant_idx = output.failed_invariant_idx;
                result.failed_successor = failed_successor;
                break;
            }
        }

        Ok(result)
    }

    /// Run a multi-level BFS exploration from initial states.
    ///
    /// Starting from `init_states`, executes BFS level-by-level using the
    /// compiled step function until either:
    /// - `max_depth` levels have been processed,
    /// - the frontier is empty (all states explored), or
    /// - an invariant violation is found.
    ///
    /// Each level's new successors become the next level's parents. The
    /// fingerprint set is shared across all levels, so cross-level dedup
    /// is automatic. Uses a single pre-allocated scratch buffer for all
    /// parents in all levels, eliminating per-parent allocation.
    ///
    /// This is the Phase 5 compiled BFS inner loop: the full BFS algorithm
    /// runs in native code for action dispatch + fingerprinting + dedup,
    /// with only the level boundary logic in Rust.
    ///
    /// Part of #3988: Phase 5 compiled BFS multi-level exploration.
    pub fn run_bfs_multi_level(
        &self,
        init_states: &[Vec<i64>],
        max_depth: usize,
    ) -> Result<BfsMultiLevelResult, BfsStepError> {
        let mut scratch = BfsStepScratch::new(self.state_len, self.succ_capacity);
        let mut result = BfsMultiLevelResult {
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

        let mut frontier: Vec<Vec<i64>> = init_states.to_vec();

        for depth in 0..max_depth {
            if frontier.is_empty() {
                break;
            }

            let mut next_frontier = Vec::new();
            let mut level_generated = 0u64;

            for parent in &frontier {
                let output = self.step_flat_into(parent, &mut scratch)?;
                level_generated = level_generated
                    .checked_add(u64::from(output.generated_count))
                    .ok_or(BfsStepError::RuntimeError)?;

                for succ in output.iter_successors() {
                    next_frontier.push(succ.to_vec());
                }

                if !output.invariant_ok {
                    result.invariant_ok = false;
                    result.failed_invariant_idx = output.failed_invariant_idx;
                    result.failed_depth = Some(depth);
                    result.failed_successor = output
                        .failed_successor_idx
                        .and_then(|idx| usize::try_from(idx).ok())
                        .and_then(|idx| output.iter_successors().nth(idx).map(|s| s.to_vec()));
                    result.total_generated = result
                        .total_generated
                        .checked_add(level_generated)
                        .ok_or(BfsStepError::RuntimeError)?;
                    result.total_states_seen = result
                        .total_states_seen
                        .checked_add(next_frontier.len() as u64)
                        .ok_or(BfsStepError::RuntimeError)?;
                    result.depths_completed = depth;
                    return Ok(result);
                }
            }

            result.total_generated = result
                .total_generated
                .checked_add(level_generated)
                .ok_or(BfsStepError::RuntimeError)?;
            result.total_states_seen = result
                .total_states_seen
                .checked_add(next_frontier.len() as u64)
                .ok_or(BfsStepError::RuntimeError)?;
            result.depths_completed = depth + 1;
            frontier = next_frontier;
        }

        Ok(result)
    }

    fn execute_raw_step_into_scratch(
        &self,
        state: &[i64],
        scratch: &mut BfsStepScratch,
    ) -> Result<BfsStepResult, BfsStepError> {
        if scratch.state_len != self.state_len || scratch.succ_capacity < self.succ_capacity {
            return Err(BfsStepError::RuntimeError);
        }

        let required_slots = self
            .succ_capacity
            .checked_mul(self.state_len)
            .ok_or(BfsStepError::RuntimeError)?;
        if scratch.succ_buf.len() < required_slots {
            return Err(BfsStepError::RuntimeError);
        }

        let mut result = BfsStepResult::default();
        let written = unsafe {
            // SAFETY: `state` matches `state_len`; `scratch` provides room for
            // at least `self.succ_capacity * state_len` i64 slots; `result` is
            // a valid out-parameter.
            (self.step_fn)(
                state.as_ptr(),
                scratch.as_mut_ptr(),
                self.succ_capacity as u32,
                &mut result,
            )
        };

        if written != result.successors_new {
            return Err(BfsStepError::RuntimeError);
        }

        match result.status {
            status::OK => Ok(result),
            status::BUFFER_OVERFLOW => Err(BfsStepError::BufferOverflow {
                partial_count: result.successors_new,
            }),
            status::RUNTIME_ERROR => Err(BfsStepError::RuntimeError),
            _ => Err(BfsStepError::RuntimeError),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::abi::JitCallOut;
    use crate::compound_layout::{StateLayout, VarLayout};

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
        unsafe {
            *out = JitCallOut::ok(1);
        }
    }

    unsafe extern "C" fn increment_slot0_by_2(
        out: *mut JitCallOut,
        state_in: *const i64,
        state_out: *mut i64,
        state_len: u32,
    ) {
        unsafe {
            increment_slot0(out, state_in, state_out, state_len);
        }

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
        unsafe {
            *out = JitCallOut::ok(1);
        }
    }

    unsafe extern "C" fn slot0_lt_100(out: *mut JitCallOut, state: *const i64, state_len: u32) {
        let state = unsafe { std::slice::from_raw_parts(state, state_len as usize) };
        let passed = state.first().copied().unwrap_or(0) < 100;
        unsafe {
            *out = JitCallOut::ok(passed as i64);
        }
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

    fn increment_action_descriptor() -> ActionDescriptor {
        ActionDescriptor {
            name: "IncSlot0".to_string(),
            action_idx: 0,
            binding_values: vec![],
            formal_values: vec![],
            read_vars: vec![0],
            write_vars: vec![0],
        }
    }

    fn set_42_action_descriptor() -> ActionDescriptor {
        ActionDescriptor {
            name: "SetSlot0To42".to_string(),
            action_idx: 0,
            binding_values: vec![],
            formal_values: vec![],
            read_vars: vec![],
            write_vars: vec![0],
        }
    }

    fn slot0_lt_100_invariant_descriptor() -> InvariantDescriptor {
        InvariantDescriptor {
            name: "Slot0Lt100".to_string(),
            invariant_idx: 0,
        }
    }

    fn aggregate_loop_outputs(step: &CompiledBfsStep, parents: &[Vec<i64>]) -> BfsBatchResult {
        let mut aggregated = BfsBatchResult {
            successors: Vec::new(),
            parents_processed: parents.len(),
            generated_count: 0,
            new_count: 0,
            invariant_ok: true,
            failed_parent_idx: None,
            failed_invariant_idx: None,
            failed_successor_idx: None,
            failed_successor: None,
        };

        for (parent_idx, parent) in parents.iter().enumerate() {
            let output = step.step(parent).expect("step");
            aggregated.generated_count += u64::from(output.generated_count);
            aggregated.new_count += output.successors.len() as u64;
            if aggregated.invariant_ok && !output.invariant_ok {
                aggregated.invariant_ok = false;
                aggregated.failed_parent_idx = Some(parent_idx);
                aggregated.failed_invariant_idx = output.failed_invariant_idx;
                aggregated.failed_successor_idx = output.failed_successor_idx;
                aggregated.failed_successor = output.failed_successor.clone();
            }
            aggregated.successors.extend(output.successors);
        }

        aggregated
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_compiled_bfs_step_build_and_run() {
        let actions = vec![increment_action_descriptor()];
        let spec = make_spec(2, actions.clone(), vec![]);
        let compiled_actions = vec![CompiledActionFn::new(actions[0].clone(), increment_slot0)];

        let step = CompiledBfsStep::build(&spec, compiled_actions, vec![], 32).expect("build");

        let output = step.step(&[7, 11]).expect("step");
        assert_eq!(output.successors, vec![vec![8, 11]]);
        assert_eq!(output.generated_count, 1);
        assert!(output.invariant_ok);
        assert_eq!(output.failed_invariant_idx, None);
        assert_eq!(output.failed_successor_idx, None);
        assert_eq!(output.failed_successor, None);
        assert_eq!(step.state_len(), 2);
        assert_eq!(step.states_seen(), 1);

        let duplicate = step.step(&[7, 11]).expect("duplicate step");
        assert_eq!(duplicate.generated_count, 1);
        assert!(duplicate.successors.is_empty());
        assert!(duplicate.invariant_ok);
        assert_eq!(step.states_seen(), 1);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_compiled_bfs_step_invariant_failure() {
        let actions = vec![increment_action_descriptor()];
        let invariants = vec![slot0_lt_100_invariant_descriptor()];
        let spec = make_spec(2, actions.clone(), invariants.clone());
        let compiled_actions = vec![CompiledActionFn::new(actions[0].clone(), increment_slot0)];
        let compiled_invariants = vec![CompiledInvariantFn::new(
            invariants[0].clone(),
            slot0_lt_100,
        )];

        let step = CompiledBfsStep::build(&spec, compiled_actions, compiled_invariants, 1000)
            .expect("build");

        let output = step.step(&[99, 0]).expect("step");
        assert!(!output.invariant_ok);
        assert_eq!(output.failed_invariant_idx, Some(0));
        assert_eq!(output.failed_successor_idx, Some(0));
        assert_eq!(output.successors.len(), 1);
        assert_eq!(output.failed_successor, Some(vec![100, 0]));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_run_bfs_batch_matches_step_loop() {
        let actions = vec![increment_action_descriptor()];
        let spec = make_spec(2, actions.clone(), vec![]);
        let parents = vec![vec![7, 11], vec![7, 11], vec![8, 11]];

        let compiled_actions_for_loop =
            vec![CompiledActionFn::new(actions[0].clone(), increment_slot0)];
        let loop_step =
            CompiledBfsStep::build(&spec, compiled_actions_for_loop, vec![], 64).expect("build");
        let expected = aggregate_loop_outputs(&loop_step, &parents);

        let compiled_actions_for_batch =
            vec![CompiledActionFn::new(actions[0].clone(), increment_slot0)];
        let batch_step =
            CompiledBfsStep::build(&spec, compiled_actions_for_batch, vec![], 64).expect("build");
        let batch = batch_step.run_bfs_batch(&parents).expect("run_bfs_batch");

        assert_eq!(batch, expected);
        assert_eq!(batch.successors, vec![vec![8, 11], vec![9, 11]]);
        assert_eq!(batch.generated_count, 3);
        assert_eq!(batch.new_count, 2);
        assert!(batch.invariant_ok);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_build_with_shared_fp_set_deduplicates_across_multiple_parents() {
        let actions = vec![set_42_action_descriptor()];
        let spec = make_spec(1, actions.clone(), vec![]);
        let shared_fp_set = Arc::new(ResizableAtomicFpSet::new(32));

        let compiled_actions = vec![CompiledActionFn::new(actions[0].clone(), set_slot0_to_42)];
        let step = CompiledBfsStep::build_with_shared_fp_set(
            &spec,
            compiled_actions,
            vec![],
            Arc::clone(&shared_fp_set),
        )
        .expect("build_with_shared_fp_set");

        let parents = vec![vec![1], vec![2], vec![3]];
        let batch = step.run_bfs_batch(&parents).expect("run_bfs_batch");

        assert_eq!(batch.successors, vec![vec![42]]);
        assert_eq!(batch.generated_count, 3);
        assert_eq!(batch.new_count, 1);
        assert!(batch.invariant_ok);
        assert_eq!(step.states_seen(), 1);
        assert_eq!(shared_fp_set.len(), 1);
        assert!(shared_fp_set.contains(state_fingerprint(&[42])));

        let later = step.run_bfs_batch(&[vec![99]]).expect("second batch");
        assert!(later.successors.is_empty());
        assert_eq!(later.generated_count, 1);
        assert_eq!(later.new_count, 0);
        assert_eq!(shared_fp_set.len(), 1);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_run_bfs_batch_tracks_invariant_failures() {
        let actions = vec![increment_action_descriptor()];
        let invariants = vec![slot0_lt_100_invariant_descriptor()];
        let spec = make_spec(1, actions.clone(), invariants.clone());
        let shared_fp_set = Arc::new(ResizableAtomicFpSet::new(32));

        let compiled_actions = vec![CompiledActionFn::new(actions[0].clone(), increment_slot0)];
        let compiled_invariants = vec![CompiledInvariantFn::new(
            invariants[0].clone(),
            slot0_lt_100,
        )];
        let step = CompiledBfsStep::build_with_shared_fp_set(
            &spec,
            compiled_actions,
            compiled_invariants,
            shared_fp_set,
        )
        .expect("build_with_shared_fp_set");

        let parents = vec![vec![0], vec![99]];
        let batch = step.run_bfs_batch(&parents).expect("run_bfs_batch");

        assert_eq!(batch.successors, vec![vec![1], vec![100]]);
        assert_eq!(batch.generated_count, 2);
        assert_eq!(batch.new_count, 2);
        assert!(!batch.invariant_ok);
        assert_eq!(batch.failed_parent_idx, Some(1));
        assert_eq!(batch.failed_invariant_idx, Some(0));
        assert_eq!(batch.failed_successor_idx, Some(0));
        assert_eq!(batch.failed_successor, Some(vec![100]));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_step_flat_basic_successor_iteration() {
        let actions = vec![increment_action_descriptor()];
        let spec = make_spec(2, actions.clone(), vec![]);
        let compiled_actions = vec![CompiledActionFn::new(actions[0].clone(), increment_slot0)];

        let step = CompiledBfsStep::build(&spec, compiled_actions, vec![], 32).expect("build");

        let flat_output = step.step_flat(&[7, 11]).expect("step_flat");
        assert_eq!(flat_output.successor_count(), 1);
        assert_eq!(flat_output.generated_count, 1);
        assert!(flat_output.invariant_ok);

        let successors: Vec<&[i64]> = flat_output.iter_successors().collect();
        assert_eq!(successors.len(), 1);
        assert_eq!(successors[0], &[8, 11]);

        // Duplicate step: same parent should produce zero new successors.
        let dup_output = step.step_flat(&[7, 11]).expect("step_flat dup");
        assert_eq!(dup_output.successor_count(), 0);
        assert_eq!(dup_output.generated_count, 1);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_step_flat_matches_step_output() {
        let actions = vec![increment_action_descriptor()];
        let spec = make_spec(2, actions.clone(), vec![]);

        // Build two identical steps with independent fp sets.
        let step_vec = CompiledBfsStep::build(
            &spec,
            vec![CompiledActionFn::new(actions[0].clone(), increment_slot0)],
            vec![],
            32,
        )
        .expect("build vec");

        let step_flat = CompiledBfsStep::build(
            &spec,
            vec![CompiledActionFn::new(actions[0].clone(), increment_slot0)],
            vec![],
            32,
        )
        .expect("build flat");

        let state = [5i64, 10];

        let vec_output = step_vec.step(&state).expect("step");
        let flat_output = step_flat.step_flat(&state).expect("step_flat");

        assert_eq!(vec_output.generated_count, flat_output.generated_count);
        assert_eq!(vec_output.invariant_ok, flat_output.invariant_ok);
        assert_eq!(vec_output.successors.len(), flat_output.successor_count());

        let flat_succs: Vec<Vec<i64>> = flat_output.iter_successors().map(|s| s.to_vec()).collect();
        assert_eq!(vec_output.successors, flat_succs);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_step_flat_with_shared_fp_set_filters_duplicates() {
        let actions = vec![set_42_action_descriptor()];
        let spec = make_spec(1, actions.clone(), vec![]);
        let shared_fp_set = Arc::new(ResizableAtomicFpSet::new(32));

        let step = CompiledBfsStep::build_with_shared_fp_set(
            &spec,
            vec![CompiledActionFn::new(actions[0].clone(), set_slot0_to_42)],
            vec![],
            Arc::clone(&shared_fp_set),
        )
        .expect("build");

        // First call: state [1] -> successor [42], new.
        let out1 = step.step_flat(&[1]).expect("step_flat 1");
        assert_eq!(out1.successor_count(), 1);
        let succs1: Vec<&[i64]> = out1.iter_successors().collect();
        assert_eq!(succs1[0], &[42]);

        // Second call: state [2] -> successor [42], already in shared set.
        let out2 = step.step_flat(&[2]).expect("step_flat 2");
        assert_eq!(out2.successor_count(), 0);
        assert_eq!(out2.generated_count, 1);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_bfs_step_scratch_reuse() {
        let actions = vec![increment_action_descriptor()];
        let spec = make_spec(2, actions.clone(), vec![]);
        let compiled_actions = vec![CompiledActionFn::new(actions[0].clone(), increment_slot0)];

        let step = CompiledBfsStep::build(&spec, compiled_actions, vec![], 32).expect("build");
        let mut scratch = BfsStepScratch::new(step.state_len, step.succ_capacity);
        let scratch_ptr = scratch.succ_buf.as_ptr();
        let scratch_capacity = scratch.succ_buf.capacity();

        {
            let output = step.step_flat_into(&[0, 10], &mut scratch).expect("step 1");
            assert_eq!(output.successor_count(), 1);
            assert_eq!(output.succ_buf_as_ptr(), scratch_ptr);
            let succs: Vec<&[i64]> = output.iter_successors().collect();
            assert_eq!(succs, vec![&[1, 10][..]]);
        }
        assert_eq!(scratch.succ_buf.as_ptr(), scratch_ptr);
        assert_eq!(scratch.succ_buf.capacity(), scratch_capacity);

        {
            let output = step.step_flat_into(&[1, 10], &mut scratch).expect("step 2");
            assert_eq!(output.successor_count(), 1);
            assert_eq!(output.succ_buf_as_ptr(), scratch_ptr);
            let succs: Vec<&[i64]> = output.iter_successors().collect();
            assert_eq!(succs, vec![&[2, 10][..]]);
        }
        assert_eq!(scratch.succ_buf.as_ptr(), scratch_ptr);
        assert_eq!(scratch.succ_buf.capacity(), scratch_capacity);

        {
            let output = step.step_flat_into(&[2, 10], &mut scratch).expect("step 3");
            assert_eq!(output.successor_count(), 1);
            assert_eq!(output.succ_buf_as_ptr(), scratch_ptr);
            let succs: Vec<&[i64]> = output.iter_successors().collect();
            assert_eq!(succs, vec![&[3, 10][..]]);
        }
        assert_eq!(scratch.succ_buf.as_ptr(), scratch_ptr);
        assert_eq!(scratch.succ_buf.capacity(), scratch_capacity);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_step_flat_into_matches_step_flat() {
        let actions = vec![increment_action_descriptor()];
        let spec = make_spec(2, actions.clone(), vec![]);

        let step_flat = CompiledBfsStep::build(
            &spec,
            vec![CompiledActionFn::new(actions[0].clone(), increment_slot0)],
            vec![],
            32,
        )
        .expect("build flat");

        let step_into = CompiledBfsStep::build(
            &spec,
            vec![CompiledActionFn::new(actions[0].clone(), increment_slot0)],
            vec![],
            32,
        )
        .expect("build into");

        let state = [5i64, 10];
        let flat_output = step_flat.step_flat(&state).expect("step_flat");
        let mut scratch = BfsStepScratch::new(step_into.state_len, step_into.succ_capacity);
        let into_output = step_into
            .step_flat_into(&state, &mut scratch)
            .expect("step_flat_into");

        assert_eq!(flat_output.generated_count, into_output.generated_count);
        assert_eq!(flat_output.invariant_ok, into_output.invariant_ok);
        assert_eq!(
            flat_output.failed_invariant_idx,
            into_output.failed_invariant_idx
        );
        assert_eq!(
            flat_output.failed_successor_idx,
            into_output.failed_successor_idx
        );
        assert_eq!(flat_output.successor_count(), into_output.successor_count());

        let flat_succs: Vec<Vec<i64>> = flat_output
            .iter_successors()
            .map(|succ| succ.to_vec())
            .collect();
        let into_succs: Vec<Vec<i64>> = into_output
            .iter_successors()
            .map(|succ| succ.to_vec())
            .collect();
        assert_eq!(flat_succs, into_succs);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_step_flat_into_dedup_with_shared_fp_set() {
        let actions = vec![set_42_action_descriptor()];
        let spec = make_spec(1, actions.clone(), vec![]);
        let shared_fp_set = Arc::new(ResizableAtomicFpSet::new(32));

        let step = CompiledBfsStep::build_with_shared_fp_set(
            &spec,
            vec![CompiledActionFn::new(actions[0].clone(), set_slot0_to_42)],
            vec![],
            Arc::clone(&shared_fp_set),
        )
        .expect("build_with_shared_fp_set");

        let mut scratch = BfsStepScratch::new(step.state_len, step.succ_capacity);

        let out1 = step.step_flat_into(&[1], &mut scratch).expect("step 1");
        assert_eq!(out1.successor_count(), 1);
        let succs1: Vec<&[i64]> = out1.iter_successors().collect();
        assert_eq!(succs1, vec![&[42][..]]);

        let out2 = step.step_flat_into(&[2], &mut scratch).expect("step 2");
        assert_eq!(out2.successor_count(), 0);
        assert_eq!(out2.generated_count, 1);
        assert_eq!(shared_fp_set.len(), 1);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_run_bfs_level_basic() {
        let actions = vec![increment_action_descriptor()];
        let spec = make_spec(2, actions.clone(), vec![]);
        let compiled_actions = vec![CompiledActionFn::new(actions[0].clone(), increment_slot0)];

        let step = CompiledBfsStep::build(&spec, compiled_actions, vec![], 32).expect("build");
        let parents = vec![vec![0, 10], vec![1, 10], vec![2, 10]];

        let level = step.run_bfs_level(&parents).expect("run_bfs_level");
        assert_eq!(
            level.new_successors,
            vec![vec![1, 10], vec![2, 10], vec![3, 10]]
        );
        assert_eq!(level.parents_processed, 3);
        assert_eq!(level.total_generated, 3);
        assert_eq!(level.total_new, 3);
        assert!(level.invariant_ok);
        assert_eq!(level.failed_parent_idx, None);
        assert_eq!(level.failed_invariant_idx, None);
        assert_eq!(level.failed_successor, None);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_run_bfs_level_invariant_failure() {
        let actions = vec![increment_action_descriptor()];
        let invariants = vec![slot0_lt_100_invariant_descriptor()];
        let spec = make_spec(1, actions.clone(), invariants.clone());
        let compiled_actions = vec![CompiledActionFn::new(actions[0].clone(), increment_slot0)];
        let compiled_invariants = vec![CompiledInvariantFn::new(
            invariants[0].clone(),
            slot0_lt_100,
        )];

        let step = CompiledBfsStep::build(&spec, compiled_actions, compiled_invariants, 1000)
            .expect("build");
        let parents = vec![vec![0], vec![99], vec![1]];

        let level = step.run_bfs_level(&parents).expect("run_bfs_level");
        assert_eq!(level.new_successors, vec![vec![1], vec![100]]);
        assert_eq!(level.parents_processed, 2);
        assert_eq!(level.total_generated, 2);
        assert_eq!(level.total_new, 2);
        assert!(!level.invariant_ok);
        assert_eq!(level.failed_parent_idx, Some(1));
        assert_eq!(level.failed_invariant_idx, Some(0));
        assert_eq!(level.failed_successor, Some(vec![100]));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_run_bfs_level_dedup_across_parents() {
        let actions = vec![set_42_action_descriptor()];
        let spec = make_spec(1, actions.clone(), vec![]);
        let shared_fp_set = Arc::new(ResizableAtomicFpSet::new(32));

        let step = CompiledBfsStep::build_with_shared_fp_set(
            &spec,
            vec![CompiledActionFn::new(actions[0].clone(), set_slot0_to_42)],
            vec![],
            Arc::clone(&shared_fp_set),
        )
        .expect("build_with_shared_fp_set");

        let parents = vec![vec![1], vec![2], vec![3]];
        let level = step.run_bfs_level(&parents).expect("run_bfs_level");

        assert_eq!(level.new_successors, vec![vec![42]]);
        assert_eq!(level.parents_processed, 3);
        assert_eq!(level.total_generated, 3);
        assert_eq!(level.total_new, 1);
        assert!(level.invariant_ok);
        assert_eq!(level.failed_parent_idx, None);
        assert_eq!(level.failed_invariant_idx, None);
        assert_eq!(level.failed_successor, None);
        assert_eq!(shared_fp_set.len(), 1);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_run_bfs_level_matches_run_bfs_batch() {
        let actions = vec![increment_action_descriptor()];
        let spec = make_spec(2, actions.clone(), vec![]);
        let parents = vec![vec![7, 11], vec![7, 11], vec![8, 11]];

        let batch_step = CompiledBfsStep::build(
            &spec,
            vec![CompiledActionFn::new(actions[0].clone(), increment_slot0)],
            vec![],
            64,
        )
        .expect("build batch");
        let level_step = CompiledBfsStep::build(
            &spec,
            vec![CompiledActionFn::new(actions[0].clone(), increment_slot0)],
            vec![],
            64,
        )
        .expect("build level");

        let batch = batch_step.run_bfs_batch(&parents).expect("run_bfs_batch");
        let level = level_step.run_bfs_level(&parents).expect("run_bfs_level");

        assert_eq!(level.new_successors, batch.successors);
        assert_eq!(level.parents_processed, batch.parents_processed);
        assert_eq!(level.total_generated, batch.generated_count);
        assert_eq!(level.total_new, batch.new_count);
        assert_eq!(level.invariant_ok, batch.invariant_ok);
        assert_eq!(level.failed_parent_idx, batch.failed_parent_idx);
        assert_eq!(level.failed_invariant_idx, batch.failed_invariant_idx);
        assert_eq!(level.failed_successor, batch.failed_successor);
    }

    /// Functional throughput check for the Phase 5 compiled BFS level path.
    ///
    /// This is not a criterion benchmark. It exercises `run_bfs_level` over
    /// progressively larger frontiers, prints wall-clock throughput, and
    /// asserts that cross-parent dedup keeps only the unique successors.
    #[cfg_attr(test, ntest::timeout(30000))]
    #[test]
    fn test_run_bfs_level_throughput_over_frontier_sizes() {
        use std::time::Instant;

        let mut second_action = increment_action_descriptor();
        second_action.name = "IncSlot0By2".to_string();
        second_action.action_idx = 1;

        let actions = vec![increment_action_descriptor(), second_action];
        let spec = make_spec(4, actions.clone(), vec![]);

        for frontier_size in [100usize, 1_000, 10_000] {
            let parents: Vec<Vec<i64>> = (0..frontier_size)
                .map(|i| vec![i as i64, 10, 20, 30])
                .collect();
            let expected_successors: Vec<Vec<i64>> = (1..=frontier_size + 1)
                .map(|i| vec![i as i64, 10, 20, 30])
                .collect();

            let step = CompiledBfsStep::build(
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
            let level = step.run_bfs_level(&parents).expect("run_bfs_level");
            let elapsed = start.elapsed();
            let elapsed_secs = elapsed.as_secs_f64().max(f64::EPSILON);

            assert_eq!(level.parents_processed, frontier_size);
            assert_eq!(level.total_generated, (frontier_size as u64) * 2);
            assert_eq!(level.total_new, (frontier_size as u64) + 1);
            assert!(level.invariant_ok);
            assert_eq!(level.new_successors, expected_successors);
            assert_eq!(step.states_seen(), frontier_size + 1);

            let mut collected = step.fp_set().collect_all();
            collected.sort_unstable();
            let mut expected_fingerprints: Vec<u64> = expected_successors
                .iter()
                .map(|state| state_fingerprint(state))
                .collect();
            expected_fingerprints.sort_unstable();
            assert_eq!(collected, expected_fingerprints);

            let states_per_sec = frontier_size as f64 / elapsed_secs;
            let generated_per_sec = level.total_generated as f64 / elapsed_secs;
            let new_per_sec = level.total_new as f64 / elapsed_secs;
            eprintln!(
                "CompiledBfsStep throughput: frontier={frontier_size}, elapsed={:.3}ms, states/sec={:.0}, generated/sec={:.0}, new/sec={:.0}",
                elapsed_secs * 1000.0,
                states_per_sec,
                generated_per_sec,
                new_per_sec,
            );
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_step_flat_invariant_failure() {
        let actions = vec![increment_action_descriptor()];
        let invariants = vec![slot0_lt_100_invariant_descriptor()];
        let spec = make_spec(2, actions.clone(), invariants.clone());
        let compiled_actions = vec![CompiledActionFn::new(actions[0].clone(), increment_slot0)];
        let compiled_invariants = vec![CompiledInvariantFn::new(
            invariants[0].clone(),
            slot0_lt_100,
        )];

        let step = CompiledBfsStep::build(&spec, compiled_actions, compiled_invariants, 1000)
            .expect("build");

        let output = step.step_flat(&[99, 0]).expect("step_flat");
        assert!(!output.invariant_ok);
        assert_eq!(output.failed_invariant_idx, Some(0));
        assert_eq!(output.failed_successor_idx, Some(0));
        assert_eq!(output.successor_count(), 1);

        // The failing successor should be [100, 0].
        let succs: Vec<&[i64]> = output.iter_successors().collect();
        assert_eq!(succs[0], &[100, 0]);
    }

    // ---- Multi-level BFS tests ----

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_run_bfs_multi_level_basic() {
        // Linear chain: state=[n,0] -> [n+1,0] for 5 depths.
        let actions = vec![increment_action_descriptor()];
        let spec = make_spec(2, actions.clone(), vec![]);
        let shared_fp = Arc::new(ResizableAtomicFpSet::new(64));

        let step = CompiledBfsStep::build_with_shared_fp_set(
            &spec,
            vec![CompiledActionFn::new(actions[0].clone(), increment_slot0)],
            vec![],
            Arc::clone(&shared_fp),
        )
        .expect("build");

        let result = step
            .run_bfs_multi_level(&[vec![0, 0]], 5)
            .expect("multi-level");

        assert_eq!(result.depths_completed, 5);
        assert!(result.invariant_ok);
        assert_eq!(result.failed_invariant_idx, None);
        assert_eq!(result.failed_depth, None);
        // Init + 5 new states = 6 total seen.
        assert_eq!(result.total_states_seen, 6);
        // 1 successor generated per depth.
        assert_eq!(result.total_generated, 5);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_run_bfs_multi_level_empty_frontier_terminates() {
        // set_slot0_to_42 always produces the same successor [42].
        // After depth 0 -> [42] is new, depth 1 -> [42] is dup -> empty frontier.
        let actions = vec![set_42_action_descriptor()];
        let spec = make_spec(1, actions.clone(), vec![]);
        let shared_fp = Arc::new(ResizableAtomicFpSet::new(32));

        let step = CompiledBfsStep::build_with_shared_fp_set(
            &spec,
            vec![CompiledActionFn::new(actions[0].clone(), set_slot0_to_42)],
            vec![],
            Arc::clone(&shared_fp),
        )
        .expect("build");

        let result = step
            .run_bfs_multi_level(&[vec![0]], 100)
            .expect("multi-level");

        // Depth 0: [0] -> [42] (new). Depth 1: [42] -> [42] (dup, empty frontier).
        // So depths_completed=2: depth 0 fully processed, depth 1 fully processed
        // (but produced empty frontier so loop breaks at start of depth 2).
        assert!(result.depths_completed <= 2);
        assert!(result.invariant_ok);
        // Init [0] + new [42] = 2 states seen.
        assert_eq!(result.total_states_seen, 2);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_run_bfs_multi_level_invariant_violation() {
        // slot0 < 100 invariant. Start at [98, 0]. At depth 2, state=[100, 0] fails.
        let actions = vec![increment_action_descriptor()];
        let invariants = vec![slot0_lt_100_invariant_descriptor()];
        let spec = make_spec(2, actions.clone(), invariants.clone());
        let shared_fp = Arc::new(ResizableAtomicFpSet::new(64));

        let step = CompiledBfsStep::build_with_shared_fp_set(
            &spec,
            vec![CompiledActionFn::new(actions[0].clone(), increment_slot0)],
            vec![CompiledInvariantFn::new(
                invariants[0].clone(),
                slot0_lt_100,
            )],
            Arc::clone(&shared_fp),
        )
        .expect("build");

        let result = step
            .run_bfs_multi_level(&[vec![98, 0]], 10)
            .expect("multi-level");

        assert!(!result.invariant_ok);
        assert_eq!(result.failed_invariant_idx, Some(0));
        // Depth 0: [98,0] -> [99,0] (passes). Depth 1: [99,0] -> [100,0] (fails).
        assert_eq!(result.failed_depth, Some(1));
        assert_eq!(result.failed_successor, Some(vec![100, 0]));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_run_bfs_multi_level_throughput() {
        // Throughput test: linear chain 100 depths, measure states/sec.
        let actions = vec![increment_action_descriptor()];
        let spec = make_spec(2, actions.clone(), vec![]);
        let shared_fp = Arc::new(ResizableAtomicFpSet::new(256));

        let step = CompiledBfsStep::build_with_shared_fp_set(
            &spec,
            vec![CompiledActionFn::new(actions[0].clone(), increment_slot0)],
            vec![],
            Arc::clone(&shared_fp),
        )
        .expect("build");

        let start = std::time::Instant::now();
        let result = step
            .run_bfs_multi_level(&[vec![0, 0]], 100)
            .expect("multi-level");
        let elapsed = start.elapsed();

        assert_eq!(result.depths_completed, 100);
        assert!(result.invariant_ok);
        assert_eq!(result.total_states_seen, 101); // init + 100 new
        assert_eq!(result.total_generated, 100);

        let elapsed_secs = elapsed.as_secs_f64().max(f64::EPSILON);
        let states_per_sec = result.total_states_seen as f64 / elapsed_secs;
        eprintln!(
            "Multi-level BFS throughput: depths={}, states_seen={}, elapsed={:.3}ms, states/sec={:.0}",
            result.depths_completed,
            result.total_states_seen,
            elapsed_secs * 1000.0,
            states_per_sec,
        );
    }
}
