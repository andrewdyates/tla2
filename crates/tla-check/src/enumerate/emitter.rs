// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Successor emission adapters for unified enumeration pipelines.
//! Test-only module (gated behind #[cfg(test)] in enumerate.rs).

use crate::error::EvalError;
use crate::state::{ArrayState, DiffChanges, DiffSuccessor};
use crate::var_index::{VarIndex, VarRegistry};
use std::convert::Infallible;
use std::ops::ControlFlow;

/// Called when enumeration finds a complete successor assignment.
pub(crate) trait SuccessorEmitter {
    /// Type carried by `ControlFlow::Break` to halt enumeration early.
    type Halt;

    /// Emit one successor derived from `working`.
    ///
    /// `base` is the source state (for diff computation); `working` is the fully
    /// assigned successor candidate. Returns `Err` if guard evaluation encounters
    /// a fatal error (TLC propagates eval errors during prime guard validation).
    fn emit(
        &mut self,
        base: &ArrayState,
        working: &ArrayState,
        registry: &VarRegistry,
    ) -> Result<ControlFlow<Self::Halt, ()>, EvalError>;
}

pub(super) struct FullStateEmitter<'a> {
    results: &'a mut Vec<ArrayState>,
    ensure_fingerprint: bool,
}

impl<'a> FullStateEmitter<'a> {
    pub(super) fn new(results: &'a mut Vec<ArrayState>, ensure_fingerprint: bool) -> Self {
        Self {
            results,
            ensure_fingerprint,
        }
    }
}

impl SuccessorEmitter for FullStateEmitter<'_> {
    type Halt = Infallible;

    fn emit(
        &mut self,
        _base: &ArrayState,
        working: &ArrayState,
        registry: &VarRegistry,
    ) -> Result<ControlFlow<Self::Halt, ()>, EvalError> {
        let mut snapshot = working.clone();
        if self.ensure_fingerprint {
            let _ = snapshot.fingerprint(registry);
        }
        self.results.push(snapshot);
        Ok(ControlFlow::Continue(()))
    }
}

pub(super) struct FilteredDiffEmitter<'a, F>
where
    F: FnMut(&ArrayState) -> bool,
{
    results: &'a mut Vec<DiffSuccessor>,
    filter: &'a mut F,
}

impl<'a, F> FilteredDiffEmitter<'a, F>
where
    F: FnMut(&ArrayState) -> bool,
{
    pub(super) fn new(results: &'a mut Vec<DiffSuccessor>, filter: &'a mut F) -> Self {
        Self { results, filter }
    }
}

impl<F> SuccessorEmitter for FilteredDiffEmitter<'_, F>
where
    F: FnMut(&ArrayState) -> bool,
{
    type Halt = Infallible;

    fn emit(
        &mut self,
        base: &ArrayState,
        working: &ArrayState,
        _registry: &VarRegistry,
    ) -> Result<ControlFlow<Self::Halt, ()>, EvalError> {
        if !(self.filter)(working) {
            return Ok(ControlFlow::Continue(()));
        }
        self.results.push(diff_successor_from_states(base, working));
        Ok(ControlFlow::Continue(()))
    }
}

fn diff_successor_from_states(base: &ArrayState, working: &ArrayState) -> DiffSuccessor {
    debug_assert_eq!(base.len(), working.len());
    let mut changes = DiffChanges::new();
    for idx in 0..working.len() {
        let var_idx = VarIndex::new(idx);
        let new_value = working.get(var_idx);
        let old_value = base.get(var_idx);
        if new_value != old_value {
            changes.push((var_idx, new_value));
        }
    }
    // Part of #228: Diff successor fingerprinting stays deferred.
    DiffSuccessor::from_changes(changes)
}
