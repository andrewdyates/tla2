// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Diff-based successor enumeration — avoids cloning full states for duplicate detection.
//!
//! Instead of producing `Vec<ArrayState>`, these functions produce `Vec<DiffSuccessor>`
//! that only track the changed variables. The full state can be materialized later,
//! but only for unique successors (~5% in high-duplicate specs).

use std::ops::ControlFlow;
use std::sync::Arc;

use crate::eval::EvalCtx;
use crate::state::{ArrayState, DiffChanges, DiffSuccessor};
use crate::var_index::{VarIndex, VarRegistry};
use crate::Value;

use super::unified_types::DiffSink;
use super::PrimedAssignment;

#[derive(Clone, Copy)]
enum DiffAssignmentChoices<'a> {
    Single(&'a Value),
    Multi(&'a [Value]),
}

/// Convert assignments to indexed diff choices, returning `None` if any InSet
/// domain is empty (no successors possible). Shared preprocessing for all
/// non-deferred diff-choice paths.
fn prepare_diff_choices<'a>(
    current_array: &ArrayState,
    num_vars: usize,
    assignments: &'a [PrimedAssignment],
    registry: &VarRegistry,
) -> Option<Vec<Option<DiffAssignmentChoices<'a>>>> {
    let mut choices: Vec<Option<DiffAssignmentChoices<'a>>> = vec![None; num_vars];
    for assignment in assignments {
        match assignment {
            PrimedAssignment::Assign(name, value) => {
                if let Some(idx) = registry.get(name) {
                    // Part of #3354: symbolic evaluation now materializes some
                    // UNCHANGED bindings as Assign(current). Keep diffs minimal by
                    // dropping assignments that are already equal to the base state.
                    if current_array.get(idx) != *value {
                        choices[idx.as_usize()] = Some(DiffAssignmentChoices::Single(value));
                    }
                }
            }
            PrimedAssignment::Unchanged(_) => {}
            PrimedAssignment::InSet(name, values) => {
                if let Some(idx) = registry.get(name) {
                    choices[idx.as_usize()] = Some(DiffAssignmentChoices::Multi(values));
                }
            }
            PrimedAssignment::DeferredExpr(_, _) => {
                unreachable!("DeferredExpr in diff successor fast path")
            }
        }
    }

    if choices
        .iter()
        .any(|c| matches!(c, Some(DiffAssignmentChoices::Multi(values)) if values.is_empty()))
    {
        return None;
    }
    Some(choices)
}

/// Accumulator version - pushes directly to external DiffSink.
///
/// Part of #188, #213: This avoids the O(n) copy from `.extend()` by pushing
/// directly to the caller's accumulator. TLC pattern from Tool.java:969.
///
/// Part of #3027: accepts `&mut dyn DiffSink` instead of `&mut Vec<DiffSuccessor>`
/// to support both batch and streaming successor processing.
pub fn build_successor_diffs_from_array_into(
    ctx: &mut EvalCtx,
    current_array: &ArrayState,
    vars: &[Arc<str>],
    assignments: &[PrimedAssignment],
    registry: &VarRegistry,
    results: &mut dyn DiffSink,
) {
    let choices = match prepare_diff_choices(current_array, vars.len(), assignments, registry) {
        Some(c) => c,
        None => return,
    };

    let mut changes: Vec<(VarIndex, &Value)> = Vec::new();
    let _ = enumerate_diff_changes_only(&choices, 0, &mut changes, &mut |changes| {
        push_diff_to_sink_with_ctx(ctx, changes, results)
    });
}

/// Push a diff to the sink, returning the sink's ControlFlow signal.
///
/// Part of #3027: Returns ControlFlow so the combination recursion can
/// short-circuit when the streaming sink signals early termination.
#[inline]
fn push_diff_to_sink_with_ctx(
    ctx: &mut EvalCtx,
    changes: &[(VarIndex, &Value)],
    sink: &mut dyn DiffSink,
) -> ControlFlow<()> {
    let owned_changes: DiffChanges = changes
        .iter()
        .map(|(var_idx, v)| (*var_idx, (*v).clone()))
        .collect();
    // Part of #228: Don't compute fingerprint during enumeration - defer to BFS worker
    sink.push_with_ctx(ctx, DiffSuccessor::from_changes(owned_changes))
}

#[cfg(test)]
#[inline]
fn push_diff_to_sink(changes: &[(VarIndex, &Value)], sink: &mut dyn DiffSink) -> ControlFlow<()> {
    let owned_changes: DiffChanges = changes
        .iter()
        .map(|(var_idx, v)| (*var_idx, (*v).clone()))
        .collect();
    sink.push(DiffSuccessor::from_changes(owned_changes))
}

/// Diff-changes-only recursion: enumerate assignment combinations without
/// materializing an `ArrayState`. Used by production diff-only paths where
/// the next state is never materialized — removes the dead
/// `current_array.clone()`. Part of #3121 Step 4.
fn enumerate_diff_changes_only<'a, F>(
    choices: &[Option<DiffAssignmentChoices<'a>>],
    idx: usize,
    changes: &mut Vec<(VarIndex, &'a Value)>,
    emit: &mut F,
) -> ControlFlow<()>
where
    F: FnMut(&[(VarIndex, &'a Value)]) -> ControlFlow<()>,
{
    if idx >= choices.len() {
        return emit(changes);
    }

    let var_idx = VarIndex::new(idx);
    match &choices[idx] {
        Some(DiffAssignmentChoices::Single(v)) => {
            changes.push((var_idx, v));
            let flow = enumerate_diff_changes_only(choices, idx + 1, changes, emit);
            changes.pop();
            flow
        }
        Some(DiffAssignmentChoices::Multi(values)) => {
            for v in *values {
                changes.push((var_idx, v));
                let flow = enumerate_diff_changes_only(choices, idx + 1, changes, emit);
                changes.pop();
                if flow.is_break() {
                    return ControlFlow::Break(());
                }
            }
            ControlFlow::Continue(())
        }
        None => enumerate_diff_changes_only(choices, idx + 1, changes, emit),
    }
}

/// Recursively enumerate all assignment combinations for paths that need the
/// materialized next state (e.g., filtered paths that apply predicates).
///
/// Part of #3027: The emit closure returns `ControlFlow<()>` and the recursion
/// propagates `Break` back up, stopping further enumeration when the sink
/// signals early termination.
#[cfg(test)]
#[allow(clippy::only_used_in_recursion)]
fn enumerate_diff_changes_with_next<'a, F>(
    choices: &[Option<DiffAssignmentChoices<'a>>],
    idx: usize,
    next: &mut ArrayState,
    changes: &mut Vec<(VarIndex, &'a Value)>,
    emit: &mut F,
) -> ControlFlow<()>
where
    F: FnMut(&ArrayState, &[(VarIndex, &'a Value)]) -> ControlFlow<()>,
{
    if idx >= choices.len() {
        return emit(next, changes);
    }

    let var_idx = VarIndex::new(idx);
    match &choices[idx] {
        Some(DiffAssignmentChoices::Single(v)) => {
            next.set(var_idx, (*v).clone());
            changes.push((var_idx, v));
            let flow = enumerate_diff_changes_with_next(choices, idx + 1, next, changes, emit);
            changes.pop();
            flow
        }
        Some(DiffAssignmentChoices::Multi(values)) => {
            for v in *values {
                next.set(var_idx, v.clone());
                changes.push((var_idx, v));
                let flow = enumerate_diff_changes_with_next(choices, idx + 1, next, changes, emit);
                changes.pop();
                if flow.is_break() {
                    return ControlFlow::Break(());
                }
            }
            ControlFlow::Continue(())
        }
        None => enumerate_diff_changes_with_next(choices, idx + 1, next, changes, emit),
    }
}

// ============================================================================
// Test-only functions — all callers are in build_tests/
// ============================================================================

#[cfg(test)]
#[inline]
fn count_diff_combinations(choices: &[Option<DiffAssignmentChoices<'_>>]) -> usize {
    let mut count = 1usize;
    for choice in choices {
        if let Some(DiffAssignmentChoices::Multi(values)) = choice {
            count = count.saturating_mul(values.len());
        }
    }
    count
}

/// Build successor DiffSuccessors from an ArrayState (avoids full state cloning)
///
/// This is an optimization for high duplicate rate scenarios. Instead of cloning
/// the full ArrayState for each successor, we only track the changes (diffs).
/// The full state can be materialized later, but only for unique successors (~5%).
#[cfg(test)]
pub fn build_successor_diffs_from_array(
    current_array: &ArrayState,
    vars: &[Arc<str>],
    assignments: &[PrimedAssignment],
    registry: &VarRegistry,
) -> Vec<DiffSuccessor> {
    let choices = match prepare_diff_choices(current_array, vars.len(), assignments, registry) {
        Some(c) => c,
        None => return Vec::new(),
    };

    let num_combinations = count_diff_combinations(&choices);
    let mut results = Vec::with_capacity(num_combinations);
    let mut changes: Vec<(VarIndex, &Value)> = Vec::new();

    let _ = enumerate_diff_changes_only(&choices, 0, &mut changes, &mut |changes| {
        push_diff_to_sink(changes, &mut results)
    });

    results
}

#[cfg(test)]
pub fn build_successor_diffs_from_array_filtered<F>(
    current_array: &ArrayState,
    vars: &[Arc<str>],
    assignments: &[PrimedAssignment],
    registry: &VarRegistry,
    mut filter: F,
) -> Vec<DiffSuccessor>
where
    F: FnMut(&ArrayState) -> bool,
{
    let choices = match prepare_diff_choices(current_array, vars.len(), assignments, registry) {
        Some(c) => c,
        None => return Vec::new(),
    };

    let num_combinations = count_diff_combinations(&choices);
    let mut results = Vec::with_capacity(num_combinations);
    let mut changes: Vec<(VarIndex, &Value)> = Vec::new();
    let mut next_array = current_array.clone_for_working();

    let _ = enumerate_diff_changes_with_next(
        &choices,
        0,
        &mut next_array,
        &mut changes,
        &mut |next, changes| {
            if filter(next) {
                let _ = push_diff_to_sink(changes, &mut results);
            }
            ControlFlow::Continue(())
        },
    );

    results
}

/// Build successor diffs with deferred expression support and prime guard filtering.
#[cfg(test)]
pub fn build_successor_diffs_with_deferred_filtered<F>(
    current_array: &ArrayState,
    vars: &[Arc<str>],
    assignments: &[PrimedAssignment],
    registry: &VarRegistry,
    ctx: &crate::eval::EvalCtx,
    mut filter: F,
) -> Result<Vec<DiffSuccessor>, crate::error::EvalError>
where
    F: FnMut(&ArrayState) -> bool,
{
    use std::convert::Infallible;
    use std::ops::ControlFlow;

    use super::build::build_successors_with_deferred;
    use super::emitter::FilteredDiffEmitter;

    let mut results = Vec::new();
    let mut emitter = FilteredDiffEmitter::new(&mut results, &mut filter);
    let flow: Result<ControlFlow<Infallible, ()>, _> = build_successors_with_deferred(
        current_array,
        vars,
        assignments,
        registry,
        ctx,
        "build_successor_diffs_with_deferred_filtered",
        &mut emitter,
    );
    match flow? {
        ControlFlow::Continue(()) => Ok(results),
        ControlFlow::Break(never) => match never {},
    }
}
