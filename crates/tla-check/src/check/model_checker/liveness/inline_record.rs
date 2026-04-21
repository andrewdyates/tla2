// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::inline_helpers::update_action_bitmask;
use crate::check::model_checker::{Fingerprint, ModelChecker};
use crate::check::{CheckError, RuntimeCheckError};
use crate::eval::EvalCtx;
use crate::liveness::{InlineEvalScope, LiveExpr};
use crate::state::ArrayState;
use crate::storage::{ActionBitmaskMap, StateBitmaskMap};
use crate::EvalCheckError;

/// Compiled liveness batch for JIT-accelerated fairness predicate evaluation.
/// When present, compiled tags are evaluated via native code; fallback tags
/// still go through the interpreter.
#[cfg(feature = "jit")]
pub(super) type CompiledBatchRef<'a> = Option<&'a tla_jit::CompiledLivenessBatch>;

/// No-op type alias when JIT feature is disabled.
#[cfg(not(feature = "jit"))]
pub(super) type CompiledBatchRef<'a> = Option<&'a ()>;

/// Record missing state-level liveness results (bitmask-only).
///
/// Part of #3992: When a compiled liveness batch is available, compiled tags
/// are evaluated via JIT-compiled native code on flattened i64 state buffers.
/// Fallback tags (and all tags when no batch is available) go through the
/// canonical AST/TIR evaluator.
///
/// Bitmask-only: results are stored as bits in `state_bitmasks[current_fp]`.
/// Fingerprint presence in the map means all tags have been evaluated.
#[allow(clippy::too_many_arguments)]
pub(super) fn record_missing_state_results(
    ctx: &mut EvalCtx,
    state_leaves: &[LiveExpr],
    state_bitmasks: &mut StateBitmaskMap,
    stuttering_allowed: bool,
    current_fp: Fingerprint,
    current_array: &ArrayState,
    successors: &[(ArrayState, Fingerprint)],
    compiled_batch: CompiledBatchRef<'_>,
) -> Result<(), CheckError> {
    // Bulk skip: if this fingerprint's state leaves have already been evaluated
    // (by a previous parent that shared this state as a successor), skip entirely.
    if state_bitmasks.contains_key(&current_fp) {
        return Ok(());
    }

    // Ensure the fingerprint has an entry even if all results are false (0 bits).
    // Presence in the map signals "all tags evaluated" for subsequent lookups.
    state_bitmasks.get_or_insert_default(current_fp);

    if state_leaves.is_empty() {
        return Ok(());
    }

    // Part of #3992: JIT-compiled fast path for state predicates.
    #[cfg(feature = "jit")]
    if let Some(batch) = compiled_batch {
        if batch.state_pred_fn.is_some() {
            return record_state_results_with_compiled_batch(
                ctx,
                state_leaves,
                state_bitmasks,
                stuttering_allowed,
                current_fp,
                current_array,
                successors,
                batch,
            );
        }
    }

    // Suppress unused variable warning when JIT feature is disabled.
    #[cfg(not(feature = "jit"))]
    let _ = compiled_batch;

    record_state_results_interpreter_only(
        ctx,
        state_leaves,
        state_bitmasks,
        stuttering_allowed,
        current_fp,
        current_array,
        successors,
    )
}

/// Pure interpreter path for state predicate evaluation.
#[allow(clippy::too_many_arguments)]
fn record_state_results_interpreter_only(
    ctx: &mut EvalCtx,
    state_leaves: &[LiveExpr],
    state_bitmasks: &mut StateBitmaskMap,
    stuttering_allowed: bool,
    current_fp: Fingerprint,
    current_array: &ArrayState,
    successors: &[(ArrayState, Fingerprint)],
) -> Result<(), CheckError> {
    let mut cached_successors =
        Vec::with_capacity(successors.len() + usize::from(stuttering_allowed));
    cached_successors.extend(successors.iter().map(|(arr, fp)| (arr, *fp)));
    if stuttering_allowed {
        cached_successors.push((current_array, current_fp));
    }

    let all_leaves: Vec<&LiveExpr> = state_leaves.iter().collect();
    let results = crate::liveness::inline_leaf_eval::eval_state_leaves_with_array_successors(
        ctx,
        &all_leaves,
        current_fp,
        current_array,
        &cached_successors,
    )
    .map_err(|e| -> CheckError { EvalCheckError::Eval(e).into() })?;
    for (tag, result) in results {
        if result && tag < 64 {
            state_bitmasks.or_bits(current_fp, 1u64 << tag);
        }
    }

    Ok(())
}

/// JIT-compiled fast path for state predicate evaluation.
///
/// Evaluates compiled tags via the native code batch function, then falls back
/// to the interpreter for any tags that could not be compiled (ENABLED,
/// StateChanged, compound-type predicates).
///
/// Part of #3992: JIT V2 Phase 10 compiled liveness wiring.
#[cfg(feature = "jit")]
#[allow(clippy::too_many_arguments)]
fn record_state_results_with_compiled_batch(
    ctx: &mut EvalCtx,
    state_leaves: &[LiveExpr],
    state_bitmasks: &mut StateBitmaskMap,
    stuttering_allowed: bool,
    current_fp: Fingerprint,
    current_array: &ArrayState,
    successors: &[(ArrayState, Fingerprint)],
    batch: &tla_jit::CompiledLivenessBatch,
) -> Result<(), CheckError> {
    // Step 1: Flatten the current state into an i64 buffer for the compiled path.
    let mut scratch = Vec::new();
    let flattened = crate::check::model_checker::invariants::flatten_state_to_i64_selective(
        current_array,
        &mut scratch,
        &[], // empty = all variables
    );

    if flattened {
        // Step 2: Evaluate compiled state predicates via native code.
        // SAFETY: scratch buffer has been populated by flatten_state_to_i64_selective
        // with length >= state_layout.num_vars(). The compiled function reads
        // exactly state_len elements from the buffer.
        let compiled_bitmask = unsafe { batch.eval_state_preds(&scratch) };

        // Step 3: OR compiled results into the bitmask map.
        if compiled_bitmask != 0 {
            state_bitmasks.or_bits(current_fp, compiled_bitmask);
        }
    }

    // Step 4: Evaluate fallback tags (and all tags if flattening failed) via interpreter.
    if !batch.fallback_state_tags.is_empty() || !flattened {
        let fallback_leaves: Vec<&LiveExpr> = if flattened {
            // Only evaluate leaves whose tags are in the fallback set.
            let fallback_set: rustc_hash::FxHashSet<u32> =
                batch.fallback_state_tags.iter().copied().collect();
            state_leaves
                .iter()
                .filter(|leaf| leaf.tag().is_some_and(|tag| fallback_set.contains(&tag)))
                .collect()
        } else {
            // Flattening failed -- evaluate ALL leaves via interpreter.
            state_leaves.iter().collect()
        };

        if !fallback_leaves.is_empty() {
            let mut cached_successors =
                Vec::with_capacity(successors.len() + usize::from(stuttering_allowed));
            cached_successors.extend(successors.iter().map(|(arr, fp)| (arr, *fp)));
            if stuttering_allowed {
                cached_successors.push((current_array, current_fp));
            }

            let results =
                crate::liveness::inline_leaf_eval::eval_state_leaves_with_array_successors(
                    ctx,
                    &fallback_leaves,
                    current_fp,
                    current_array,
                    &cached_successors,
                )
                .map_err(|e| -> CheckError { EvalCheckError::Eval(e).into() })?;

            for (tag, result) in results {
                if result && tag < 64 {
                    state_bitmasks.or_bits(current_fp, 1u64 << tag);
                }
            }
        }
    }

    Ok(())
}

/// Record missing action-level liveness results (bitmask-only).
///
/// Part of #3992: When a compiled liveness batch is available, compiled tags
/// are evaluated via JIT-compiled native code. Fallback tags go through the
/// canonical AST/TIR evaluator.
///
/// Bitmask-only: results are stored as bits in `action_bitmasks[(current_fp, next_fp)]`.
/// Key presence in the map means all tags have been evaluated for this transition.
#[allow(clippy::too_many_arguments)]
pub(super) fn record_missing_action_results(
    ctx: &mut EvalCtx,
    action_leaves: &[LiveExpr],
    action_bitmasks: &mut ActionBitmaskMap,
    current_fp: Fingerprint,
    current_array: &ArrayState,
    next_fp: Fingerprint,
    next_array: &ArrayState,
    compiled_batch: CompiledBatchRef<'_>,
) -> Result<(), CheckError> {
    // Bulk skip: if this transition's action leaves have already been
    // fully evaluated, skip. Key presence = "all tags evaluated" invariant.
    //
    // Part of #3208 fix (Bug D): This invariant requires that ONLY this
    // function and the all_groups_disabled optimization create map keys.
    // The action provenance bypass and subscript short-circuit must NOT
    // create keys -- they may only OR bits into existing entries. See
    // update_action_bitmask() and apply_subscript_short_circuit_bitmask().
    if action_bitmasks.contains_key(&(current_fp, next_fp)) {
        return Ok(());
    }

    // Ensure the transition has an entry even if all results are false.
    action_bitmasks.get_or_insert_default((current_fp, next_fp));

    if action_leaves.is_empty() {
        return Ok(());
    }

    // Part of #3992: JIT-compiled fast path for action predicates.
    #[cfg(feature = "jit")]
    if let Some(batch) = compiled_batch {
        if batch.action_pred_fn.is_some() {
            return record_action_results_with_compiled_batch(
                ctx,
                action_leaves,
                action_bitmasks,
                current_fp,
                current_array,
                next_fp,
                next_array,
                batch,
            );
        }
    }

    #[cfg(not(feature = "jit"))]
    let _ = compiled_batch;

    record_action_results_interpreter_only(
        ctx,
        action_leaves,
        action_bitmasks,
        current_fp,
        current_array,
        next_fp,
        next_array,
    )
}

/// Pure interpreter path for action predicate evaluation.
#[allow(clippy::too_many_arguments)]
fn record_action_results_interpreter_only(
    ctx: &mut EvalCtx,
    action_leaves: &[LiveExpr],
    action_bitmasks: &mut ActionBitmaskMap,
    current_fp: Fingerprint,
    current_array: &ArrayState,
    next_fp: Fingerprint,
    next_array: &ArrayState,
) -> Result<(), CheckError> {
    let all_leaves: Vec<&LiveExpr> = action_leaves.iter().collect();
    let results = crate::liveness::inline_leaf_eval::eval_action_leaves_array(
        ctx,
        &all_leaves,
        current_fp,
        current_array,
        next_fp,
        next_array,
    )
    .map_err(|e| -> CheckError { EvalCheckError::Eval(e).into() })?;
    for (tag, result) in results {
        if result && tag < 64 {
            action_bitmasks.or_bits((current_fp, next_fp), 1u64 << tag);
        }
    }

    Ok(())
}

/// JIT-compiled fast path for action predicate evaluation.
///
/// Part of #3992: JIT V2 Phase 10 compiled liveness wiring.
#[cfg(feature = "jit")]
#[allow(clippy::too_many_arguments)]
fn record_action_results_with_compiled_batch(
    ctx: &mut EvalCtx,
    action_leaves: &[LiveExpr],
    action_bitmasks: &mut ActionBitmaskMap,
    current_fp: Fingerprint,
    current_array: &ArrayState,
    next_fp: Fingerprint,
    next_array: &ArrayState,
    batch: &tla_jit::CompiledLivenessBatch,
) -> Result<(), CheckError> {
    // Flatten both current and next states for the compiled path.
    let mut current_scratch = Vec::new();
    let mut next_scratch = Vec::new();
    let current_ok = crate::check::model_checker::invariants::flatten_state_to_i64_selective(
        current_array,
        &mut current_scratch,
        &[], // empty = all variables
    );
    let next_ok = crate::check::model_checker::invariants::flatten_state_to_i64_selective(
        next_array,
        &mut next_scratch,
        &[], // empty = all variables
    );

    if current_ok && next_ok {
        // SAFETY: Both scratch buffers have been populated by flatten_state_to_i64_selective
        // with length >= state_layout.num_vars().
        let compiled_bitmask =
            unsafe { batch.eval_action_preds(&current_scratch, &next_scratch) };

        if compiled_bitmask != 0 {
            action_bitmasks.or_bits((current_fp, next_fp), compiled_bitmask);
        }
    }

    // Evaluate fallback tags (or all tags if flattening failed) via interpreter.
    if !batch.fallback_action_tags.is_empty() || !current_ok || !next_ok {
        let fallback_leaves: Vec<&LiveExpr> = if current_ok && next_ok {
            let fallback_set: rustc_hash::FxHashSet<u32> =
                batch.fallback_action_tags.iter().copied().collect();
            action_leaves
                .iter()
                .filter(|leaf| leaf.tag().is_some_and(|tag| fallback_set.contains(&tag)))
                .collect()
        } else {
            action_leaves.iter().collect()
        };

        if !fallback_leaves.is_empty() {
            let results = crate::liveness::inline_leaf_eval::eval_action_leaves_array(
                ctx,
                &fallback_leaves,
                current_fp,
                current_array,
                next_fp,
                next_array,
            )
            .map_err(|e| -> CheckError { EvalCheckError::Eval(e).into() })?;

            for (tag, result) in results {
                if result && tag < 64 {
                    action_bitmasks.or_bits((current_fp, next_fp), 1u64 << tag);
                }
            }
        }
    }

    Ok(())
}

// ── Top-level inline liveness recording ──────────────────────────────────

impl<'a> ModelChecker<'a> {
    /// Record inline liveness results for all successors of the current state.
    ///
    /// Part of #3100: `action_tags` is a parallel slice to `successors` carrying
    /// the split_action index that produced each successor. When a tag matches an
    /// entry in `action_provenance_tags`, the corresponding ActionPred result is
    /// pre-populated as TRUE, skipping expensive AST evaluation.
    pub(in crate::check::model_checker) fn record_inline_liveness_results(
        &mut self,
        current_fp: Fingerprint,
        current_array: &ArrayState,
        successors: &[(ArrayState, Fingerprint)],
        action_tags: &[Option<usize>],
    ) -> Result<(), CheckError> {
        if !self.inline_liveness_active() {
            return Ok(());
        }

        // Establish the per-parent state boundary once before any inline leaf
        // work. This preserves persistent entries while making the
        // `eval_entry_inline` fast path safe for action-only plans whose first
        // leaf would otherwise skip the normal `eval_entry` state-change hook.
        crate::eval::clear_for_state_boundary();
        let boundary = InlineEvalScope::new();
        let result = (|| {
            // Part of #3992: Get compiled liveness batch reference for JIT-accelerated
            // fairness predicate evaluation.
            #[cfg(feature = "jit")]
            let compiled_batch: CompiledBatchRef<'_> =
                self.liveness_cache.compiled_liveness_batch.as_ref();
            #[cfg(not(feature = "jit"))]
            let compiled_batch: CompiledBatchRef<'_> = None;

            if self.inline_fairness_active() {
                // Part of #3208 fix (Bug C): ENABLED provenance bypass disabled.
                //
                // The bypass (Part of #3100) determined ENABLED from BFS action
                // tags instead of AST evaluation. It only covers ENABLED tags
                // that have EnabledProvenanceEntry (actions with
                // split_action_fast_path_safe hints). Actions with existential
                // quantifiers (like SF_vars(\E S: Allocate(c,S))) don't produce
                // hints, so their ENABLED tags have no provenance entry.
                //
                // Two bugs in the bypass:
                // 1. Writing to inline_state_bitmasks created the map key,
                //    causing record_missing_state_results to skip all remaining
                //    leaves (including non-provenance-covered SF ENABLED tags).
                // 2. set_enabled_cache cached values that could disagree with
                //    the full evaluator (provenance checks action tag presence,
                //    not the full action predicate with bindings/quantifiers).
                //
                // Fix: Let record_missing_state_results handle all ENABLED
                // evaluation. The bypass can be re-enabled with proper coverage
                // tracking (only cache when ALL ENABLED tags have provenance).

                record_missing_state_results(
                    &mut self.ctx,
                    &self.liveness_cache.fairness_state_checks,
                    &mut self.liveness_cache.inline_state_bitmasks,
                    self.exploration.stuttering_allowed,
                    current_fp,
                    current_array,
                    successors,
                    compiled_batch,
                )?;

                if !self.liveness_cache.fairness_action_checks.is_empty() {
                    // Part of #3100: ENABLED-based action skip. When ENABLED is false,
                    // <<A>>_vars is false for ALL transitions. Read from state bitmask
                    // (record_missing_state_results just ran, so all tags are evaluated;
                    // bit not set = false).
                    if !self.liveness_cache.enabled_action_groups.is_empty() {
                        let state_bits = self
                            .liveness_cache
                            .inline_state_bitmasks
                            .get(&current_fp)
                            .unwrap_or(0);
                        // Part of #3208: Only pre-populate zero entries when ALL
                        // enabled_action_groups have ENABLED=false. The previous
                        // per-group approach created entries when ANY single group
                        // was disabled, which caused record_missing_action_results
                        // to skip evaluation for OTHER groups' action tags (their
                        // bits remained at 0 even when the action fires).
                        let all_groups_disabled = self
                            .liveness_cache
                            .enabled_action_groups
                            .iter()
                            .all(|group| {
                                !(group.enabled_tag < 64
                                    && state_bits & (1u64 << group.enabled_tag) != 0)
                            });
                        if all_groups_disabled {
                            // All action groups disabled → all action tags are
                            // FALSE for every successor. Create entries to signal
                            // "all tags evaluated" (0 bits = all false).
                            for (_, next_fp) in successors {
                                self.liveness_cache
                                    .inline_action_bitmasks
                                    .get_or_insert_default((current_fp, *next_fp));
                            }
                            if self.exploration.stuttering_allowed {
                                self.liveness_cache
                                    .inline_action_bitmasks
                                    .get_or_insert_default((current_fp, current_fp));
                            }
                        }
                    }

                    let has_provenance = !self
                        .liveness_cache
                        .action_fast_path_provenance_tags
                        .is_empty()
                        && !action_tags.is_empty();

                    for (i, (next_array, next_fp)) in successors.iter().enumerate() {
                        // Part of #3100: Pre-populate TRUE for ActionPred leaves whose
                        // provenance matches the successor's action tag.
                        if has_provenance {
                            if let Some(Some(action_idx)) = action_tags.get(i) {
                                if let Some(tags) = self
                                    .liveness_cache
                                    .action_fast_path_provenance_tags
                                    .get(*action_idx)
                                {
                                    for tag in tags {
                                        update_action_bitmask(
                                            &mut self.liveness_cache.inline_action_bitmasks,
                                            current_fp,
                                            *next_fp,
                                            *tag,
                                            true,
                                        );
                                    }
                                }
                            }
                        }

                        // Part of #3100: Subscript-based ActionPred skip (TLC LNAction).
                        super::subscript_action_pair::apply_subscript_short_circuit_bitmask(
                            &self.ctx,
                            &mut self.liveness_cache.inline_action_bitmasks,
                            &self.liveness_cache.subscript_action_pairs,
                            current_fp,
                            current_array,
                            *next_fp,
                            next_array,
                        )?;

                        record_missing_action_results(
                            &mut self.ctx,
                            &self.liveness_cache.fairness_action_checks,
                            &mut self.liveness_cache.inline_action_bitmasks,
                            current_fp,
                            current_array,
                            *next_fp,
                            next_array,
                            compiled_batch,
                        )?;
                    }
                }

                // Part of #3100: Stuttering shortcut — ensure stuttering transitions
                // have an entry in the bitmask map (all action tags are FALSE for
                // stuttering since StateChanged = FALSE → <<A>>_vars = FALSE).
                if self.exploration.stuttering_allowed {
                    self.liveness_cache
                        .inline_action_bitmasks
                        .get_or_insert_default((current_fp, current_fp));
                }
            }

            if !self.liveness_cache.inline_property_plans.is_empty() {
                let stuttering_allowed = self.exploration.stuttering_allowed;
                let ctx = &mut self.ctx;
                for plan in &mut self.liveness_cache.inline_property_plans {
                    plan.record_results(
                        ctx,
                        stuttering_allowed,
                        current_fp,
                        current_array,
                        successors,
                    )?;
                    plan.maybe_flush().map_err(|e| {
                        CheckError::Runtime(RuntimeCheckError::Internal(format!(
                            "disk property bitmask flush failed: {e}"
                        )))
                    })?;
                }
            }

            // Part of #3177: Periodically flush disk-backed bitmask hot tiers
            // to keep BFS memory bounded for billion-state specs.
            self.liveness_cache
                .inline_state_bitmasks
                .maybe_flush()
                .map_err(|e| {
                    CheckError::Runtime(RuntimeCheckError::Internal(format!(
                        "disk state bitmask flush failed: {e}"
                    )))
                })?;
            self.liveness_cache
                .inline_action_bitmasks
                .maybe_flush()
                .map_err(|e| {
                    CheckError::Runtime(RuntimeCheckError::Internal(format!(
                        "disk action bitmask flush failed: {e}"
                    )))
                })?;

            Ok(())
        })();
        boundary.finish();
        result
    }
}
