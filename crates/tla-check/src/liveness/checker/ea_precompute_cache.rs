// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bitmask-only cache helpers for composite liveness checks.
//!
//! Part of #3174: Per-tag cross-property HashMap caches removed.
//! All cache operations use bitmask-indexed inline results.

use super::{InlineCheckResults, LiveExpr, LivenessChecker};
use crate::state::Fingerprint;
use crate::storage::{ActionBitmaskLookup, StateBitmaskLookup};
use rustc_hash::FxHashMap;

/// Part of #3100: Reconstruct a check result from pre-built tag bitmasks.
///
/// `state_bits` has bit `tag` set when `(fp, tag) → true`.
/// `action_bits` has bit `tag` set when `(from_fp, to_fp, tag) → true`.
/// This avoids hash map lookups entirely — only bitwise operations.
pub(super) fn reconstruct_check_from_tag_bits(
    expr: &LiveExpr,
    state_bits: u64,
    action_bits: u64,
) -> bool {
    match expr {
        LiveExpr::Bool(b) => *b,
        LiveExpr::StatePred { tag, .. } | LiveExpr::Enabled { tag, .. } => {
            *tag < 64 && state_bits & (1u64 << *tag) != 0
        }
        LiveExpr::ActionPred { tag, .. } | LiveExpr::StateChanged { tag, .. } => {
            *tag < 64 && action_bits & (1u64 << *tag) != 0
        }
        LiveExpr::Not(inner) => !reconstruct_check_from_tag_bits(inner, state_bits, action_bits),
        LiveExpr::And(exprs) => exprs
            .iter()
            .all(|e| reconstruct_check_from_tag_bits(e, state_bits, action_bits)),
        LiveExpr::Or(exprs) => exprs
            .iter()
            .any(|e| reconstruct_check_from_tag_bits(e, state_bits, action_bits)),
        LiveExpr::Always(_) | LiveExpr::Eventually(_) | LiveExpr::Next(_) => false,
    }
}

impl LivenessChecker {
    /// Check if ALL used check expressions have only fairness-tagged or inline-tagged leaves.
    ///
    /// When true, all checks can be reconstructed purely from the inline bitmask
    /// cache without cloning any states or evaluating any expressions.
    ///
    /// Part of #3149: Requires actual bitmask data (inline_results) to be present.
    /// Without bitmask data, reconstruction would produce all-zero masks, causing
    /// ENABLED to evaluate as false for all states — making WF trivially satisfied
    /// and producing false-positive liveness violations.
    pub(super) fn all_checks_structurally_cached(
        check_state: &[LiveExpr],
        check_action: &[LiveExpr],
        state_used: &[bool],
        action_used: &[bool],
        max_fairness_tag: u32,
        inline_results: Option<InlineCheckResults<'_>>,
    ) -> bool {
        if inline_results.is_none() {
            return false;
        }
        let state_ok = check_state.iter().enumerate().all(|(i, check)| {
            !state_used.get(i).copied().unwrap_or(false)
                || Self::all_leaves_within_tag_range(
                    check,
                    max_fairness_tag,
                    inline_results.map_or(0, |results| results.max_tag),
                )
        });
        let action_ok = check_action.iter().enumerate().all(|(i, check)| {
            !action_used.get(i).copied().unwrap_or(false)
                || Self::all_leaves_within_tag_range(
                    check,
                    max_fairness_tag,
                    inline_results.map_or(0, |results| results.max_tag),
                )
        });
        state_ok && action_ok
    }

    /// Check if all leaf nodes in a LiveExpr tree are covered by a shared fairness cache
    /// or by the property-scoped inline cache.
    pub(super) fn all_leaves_within_tag_range(
        expr: &LiveExpr,
        max_fairness_tag: u32,
        max_inline_tag: u32,
    ) -> bool {
        match expr {
            LiveExpr::Bool(_) => true,
            LiveExpr::StatePred { tag, .. }
            | LiveExpr::Enabled { tag, .. }
            | LiveExpr::ActionPred { tag, .. }
            | LiveExpr::StateChanged { tag, .. } => {
                *tag > 0 && (*tag <= max_fairness_tag || *tag <= max_inline_tag)
            }
            LiveExpr::Not(inner) => {
                Self::all_leaves_within_tag_range(inner, max_fairness_tag, max_inline_tag)
            }
            LiveExpr::And(exprs) | LiveExpr::Or(exprs) => exprs
                .iter()
                .all(|e| Self::all_leaves_within_tag_range(e, max_fairness_tag, max_inline_tag)),
            LiveExpr::Always(_) | LiveExpr::Eventually(_) | LiveExpr::Next(_) => false,
        }
    }

    /// Fast path for `populate_node_check_masks`: reconstruct all check masks
    /// purely from bitmask caches without cloning any states (#3065, #3100, #3174).
    ///
    /// Part of #3174: Simplified — no cross-property per-tag caches.
    /// Bitmask maps are borrowed directly from inline results.
    pub(super) fn populate_node_check_masks_from_cache(
        &mut self,
        check_action: &[LiveExpr],
        check_state: &[LiveExpr],
        action_used: &[bool],
        state_used: &[bool],
        _max_fairness_tag: u32,
        inline_results: Option<InlineCheckResults<'_>>,
    ) -> Result<(), crate::error::EvalError> {
        use super::check_mask::CheckMask;

        let empty_state_bitmasks: FxHashMap<Fingerprint, u64> = FxHashMap::default();
        let empty_action_bitmasks: FxHashMap<(Fingerprint, Fingerprint), u64> =
            FxHashMap::default();

        let (state_tag_bits, action_tag_bits): (&dyn StateBitmaskLookup, &dyn ActionBitmaskLookup) =
            if let Some(results) = inline_results {
                (results.state_bitmasks, results.action_bitmasks)
            } else {
                (&empty_state_bitmasks, &empty_action_bitmasks)
            };

        // Single merged pass: compute masks from bitmask cache + write to NodeInfo.
        struct NodeRef {
            node: super::BehaviorGraphNode,
            succ_fps: Vec<Fingerprint>,
        }
        let node_refs: Vec<NodeRef> = self
            .graph
            .node_keys()
            .into_iter()
            .map(|node| {
                self.graph
                    .try_get_node_info(&node)?
                    .ok_or_else(|| crate::error::EvalError::Internal {
                        message: format!(
                            "populate_node_check_masks_from_cache: missing node info for {node}"
                        ),
                        span: None,
                    })
                    .map(|info| NodeRef {
                        node,
                        succ_fps: info.successors.iter().map(|s| s.state_fp).collect(),
                    })
            })
            .collect::<Result<Vec<_>, _>>()?;

        let mut state_fp_cache: FxHashMap<Fingerprint, CheckMask> = FxHashMap::default();
        let mut action_fp_cache: FxHashMap<(Fingerprint, Fingerprint), CheckMask> =
            FxHashMap::default();
        for nr in &node_refs {
            self.graph.update_node_info(&nr.node, |info| {
                let from_fp = nr.node.state_fp;

                info.state_check_mask = state_fp_cache
                    .entry(from_fp)
                    .or_insert_with(|| {
                        let sbits = state_tag_bits.get_bits(&from_fp).unwrap_or(0);
                        let mut mask = CheckMask::new();
                        for (ci, check) in check_state.iter().enumerate() {
                            if state_used.get(ci).copied().unwrap_or(false)
                                && reconstruct_check_from_tag_bits(check, sbits, 0)
                            {
                                mask.set(ci);
                            }
                        }
                        mask
                    })
                    .clone();

                let sbits = state_tag_bits.get_bits(&from_fp).unwrap_or(0);
                info.action_check_masks = nr
                    .succ_fps
                    .iter()
                    .map(|&to_fp| {
                        action_fp_cache
                            .entry((from_fp, to_fp))
                            .or_insert_with(|| {
                                let abits =
                                    action_tag_bits.get_bits(&(from_fp, to_fp)).unwrap_or(0);
                                let mut mask = CheckMask::new();
                                for (ci, check) in check_action.iter().enumerate() {
                                    if action_used.get(ci).copied().unwrap_or(false)
                                        && reconstruct_check_from_tag_bits(check, sbits, abits)
                                    {
                                        mask.set(ci);
                                    }
                                }
                                mask
                            })
                            .clone()
                    })
                    .collect();
            })?;
        }

        Ok(())
    }
}
