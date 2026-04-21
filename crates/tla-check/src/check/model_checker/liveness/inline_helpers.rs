// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::liveness::LiveExpr;
use crate::state::Fingerprint;
use crate::storage::ActionBitmaskMap;
use rustc_hash::FxHashSet;

/// Recursively collect unique state and action leaf expressions from a
/// `LiveExpr` tree, deduplicating by tag.
pub(super) fn collect_live_leaves(
    expr: &LiveExpr,
    state_leaves: &mut Vec<LiveExpr>,
    action_leaves: &mut Vec<LiveExpr>,
    seen_state_tags: &mut FxHashSet<u32>,
    seen_action_tags: &mut FxHashSet<u32>,
) {
    match expr {
        LiveExpr::StatePred { tag, .. } | LiveExpr::Enabled { tag, .. } => {
            if seen_state_tags.insert(*tag) {
                state_leaves.push(expr.clone());
            }
        }
        LiveExpr::ActionPred { tag, .. } | LiveExpr::StateChanged { tag, .. } => {
            if seen_action_tags.insert(*tag) {
                action_leaves.push(expr.clone());
            }
        }
        LiveExpr::Not(inner)
        | LiveExpr::Always(inner)
        | LiveExpr::Eventually(inner)
        | LiveExpr::Next(inner) => collect_live_leaves(
            inner,
            state_leaves,
            action_leaves,
            seen_state_tags,
            seen_action_tags,
        ),
        LiveExpr::And(exprs) | LiveExpr::Or(exprs) => {
            for inner in exprs {
                collect_live_leaves(
                    inner,
                    state_leaves,
                    action_leaves,
                    seen_state_tags,
                    seen_action_tags,
                );
            }
        }
        LiveExpr::Bool(_) => {}
    }
}

/// Part of #3100: Update bitmask for a single action result insert.
/// Only sets bits for TRUE results with tag < 64.
///
/// Part of #3208 fix (Bug D): Only OR bits into EXISTING entries. Does
/// NOT create new keys. This preserves the "key presence = all tags
/// evaluated" invariant used by record_missing_action_results. Callers
/// that pre-populate partial results (action provenance, subscript
/// short-circuit) must not create keys — only record_missing_action_results
/// and the all_groups_disabled optimization may create keys.
#[inline]
pub(super) fn update_action_bitmask(
    bitmasks: &mut ActionBitmaskMap,
    from_fp: Fingerprint,
    to_fp: Fingerprint,
    tag: u32,
    result: bool,
) {
    if result && tag < 64 {
        if let Some(bits) = bitmasks.get_mut(&(from_fp, to_fp)) {
            *bits |= 1u64 << tag;
        }
    }
}
