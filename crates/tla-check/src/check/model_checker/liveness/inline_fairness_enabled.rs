// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::check::model_checker::mc_struct::ActionInstanceMeta;
use crate::liveness::{ActionPredHint, LiveExpr};
use rustc_hash::FxHashSet;
use std::sync::Arc;

/// Part of #3100: ENABLED-to-action tag mapping for the WF disjunction short-circuit.
/// Each WF/SF fairness constraint produces an `enabled_tag` plus the paired
/// `ActionPred`/`StateChanged` `action_tags`; when ENABLED is false for state `s`,
/// those action tags are false for every transition from `s`.
pub(in crate::check::model_checker) struct EnabledActionGroup {
    pub(in crate::check::model_checker) enabled_tag: u32,
    pub(in crate::check::model_checker) action_tags: Vec<u32>,
}

/// Part of #3100: ENABLED provenance bypass — ENABLED tag → split_action indices.
/// Fields `enabled_tag` and `require_state_change` stored but not yet read
/// (pending #3208 bypass re-enablement). Only `split_action_indices` is consumed.
// Keep the full tuple shape in place so the ENABLED provenance bypass can be
// re-enabled without rewriting the cache plumbing around this struct.
#[allow(dead_code)]
pub(in crate::check::model_checker) struct EnabledProvenanceEntry {
    pub(in crate::check::model_checker) enabled_tag: u32,
    pub(in crate::check::model_checker) require_state_change: bool,
    pub(in crate::check::model_checker) split_action_indices: Vec<usize>,
}

/// Extract ENABLED-to-action tag groups from a fairness `LiveExpr`.
///
/// Matches the WF/SF tree structures produced by `fairness_to_live_expr`:
/// - WF: `Always(Eventually(Or([Not(Enabled{E}), And([ActionPred{A}, StateChanged{S}])])))`
/// - SF: `Or([Eventually(Always(Not(Enabled{E}))), Always(Eventually(And([AP{A}, SC{S}])))])`
fn extract_enabled_action_group(expr: &LiveExpr) -> Option<EnabledActionGroup> {
    match expr {
        // WF: Always(Eventually(Or([Not(Enabled), And([AP, SC])])))
        LiveExpr::Always(inner) => {
            if let LiveExpr::Eventually(inner2) = inner.as_ref() {
                extract_from_wf_disjunction(inner2)
            } else {
                None
            }
        }
        // SF: Or([Eventually(Always(Not(Enabled))), Always(Eventually(And([AP, SC])))])
        LiveExpr::Or(disjuncts) if disjuncts.len() == 2 => {
            let enabled_tag = extract_enabled_from_ea_not(&disjuncts[0]);
            let action_tags = extract_action_tags_from_ae_and(&disjuncts[1]);
            match (enabled_tag, action_tags) {
                (Some(e), Some(tags)) => Some(EnabledActionGroup {
                    enabled_tag: e,
                    action_tags: tags,
                }),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Extract ENABLED-to-action tag groups from a fairness expression, handling
/// quantified fairness that produces `And([wf1, wf2, ...])` conjunctions.
pub(super) fn extract_enabled_action_groups(expr: &LiveExpr, groups: &mut Vec<EnabledActionGroup>) {
    if let Some(group) = extract_enabled_action_group(expr) {
        groups.push(group);
    } else if let LiveExpr::And(conjuncts) = expr {
        // Quantified fairness like `\A p \in S: WF_vars(Act(p))` produces
        // And([WF_1, WF_2, ...]) — extract from each conjunct.
        for conjunct in conjuncts {
            extract_enabled_action_groups(conjunct, groups);
        }
    }
}

/// Match `Or([Not(Enabled{E}), And([leaves...])])` and extract the group.
fn extract_from_wf_disjunction(expr: &LiveExpr) -> Option<EnabledActionGroup> {
    if let LiveExpr::Or(disjuncts) = expr {
        if disjuncts.len() != 2 {
            return None;
        }
        let enabled_tag = if let LiveExpr::Not(inner) = &disjuncts[0] {
            if let LiveExpr::Enabled { tag, .. } = inner.as_ref() {
                Some(*tag)
            } else {
                None
            }
        } else {
            None
        };
        let action_tags = collect_all_action_leaf_tags(&disjuncts[1]);
        match (enabled_tag, action_tags) {
            (Some(e), tags) if !tags.is_empty() => Some(EnabledActionGroup {
                enabled_tag: e,
                action_tags: tags,
            }),
            _ => None,
        }
    } else {
        None
    }
}

fn extract_enabled_from_ea_not(expr: &LiveExpr) -> Option<u32> {
    if let LiveExpr::Eventually(inner) = expr {
        if let LiveExpr::Always(inner2) = inner.as_ref() {
            if let LiveExpr::Not(inner3) = inner2.as_ref() {
                if let LiveExpr::Enabled { tag, .. } = inner3.as_ref() {
                    return Some(*tag);
                }
            }
        }
    }
    None
}

fn extract_action_tags_from_ae_and(expr: &LiveExpr) -> Option<Vec<u32>> {
    if let LiveExpr::Always(inner) = expr {
        if let LiveExpr::Eventually(inner2) = inner.as_ref() {
            let tags = collect_all_action_leaf_tags(inner2);
            if !tags.is_empty() {
                return Some(tags);
            }
        }
    }
    None
}

fn collect_all_action_leaf_tags(expr: &LiveExpr) -> Vec<u32> {
    match expr {
        LiveExpr::ActionPred { tag, .. } | LiveExpr::StateChanged { tag, .. } => vec![*tag],
        LiveExpr::And(exprs) | LiveExpr::Or(exprs) => exprs
            .iter()
            .flat_map(collect_all_action_leaf_tags)
            .collect(),
        LiveExpr::Not(inner)
        | LiveExpr::Always(inner)
        | LiveExpr::Eventually(inner)
        | LiveExpr::Next(inner) => collect_all_action_leaf_tags(inner),
        _ => vec![],
    }
}

pub(super) fn build_enabled_provenance(
    groups: &[EnabledActionGroup],
    state_checks: &[LiveExpr],
    action_provenance: &[Vec<u32>],
) -> Vec<EnabledProvenanceEntry> {
    if action_provenance.is_empty() {
        return Vec::new();
    }
    let mut entries = Vec::with_capacity(groups.len());
    for group in groups {
        let rsc = state_checks.iter().any(|leaf| {
            matches!(leaf, LiveExpr::Enabled { tag, require_state_change: true, .. } if *tag == group.enabled_tag)
        });
        let tag_set: FxHashSet<u32> = group.action_tags.iter().copied().collect();
        let splits: Vec<usize> = action_provenance
            .iter()
            .enumerate()
            .filter(|(_, tags)| tags.iter().any(|t| tag_set.contains(t)))
            .map(|(idx, _)| idx)
            .collect();
        if !splits.is_empty() {
            entries.push(EnabledProvenanceEntry {
                enabled_tag: group.enabled_tag,
                require_state_change: rsc,
                split_action_indices: splits,
            });
        }
    }
    entries
}

/// Build action provenance tags from action pred hints and split action metadata.
///
/// Returns `(provenance_tags, fast_path_provenance_tags)` indexed by split action index.
/// Each inner vector contains the fairness ActionPred tags that match that split action.
pub(super) fn build_action_provenance_from_hints(
    hints: &[ActionPredHint],
    meta: &[ActionInstanceMeta],
    action_checks: &[LiveExpr],
) -> (Vec<Vec<u32>>, Vec<Vec<u32>>) {
    let mut provenance_tags = vec![Vec::new(); meta.len()];
    let mut fast_path_provenance_tags = vec![Vec::new(); meta.len()];

    for hint in hints {
        // Find the ActionPred leaf to get its liveness quantifier bindings
        let leaf_bindings: Option<&crate::eval::BindingChain> =
            action_checks.iter().find_map(|leaf| match leaf {
                LiveExpr::ActionPred {
                    tag: t, bindings, ..
                } if *t == hint.tag => bindings.as_ref(),
                _ => None,
            });

        // Collect binding values from the ActionPred's BindingChain
        let leaf_binding_values: Vec<(Arc<str>, crate::Value)> = leaf_bindings
            .map(|chain| {
                chain
                    .iter_eager()
                    .map(|(_, name, val)| (name, val))
                    .collect()
            })
            .unwrap_or_default();

        // Merge leaf quantifier bindings with the hint's const-level actual-arg bindings.
        let mut expected_bindings = leaf_binding_values;
        for (name, val) in &hint.actual_arg_bindings {
            if !expected_bindings.iter().any(|(n, _)| n == name) {
                expected_bindings.push((Arc::clone(name), val.clone()));
            }
        }

        // Match against ALL split_action_meta entries by name + bindings.
        for (idx, m) in meta.iter().enumerate() {
            let name_matches = m.name.as_deref() == Some(hint.name.as_ref());
            if !name_matches {
                continue;
            }

            let bindings_match = if expected_bindings.is_empty() && m.bindings.is_empty() {
                true
            } else {
                expected_bindings.iter().all(|(en, ev)| {
                    m.bindings
                        .iter()
                        .any(|(mn, mv)| mn.as_ref() == en.as_ref() && mv == ev)
                })
            };

            if bindings_match {
                provenance_tags[idx].push(hint.tag);
                if hint.split_action_fast_path_safe {
                    fast_path_provenance_tags[idx].push(hint.tag);
                }
            }
        }
    }

    // Deduplicate each inner vector for clean lookup at record time.
    for tags in &mut provenance_tags {
        tags.sort_unstable();
        tags.dedup();
    }
    for tags in &mut fast_path_provenance_tags {
        tags.sort_unstable();
        tags.dedup();
    }

    (provenance_tags, fast_path_provenance_tags)
}

/// Log inline fairness cache statistics when liveness profiling is enabled.
pub(super) fn log_inline_fairness_stats(
    state_checks: &[LiveExpr],
    action_checks: &[LiveExpr],
    provenance_len: usize,
    fast_path_provenance_len: usize,
    enabled_groups: &[EnabledActionGroup],
    subscript_pairs_len: usize,
    max_tag: u32,
    enabled_provenance: &[EnabledProvenanceEntry],
) {
    if !super::super::debug::liveness_profile() {
        return;
    }
    let enabled_skip_tags: usize = enabled_groups.iter().map(|g| g.action_tags.len()).sum();
    eprintln!(
        "[inline-fairness] leaves: {} state, {} action, {} provenance slots, \
         {} fast-path provenance slots, {} enabled-skip groups ({} action tags), \
         {} subscript-action pairs, max_tag={}",
        state_checks.len(),
        action_checks.len(),
        provenance_len,
        fast_path_provenance_len,
        enabled_groups.len(),
        enabled_skip_tags,
        subscript_pairs_len,
        max_tag,
    );
    if !enabled_provenance.is_empty() {
        let n: usize = enabled_provenance
            .iter()
            .map(|e| e.split_action_indices.len())
            .sum();
        eprintln!(
            "[inline-fairness] enabled provenance: {} entries, {} total split_action mappings",
            enabled_provenance.len(),
            n
        );
    }
}
