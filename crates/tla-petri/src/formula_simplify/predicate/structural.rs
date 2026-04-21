// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tiers 3-4: structural fireability pruning and deadlock-pattern collapse.

use crate::formula_simplify::SimplificationContext;
use crate::property_xml::StatePredicate;

/// Tier 3: structural fireability pruning.
///
/// For `IsFireable(names)`, drop transitions that are structurally disabled
/// (some input arc weight exceeds the P-invariant upper bound for that place).
/// If all transitions are pruned → False. If the list is unchanged, keep as-is.
pub(super) fn fireability_prune(
    pred: &StatePredicate,
    ctx: &SimplificationContext<'_>,
) -> StatePredicate {
    if let StatePredicate::IsFireable(names) = pred {
        let mut remaining = Vec::with_capacity(names.len());
        for name in names {
            if let Some(indices) = ctx.aliases.resolve_transitions(name) {
                let any_live = indices
                    .iter()
                    .any(|idx| !ctx.facts.structurally_disabled[idx.0 as usize]);
                if any_live {
                    remaining.push(name.clone());
                }
            } else {
                remaining.push(name.clone());
            }
        }
        if remaining.is_empty() {
            StatePredicate::False
        } else if remaining.len() == names.len() {
            pred.clone()
        } else {
            StatePredicate::IsFireable(remaining)
        }
    } else {
        pred.clone()
    }
}

/// Tier 4: deadlock-pattern collapse.
///
/// Recognize `Not(IsFireable(all_transitions))` as "deadlock exists".
/// If `structural_deadlock_free` proves no deadlock → rewrite to False.
pub(super) fn deadlock_collapse(
    pred: &StatePredicate,
    ctx: &SimplificationContext<'_>,
) -> StatePredicate {
    if let StatePredicate::Not(inner) = pred {
        if let StatePredicate::IsFireable(names) = inner.as_ref() {
            if ctx.facts.deadlock_free == Some(true)
                && covers_all_transitions(names, ctx.net, ctx.aliases)
            {
                return StatePredicate::False;
            }
        }
    }
    pred.clone()
}

/// Check if an `IsFireable` name list covers all transitions in the net.
fn covers_all_transitions(
    names: &[String],
    net: &crate::petri_net::PetriNet,
    aliases: &crate::model::PropertyAliases,
) -> bool {
    let mut covered = vec![false; net.num_transitions()];
    for name in names {
        if let Some(indices) = aliases.resolve_transitions(name) {
            for idx in indices {
                if (idx.0 as usize) < covered.len() {
                    covered[idx.0 as usize] = true;
                }
            }
        } else {
            return false;
        }
    }
    covered.iter().all(|&c| c)
}
