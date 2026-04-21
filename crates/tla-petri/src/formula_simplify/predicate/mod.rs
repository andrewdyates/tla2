// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! State-predicate simplification using structural facts and LP proofs.
//!
//! Six tiers of proof power applied bottom-up:
//!
//! 1. **Cached per-atom LP truth** — resolve `IntLe` leaves before boolean fold.
//! 2. **Pure boolean folding** — And/Or with True/False, Not of constants.
//! 3. **Structural fireability pruning** — drop disabled transitions.
//! 4. **Deadlock-pattern collapse** — Not(IsFireable(all)) when deadlock-free.
//! 5. **P-invariant implication fold** — pairwise atom rewrites via binary invariants.
//! 6. **Whole-predicate LP proofs** — conjunction-level unreachable/always-true.

mod atom_truth;
mod boolean;
mod implication;
mod structural;
mod whole_lp;

use crate::property_xml::StatePredicate;

use super::SimplificationContext;

use atom_truth::simplify_int_le_atom;
use boolean::boolean_fold;
use implication::implication_fold;
use structural::{deadlock_collapse, fireability_prune};
use whole_lp::lp_prove;

/// Simplify a state predicate using structural facts and LP proofs.
///
/// Returns a semantically equivalent (possibly simpler) predicate.
/// Never strengthens or weakens the original; every rewrite is sound.
pub(crate) fn simplify_predicate_ctx(
    pred: &StatePredicate,
    ctx: &mut SimplificationContext<'_>,
) -> StatePredicate {
    // Recurse into children first (bottom-up).
    let simplified = simplify_children(pred, ctx);

    // Tier 1: per-atom LP truth on IntLe leaves.
    let atom_simplified = simplify_int_le_atom(&simplified, ctx);

    // Tier 2: pure boolean folding.
    let folded = boolean_fold(&atom_simplified);

    // Tier 3: structural fireability pruning.
    let pruned = fireability_prune(&folded, ctx);

    // Tier 4: deadlock-pattern collapse.
    let collapsed = deadlock_collapse(&pruned, ctx);

    // Second boolean fold after structural rewrites.
    let refolded = boolean_fold(&collapsed);

    // Tier 5: P-invariant implication fold (pairwise atom rewrites).
    let implied = implication_fold(&refolded, ctx);
    let rerefolded = boolean_fold(&implied);

    // Tier 6: whole-predicate LP proofs (conjunction-level).
    lp_prove(&rerefolded, ctx)
}

/// Convenience wrapper for test code using the old `(pred, net, facts, aliases)` signature.
#[cfg(test)]
pub(crate) fn simplify_predicate(
    pred: &StatePredicate,
    net: &crate::petri_net::PetriNet,
    facts: &super::facts::SimplificationFacts,
    aliases: &crate::model::PropertyAliases,
) -> StatePredicate {
    let mut ctx = SimplificationContext::new(net, aliases, facts.clone());
    simplify_predicate_ctx(pred, &mut ctx)
}

/// Recurse into children of compound predicates.
fn simplify_children(pred: &StatePredicate, ctx: &mut SimplificationContext<'_>) -> StatePredicate {
    match pred {
        StatePredicate::And(children) => {
            let simplified: Vec<_> = children
                .iter()
                .map(|c| simplify_predicate_ctx(c, ctx))
                .collect();
            StatePredicate::And(simplified)
        }
        StatePredicate::Or(children) => {
            let simplified: Vec<_> = children
                .iter()
                .map(|c| simplify_predicate_ctx(c, ctx))
                .collect();
            StatePredicate::Or(simplified)
        }
        StatePredicate::Not(inner) => {
            StatePredicate::Not(Box::new(simplify_predicate_ctx(inner, ctx)))
        }
        // Leaves: no children to recurse into.
        _ => pred.clone(),
    }
}
