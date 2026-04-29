// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! CTL/LTL alias-aware temporal support walkers.

use crate::model::PropertyAliases;
use crate::property_xml::{CtlFormula, Formula, LtlFormula, Property, StatePredicate};
use crate::reduction::ReducedNet;
use crate::resolved_predicate::resolve_predicate_with_aliases;

use super::collectors::collect_predicate_support;
use super::types::QuerySupport;

/// Compute the reduced-net support set for a batch of CTL properties.
///
/// Walks each CTL formula tree to find atom predicates, resolves them to
/// original-net indices, and collects the corresponding reduced-net places
/// and transitions. Returns `None` if any atom references a place removed
/// by reduction without a reconstruction.
pub(crate) fn ctl_support_with_aliases(
    reduced: &ReducedNet,
    properties: &[Property],
    aliases: &PropertyAliases,
) -> Option<QuerySupport> {
    let mut support = QuerySupport::new(reduced.net.num_places(), reduced.net.num_transitions());
    for prop in properties {
        if let Formula::Ctl(ctl) = &prop.formula {
            ctl_formula_support_with_aliases(ctl, reduced, aliases, &mut support)?;
        }
    }
    Some(support)
}

fn ctl_formula_support_with_aliases(
    formula: &CtlFormula,
    reduced: &ReducedNet,
    aliases: &PropertyAliases,
    support: &mut QuerySupport,
) -> Option<()> {
    match formula {
        CtlFormula::Atom(pred) => collect_state_predicate_support(pred, reduced, aliases, support),
        CtlFormula::Not(inner)
        | CtlFormula::EX(inner)
        | CtlFormula::AX(inner)
        | CtlFormula::EF(inner)
        | CtlFormula::AF(inner)
        | CtlFormula::EG(inner)
        | CtlFormula::AG(inner) => {
            ctl_formula_support_with_aliases(inner, reduced, aliases, support)
        }
        CtlFormula::And(children) | CtlFormula::Or(children) => {
            for child in children {
                ctl_formula_support_with_aliases(child, reduced, aliases, support)?;
            }
            Some(())
        }
        CtlFormula::EU(phi, psi) | CtlFormula::AU(phi, psi) => {
            ctl_formula_support_with_aliases(phi, reduced, aliases, support)?;
            ctl_formula_support_with_aliases(psi, reduced, aliases, support)
        }
    }
}

/// Compute the reduced-net support set for a single LTL property.
pub(crate) fn ltl_property_support_with_aliases(
    reduced: &ReducedNet,
    property: &Property,
    aliases: &PropertyAliases,
) -> Option<QuerySupport> {
    let mut support = QuerySupport::new(reduced.net.num_places(), reduced.net.num_transitions());
    if let Formula::Ltl(ltl) = &property.formula {
        ltl_formula_support_with_aliases(ltl, reduced, aliases, &mut support)?;
    }
    Some(support)
}

fn ltl_formula_support_with_aliases(
    formula: &LtlFormula,
    reduced: &ReducedNet,
    aliases: &PropertyAliases,
    support: &mut QuerySupport,
) -> Option<()> {
    match formula {
        LtlFormula::Atom(pred) => collect_state_predicate_support(pred, reduced, aliases, support),
        LtlFormula::Not(inner)
        | LtlFormula::Next(inner)
        | LtlFormula::Finally(inner)
        | LtlFormula::Globally(inner) => {
            ltl_formula_support_with_aliases(inner, reduced, aliases, support)
        }
        LtlFormula::And(children) | LtlFormula::Or(children) => {
            for child in children {
                ltl_formula_support_with_aliases(child, reduced, aliases, support)?;
            }
            Some(())
        }
        LtlFormula::Until(phi, psi) => {
            ltl_formula_support_with_aliases(phi, reduced, aliases, support)?;
            ltl_formula_support_with_aliases(psi, reduced, aliases, support)
        }
    }
}

/// Resolve a `StatePredicate` (string-based) to `ResolvedPredicate` (index-based)
/// and collect its support in reduced-net space.
fn collect_state_predicate_support(
    pred: &StatePredicate,
    reduced: &ReducedNet,
    aliases: &PropertyAliases,
    support: &mut QuerySupport,
) -> Option<()> {
    let resolved = resolve_predicate_with_aliases(pred, aliases);
    collect_predicate_support(&resolved, reduced, support)
}

#[cfg(test)]
pub(crate) fn ctl_support(
    reduced: &ReducedNet,
    properties: &[Property],
    place_map: &std::collections::HashMap<&str, crate::petri_net::PlaceIdx>,
    trans_map: &std::collections::HashMap<&str, crate::petri_net::TransitionIdx>,
) -> Option<QuerySupport> {
    let aliases = PropertyAliases {
        place_aliases: place_map
            .iter()
            .map(|(name, idx)| ((*name).to_string(), vec![*idx]))
            .collect(),
        transition_aliases: trans_map
            .iter()
            .map(|(name, idx)| ((*name).to_string(), vec![*idx]))
            .collect(),
    };
    ctl_support_with_aliases(reduced, properties, &aliases)
}
