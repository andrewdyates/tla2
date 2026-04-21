// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::model::PropertyAliases;
use crate::property_xml::CtlFormula;
use crate::resolved_predicate::{resolve_predicate_with_aliases, ResolvedPredicate};
use tla_mc_core::CtlFormula as GenericCtlFormula;

/// Resolved CTL formula with indices instead of names.
pub(super) type ResolvedCtl = GenericCtlFormula<ResolvedPredicate>;

pub(super) fn resolve_ctl_with_aliases(
    formula: &CtlFormula,
    aliases: &PropertyAliases,
) -> ResolvedCtl {
    match formula {
        CtlFormula::Atom(predicate) => {
            ResolvedCtl::Atom(resolve_predicate_with_aliases(predicate, aliases))
        }
        CtlFormula::Not(inner) => {
            ResolvedCtl::Not(Box::new(resolve_ctl_with_aliases(inner, aliases)))
        }
        CtlFormula::And(children) => ResolvedCtl::And(
            children
                .iter()
                .map(|child| resolve_ctl_with_aliases(child, aliases))
                .collect(),
        ),
        CtlFormula::Or(children) => ResolvedCtl::Or(
            children
                .iter()
                .map(|child| resolve_ctl_with_aliases(child, aliases))
                .collect(),
        ),
        CtlFormula::EX(inner) => {
            ResolvedCtl::EX(Box::new(resolve_ctl_with_aliases(inner, aliases)))
        }
        CtlFormula::AX(inner) => {
            ResolvedCtl::AX(Box::new(resolve_ctl_with_aliases(inner, aliases)))
        }
        CtlFormula::EF(inner) => {
            ResolvedCtl::EF(Box::new(resolve_ctl_with_aliases(inner, aliases)))
        }
        CtlFormula::AF(inner) => {
            ResolvedCtl::AF(Box::new(resolve_ctl_with_aliases(inner, aliases)))
        }
        CtlFormula::EG(inner) => {
            ResolvedCtl::EG(Box::new(resolve_ctl_with_aliases(inner, aliases)))
        }
        CtlFormula::AG(inner) => {
            ResolvedCtl::AG(Box::new(resolve_ctl_with_aliases(inner, aliases)))
        }
        CtlFormula::EU(phi, psi) => ResolvedCtl::EU(
            Box::new(resolve_ctl_with_aliases(phi, aliases)),
            Box::new(resolve_ctl_with_aliases(psi, aliases)),
        ),
        CtlFormula::AU(phi, psi) => ResolvedCtl::AU(
            Box::new(resolve_ctl_with_aliases(phi, aliases)),
            Box::new(resolve_ctl_with_aliases(psi, aliases)),
        ),
    }
}

#[cfg(test)]
pub(super) fn resolve_ctl(
    formula: &CtlFormula,
    place_map: &std::collections::HashMap<&str, crate::petri_net::PlaceIdx>,
    trans_map: &std::collections::HashMap<&str, crate::petri_net::TransitionIdx>,
) -> ResolvedCtl {
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
    resolve_ctl_with_aliases(formula, &aliases)
}
