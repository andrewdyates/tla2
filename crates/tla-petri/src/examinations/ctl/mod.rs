// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! CTL model checking via fixpoint iteration on finite state graphs.
//!
//! Evaluates CTL formulas bottom-up by computing satisfying state sets.
//! Uses backward BFS for least fixpoints (EF, EU, AF, AU) and iterative
//! removal for greatest fixpoints (EG, AG).
//!
//! Deadlock semantics follow the MCC convention (maximal-path):
//! - EX(φ) at deadlock = FALSE (no successor exists)
//! - AX(φ) at deadlock = TRUE (vacuously true)
//! - EG(φ) at deadlock = φ (maximal path is just the state itself)

mod checker;
mod local_checker;
mod pipeline;
mod resolve;
mod routing;

#[cfg(test)]
mod tests;

use crate::explorer::ExplorationConfig;
use crate::model::PropertyAliases;
use crate::output::Verdict;
use crate::petri_net::PetriNet;
#[cfg(test)]
use crate::property_xml::CtlFormula;
use crate::property_xml::Property;

#[cfg(test)]
pub(crate) use routing::{
    classify_shallow_ctl, classify_shallow_ctl_suffix, ShallowCtl, ShallowCtlSuffix,
};

#[cfg(test)]
pub(crate) use routing::{ctl_batch_contains_next_step, ctl_formula_contains_next_step};

// Historical MCC 2024 CTL wrong-answer IDs. The deadlock/maximal-path
// semantics fix retired these production guards, but tests still consume the
// centralized slice to prevent silent reintroduction.
const KNOWN_MCC_CTL_SOUNDNESS_GUARDS: &[&str] = &[];

#[derive(Clone, Copy, PartialEq, Eq)]
enum SoundnessGuardMode {
    Enforce,
    #[cfg(test)]
    Ignore,
}

fn is_known_mcc_ctl_soundness_guard(property_id: &str) -> bool {
    KNOWN_MCC_CTL_SOUNDNESS_GUARDS.contains(&property_id)
}

#[cfg(test)]
pub(crate) fn known_mcc_ctl_soundness_guards() -> &'static [&'static str] {
    KNOWN_MCC_CTL_SOUNDNESS_GUARDS
}

/// Run CTL model checking for a set of properties.
///
/// Returns `(property_id, verdict)` for each property.
///
/// Safety: returns `CannotCompute` for any formula with unresolved place or
/// transition names. Silent name drops during resolution produce degenerate
/// predicates (`False` for is-fireable, `0` for tokens-count) that corrupt
/// evaluation results.
#[cfg(test)]
pub(crate) fn check_ctl_properties(
    net: &PetriNet,
    properties: &[Property],
    config: &ExplorationConfig,
) -> Vec<(String, Verdict)> {
    let aliases = PropertyAliases::identity(net);
    pipeline::check_ctl_properties_inner(
        net,
        properties,
        &aliases,
        config,
        SoundnessGuardMode::Enforce,
        false,
    )
}

pub(crate) fn check_ctl_properties_with_aliases(
    net: &PetriNet,
    properties: &[Property],
    aliases: &PropertyAliases,
    config: &ExplorationConfig,
) -> Vec<(String, Verdict)> {
    pipeline::check_ctl_properties_inner(
        net,
        properties,
        aliases,
        config,
        SoundnessGuardMode::Enforce,
        false,
    )
}

pub(crate) fn check_ctl_properties_with_flush(
    net: &PetriNet,
    properties: &[Property],
    aliases: &PropertyAliases,
    config: &ExplorationConfig,
) -> Vec<(String, Verdict)> {
    pipeline::check_ctl_properties_inner(
        net,
        properties,
        aliases,
        config,
        SoundnessGuardMode::Enforce,
        true,
    )
}

#[cfg(test)]
pub(crate) fn check_ctl_properties_ignoring_soundness_guards(
    net: &PetriNet,
    properties: &[Property],
    config: &ExplorationConfig,
) -> Vec<(String, Verdict)> {
    let aliases = PropertyAliases::identity(net);
    pipeline::check_ctl_properties_inner(
        net,
        properties,
        &aliases,
        config,
        SoundnessGuardMode::Ignore,
        false,
    )
}

#[cfg(test)]
fn count_unresolved_ctl(
    formula: &CtlFormula,
    place_map: &std::collections::HashMap<&str, crate::petri_net::PlaceIdx>,
    trans_map: &std::collections::HashMap<&str, crate::petri_net::TransitionIdx>,
) -> (usize, usize) {
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
    pipeline::count_unresolved_ctl_with_aliases(formula, &aliases)
}
