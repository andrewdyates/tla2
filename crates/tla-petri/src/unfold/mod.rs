// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Colored-to-P/T net unfolding engine.
//!
//! Takes a [`ColoredNet`] and produces a standard [`PetriNet`] plus
//! [`PropertyAliases`] mapping colored names to unfolded indices.
//!
//! Phase 2: handles `CyclicEnum`, `Dot`, and `Product` sorts.

mod context;
mod places;
mod transitions;

use crate::error::PnmlError;
use crate::hlpnml::ColoredNet;
use crate::model::PropertyAliases;
use crate::petri_net::PetriNet;

use context::UnfoldContext;
use places::unfold_places;
use transitions::unfold_transitions;

/// Maximum number of unfolded places before aborting.
const MAX_UNFOLDED_PLACES: usize = 100_000;
/// Maximum number of unfolded transitions before aborting.
const MAX_UNFOLDED_TRANSITIONS: usize = 500_000;

/// Result of unfolding a colored net.
pub(crate) struct UnfoldedNet {
    pub net: PetriNet,
    pub aliases: PropertyAliases,
}

/// A concrete color value (index into the sort's constant list).
type ColorValue = usize;

/// Unfold a colored net into a standard P/T net.
///
/// Returns the unfolded net and property aliases mapping colored names
/// to their unfolded P/T indices.
///
/// # Errors
///
/// Returns `PnmlError` if the unfolded net exceeds size limits or if
/// the colored net contains unsupported constructs.
pub(crate) fn unfold_to_pt(colored: &ColoredNet) -> Result<UnfoldedNet, PnmlError> {
    let ctx = UnfoldContext::new(colored)?;

    // Phase 1: Unfold places.
    let pu = unfold_places(&ctx, colored)?;

    // Phase 2: Unfold transitions.
    let tu = unfold_transitions(&ctx, colored, &pu)?;

    let net = PetriNet {
        name: colored.name.clone(),
        places: pu.places,
        transitions: tu.transitions,
        initial_marking: pu.initial_marking,
    };

    let aliases = PropertyAliases {
        place_aliases: pu.place_aliases,
        transition_aliases: tu.transition_aliases,
    };

    Ok(UnfoldedNet { net, aliases })
}

#[cfg(test)]
#[path = "../unfold_tests.rs"]
mod tests;
