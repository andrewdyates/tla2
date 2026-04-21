// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! LTL atom context: precomputed atom satisfaction for all system states.

use crate::model::PropertyAliases;
use crate::property_xml::StatePredicate;
use crate::resolved_predicate::{resolve_predicate_with_aliases, ResolvedPredicate};

#[cfg(test)]
use crate::explorer::FullReachabilityGraph;
#[cfg(test)]
use crate::petri_net::{PetriNet, PlaceIdx, TransitionIdx};
#[cfg(test)]
use crate::resolved_predicate::eval_predicate;
#[cfg(test)]
use std::collections::HashMap;

/// Preserve the old Buchi atom-resolution entry point as a thin compatibility
/// wrapper over the shared predicate resolver.
pub(crate) fn resolve_atom_with_aliases(
    predicate: &StatePredicate,
    aliases: &PropertyAliases,
) -> ResolvedPredicate {
    resolve_predicate_with_aliases(predicate, aliases)
}

#[cfg(test)]
pub(crate) fn resolve_atom(
    predicate: &StatePredicate,
    place_map: &HashMap<&str, PlaceIdx>,
    trans_map: &HashMap<&str, TransitionIdx>,
) -> ResolvedPredicate {
    crate::resolved_predicate::resolve_predicate(predicate, place_map, trans_map)
}

/// Context for LTL model checking: resolved atoms + system graph.
///
/// Legacy path: used by `product.rs` (pre-built product emptiness).
/// New on-the-fly path evaluates atoms lazily and does not use this struct.
#[cfg(test)]
pub(crate) struct LtlContext<'a> {
    pub full: &'a FullReachabilityGraph,
    /// Precomputed: atom_sat[atom_id][state_id] = whether atom holds at state.
    atom_sat: Vec<Vec<bool>>,
}

#[cfg(test)]
impl<'a> LtlContext<'a> {
    pub fn new(
        atoms: Vec<ResolvedPredicate>,
        full: &'a FullReachabilityGraph,
        net: &'a PetriNet,
    ) -> Self {
        let n = full.graph.num_states as usize;
        let atom_sat: Vec<Vec<bool>> = atoms
            .iter()
            .map(|atom| {
                (0..n)
                    .map(|s| eval_predicate(atom, &full.markings[s], net))
                    .collect()
            })
            .collect();
        Self { full, atom_sat }
    }

    pub(super) fn atom_holds(&self, atom_id: usize, state_id: u32) -> bool {
        self.atom_sat[atom_id][state_id as usize]
    }
}
