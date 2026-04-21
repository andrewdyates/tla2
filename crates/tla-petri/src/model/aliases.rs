// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::{HashMap, HashSet};

use crate::petri_net::{PetriNet, PlaceIdx, TransitionIdx};

/// One-to-many alias tables mapping MCC property names to net indices.
///
/// For P/T nets every alias vector has length 1 (identity mapping).
/// For colored nets each colored name maps to its unfolded indices.
#[derive(Debug, Clone)]
pub(crate) struct PropertyAliases {
    pub(crate) place_aliases: HashMap<String, Vec<PlaceIdx>>,
    pub(crate) transition_aliases: HashMap<String, Vec<TransitionIdx>>,
}

impl PropertyAliases {
    /// Build identity aliases from a P/T net: each place/transition ID
    /// maps to exactly itself.
    pub(crate) fn identity(net: &PetriNet) -> Self {
        let mut place_aliases = HashMap::with_capacity(net.places.len());
        let mut transition_aliases = HashMap::with_capacity(net.transitions.len());

        for (i, place) in net.places.iter().enumerate() {
            let idx = PlaceIdx(i as u32);
            place_aliases.insert(place.id.clone(), vec![idx]);
            if let Some(ref name) = place.name {
                if name != &place.id {
                    place_aliases.insert(name.clone(), vec![idx]);
                }
            }
        }

        for (i, trans) in net.transitions.iter().enumerate() {
            let idx = TransitionIdx(i as u32);
            transition_aliases.insert(trans.id.clone(), vec![idx]);
            if let Some(ref name) = trans.name {
                if name != &trans.id {
                    transition_aliases.insert(name.clone(), vec![idx]);
                }
            }
        }

        Self {
            place_aliases,
            transition_aliases,
        }
    }

    #[must_use]
    pub(crate) fn resolve_places(&self, name: &str) -> Option<&[PlaceIdx]> {
        self.place_aliases
            .get(name)
            .map(Vec::as_slice)
            .filter(|indices| !indices.is_empty())
    }

    #[must_use]
    pub(crate) fn resolve_transitions(&self, name: &str) -> Option<&[TransitionIdx]> {
        self.transition_aliases
            .get(name)
            .map(Vec::as_slice)
            .filter(|indices| !indices.is_empty())
    }

    /// Extract colored place groups for OneSafe checking.
    ///
    /// Returns groups of unfolded place indices that share a colored parent.
    /// For P/T nets (identity aliases), all groups have size 1, so this
    /// returns an empty vec (no grouping needed). For colored nets, groups
    /// with size > 1 indicate multi-color places.
    #[must_use]
    pub(crate) fn colored_place_groups(&self) -> Vec<Vec<usize>> {
        let mut seen = HashSet::new();
        let mut groups = Vec::new();
        for indices in self.place_aliases.values() {
            if indices.len() <= 1 {
                continue;
            }
            let mut key: Vec<usize> = indices.iter().map(|idx| idx.0 as usize).collect();
            key.sort_unstable();
            if seen.insert(key.clone()) {
                groups.push(key);
            }
        }
        groups
    }
}
