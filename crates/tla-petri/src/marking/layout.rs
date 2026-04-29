// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::width::{determine_width_with_invariants, TokenWidth};
use crate::invariant::{compute_p_invariants, find_implied_places, ImpliedPlace};
use crate::petri_net::PetriNet;

/// Configuration for packing markings with optional implied place exclusion.
///
/// When implied places are detected via P-invariants, the packed representation
/// omits them from the hash key, reducing per-state memory. The full marking
/// (including implied places) is reconstructed on unpack.
#[derive(Debug, Clone)]
pub(crate) struct MarkingConfig {
    /// Token storage width.
    pub(crate) width: TokenWidth,
    /// Total number of places in the original net.
    pub(crate) num_places: usize,
    /// Number of places in the packed form (num_places - excluded count).
    pub(crate) packed_len: usize,
    /// Bitset: excluded[i] = true if place i is an implied place.
    pub(super) excluded: Vec<bool>,
    /// Implied places with reconstruction data, sorted by place index.
    pub(super) implied: Vec<ImpliedPlace>,
}

impl MarkingConfig {
    /// Create a config with no excluded places.
    pub(crate) fn standard(num_places: usize, width: TokenWidth) -> Self {
        Self {
            width,
            num_places,
            packed_len: num_places,
            excluded: vec![false; num_places],
            implied: vec![],
        }
    }

    /// Create a config that excludes implied places from the packed form.
    pub(crate) fn with_implied(
        num_places: usize,
        width: TokenWidth,
        implied: Vec<ImpliedPlace>,
    ) -> Self {
        let mut excluded = vec![false; num_places];
        for implied_place in &implied {
            excluded[implied_place.place] = true;
        }
        let packed_len = excluded.iter().filter(|&&is_excluded| !is_excluded).count();
        Self {
            width,
            num_places,
            packed_len,
            excluded,
            implied,
        }
    }

    /// True if any places are excluded.
    #[cfg_attr(not(test), allow(dead_code))]
    #[must_use]
    pub(crate) fn has_exclusions(&self) -> bool {
        !self.implied.is_empty()
    }

    /// Number of excluded (implied) places.
    #[cfg_attr(not(test), allow(dead_code))]
    #[must_use]
    pub(crate) fn num_excluded(&self) -> usize {
        self.implied.len()
    }

    pub(super) fn stored_places(&self) -> impl Iterator<Item = usize> + '_ {
        (0..self.num_places).filter(|&place| !self.excluded[place])
    }

    pub(super) fn implied_places(&self) -> &[ImpliedPlace] {
        &self.implied
    }

    pub(crate) fn excluded_places(&self) -> &[bool] {
        &self.excluded
    }
}

/// Fully analyzed packed-marking layout for an explored Petri net.
#[derive(Debug, Clone)]
pub(crate) struct PreparedMarking {
    pub(crate) config: MarkingConfig,
    pub(crate) width: TokenWidth,
}

impl PreparedMarking {
    /// Derive the packed-marking layout used by exploration backends.
    #[must_use]
    pub(crate) fn analyze(net: &PetriNet) -> Self {
        let invariants = compute_p_invariants(net);
        let width = determine_width_with_invariants(net, &invariants);
        let implied = find_implied_places(&invariants);
        let config = if implied.is_empty() {
            MarkingConfig::standard(net.num_places(), width)
        } else {
            MarkingConfig::with_implied(net.num_places(), width, implied)
        };
        Self { config, width }
    }

    #[must_use]
    pub(crate) fn packed_capacity(&self) -> usize {
        self.packed_places() * self.width.bytes()
    }

    #[must_use]
    pub(crate) fn packed_places(&self) -> usize {
        self.config.packed_len
    }
}
