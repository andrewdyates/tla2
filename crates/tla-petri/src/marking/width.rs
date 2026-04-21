// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::invariant::{structural_place_bound, PInvariant};
use crate::petri_net::PetriNet;

/// Token storage width for memory-efficient BFS exploration.
///
/// Determined by structural analysis of the Petri net. For token-conserving
/// nets (every transition preserves total token count), the maximum tokens
/// in any single place is bounded by the initial total token count, enabling
/// up to 8x memory savings per stored state.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum TokenWidth {
    /// All reachable token counts fit in u8 (<= 255). 8x savings.
    U8,
    /// All reachable token counts fit in u16 (<= 65535). 4x savings.
    U16,
    /// Full u64 width. No savings.
    U64,
}

impl TokenWidth {
    /// Bytes per token value.
    #[must_use]
    pub fn bytes(self) -> usize {
        match self {
            Self::U8 => 1,
            Self::U16 => 2,
            Self::U64 => 8,
        }
    }
}

/// Determine the compact token width for a Petri net.
///
/// For token-conserving nets (every transition has equal total input and
/// output weights), the total token count is invariant across all reachable
/// markings. This bounds max(any place) <= total(initial marking), enabling
/// compact storage when the total is small.
///
/// Non-conserving nets fall back to full u64 width.
pub(crate) fn determine_width(net: &PetriNet) -> TokenWidth {
    let conserving = net.transitions.iter().all(|transition| {
        let in_weight: u64 = transition.inputs.iter().map(|arc| arc.weight).sum();
        let out_weight: u64 = transition.outputs.iter().map(|arc| arc.weight).sum();
        in_weight == out_weight
    });

    if !conserving {
        return TokenWidth::U64;
    }

    let total: u64 = net.initial_marking.iter().sum();
    if total <= u8::MAX as u64 {
        TokenWidth::U8
    } else if total <= u16::MAX as u64 {
        TokenWidth::U16
    } else {
        TokenWidth::U64
    }
}

/// Determine compact token width using P-invariant structural bounds.
///
/// Strictly tighter than [`determine_width`] for nets where P-invariants
/// provide per-place bounds even when the net is not globally conserving,
/// or where invariant bounds are tighter than the initial token total.
///
/// Falls back to [`determine_width`] if `invariants` is empty or any
/// place is uncovered by invariants.
pub(crate) fn determine_width_with_invariants(
    net: &PetriNet,
    invariants: &[PInvariant],
) -> TokenWidth {
    if invariants.is_empty() || net.places.is_empty() {
        return determine_width(net);
    }

    let mut max_bound: u64 = 0;
    for place in 0..net.num_places() {
        match structural_place_bound(invariants, place) {
            Some(bound) => max_bound = max_bound.max(bound),
            None => return determine_width(net),
        }
    }

    let invariant_width = if max_bound <= u8::MAX as u64 {
        TokenWidth::U8
    } else if max_bound <= u16::MAX as u64 {
        TokenWidth::U16
    } else {
        TokenWidth::U64
    };

    let base_width = determine_width(net);
    if invariant_width.bytes() < base_width.bytes() {
        invariant_width
    } else {
        base_width
    }
}
