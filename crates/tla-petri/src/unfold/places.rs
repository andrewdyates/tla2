// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Place expansion and initial-marking evaluation for colored-net unfolding.

use std::collections::HashMap;

use crate::error::PnmlError;
use crate::hlpnml::{ColorExpr, ColorSort, ColoredNet};
use crate::petri_net::{PlaceIdx, PlaceInfo};

use super::context::UnfoldContext;
use super::{ColorValue, MAX_UNFOLDED_PLACES};

/// Result of unfolding all colored places.
pub(super) struct PlaceUnfolding {
    pub(super) places: Vec<PlaceInfo>,
    pub(super) initial_marking: Vec<u64>,
    pub(super) place_aliases: HashMap<String, Vec<PlaceIdx>>,
    /// Map: (colored_place_id, color_value) → PlaceIdx in unfolded net.
    pub(super) place_map: HashMap<(String, ColorValue), PlaceIdx>,
    pub(super) place_sort_ids: HashMap<String, String>,
}

/// Unfold all colored places into P/T places.
pub(super) fn unfold_places(
    ctx: &UnfoldContext,
    colored: &ColoredNet,
) -> Result<PlaceUnfolding, PnmlError> {
    let mut places = Vec::new();
    let mut initial_marking = Vec::new();
    let mut place_aliases: HashMap<String, Vec<PlaceIdx>> = HashMap::new();
    let mut place_map: HashMap<(String, ColorValue), PlaceIdx> = HashMap::new();
    let place_sort_ids: HashMap<String, String> = colored
        .places
        .iter()
        .map(|place| (place.id.clone(), place.sort_id.clone()))
        .collect();

    for cp in &colored.places {
        let sort = ctx.sort_for_place(cp)?;
        let cardinality = ctx.sort_cardinality(sort)?;
        let sort_name = sort.name().to_string();
        let constants = ctx.sort_value_names(sort)?;

        let mut alias_indices = Vec::with_capacity(cardinality);

        // Evaluate initial marking per color.
        let marking_per_color = ctx.eval_initial_marking(cp, sort)?;

        for (color_idx, constant_name) in constants.iter().enumerate() {
            let pidx = PlaceIdx(places.len() as u32);

            if places.len() >= MAX_UNFOLDED_PLACES {
                return Err(PnmlError::UnsupportedNetType {
                    net_type: format!(
                        "unfolded net exceeds {} places (model too large)",
                        MAX_UNFOLDED_PLACES
                    ),
                });
            }

            let unfolded_id = format!("{}_{}", cp.id, constant_name);
            places.push(PlaceInfo {
                id: unfolded_id,
                name: None,
            });

            initial_marking.push(marking_per_color[color_idx]);

            place_map.insert((cp.id.clone(), color_idx), pidx);
            alias_indices.push(pidx);
        }

        // Register aliases: both the place id and name map to all unfolded copies.
        place_aliases.insert(cp.id.clone(), alias_indices.clone());
        if let Some(ref name) = cp.name {
            if name != &cp.id {
                place_aliases.insert(name.clone(), alias_indices.clone());
            }
        }
        // Also register by sort name for `tokens-count` on sort names.
        place_aliases
            .entry(sort_name)
            .or_default()
            .extend_from_slice(&alias_indices);
    }

    Ok(PlaceUnfolding {
        places,
        initial_marking,
        place_aliases,
        place_map,
        place_sort_ids,
    })
}

// ---------------------------------------------------------------------------
// Marking evaluation (impl UnfoldContext)
// ---------------------------------------------------------------------------

impl UnfoldContext {
    /// Evaluate initial marking per color value.
    pub(super) fn eval_initial_marking(
        &self,
        place: &crate::hlpnml::ColoredPlace,
        sort: &ColorSort,
    ) -> Result<Vec<u64>, PnmlError> {
        let cardinality = self.sort_cardinality(sort)?;
        let mut marking = vec![0u64; cardinality];

        match &place.initial_marking {
            None => {} // No initial marking = all zeros.
            Some(ColorExpr::All { .. }) => {
                marking.fill(1);
            }
            Some(expr) => {
                self.eval_marking_expr(expr, sort, &mut marking)?;
            }
        }

        Ok(marking)
    }

    /// Evaluate a marking expression, adding tokens to the per-color vector.
    fn eval_marking_expr(
        &self,
        expr: &ColorExpr,
        sort: &ColorSort,
        marking: &mut [u64],
    ) -> Result<(), PnmlError> {
        match expr {
            ColorExpr::All { .. } => {
                for m in marking.iter_mut() {
                    *m += 1;
                }
            }
            ColorExpr::NumberOf { count, color } => {
                let empty_binding = HashMap::new();
                if let Some(idx) = self.eval_color_value_for_sort(color, &empty_binding, sort)? {
                    marking[idx] += count;
                } else {
                    // Variable in initial marking — treat as "all" with multiplicity.
                    for m in marking.iter_mut() {
                        *m += count;
                    }
                }
            }
            ColorExpr::Add(children) => {
                for child in children {
                    self.eval_marking_expr(child, sort, marking)?;
                }
            }
        }
        Ok(())
    }
}
