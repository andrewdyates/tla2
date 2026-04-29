// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::error::PnmlError;
use crate::petri_net::TransitionIdx;

use super::super::ReducedNet;

/// Apply Tapaal-style pre-firing on the reduced net's initial marking.
///
/// This is intentionally opt-in and query-guarded: it mutates the initial
/// marking but does not remove transitions or places. Callers must protect any
/// reduced-net places whose values or fireability atoms are semantically
/// observable in the target examination.
///
/// Matches the upstream Rule Q shape more closely than the earlier local
/// design:
/// - fires a transition as many whole times as the current initial marking
///   allows (`k = min(marking[p] / weight)` over the preset)
/// - requires each preset place to have this transition as its sole consumer
/// - requires preset and postset to be disjoint
/// - leaves the transition in the net so it may still fire later if re-enabled
pub(crate) fn apply_query_guarded_prefire(
    reduced: &mut ReducedNet,
    protected_places: &[bool],
) -> Result<bool, PnmlError> {
    assert_eq!(
        protected_places.len(),
        reduced.net.num_places(),
        "protected place mask must match reduced net place count"
    );

    let mut consumers: Vec<Vec<TransitionIdx>> = vec![Vec::new(); reduced.net.num_places()];
    for (tidx, transition) in reduced.net.transitions.iter().enumerate() {
        let transition_idx = TransitionIdx(tidx as u32);
        for arc in &transition.inputs {
            let slot = &mut consumers[arc.place.0 as usize];
            if !slot.contains(&transition_idx) {
                slot.push(transition_idx);
            }
        }
    }

    let mut changed = false;
    for (tidx, transition) in reduced.net.transitions.iter().enumerate() {
        if transition.inputs.is_empty() {
            continue;
        }

        let preset_postset_disjoint = transition.inputs.iter().all(|input| {
            transition
                .outputs
                .iter()
                .all(|output| output.place != input.place)
        });
        if !preset_postset_disjoint {
            continue;
        }

        let mut fire_count = 0u64;
        let mut eligible = true;
        for arc in &transition.inputs {
            let place = arc.place.0 as usize;
            if protected_places[place]
                || consumers[place].len() != 1
                || consumers[place][0] != TransitionIdx(tidx as u32)
            {
                eligible = false;
                break;
            }

            let enabled_count = reduced.net.initial_marking[place] / arc.weight;
            if enabled_count == 0 {
                eligible = false;
                break;
            }
            fire_count = if fire_count == 0 {
                enabled_count
            } else {
                fire_count.min(enabled_count)
            };
        }

        if !eligible {
            continue;
        }

        if transition
            .outputs
            .iter()
            .any(|arc| protected_places[arc.place.0 as usize])
        {
            continue;
        }

        for arc in &transition.inputs {
            let place = arc.place.0 as usize;
            let consumed =
                arc.weight
                    .checked_mul(fire_count)
                    .ok_or_else(|| PnmlError::ReductionOverflow {
                        context: format!("prefire input overflow on place {place}"),
                    })?;
            reduced.net.initial_marking[place] -= consumed;
        }
        for arc in &transition.outputs {
            let place = arc.place.0 as usize;
            let produced =
                arc.weight
                    .checked_mul(fire_count)
                    .ok_or_else(|| PnmlError::ReductionOverflow {
                        context: format!("prefire output overflow on place {place}"),
                    })?;
            reduced.net.initial_marking[place] = reduced.net.initial_marking[place]
                .checked_add(produced)
                .ok_or_else(|| PnmlError::ReductionOverflow {
                    context: format!("prefire marking overflow on place {place}"),
                })?;
        }
        changed = true;
    }

    Ok(changed)
}
