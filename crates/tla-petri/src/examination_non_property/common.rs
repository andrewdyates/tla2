// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::error::PnmlError;
use crate::output::Verdict;
use crate::petri_net::{self, PetriNet, PlaceIdx, TransitionIdx};
use crate::reduction::ReducedNet;

pub(super) fn reduction_cannot_compute(examination: &str, error: &PnmlError) -> Verdict {
    eprintln!("{examination}: CANNOT_COMPUTE ({error})");
    Verdict::CannotCompute
}

pub(super) fn checkpoint_cannot_compute(examination: &str, error: &std::io::Error) -> Verdict {
    eprintln!("{examination}: CANNOT_COMPUTE (checkpoint error: {error})");
    Verdict::CannotCompute
}

/// Re-add self-loop transitions to the reduced net.
///
/// Self-loop transitions (zero net effect) are removed by the reduction
/// pipeline because they don't change the marking. However, they ARE real
/// fireable transitions and their absence is unsound for:
/// - **Deadlock**: a state with only self-loop transitions enabled is NOT dead.
/// - **QuasiLiveness**: a self-loop must fire at least once to be quasi-live.
/// - **Liveness**: a self-loop must be fireable from every reachable marking.
///
/// For each self-loop transition that was removed by the reduction pipeline,
/// remap its arcs to reduced-net coordinates and add it back. Constant places
/// with sufficient tokens are dropped from the arc list (always satisfied).
/// Transitions that reference removed places with insufficient tokens are
/// skipped entirely (can never fire). Returns the number of self-loops that
/// were skipped because they are provably dead -- callers that need all
/// transitions to be fireable (quasi-liveness, liveness) should check this.
#[allow(dead_code)] // Retained for future deadlock-safe reduction re-enablement (#1506)
pub(super) fn restore_self_loops(reduced: &mut ReducedNet, original_net: &PetriNet) -> u32 {
    if reduced.report.self_loop_transitions.is_empty() {
        return 0;
    }

    let mut skipped = 0u32;
    for &TransitionIdx(t) in &reduced.report.self_loop_transitions {
        let orig = &original_net.transitions[t as usize];
        let mut remapped_inputs = Vec::new();
        let mut skip = false;

        for arc in &orig.inputs {
            let orig_place = arc.place.0 as usize;
            if let Some(new_place) = reduced.place_map[orig_place] {
                let scale = reduced.place_scales[orig_place];
                // Self-loop arcs always divide evenly by GCD scale
                // because both input and output have the same weight.
                let scaled_weight = arc.weight / scale;
                remapped_inputs.push(petri_net::Arc {
                    place: new_place,
                    weight: scaled_weight,
                });
            } else if let Some(value) = reduced.constant_value(PlaceIdx(orig_place as u32)) {
                if value < arc.weight {
                    skip = true;
                    break;
                }
                // Constant place with sufficient tokens - arc always satisfied.
            } else {
                // Place removed (isolated/redundant), tokens unknown - skip.
                skip = true;
                break;
            }
        }

        if skip {
            skipped += 1;
            continue;
        }

        // Self-loop outputs mirror inputs; remap the same way.
        let mut remapped_outputs = Vec::new();
        for arc in &orig.outputs {
            let orig_place = arc.place.0 as usize;
            if let Some(new_place) = reduced.place_map[orig_place] {
                let scale = reduced.place_scales[orig_place];
                remapped_outputs.push(petri_net::Arc {
                    place: new_place,
                    weight: arc.weight / scale,
                });
            }
            // Removed places: no output arc needed (tokens go nowhere).
        }

        let new_tidx = TransitionIdx(reduced.net.transitions.len() as u32);
        reduced.net.transitions.push(petri_net::TransitionInfo {
            id: orig.id.clone(),
            name: orig.name.clone(),
            inputs: remapped_inputs,
            outputs: remapped_outputs,
        });
        reduced.transition_map[t as usize] = Some(new_tidx);
        reduced.transition_unmap.push(TransitionIdx(t));
    }
    skipped
}
