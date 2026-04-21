// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::error::PnmlError;
use crate::petri_net::{PetriNet, PlaceIdx};

use super::ReducedNet;

fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let r = a % b;
        a = b;
        b = r;
    }
    a
}

fn place_factor(net: &PetriNet, place: PlaceIdx) -> u64 {
    let mut factor = net.initial_marking[place.0 as usize];

    for transition in &net.transitions {
        for arc in transition.inputs.iter().chain(transition.outputs.iter()) {
            if arc.place == place {
                factor = gcd(factor, arc.weight);
            }
        }
    }

    factor
}

pub(crate) fn apply_final_place_gcd_scaling(reduced: &mut ReducedNet) -> Result<(), PnmlError> {
    let factors: Vec<u64> = (0..reduced.net.num_places())
        .map(|idx| place_factor(&reduced.net, PlaceIdx(idx as u32)))
        .collect();

    for (reduced_idx, factor) in factors.into_iter().enumerate() {
        if factor <= 1 {
            continue;
        }

        reduced.net.initial_marking[reduced_idx] /= factor;

        for transition in &mut reduced.net.transitions {
            for arc in transition
                .inputs
                .iter_mut()
                .chain(transition.outputs.iter_mut())
            {
                if arc.place.0 as usize == reduced_idx {
                    arc.weight /= factor;
                }
            }
        }

        let PlaceIdx(orig_idx) = reduced.place_unmap[reduced_idx];
        reduced.place_scales[orig_idx as usize] = reduced.place_scales[orig_idx as usize]
            .checked_mul(factor)
            .ok_or_else(|| PnmlError::ReductionOverflow {
                context: format!("place scale overflow while scaling original place {orig_idx}"),
            })?;
    }

    Ok(())
}
