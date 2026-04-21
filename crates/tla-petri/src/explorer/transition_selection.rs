// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::petri_net::{PetriNet, TransitionIdx};
use crate::stubborn::{compute_stubborn_set, DependencyGraph, PorStrategy};

pub(crate) fn enabled_transitions_into(
    net: &PetriNet,
    marking: &[u64],
    num_transitions: usize,
    dep_graph: Option<&DependencyGraph>,
    por_strategy: &PorStrategy,
    out: &mut Vec<TransitionIdx>,
) {
    out.clear();

    if let Some(transitions) =
        dep_graph.and_then(|dep| compute_stubborn_set(net, marking, dep, por_strategy))
    {
        out.extend(transitions);
        return;
    }

    for tidx in 0..num_transitions {
        let trans = TransitionIdx(tidx as u32);
        if net.is_enabled(marking, trans) {
            out.push(trans);
        }
    }
}
