// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::super::examination_plan::ExecutionPlan;
use super::common::checkpoint_cannot_compute;
use crate::examinations::state_space::{StateSpaceObserver, StateSpaceStats};
use crate::explorer::ExplorationConfig;
use crate::petri_net::PetriNet;
use crate::stubborn::PorStrategy;

pub(crate) fn state_space_stats(
    net: &PetriNet,
    config: &ExplorationConfig,
) -> Option<StateSpaceStats> {
    // Soundness guard (#1483): StateSpace requires state/edge counts of the
    // ORIGINAL net. Structural reduction changes the reachability graph, so
    // reduced-net counts are wrong. We explore the original net directly.
    //
    // When the original net is too large to explore completely, we return
    // None (CANNOT_COMPUTE = 0 pts) instead of reporting wrong counts
    // from the reduced net (-8 pts per wrong value).
    let plan = ExecutionPlan::observer(PorStrategy::None);
    let config = config.refitted_for_net(net);
    let mut observer = StateSpaceObserver::new(&net.initial_marking);
    let result = match plan.run_checkpointable_observer(net, &config, &mut observer) {
        Ok(result) => result,
        Err(error) => {
            let _ = checkpoint_cannot_compute("StateSpace", &error);
            return None;
        }
    };
    if !result.completed {
        return None;
    }

    let stats = observer.stats();
    Some(StateSpaceStats {
        states: stats.states,
        edges: stats.edges,
        max_token_in_place: stats.max_token_in_place,
        max_token_sum: stats.max_token_sum,
    })
}
