// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::explorer::ExplorationConfig;
use crate::reduction::ReducedNet;
use crate::stubborn::PorStrategy;

use super::query_support::{reachability_support, visible_transitions_for_support};
use super::reachability::PropertyTracker;

pub(super) fn reachability_por_config(
    reduced: &ReducedNet,
    trackers: &[PropertyTracker],
    config: &ExplorationConfig,
) -> ExplorationConfig {
    let base = config.clone();

    match reachability_support(reduced, trackers)
        .and_then(|support| visible_transitions_for_support(&reduced.net, &support))
    {
        Some(visible) => base.with_por(PorStrategy::SafetyPreserving { visible }),
        None => base,
    }
}
