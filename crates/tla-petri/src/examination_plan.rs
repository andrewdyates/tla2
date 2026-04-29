// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared observer-vs-graph execution planning for examinations.

use crate::explorer::{
    explore_and_build_graph, explore_checkpointable_observer, explore_observer,
    CheckpointableObserver, ExplorationConfig, ExplorationResult, ParallelExplorationObserver,
    ReachabilityGraph,
};
use crate::petri_net::PetriNet;
use crate::stubborn::PorStrategy;

enum ExecutionShape {
    Observer,
    Graph,
}

pub(crate) struct ExecutionPlan {
    shape: ExecutionShape,
    por: PorStrategy,
}

impl ExecutionPlan {
    pub(crate) fn observer(por: PorStrategy) -> Self {
        Self {
            shape: ExecutionShape::Observer,
            por,
        }
    }

    pub(crate) fn graph() -> Self {
        Self {
            shape: ExecutionShape::Graph,
            por: PorStrategy::None,
        }
    }

    fn config(&self, base: &ExplorationConfig) -> ExplorationConfig {
        base.clone().with_por(self.por.clone())
    }

    pub(crate) fn run_observer<O>(
        &self,
        net: &PetriNet,
        base: &ExplorationConfig,
        observer: &mut O,
    ) -> ExplorationResult
    where
        O: ParallelExplorationObserver + Send,
    {
        debug_assert!(matches!(self.shape, ExecutionShape::Observer));
        let config = self.config(base);
        explore_observer(net, &config, observer)
    }

    pub(crate) fn run_checkpointable_observer<O>(
        &self,
        net: &PetriNet,
        base: &ExplorationConfig,
        observer: &mut O,
    ) -> std::io::Result<ExplorationResult>
    where
        O: ParallelExplorationObserver + CheckpointableObserver + Send,
    {
        debug_assert!(matches!(self.shape, ExecutionShape::Observer));
        let config = self.config(base);
        if config.checkpoint().is_some() {
            explore_checkpointable_observer(net, &config, observer)
        } else {
            Ok(explore_observer(net, &config, observer))
        }
    }

    pub(crate) fn run_graph(&self, net: &PetriNet, base: &ExplorationConfig) -> ReachabilityGraph {
        debug_assert!(matches!(self.shape, ExecutionShape::Graph));
        let config = self.config(base);
        explore_and_build_graph(net, &config)
    }
}
