// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! OneSafe examination.
//!
//! Checks whether the net is 1-safe: no place ever holds more than 1 token
//! in any reachable marking. Stops immediately on counterexample.

use crate::explorer::{
    CheckpointableObserver, ExplorationConfig, ExplorationObserver, ParallelExplorationObserver,
    ParallelExplorationSummary,
};
use crate::petri_net::{PetriNet, TransitionIdx};
use crate::reduction::ReducedNet;
use crate::stubborn::PorStrategy;
use serde::{Deserialize, Serialize};

/// Observer that stops when any place exceeds 1 token.
///
/// For colored models, "1-safe" means no *colored* place holds more than
/// 1 token total (sum across all color instances). The `colored_groups`
/// field maps each colored place to its unfolded PT place indices. When
/// groups are empty, the observer checks individual PT places (standard).
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub(crate) struct OneSafeObserver {
    not_safe: bool,
    /// Groups of unfolded place indices that share a colored parent.
    /// Empty for PT nets (no grouping needed).
    colored_groups: Vec<Vec<usize>>,
}

impl OneSafeObserver {
    #[must_use]
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Create an observer for colored models with place groups.
    ///
    /// Each group is a set of unfolded place indices that correspond to the
    /// same colored place. OneSafe for colored nets means no group's sum
    /// exceeds 1.
    #[must_use]
    pub(crate) fn new_colored(colored_groups: Vec<Vec<usize>>) -> Self {
        Self {
            not_safe: false,
            colored_groups,
        }
    }

    /// Returns true if the net is 1-safe (no place ever exceeds 1 token).
    /// Only meaningful if exploration completed or a counterexample was found.
    #[must_use]
    pub(crate) fn is_safe(&self) -> bool {
        !self.not_safe
    }
}

fn one_safe_risky_places(net: &PetriNet) -> Vec<bool> {
    crate::invariant::structural_place_bounds(net)
        .into_iter()
        .map(|bound| !matches!(bound, Some(value) if value <= 1))
        .collect()
}

fn visible_transitions_for_one_safe(net: &PetriNet, risky_places: &[bool]) -> Vec<TransitionIdx> {
    net.transitions
        .iter()
        .enumerate()
        .filter_map(|(idx, transition)| {
            let touches_risky = transition
                .inputs
                .iter()
                .chain(transition.outputs.iter())
                .any(|arc| risky_places[arc.place.0 as usize]);
            touches_risky.then_some(TransitionIdx(idx as u32))
        })
        .collect()
}

/// Build an `ExplorationConfig` with POR for OneSafe.
///
/// Places already proven structurally 1-safe on the reduced net cannot witness
/// a counterexample, so transitions touching only those places may remain
/// invisible to the safety-preserving stubborn-set closure.
pub(crate) fn one_safe_por_config(
    reduced: &ReducedNet,
    config: &ExplorationConfig,
) -> ExplorationConfig {
    let base = config.clone();

    let risky_places = one_safe_risky_places(&reduced.net);
    if !risky_places.iter().any(|risky| *risky) {
        return base;
    }

    let visible = visible_transitions_for_one_safe(&reduced.net, &risky_places);
    if visible.is_empty() || visible.len() >= reduced.net.num_transitions() {
        return base;
    }

    base.with_por(PorStrategy::SafetyPreserving { visible })
}

impl ExplorationObserver for OneSafeObserver {
    fn on_new_state(&mut self, marking: &[u64]) -> bool {
        if !self.colored_groups.is_empty() {
            // Colored model: check that no colored place group sum exceeds 1.
            for group in &self.colored_groups {
                let sum: u64 = group.iter().map(|&p| marking[p]).sum();
                if sum > 1 {
                    self.not_safe = true;
                    return false;
                }
            }
        } else if marking.iter().any(|&t| t > 1) {
            self.not_safe = true;
            return false; // stop exploration
        }
        true
    }

    fn on_transition_fire(&mut self, _trans: TransitionIdx) -> bool {
        true
    }

    fn on_deadlock(&mut self, _marking: &[u64]) {}

    fn is_done(&self) -> bool {
        self.not_safe
    }
}

pub(crate) struct OneSafeSummary {
    not_safe: bool,
    /// Cloned from parent observer for colored group checking.
    colored_groups: Vec<Vec<usize>>,
}

impl ParallelExplorationSummary for OneSafeSummary {
    fn on_new_state(&mut self, marking: &[u64]) {
        if !self.colored_groups.is_empty() {
            for group in &self.colored_groups {
                let sum: u64 = group.iter().map(|&p| marking[p]).sum();
                if sum > 1 {
                    self.not_safe = true;
                    return;
                }
            }
        } else if marking.iter().any(|&t| t > 1) {
            self.not_safe = true;
        }
    }

    fn on_transition_fire(&mut self, _trans: TransitionIdx) {}

    fn on_deadlock(&mut self, _marking: &[u64]) {}

    fn stop_requested(&self) -> bool {
        self.not_safe
    }
}

impl ParallelExplorationObserver for OneSafeObserver {
    type Summary = OneSafeSummary;

    fn new_summary(&self) -> Self::Summary {
        OneSafeSummary {
            not_safe: false,
            colored_groups: self.colored_groups.clone(),
        }
    }

    fn merge_summary(&mut self, summary: Self::Summary) {
        self.not_safe |= summary.not_safe;
    }
}

impl CheckpointableObserver for OneSafeObserver {
    type Snapshot = Self;

    const CHECKPOINT_KIND: &'static str = "OneSafeObserver";

    fn snapshot(&self) -> Self::Snapshot {
        self.clone()
    }

    fn restore_from_snapshot(&mut self, snapshot: Self::Snapshot) {
        *self = snapshot;
    }
}
