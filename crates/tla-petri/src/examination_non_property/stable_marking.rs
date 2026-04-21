// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::super::super::examination_plan::ExecutionPlan;
use super::common::checkpoint_cannot_compute;
use crate::examinations::global_properties_bmc;
use crate::examinations::global_properties_pdr;
use crate::examinations::stable_marking::StableMarkingObserver;
use crate::explorer::{
    explore_observer, CheckpointableObserver, ExplorationConfig, ExplorationObserver,
    ParallelExplorationObserver, ParallelExplorationSummary,
};
use crate::output::Verdict;
use crate::petri_net::{PetriNet, TransitionIdx};
use crate::reduction::{analyze, ReducedNet};
use crate::stubborn::PorStrategy;
use serde::{Deserialize, Serialize};

/// Observer for StableMarking on colored models.
///
/// Checks group-level stability: a colored place group is "stable" if the
/// sum of tokens across all unfolded instances stays constant.
#[derive(Debug, Clone, Serialize, Deserialize)]
struct ColoredStableMarkingObserver {
    groups: Vec<Vec<usize>>,
    initial_sums: Vec<u64>,
    unstable: Vec<bool>,
    unstable_count: usize,
}

impl ExplorationObserver for ColoredStableMarkingObserver {
    fn on_new_state(&mut self, marking: &[u64]) -> bool {
        for (gi, group) in self.groups.iter().enumerate() {
            if !self.unstable[gi] {
                let sum: u64 = group.iter().map(|&p| marking[p]).sum();
                if sum != self.initial_sums[gi] {
                    self.unstable[gi] = true;
                    self.unstable_count += 1;
                    if self.unstable_count == self.groups.len() {
                        return false; // all groups unstable
                    }
                }
            }
        }
        true
    }

    fn on_transition_fire(&mut self, _trans: TransitionIdx) -> bool {
        true
    }

    fn on_deadlock(&mut self, _marking: &[u64]) {}

    fn is_done(&self) -> bool {
        self.unstable_count == self.groups.len()
    }
}

struct ColoredStableMarkingSummary {
    groups: Vec<Vec<usize>>,
    initial_sums: Vec<u64>,
    unstable: Vec<bool>,
}

impl ParallelExplorationSummary for ColoredStableMarkingSummary {
    fn on_new_state(&mut self, marking: &[u64]) {
        for (gi, group) in self.groups.iter().enumerate() {
            if !self.unstable[gi] {
                let sum: u64 = group.iter().map(|&p| marking[p]).sum();
                if sum != self.initial_sums[gi] {
                    self.unstable[gi] = true;
                }
            }
        }
    }

    fn on_transition_fire(&mut self, _trans: TransitionIdx) {}
    fn on_deadlock(&mut self, _marking: &[u64]) {}

    fn stop_requested(&self) -> bool {
        self.unstable.iter().all(|&u| u)
    }
}

impl ParallelExplorationObserver for ColoredStableMarkingObserver {
    type Summary = ColoredStableMarkingSummary;

    fn new_summary(&self) -> Self::Summary {
        ColoredStableMarkingSummary {
            groups: self.groups.clone(),
            initial_sums: self.initial_sums.clone(),
            unstable: vec![false; self.groups.len()],
        }
    }

    fn merge_summary(&mut self, summary: Self::Summary) {
        for (gi, unstable) in summary.unstable.into_iter().enumerate() {
            if unstable && !self.unstable[gi] {
                self.unstable[gi] = true;
                self.unstable_count += 1;
            }
        }
    }
}

impl CheckpointableObserver for ColoredStableMarkingObserver {
    type Snapshot = Self;

    const CHECKPOINT_KIND: &'static str = "ColoredStableMarkingObserver";

    fn snapshot(&self) -> Self::Snapshot {
        self.clone()
    }

    fn restore_from_snapshot(&mut self, snapshot: Self::Snapshot) {
        *self = snapshot;
    }
}

pub(crate) fn stable_marking_verdict(
    net: &PetriNet,
    config: &ExplorationConfig,
    colored_groups: &[Vec<usize>],
) -> Verdict {
    // Check for structurally stable places on the ORIGINAL (pre-reduction)
    // net. A place is truly stable only if every transition in the original
    // net has zero net effect on it. We must NOT use reduced.report here
    // because iterative reduction (agglomerations) can remove transitions
    // that affect a place, making it appear constant in the reduced net
    // while it is NOT constant in the original net.
    let pre_reduction = analyze(net);
    if !colored_groups.is_empty() {
        // Colored: a colored place group is structurally stable if every
        // transition has zero net effect on the group sum.
        let has_stable_group = colored_groups.iter().any(|group| {
            net.transitions.iter().all(|t| {
                let flow_in: i64 = t
                    .inputs
                    .iter()
                    .filter(|a| group.contains(&(a.place.0 as usize)))
                    .map(|a| a.weight as i64)
                    .sum();
                let flow_out: i64 = t
                    .outputs
                    .iter()
                    .filter(|a| group.contains(&(a.place.0 as usize)))
                    .map(|a| a.weight as i64)
                    .sum();
                flow_in == flow_out
            })
        });
        if has_stable_group {
            return Verdict::True;
        }
    } else {
        let has_structurally_stable =
            !pre_reduction.constant_places.is_empty() || !pre_reduction.isolated_places.is_empty();
        if has_structurally_stable {
            return Verdict::True;
        }
    }

    // For colored models, skip reduction and BFS on original net with
    // group-level stability check (group-level token accounting through
    // reduction is complex and potentially unsound).
    if !colored_groups.is_empty() {
        let initial_group_sums: Vec<u64> = colored_groups
            .iter()
            .map(|g| g.iter().map(|&p| net.initial_marking[p]).sum())
            .collect();
        let n_groups = colored_groups.len();
        let mut observer = ColoredStableMarkingObserver {
            groups: colored_groups.to_vec(),
            initial_sums: initial_group_sums,
            unstable: vec![false; n_groups],
            unstable_count: 0,
        };
        let result = if config.checkpoint().is_some() {
            match crate::explorer::explore_checkpointable_observer(net, config, &mut observer) {
                Ok(result) => result,
                Err(error) => return checkpoint_cannot_compute("StableMarking", &error),
            }
        } else {
            explore_observer(net, config, &mut observer)
        };
        return if observer.unstable_count == colored_groups.len() {
            Verdict::False
        } else if result.completed {
            Verdict::True
        } else {
            Verdict::CannotCompute
        };
    }

    // --- Identity net (no reduction) ---
    // Structural reductions are currently unsound for StableMarking: on nets
    // like FMS-PT-*, agglomeration suppresses dynamic behavior, making places
    // appear constant when they are not (flipping FALSE to TRUE). Use the
    // identity net until a sound reduction contract is validated.
    let reduced = ReducedNet::identity(net);
    let config = config.refitted_for_net(&reduced.net);

    // SMT-based BMC + k-induction for stability on the reduced net.
    // Even when inconclusive, partial per-place instability seeds the observer.
    let mut bmc_unstable =
        match global_properties_bmc::run_stable_marking_bmc(&reduced.net, config.deadline()) {
            Some(result) => {
                if let Some(verdict) = result.verdict {
                    return if verdict {
                        Verdict::True
                    } else {
                        Verdict::False
                    };
                }
                result.unstable
            }
            None => vec![false; reduced.net.num_places()],
        };

    // PDR/IC3 for StableMarking: proves individual places stable or unstable.
    // Merges results with BMC to seed the BFS observer.
    if let Some(pdr_result) =
        global_properties_pdr::run_stable_marking_pdr(&reduced.net, config.deadline())
    {
        if let Some(verdict) = pdr_result.verdict {
            return if verdict {
                Verdict::True
            } else {
                Verdict::False
            };
        }
        // Merge PDR instability results with BMC results.
        for (i, &pdr_unstable) in pdr_result.unstable.iter().enumerate() {
            if pdr_unstable {
                bmc_unstable[i] = true;
            }
        }
    }

    // POR: StableMarking checks ALL places against their initial values, so
    // every transition is visible (any transition changes some place's count).
    // SafetyPreserving would degenerate to full exploration. No benefit.
    let plan = ExecutionPlan::observer(PorStrategy::None);
    // Seed the observer with BMC results so BFS starts with known-unstable
    // places already eliminated.
    let mut observer =
        StableMarkingObserver::new_seeded(&reduced.net.initial_marking, &bmc_unstable);
    let result = match plan.run_checkpointable_observer(&reduced.net, &config, &mut observer) {
        Ok(result) => result,
        Err(error) => return checkpoint_cannot_compute("StableMarking", &error),
    };

    if observer.all_unstable() {
        Verdict::False
    } else if result.completed {
        Verdict::True
    } else {
        Verdict::CannotCompute
    }
}
