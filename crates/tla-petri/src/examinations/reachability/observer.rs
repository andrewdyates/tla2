// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Runtime observation types for reachability examinations.

use crate::explorer::{
    CheckpointableObserver, ExplorationObserver, ParallelExplorationObserver,
    ParallelExplorationSummary,
};
use crate::petri_net::{PetriNet, TransitionIdx};
use crate::property_xml::PathQuantifier;
#[cfg(test)]
use crate::property_xml::{Formula, Property, ReachabilityFormula};
use crate::resolved_predicate::eval_predicate;
#[cfg(test)]
use crate::resolved_predicate::resolve_predicate_with_aliases;
use serde::{Deserialize, Serialize};

use super::types::{resolve_tracker, PropertyTracker, ReachabilityResolutionSource};
#[cfg(test)]
use crate::model::PropertyAliases;

/// Observer for ReachabilityCardinality and ReachabilityFireability.
pub(crate) struct ReachabilityObserver<'a> {
    net: &'a PetriNet,
    trackers: Vec<PropertyTracker>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct ReachabilityCheckpointSnapshot {
    trackers: Vec<PropertyTracker>,
}

impl<'a> ReachabilityObserver<'a> {
    /// Create an observer for reachability properties.
    ///
    /// Resolves place and transition names against the net. Non-Reachability
    /// formula properties are silently skipped.
    #[cfg(test)]
    #[must_use]
    pub(crate) fn new(net: &'a PetriNet, properties: &[Property]) -> Self {
        let aliases = PropertyAliases::identity(net);

        let trackers = properties
            .iter()
            .filter_map(|prop| {
                let Formula::Reachability(ReachabilityFormula {
                    quantifier,
                    predicate,
                }) = &prop.formula
                else {
                    return None;
                };
                let resolved = resolve_predicate_with_aliases(predicate, &aliases);
                Some(PropertyTracker {
                    id: prop.id.clone(),
                    quantifier: *quantifier,
                    predicate: resolved,
                    verdict: None,
                    resolved_by: None,
                    flushed: false,
                })
            })
            .collect();

        Self { net, trackers }
    }

    /// Create an observer from pre-resolved trackers with optional seed verdicts.
    ///
    /// Used by BMC integration: trackers that already have `verdict = Some(...)`
    /// from BMC witness discovery are skipped during BFS exploration.
    #[must_use]
    pub(crate) fn from_trackers(net: &'a PetriNet, trackers: Vec<PropertyTracker>) -> Self {
        Self { net, trackers }
    }

    pub(super) fn into_trackers(self) -> Vec<PropertyTracker> {
        self.trackers
    }

    /// Returns (property_id, verdict) for each property.
    /// `None` verdict means the exploration was inconclusive.
    #[cfg_attr(not(test), allow(dead_code))]
    #[must_use]
    pub(crate) fn results(&self) -> Vec<(&str, Option<bool>)> {
        self.trackers
            .iter()
            .map(|t| (t.id.as_str(), t.verdict))
            .collect()
    }

    /// Returns definitive verdicts assuming full exploration completed.
    #[cfg_attr(not(test), allow(dead_code))]
    #[must_use]
    pub(crate) fn results_completed(&self) -> Vec<(&str, bool)> {
        self.trackers
            .iter()
            .map(|t| {
                let v = t.verdict.unwrap_or(match t.quantifier {
                    PathQuantifier::EF => false, // never found a witness
                    PathQuantifier::AG => true,  // never found a counterexample
                });
                (t.id.as_str(), v)
            })
            .collect()
    }

    /// Check if all properties have definitive verdicts (can early-terminate).
    fn all_decided(&self) -> bool {
        self.trackers.iter().all(|t| t.verdict.is_some())
    }
}

impl ExplorationObserver for ReachabilityObserver<'_> {
    fn on_new_state(&mut self, marking: &[u64]) -> bool {
        for tracker in &mut self.trackers {
            if tracker.verdict.is_some() {
                continue;
            }
            let sat = eval_predicate(&tracker.predicate, marking, self.net);
            match tracker.quantifier {
                PathQuantifier::EF => {
                    if sat {
                        resolve_tracker(
                            tracker,
                            true,
                            ReachabilityResolutionSource::BfsWitness,
                            None,
                        );
                    }
                }
                PathQuantifier::AG => {
                    if !sat {
                        resolve_tracker(
                            tracker,
                            false,
                            ReachabilityResolutionSource::BfsCounterexample,
                            None,
                        );
                    }
                }
            }
        }
        !self.all_decided()
    }

    fn on_transition_fire(&mut self, _trans: TransitionIdx) -> bool {
        true
    }

    fn on_deadlock(&mut self, _marking: &[u64]) {}

    fn is_done(&self) -> bool {
        self.all_decided()
    }
}

pub(crate) struct ReachabilitySummary<'a> {
    net: &'a PetriNet,
    trackers: Vec<PropertyTracker>,
}

impl ReachabilitySummary<'_> {
    fn all_decided(&self) -> bool {
        self.trackers
            .iter()
            .all(|tracker| tracker.verdict.is_some())
    }
}

impl ParallelExplorationSummary for ReachabilitySummary<'_> {
    fn on_new_state(&mut self, marking: &[u64]) {
        for tracker in &mut self.trackers {
            if tracker.verdict.is_some() {
                continue;
            }
            let sat = eval_predicate(&tracker.predicate, marking, self.net);
            match tracker.quantifier {
                PathQuantifier::EF => {
                    if sat {
                        resolve_tracker(
                            tracker,
                            true,
                            ReachabilityResolutionSource::BfsWitness,
                            None,
                        );
                    }
                }
                PathQuantifier::AG => {
                    if !sat {
                        resolve_tracker(
                            tracker,
                            false,
                            ReachabilityResolutionSource::BfsCounterexample,
                            None,
                        );
                    }
                }
            }
        }
    }

    fn on_transition_fire(&mut self, _trans: TransitionIdx) {}

    fn on_deadlock(&mut self, _marking: &[u64]) {}

    fn stop_requested(&self) -> bool {
        self.all_decided()
    }
}

impl<'a> ParallelExplorationObserver for ReachabilityObserver<'a> {
    type Summary = ReachabilitySummary<'a>;

    fn new_summary(&self) -> Self::Summary {
        ReachabilitySummary {
            net: self.net,
            trackers: self.trackers.clone(),
        }
    }

    fn merge_summary(&mut self, summary: Self::Summary) {
        for (tracker, merged) in self.trackers.iter_mut().zip(summary.trackers) {
            if tracker.verdict.is_none() {
                tracker.verdict = merged.verdict;
                tracker.resolved_by = merged.resolved_by;
            }
        }
    }
}

impl CheckpointableObserver for ReachabilityObserver<'_> {
    type Snapshot = ReachabilityCheckpointSnapshot;

    const CHECKPOINT_KIND: &'static str = "ReachabilityObserver";

    fn snapshot(&self) -> Self::Snapshot {
        ReachabilityCheckpointSnapshot {
            trackers: self.trackers.clone(),
        }
    }

    fn restore_from_snapshot(&mut self, snapshot: Self::Snapshot) {
        self.trackers = snapshot.trackers;
    }
}
