// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared witness validation boundary for reachability seeders.

use crate::petri_net::{PetriNet, TransitionIdx};
use crate::property_xml::PathQuantifier;
use crate::resolved_predicate::{eval_predicate, ResolvedPredicate};

use super::reachability::{resolve_tracker, PropertyTracker, ReachabilityResolutionSource};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum WitnessSeedSource {
    RandomWalk,
    Heuristic,
}

impl WitnessSeedSource {
    fn as_str(self) -> &'static str {
        match self {
            Self::RandomWalk => "random-walk",
            Self::Heuristic => "heuristic",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct WitnessCandidate {
    pub(crate) tracker_slot: usize,
    pub(crate) source: WitnessSeedSource,
    pub(crate) trace: Vec<TransitionIdx>,
}

#[derive(Debug, Clone)]
pub(crate) struct WitnessValidationTarget {
    pub(crate) original_predicate: ResolvedPredicate,
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct WitnessValidationContext<'a> {
    net: &'a PetriNet,
    targets: &'a [WitnessValidationTarget],
}

impl<'a> WitnessValidationContext<'a> {
    #[must_use]
    pub(crate) fn new(net: &'a PetriNet, targets: &'a [WitnessValidationTarget]) -> Self {
        Self { net, targets }
    }
}

#[cfg(test)]
#[must_use]
pub(crate) fn validation_targets_from_trackers(
    trackers: &[PropertyTracker],
) -> Vec<WitnessValidationTarget> {
    trackers
        .iter()
        .map(|tracker| WitnessValidationTarget {
            original_predicate: tracker.predicate.clone(),
        })
        .collect()
}

#[must_use]
pub(crate) fn candidates_for_marking(
    trackers: &[PropertyTracker],
    marking: &[u64],
    net: &PetriNet,
    source: WitnessSeedSource,
    trace: &[TransitionIdx],
) -> Vec<WitnessCandidate> {
    let trace = trace.to_vec();
    trackers
        .iter()
        .enumerate()
        .filter_map(|(slot, tracker)| {
            if tracker.verdict.is_some() {
                return None;
            }
            let sat = eval_predicate(&tracker.predicate, marking, net);
            let matched = match tracker.quantifier {
                PathQuantifier::EF => sat,
                PathQuantifier::AG => !sat,
            };
            matched.then(|| WitnessCandidate {
                tracker_slot: slot,
                source,
                trace: trace.clone(),
            })
        })
        .collect()
}

pub(crate) fn apply_validated_witnesses(
    ctx: &WitnessValidationContext<'_>,
    trackers: &mut [PropertyTracker],
    candidates: impl IntoIterator<Item = WitnessCandidate>,
) -> usize {
    candidates
        .into_iter()
        .filter(|candidate| apply_validated_witness(ctx, trackers, candidate))
        .count()
}

fn apply_validated_witness(
    ctx: &WitnessValidationContext<'_>,
    trackers: &mut [PropertyTracker],
    candidate: &WitnessCandidate,
) -> bool {
    let Some(tracker) = trackers.get_mut(candidate.tracker_slot) else {
        eprintln!(
            "Reachability witness rejected: {} supplied out-of-range slot {}",
            candidate.source.as_str(),
            candidate.tracker_slot,
        );
        return false;
    };
    if tracker.verdict.is_some() {
        return false;
    }

    let Some(target) = ctx.targets.get(candidate.tracker_slot) else {
        eprintln!(
            "Reachability witness rejected: {} missing validation target for {}",
            candidate.source.as_str(),
            tracker.id,
        );
        return false;
    };

    let mut marking = ctx.net.initial_marking.clone();
    for &transition in &candidate.trace {
        if !ctx.net.is_enabled(&marking, transition) {
            eprintln!(
                "Reachability witness rejected: {} trace disabled for {} at {:?}",
                candidate.source.as_str(),
                tracker.id,
                transition,
            );
            return false;
        }
        ctx.net.apply_delta(&mut marking, transition);
    }

    let sat = eval_predicate(&target.original_predicate, &marking, ctx.net);
    let validated = match tracker.quantifier {
        PathQuantifier::EF => sat,
        PathQuantifier::AG => !sat,
    };
    if !validated {
        eprintln!(
            "Reachability witness rejected: {} original predicate mismatch for {}",
            candidate.source.as_str(),
            tracker.id,
        );
        return false;
    }

    let source = match candidate.source {
        WitnessSeedSource::RandomWalk => ReachabilityResolutionSource::RandomWalk,
        WitnessSeedSource::Heuristic => ReachabilityResolutionSource::Heuristic,
    };
    let verdict = matches!(tracker.quantifier, PathQuantifier::EF);
    resolve_tracker(tracker, verdict, source, None);
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::petri_net::{Arc, PlaceIdx, PlaceInfo, TransitionInfo};
    use crate::resolved_predicate::{ResolvedIntExpr, ResolvedPredicate};

    fn arc(place: u32, weight: u64) -> Arc {
        Arc {
            place: PlaceIdx(place),
            weight,
        }
    }

    fn place(id: &str) -> PlaceInfo {
        PlaceInfo {
            id: id.to_string(),
            name: None,
        }
    }

    fn transition(id: &str, inputs: Vec<Arc>, outputs: Vec<Arc>) -> TransitionInfo {
        TransitionInfo {
            id: id.to_string(),
            name: None,
            inputs,
            outputs,
        }
    }

    fn linear_net() -> PetriNet {
        PetriNet {
            name: Some("linear".to_string()),
            places: vec![place("p0"), place("p1")],
            transitions: vec![transition("t0", vec![arc(0, 1)], vec![arc(1, 1)])],
            initial_marking: vec![1, 0],
        }
    }

    fn tokens_ge(place: u32, threshold: u64) -> ResolvedPredicate {
        ResolvedPredicate::IntLe(
            ResolvedIntExpr::Constant(threshold),
            ResolvedIntExpr::TokensCount(vec![PlaceIdx(place)]),
        )
    }

    fn ef_tracker(id: &str, predicate: ResolvedPredicate) -> PropertyTracker {
        PropertyTracker {
            id: id.to_string(),
            quantifier: PathQuantifier::EF,
            predicate,
            verdict: None,
            resolved_by: None,
            flushed: false,
        }
    }

    fn ag_tracker(id: &str, predicate: ResolvedPredicate) -> PropertyTracker {
        PropertyTracker {
            id: id.to_string(),
            quantifier: PathQuantifier::AG,
            predicate,
            verdict: None,
            resolved_by: None,
            flushed: false,
        }
    }

    #[test]
    fn test_validation_accepts_valid_ef_witness() {
        let net = linear_net();
        let mut trackers = vec![ef_tracker("ef", tokens_ge(1, 1))];
        let targets = validation_targets_from_trackers(&trackers);
        let ctx = WitnessValidationContext::new(&net, &targets);

        let accepted = apply_validated_witnesses(
            &ctx,
            &mut trackers,
            [WitnessCandidate {
                tracker_slot: 0,
                source: WitnessSeedSource::RandomWalk,
                trace: vec![TransitionIdx(0)],
            }],
        );

        assert_eq!(accepted, 1);
        assert_eq!(trackers[0].verdict, Some(true));
    }

    #[test]
    fn test_validation_accepts_valid_ag_counterexample() {
        let net = linear_net();
        let mut trackers = vec![ag_tracker(
            "ag",
            ResolvedPredicate::Not(Box::new(tokens_ge(1, 1))),
        )];
        let targets = validation_targets_from_trackers(&trackers);
        let ctx = WitnessValidationContext::new(&net, &targets);

        let accepted = apply_validated_witnesses(
            &ctx,
            &mut trackers,
            [WitnessCandidate {
                tracker_slot: 0,
                source: WitnessSeedSource::Heuristic,
                trace: vec![TransitionIdx(0)],
            }],
        );

        assert_eq!(accepted, 1);
        assert_eq!(trackers[0].verdict, Some(false));
    }

    #[test]
    fn test_validation_rejects_disabled_trace() {
        let net = linear_net();
        let mut trackers = vec![ef_tracker("ef", tokens_ge(1, 1))];
        let targets = validation_targets_from_trackers(&trackers);
        let ctx = WitnessValidationContext::new(&net, &targets);

        let accepted = apply_validated_witnesses(
            &ctx,
            &mut trackers,
            [WitnessCandidate {
                tracker_slot: 0,
                source: WitnessSeedSource::RandomWalk,
                trace: vec![TransitionIdx(0), TransitionIdx(0)],
            }],
        );

        assert_eq!(accepted, 0);
        assert_eq!(trackers[0].verdict, None);
    }

    #[test]
    fn test_validation_rejects_original_predicate_mismatch() {
        let net = linear_net();
        let mut trackers = vec![ef_tracker("ef", ResolvedPredicate::True)];
        let targets = vec![WitnessValidationTarget {
            original_predicate: tokens_ge(1, 2),
        }];
        let ctx = WitnessValidationContext::new(&net, &targets);

        let accepted = apply_validated_witnesses(
            &ctx,
            &mut trackers,
            [WitnessCandidate {
                tracker_slot: 0,
                source: WitnessSeedSource::Heuristic,
                trace: vec![TransitionIdx(0)],
            }],
        );

        assert_eq!(accepted, 0);
        assert_eq!(trackers[0].verdict, None);
    }
}
