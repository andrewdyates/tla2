// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Random walk witness search for reachability properties.
//!
//! Lightweight under-approximation: fires random enabled transitions from the
//! initial marking to find witnesses for EF(φ) properties. Cannot prove
//! EF(φ)=FALSE or AG(φ)=TRUE — unresolved trackers remain `verdict: None`
//! and fall through to BFS.
//!
//! Sound because: any marking reached by firing enabled transitions from the
//! initial marking is by definition reachable, so a witness found here is valid.

use std::time::Instant;

use rand::rngs::SmallRng;
use rand::{Rng, SeedableRng};

use crate::examinations::reachability_witness::{
    apply_validated_witnesses, candidates_for_marking, WitnessSeedSource, WitnessValidationContext,
};
use crate::petri_net::{PetriNet, TransitionIdx};

use super::reachability::PropertyTracker;

/// Default number of independent random walks.
const DEFAULT_WALKS: u32 = 1000;

/// Default maximum steps per walk before restarting.
const DEFAULT_MAX_STEPS: u32 = 10_000;

/// Run random walks to find witnesses for unresolved EF(φ) properties.
///
/// For each unresolved `PropertyTracker` where `quantifier == EF` and
/// `verdict.is_none()`, attempt to find a marking satisfying the predicate
/// via random simulation on the original (unreduced) net.
///
/// Also seeds AG(φ)=FALSE by finding counterexamples (markings where ¬φ).
pub(crate) fn run_random_walk_seeding(
    net: &PetriNet,
    trackers: &mut [PropertyTracker],
    validation: &WitnessValidationContext<'_>,
    deadline: Option<Instant>,
) {
    run_random_walk_seeding_params(
        net,
        trackers,
        validation,
        deadline,
        DEFAULT_WALKS,
        DEFAULT_MAX_STEPS,
    );
}

/// Parameterized version for testing.
pub(crate) fn run_random_walk_seeding_params(
    net: &PetriNet,
    trackers: &mut [PropertyTracker],
    validation: &WitnessValidationContext<'_>,
    deadline: Option<Instant>,
    walks: u32,
    max_steps: u32,
) {
    // The initial marking is reachable even if the net has no enabled moves.
    validate_marking(trackers, &net.initial_marking, net, &[], validation);
    if net.num_transitions() == 0 || walks == 0 || all_walkable_resolved(trackers) {
        return;
    }

    let mut rng = SmallRng::from_entropy();
    let mut marking = vec![0u64; net.num_places()];
    let mut enabled = Vec::with_capacity(net.num_transitions());
    let mut path = Vec::with_capacity(max_steps as usize);

    for walk_id in 0..walks {
        // Check deadline and early-exit conditions every 100 walks.
        if walk_id % 100 == 0 {
            if let Some(dl) = deadline {
                if Instant::now() >= dl {
                    break;
                }
            }
            if all_walkable_resolved(trackers) {
                break;
            }
        }

        // Start from initial marking.
        marking.copy_from_slice(&net.initial_marking);
        path.clear();

        for _step in 0..max_steps {
            // Collect enabled transitions.
            enabled.clear();
            for t in 0..net.num_transitions() {
                let tidx = TransitionIdx(t as u32);
                if net.is_enabled(&marking, tidx) {
                    enabled.push(tidx);
                }
            }

            // Deadlock: no enabled transitions, restart walk.
            if enabled.is_empty() {
                break;
            }

            // Fire a random enabled transition in place.
            let chosen = enabled[rng.gen_range(0..enabled.len())];
            net.apply_delta(&mut marking, chosen);
            path.push(chosen);
            validate_marking(trackers, &marking, net, &path, validation);
            if all_walkable_resolved(trackers) {
                break;
            }
        }
    }
}

/// Check if all walkable (EF or AG) trackers have been resolved.
fn all_walkable_resolved(trackers: &[PropertyTracker]) -> bool {
    trackers.iter().all(|t| t.verdict.is_some())
}

fn validate_marking(
    trackers: &mut [PropertyTracker],
    marking: &[u64],
    net: &PetriNet,
    path: &[TransitionIdx],
    validation: &WitnessValidationContext<'_>,
) {
    let candidates =
        candidates_for_marking(trackers, marking, net, WitnessSeedSource::RandomWalk, path);
    apply_validated_witnesses(validation, trackers, candidates);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::examinations::reachability_witness::{
        validation_targets_from_trackers, WitnessValidationContext,
    };
    use crate::petri_net::{Arc, PetriNet, PlaceIdx, PlaceInfo, TransitionInfo};
    use crate::property_xml::PathQuantifier;
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

    /// Build a simple mutex net:
    ///   p_free(2) -> t_enter -> p_critical
    ///   p_critical -> t_exit -> p_free
    ///
    /// Initial: p_free=2, p_critical=0
    /// Reachable: p_critical can reach 1 (but not 2 in a well-designed mutex,
    /// though this net allows it since there's no mutual exclusion guard).
    fn mutex_net() -> PetriNet {
        PetriNet {
            name: Some("mutex".to_string()),
            places: vec![place("p_free"), place("p_critical")],
            transitions: vec![
                transition("t_enter", vec![arc(0, 1)], vec![arc(1, 1)]),
                transition("t_exit", vec![arc(1, 1)], vec![arc(0, 1)]),
            ],
            initial_marking: vec![2, 0],
        }
    }

    /// Build a 1-safe net where tokens(p1) can never reach 100.
    fn one_safe_net() -> PetriNet {
        PetriNet {
            name: Some("one_safe".to_string()),
            places: vec![place("p0"), place("p1")],
            transitions: vec![
                transition("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
                transition("t1", vec![arc(1, 1)], vec![arc(0, 1)]),
            ],
            initial_marking: vec![1, 0],
        }
    }

    /// Build a net that deadlocks after 1 step.
    fn deadlock_net() -> PetriNet {
        PetriNet {
            name: Some("deadlock".to_string()),
            places: vec![place("p0"), place("p1")],
            transitions: vec![
                transition("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
                // No transition to consume from p1 — deadlock after firing t0.
            ],
            initial_marking: vec![1, 0],
        }
    }

    fn ef_tracker(id: &str, pred: ResolvedPredicate) -> PropertyTracker {
        PropertyTracker {
            id: id.to_string(),
            quantifier: PathQuantifier::EF,
            predicate: pred,
            verdict: None,
            resolved_by: None,
            flushed: false,
        }
    }

    fn ag_tracker(id: &str, pred: ResolvedPredicate) -> PropertyTracker {
        PropertyTracker {
            id: id.to_string(),
            quantifier: PathQuantifier::AG,
            predicate: pred,
            verdict: None,
            resolved_by: None,
            flushed: false,
        }
    }

    /// tokens(place) >= threshold as IntLe(Constant(threshold), TokensCount([place])).
    fn tokens_ge(place: u32, threshold: u64) -> ResolvedPredicate {
        ResolvedPredicate::IntLe(
            ResolvedIntExpr::Constant(threshold),
            ResolvedIntExpr::TokensCount(vec![PlaceIdx(place)]),
        )
    }

    #[test]
    fn test_random_walk_finds_witness() {
        let net = mutex_net();
        // EF(tokens(p_critical) >= 1) — should be TRUE (reachable by firing t_enter).
        let pred = tokens_ge(1, 1);
        let mut trackers = vec![ef_tracker("prop1", pred)];
        let targets = validation_targets_from_trackers(&trackers);
        let validation = WitnessValidationContext::new(&net, &targets);

        run_random_walk_seeding_params(&net, &mut trackers, &validation, None, 100, 100);

        assert_eq!(
            trackers[0].verdict,
            Some(true),
            "random walk should find EF witness"
        );
    }

    #[test]
    fn test_random_walk_finds_ag_counterexample() {
        let net = mutex_net();
        // AG(NOT(tokens(p_critical) >= 1)) — FALSE because t_enter makes p_critical >= 1.
        let pred = ResolvedPredicate::Not(Box::new(tokens_ge(1, 1)));
        let mut trackers = vec![ag_tracker("prop_ag", pred)];
        let targets = validation_targets_from_trackers(&trackers);
        let validation = WitnessValidationContext::new(&net, &targets);

        run_random_walk_seeding_params(&net, &mut trackers, &validation, None, 100, 100);

        assert_eq!(
            trackers[0].verdict,
            Some(false),
            "random walk should find AG counterexample"
        );
    }

    #[test]
    fn test_random_walk_unreachable_leaves_none() {
        let net = one_safe_net();
        // EF(tokens(p1) >= 100) — unreachable on a 1-safe net.
        let pred = tokens_ge(1, 100);
        let mut trackers = vec![ef_tracker("prop_unreach", pred)];
        let targets = validation_targets_from_trackers(&trackers);
        let validation = WitnessValidationContext::new(&net, &targets);

        run_random_walk_seeding_params(&net, &mut trackers, &validation, None, 100, 100);

        assert_eq!(
            trackers[0].verdict, None,
            "random walk should not claim FALSE for unreachable EF"
        );
    }

    #[test]
    fn test_random_walk_deadlock_restarts() {
        let net = deadlock_net();
        // EF(tokens(p1) >= 1) — reachable after 1 step (t0 fires once then deadlock).
        let pred = tokens_ge(1, 1);
        let mut trackers = vec![ef_tracker("prop_dead", pred)];
        let targets = validation_targets_from_trackers(&trackers);
        let validation = WitnessValidationContext::new(&net, &targets);

        run_random_walk_seeding_params(&net, &mut trackers, &validation, None, 100, 100);

        assert_eq!(
            trackers[0].verdict,
            Some(true),
            "random walk should find witness before deadlock"
        );
    }

    #[test]
    fn test_random_walk_respects_deadline() {
        let net = one_safe_net();
        let pred = tokens_ge(1, 100);
        let mut trackers = vec![ef_tracker("prop_timeout", pred)];
        let targets = validation_targets_from_trackers(&trackers);
        let validation = WitnessValidationContext::new(&net, &targets);

        // Deadline already passed — should return immediately.
        let deadline = Some(Instant::now());
        run_random_walk_seeding_params(
            &net,
            &mut trackers,
            &validation,
            deadline,
            100_000,
            100_000,
        );

        assert_eq!(
            trackers[0].verdict, None,
            "random walk should respect deadline and not resolve"
        );
    }

    #[test]
    fn test_random_walk_empty_net() {
        let net = PetriNet {
            name: None,
            places: vec![place("p0")],
            transitions: vec![],
            initial_marking: vec![5],
        };
        let pred = tokens_ge(0, 10);
        let mut trackers = vec![ef_tracker("prop_empty", pred)];
        let targets = validation_targets_from_trackers(&trackers);
        let validation = WitnessValidationContext::new(&net, &targets);

        run_random_walk_seeding_params(&net, &mut trackers, &validation, None, 100, 100);

        assert_eq!(
            trackers[0].verdict, None,
            "empty net should leave verdict as None"
        );
    }

    #[test]
    fn test_random_walk_empty_net_checks_initial_marking() {
        let net = PetriNet {
            name: None,
            places: vec![place("p0")],
            transitions: vec![],
            initial_marking: vec![5],
        };
        let mut ef_trackers = vec![ef_tracker("prop_init_true", tokens_ge(0, 5))];
        let ef_targets = validation_targets_from_trackers(&ef_trackers);
        let ef_validation = WitnessValidationContext::new(&net, &ef_targets);

        run_random_walk_seeding_params(&net, &mut ef_trackers, &ef_validation, None, 100, 100);

        assert_eq!(
            ef_trackers[0].verdict,
            Some(true),
            "initial marking is reachable and should satisfy EF witness checks"
        );

        let pred = ResolvedPredicate::Not(Box::new(tokens_ge(0, 5)));
        let mut ag_trackers = vec![ag_tracker("prop_init_false", pred)];
        let ag_targets = validation_targets_from_trackers(&ag_trackers);
        let ag_validation = WitnessValidationContext::new(&net, &ag_targets);

        run_random_walk_seeding_params(&net, &mut ag_trackers, &ag_validation, None, 100, 100);

        assert_eq!(
            ag_trackers[0].verdict,
            Some(false),
            "initial marking counterexample should seed AG(false) even without transitions"
        );
    }
}
