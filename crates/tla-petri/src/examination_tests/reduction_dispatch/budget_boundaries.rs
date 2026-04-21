// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Exact-budget boundary tests.
//!
//! These verify that examinations produce correct verdicts (not CANNOT_COMPUTE)
//! when max_states exactly equals the reachable state space size. Off-by-one
//! bugs in the exploration loop or budget check can cause exploration to stop
//! one state short of completing, yielding false CANNOT_COMPUTE results.

use crate::explorer::ExplorationConfig;
use crate::output::Verdict;
use crate::petri_net::{Arc, PetriNet, PlaceIdx, PlaceInfo, TransitionInfo};

use super::super::super::{deadlock_verdict, liveness_verdict};
use super::super::fixtures::counting_net;

fn non_free_choice_budget_net() -> PetriNet {
    PetriNet {
        name: Some("non-free-choice-budget".into()),
        places: vec![
            PlaceInfo {
                id: "P0".into(),
                name: None,
            },
            PlaceInfo {
                id: "P1".into(),
                name: None,
            },
            PlaceInfo {
                id: "P2".into(),
                name: None,
            },
        ],
        transitions: vec![
            TransitionInfo {
                id: "T0".into(),
                name: None,
                inputs: vec![Arc {
                    place: PlaceIdx(0),
                    weight: 1,
                }],
                outputs: vec![Arc {
                    place: PlaceIdx(1),
                    weight: 1,
                }],
            },
            TransitionInfo {
                id: "T1".into(),
                name: None,
                inputs: vec![
                    Arc {
                        place: PlaceIdx(0),
                        weight: 1,
                    },
                    Arc {
                        place: PlaceIdx(1),
                        weight: 1,
                    },
                ],
                outputs: vec![Arc {
                    place: PlaceIdx(2),
                    weight: 1,
                }],
            },
        ],
        initial_marking: vec![1, 1, 0],
    }
}

/// non_free_choice_budget_net has exactly 3 reachable states:
/// [1,1,0], [0,2,0], [0,0,1]. It is not live, and the structural liveness
/// theorem does not apply because the net is non-free-choice.
#[test]
fn test_liveness_exact_budget_completes_not_live() {
    let config = ExplorationConfig::new(3);
    assert_eq!(
        liveness_verdict(&non_free_choice_budget_net(), &config),
        Verdict::False
    );
}

/// Same net, budget=2 — one state short for full graph. However, the deadlock
/// BMC (added as a pre-graph liveness check) finds the reachable deadlock at
/// [0,2,0] (depth 1) and correctly concludes NOT live without needing the
/// full graph at all. Previously this returned CannotCompute.
#[test]
fn test_liveness_tight_budget_resolved_by_bmc() {
    let config = ExplorationConfig::new(2);
    assert_eq!(
        liveness_verdict(&non_free_choice_budget_net(), &config),
        Verdict::False
    );
}

/// counting_net with exact budget: deadlock is reachable (at [0,3]).
/// Budget=4 should allow full exploration.
#[test]
fn test_deadlock_exact_budget_completes() {
    let config = ExplorationConfig::new(4);
    assert_eq!(deadlock_verdict(&counting_net(), &config), Verdict::True);
}
