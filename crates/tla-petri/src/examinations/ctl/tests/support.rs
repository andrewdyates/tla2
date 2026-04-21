// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::HashMap;

use super::super::checker::CtlChecker;
use super::super::resolve::resolve_ctl;

use crate::examinations::query_support::{
    closure_on_reduced_net, ctl_support, relevance_cone_on_reduced_net,
};
use crate::examinations::reachability::protected_places_for_prefire;
use crate::explorer::{explore_full, ExplorationConfig};
use crate::output::Verdict;
use crate::petri_net::{Arc, PetriNet, PlaceIdx, PlaceInfo, TransitionIdx, TransitionInfo};
use crate::property_xml::{CtlFormula, Formula, IntExpr, Property, StatePredicate};
use crate::query_slice::{build_query_local_slice, build_query_slice, QuerySlice};
use crate::reduction::{
    apply_final_place_gcd_scaling, reduce_iterative_structural_with_protected, ReducedNet,
};

pub(super) fn simple_net() -> PetriNet {
    PetriNet {
        name: Some(String::from("test")),
        places: vec![
            PlaceInfo {
                id: String::from("p0"),
                name: None,
            },
            PlaceInfo {
                id: String::from("p1"),
                name: None,
            },
        ],
        transitions: vec![TransitionInfo {
            id: String::from("t0"),
            name: None,
            inputs: vec![Arc {
                place: PlaceIdx(0),
                weight: 1,
            }],
            outputs: vec![Arc {
                place: PlaceIdx(1),
                weight: 1,
            }],
        }],
        initial_marking: vec![2, 0],
    }
}

/// Three-state CTL suffix witness:
/// start -> loop or bad, and loop -> loop or bad.
///
/// This distinguishes:
/// - non-bottom cycle witness for EG(not bad)
/// - reachable exit to bad, so AF(bad) is false
pub(super) fn suffix_cycle_net() -> PetriNet {
    PetriNet {
        name: Some(String::from("suffix-cycle")),
        places: vec![
            PlaceInfo {
                id: String::from("start"),
                name: None,
            },
            PlaceInfo {
                id: String::from("loop"),
                name: None,
            },
            PlaceInfo {
                id: String::from("bad"),
                name: None,
            },
        ],
        transitions: vec![
            TransitionInfo {
                id: String::from("to_loop"),
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
                id: String::from("to_bad_from_start"),
                name: None,
                inputs: vec![Arc {
                    place: PlaceIdx(0),
                    weight: 1,
                }],
                outputs: vec![Arc {
                    place: PlaceIdx(2),
                    weight: 1,
                }],
            },
            TransitionInfo {
                id: String::from("stay_loop"),
                name: None,
                inputs: vec![Arc {
                    place: PlaceIdx(1),
                    weight: 1,
                }],
                outputs: vec![Arc {
                    place: PlaceIdx(1),
                    weight: 1,
                }],
            },
            TransitionInfo {
                id: String::from("exit_bad"),
                name: None,
                inputs: vec![Arc {
                    place: PlaceIdx(1),
                    weight: 1,
                }],
                outputs: vec![Arc {
                    place: PlaceIdx(2),
                    weight: 1,
                }],
            },
        ],
        initial_marking: vec![1, 0, 0],
    }
}

/// Three-state acyclic CTL suffix net:
/// start -> mid -> bad.
///
/// This distinguishes:
/// - no cycle or deadlock inside not-bad region, so EG(not bad) is false
/// - every maximal path reaches bad, so AF(bad) is true
pub(super) fn suffix_exit_net() -> PetriNet {
    PetriNet {
        name: Some(String::from("suffix-exit")),
        places: vec![
            PlaceInfo {
                id: String::from("start"),
                name: None,
            },
            PlaceInfo {
                id: String::from("mid"),
                name: None,
            },
            PlaceInfo {
                id: String::from("bad"),
                name: None,
            },
        ],
        transitions: vec![
            TransitionInfo {
                id: String::from("to_mid"),
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
                id: String::from("to_bad"),
                name: None,
                inputs: vec![Arc {
                    place: PlaceIdx(1),
                    weight: 1,
                }],
                outputs: vec![Arc {
                    place: PlaceIdx(2),
                    weight: 1,
                }],
            },
        ],
        initial_marking: vec![1, 0, 0],
    }
}

pub(super) fn make_ctl_prop(id: &str, ctl: CtlFormula) -> Property {
    Property {
        id: id.to_string(),
        formula: Formula::Ctl(ctl),
    }
}

pub(super) fn reduce_with_ctl_protection(net: &PetriNet, properties: &[Property]) -> ReducedNet {
    let identity = ReducedNet::identity(net);
    let place_map: HashMap<&str, PlaceIdx> = net
        .places
        .iter()
        .enumerate()
        .map(|(i, place)| (place.id.as_str(), PlaceIdx(i as u32)))
        .collect();
    let trans_map: HashMap<&str, TransitionIdx> = net
        .transitions
        .iter()
        .enumerate()
        .map(|(i, transition)| (transition.id.as_str(), TransitionIdx(i as u32)))
        .collect();
    let protected = ctl_support(&identity, properties, &place_map, &trans_map)
        .map(|support| protected_places_for_prefire(net, &support))
        .unwrap_or_else(|| vec![true; net.num_places()]);
    let mut reduced = reduce_iterative_structural_with_protected(net, &protected)
        .expect("reduction should succeed");
    apply_final_place_gcd_scaling(&mut reduced).expect("GCD scaling should succeed");
    reduced
}

pub(super) fn build_ctl_slice(
    net: &PetriNet,
    properties: &[Property],
) -> Option<(ReducedNet, QuerySlice)> {
    let reduced = reduce_with_ctl_protection(net, properties);
    let place_map: HashMap<&str, PlaceIdx> = net
        .places
        .iter()
        .enumerate()
        .map(|(i, place)| (place.id.as_str(), PlaceIdx(i as u32)))
        .collect();
    let trans_map: HashMap<&str, TransitionIdx> = net
        .transitions
        .iter()
        .enumerate()
        .map(|(i, transition)| (transition.id.as_str(), TransitionIdx(i as u32)))
        .collect();

    let support = ctl_support(&reduced, properties, &place_map, &trans_map)?;

    // Mirror production strategy: use deep slice when no EX/AX in the batch.
    let use_deep = !super::super::ctl_batch_contains_next_step(properties);
    if use_deep {
        let cone = relevance_cone_on_reduced_net(&reduced.net, support);
        let slice = build_query_local_slice(&reduced.net, &cone)?;
        Some((reduced, slice))
    } else {
        let closure = closure_on_reduced_net(&reduced.net, support);
        let slice = build_query_slice(&reduced.net, &closure)?;
        Some((reduced, slice))
    }
}

pub(super) fn check_ctl_properties_unsliced(
    net: &PetriNet,
    properties: &[Property],
    config: &ExplorationConfig,
) -> Vec<(String, Verdict)> {
    let reduced = reduce_with_ctl_protection(net, properties);
    let place_map: HashMap<&str, PlaceIdx> = net
        .places
        .iter()
        .enumerate()
        .map(|(i, place)| (place.id.as_str(), PlaceIdx(i as u32)))
        .collect();
    let trans_map: HashMap<&str, TransitionIdx> = net
        .transitions
        .iter()
        .enumerate()
        .map(|(i, transition)| (transition.id.as_str(), TransitionIdx(i as u32)))
        .collect();

    let config = config.refitted_for_net(&reduced.net);
    let mut full = explore_full(&reduced.net, &config);
    if !full.graph.completed {
        return properties
            .iter()
            .map(|prop| (prop.id.clone(), Verdict::CannotCompute))
            .collect();
    }

    for marking in &mut full.markings {
        *marking = reduced
            .expand_marking(marking)
            .expect("marking expansion should succeed");
    }

    let checker = CtlChecker::new(&full, net);
    properties
        .iter()
        .map(|prop| {
            let verdict = match &prop.formula {
                Formula::Ctl(ctl) => {
                    let (_, unresolved) =
                        super::super::count_unresolved_ctl(ctl, &place_map, &trans_map);
                    if unresolved > 0 {
                        Verdict::CannotCompute
                    } else {
                        let resolved = resolve_ctl(ctl, &place_map, &trans_map);
                        if checker.eval(&resolved)[0] {
                            Verdict::True
                        } else {
                            Verdict::False
                        }
                    }
                }
                _ => Verdict::CannotCompute,
            };
            (prop.id.clone(), verdict)
        })
        .collect()
}

/// Two disconnected components: A (a0→ta→a1) and B (b0→tb→b1).
/// A formula referencing only component A should be sliced away from B.
pub(super) fn disconnected_two_component_net() -> PetriNet {
    PetriNet {
        name: Some(String::from("disconnected")),
        places: vec![
            PlaceInfo {
                id: String::from("a0"),
                name: None,
            },
            PlaceInfo {
                id: String::from("a1"),
                name: None,
            },
            PlaceInfo {
                id: String::from("b0"),
                name: None,
            },
            PlaceInfo {
                id: String::from("b1"),
                name: None,
            },
        ],
        transitions: vec![
            TransitionInfo {
                id: String::from("ta"),
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
                id: String::from("tb"),
                name: None,
                inputs: vec![Arc {
                    place: PlaceIdx(2),
                    weight: 1,
                }],
                outputs: vec![Arc {
                    place: PlaceIdx(3),
                    weight: 1,
                }],
            },
        ],
        initial_marking: vec![1, 0, 1, 0],
    }
}

pub(super) fn component_a_ctl_props() -> Vec<Property> {
    vec![
        make_ctl_prop(
            "slice-a",
            CtlFormula::EF(Box::new(CtlFormula::Atom(StatePredicate::IntLe(
                IntExpr::Constant(1),
                IntExpr::TokensCount(vec![String::from("a1")]),
            )))),
        ),
        make_ctl_prop(
            "slice-fire",
            CtlFormula::EF(Box::new(CtlFormula::Atom(StatePredicate::IsFireable(
                vec![String::from("ta")],
            )))),
        ),
    ]
}

/// Self-contained two-state cycle: P0(1) ↔ P1, T0: P0→P1, T1: P1→P0.
/// Two reachable states, always one transition enabled.
pub(super) fn ctl_budget_cycle_net() -> PetriNet {
    PetriNet {
        name: Some(String::from("ctl-budget-cycle")),
        places: vec![
            PlaceInfo {
                id: String::from("p0"),
                name: None,
            },
            PlaceInfo {
                id: String::from("p1"),
                name: None,
            },
        ],
        transitions: vec![
            TransitionInfo {
                id: String::from("t0"),
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
                id: String::from("t1"),
                name: None,
                inputs: vec![Arc {
                    place: PlaceIdx(1),
                    weight: 1,
                }],
                outputs: vec![Arc {
                    place: PlaceIdx(0),
                    weight: 1,
                }],
            },
        ],
        initial_marking: vec![1, 0],
    }
}

/// AG(is-fireable(t0, t1)) — always at least one transition enabled.
/// Not a simplifier tautology, requires exploring all reachable states.
pub(super) fn ctl_budget_ag_fireable() -> CtlFormula {
    CtlFormula::AG(Box::new(CtlFormula::Atom(StatePredicate::IsFireable(
        vec![String::from("t0"), String::from("t1")],
    ))))
}

/// Initial state has one short witness branch and one noisy branch.
///
/// With `max_states = 3`, full-graph CTL exploration aborts while expanding the
/// initial state's second successor, but a local checker can still prove
/// `EX(AX(goal >= 1))` by following the witness branch first.
pub(super) fn ctl_local_fallback_net() -> PetriNet {
    PetriNet {
        name: Some(String::from("ctl-local-fallback")),
        places: vec![
            PlaceInfo {
                id: String::from("start"),
                name: None,
            },
            PlaceInfo {
                id: String::from("witness"),
                name: None,
            },
            PlaceInfo {
                id: String::from("goal"),
                name: None,
            },
            PlaceInfo {
                id: String::from("noise"),
                name: None,
            },
        ],
        transitions: vec![
            TransitionInfo {
                id: String::from("to_witness"),
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
                id: String::from("to_noise"),
                name: None,
                inputs: vec![Arc {
                    place: PlaceIdx(0),
                    weight: 1,
                }],
                outputs: vec![
                    Arc {
                        place: PlaceIdx(0),
                        weight: 1,
                    },
                    Arc {
                        place: PlaceIdx(3),
                        weight: 1,
                    },
                ],
            },
            TransitionInfo {
                id: String::from("to_goal"),
                name: None,
                inputs: vec![Arc {
                    place: PlaceIdx(1),
                    weight: 1,
                }],
                outputs: vec![Arc {
                    place: PlaceIdx(2),
                    weight: 1,
                }],
            },
            TransitionInfo {
                id: String::from("grow_noise"),
                name: None,
                inputs: vec![Arc {
                    place: PlaceIdx(3),
                    weight: 1,
                }],
                outputs: vec![Arc {
                    place: PlaceIdx(3),
                    weight: 2,
                }],
            },
        ],
        initial_marking: vec![1, 0, 0, 0],
    }
}

pub(super) fn ctl_local_fallback_formula() -> CtlFormula {
    CtlFormula::EX(Box::new(CtlFormula::AX(Box::new(CtlFormula::Atom(
        atom_pred("goal", 1),
    )))))
}

pub(super) fn atom_pred(place: &str, ge_value: u64) -> StatePredicate {
    StatePredicate::IntLe(
        IntExpr::Constant(ge_value),
        IntExpr::TokensCount(vec![place.to_string()]),
    )
}
