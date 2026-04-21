// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for closure, relevance cone, and visibility helpers.

use crate::examinations::query_support::{
    closure_on_reduced_net, relevance_cone_on_reduced_net, visible_transitions_for_support,
    QuerySupport,
};
use crate::petri_net::{Arc, PetriNet, PlaceIdx, PlaceInfo, TransitionIdx, TransitionInfo};

fn disconnected_net() -> PetriNet {
    PetriNet {
        name: Some(String::from("disconnected")),
        places: vec![
            PlaceInfo {
                id: String::from("p0"),
                name: None,
            },
            PlaceInfo {
                id: String::from("p1"),
                name: None,
            },
            PlaceInfo {
                id: String::from("q0"),
                name: None,
            },
            PlaceInfo {
                id: String::from("q1"),
                name: None,
            },
        ],
        transitions: vec![
            TransitionInfo {
                id: String::from("tp"),
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
                id: String::from("tq"),
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

#[test]
fn test_closure_keeps_only_connected_component() {
    let net = disconnected_net();
    let seeds = QuerySupport {
        places: vec![true, false, false, false],
        transitions: vec![false, false],
    };

    let closure = closure_on_reduced_net(&net, seeds);
    assert_eq!(closure.places, vec![true, true, false, false]);
    assert_eq!(closure.transitions, vec![true, false]);
}

#[test]
fn test_visible_transitions_for_support_marks_component_neighbors() {
    let net = disconnected_net();
    let support = QuerySupport {
        places: vec![false, true, false, false],
        transitions: vec![false, false],
    };

    assert_eq!(
        visible_transitions_for_support(&net, &support),
        Some(vec![TransitionIdx(0)])
    );
}

/// Net with a forward-only sink tail:
///   p0 --(t0)--> p1, p_sink
///   p_sink --(t_sink)--> p_dead
///
/// Querying p0: the closure keeps everything (connected), but the
/// relevance cone drops p_sink, t_sink, p_dead because they only
/// appear in t0's postset and never feed back.
fn sink_tail_net() -> PetriNet {
    PetriNet {
        name: Some(String::from("sink-tail")),
        places: vec![
            PlaceInfo {
                id: String::from("p0"),
                name: None,
            },
            PlaceInfo {
                id: String::from("p1"),
                name: None,
            },
            PlaceInfo {
                id: String::from("p_sink"),
                name: None,
            },
            PlaceInfo {
                id: String::from("p_dead"),
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
                outputs: vec![
                    Arc {
                        place: PlaceIdx(1),
                        weight: 1,
                    },
                    Arc {
                        place: PlaceIdx(2),
                        weight: 1,
                    },
                ],
            },
            TransitionInfo {
                id: String::from("t_sink"),
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
        initial_marking: vec![1, 0, 0, 0],
    }
}

#[test]
fn test_relevance_cone_drops_sink_tail() {
    let net = sink_tail_net();
    let seeds = QuerySupport {
        places: vec![true, false, false, false],
        transitions: vec![false, false],
    };

    let closure = closure_on_reduced_net(&net, seeds.clone());
    assert_eq!(closure.places, vec![true, true, true, true]);
    assert_eq!(closure.transitions, vec![true, true]);

    let cone = relevance_cone_on_reduced_net(&net, seeds);
    assert_eq!(cone.places, vec![true, false, false, false]);
    assert_eq!(cone.transitions, vec![true, false]);
}

fn feedback_net() -> PetriNet {
    PetriNet {
        name: Some(String::from("feedback")),
        places: vec![
            PlaceInfo {
                id: String::from("p0"),
                name: None,
            },
            PlaceInfo {
                id: String::from("q"),
                name: None,
            },
            PlaceInfo {
                id: String::from("sink"),
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
                outputs: vec![
                    Arc {
                        place: PlaceIdx(1),
                        weight: 1,
                    },
                    Arc {
                        place: PlaceIdx(2),
                        weight: 1,
                    },
                ],
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
        initial_marking: vec![1, 0, 0],
    }
}

#[test]
fn test_relevance_cone_keeps_feedback_path() {
    let net = feedback_net();
    let seeds = QuerySupport {
        places: vec![true, false, false],
        transitions: vec![false, false],
    };

    let cone = relevance_cone_on_reduced_net(&net, seeds);
    assert_eq!(cone.places, vec![true, true, false]);
    assert_eq!(cone.transitions, vec![true, true]);
}
