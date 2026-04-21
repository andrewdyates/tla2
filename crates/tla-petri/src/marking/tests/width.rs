// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::{conserving_net, non_conserving_net};
use crate::invariant::{compute_p_invariants, PInvariant};
use crate::marking::{determine_width, determine_width_with_invariants, TokenWidth};
use crate::petri_net::{Arc, PetriNet, PlaceIdx, PlaceInfo, TransitionInfo};

#[test]
fn test_determine_width_conserving_small_total() {
    let net = conserving_net(vec![3, 0]);
    assert_eq!(determine_width(&net), TokenWidth::U8);
}

#[test]
fn test_determine_width_conserving_exactly_u8_boundary() {
    let net = conserving_net(vec![255, 0]);
    assert_eq!(determine_width(&net), TokenWidth::U8);
}

#[test]
fn test_determine_width_conserving_u16() {
    let net = conserving_net(vec![256, 0]);
    assert_eq!(determine_width(&net), TokenWidth::U16);
}

#[test]
fn test_determine_width_conserving_large() {
    let net = conserving_net(vec![70_000, 0]);
    assert_eq!(determine_width(&net), TokenWidth::U64);
}

#[test]
fn test_determine_width_non_conserving_falls_back_to_u64() {
    let net = non_conserving_net();
    assert_eq!(determine_width(&net), TokenWidth::U64);
}

#[test]
fn test_determine_width_empty_net() {
    let net = PetriNet {
        name: None,
        places: vec![],
        transitions: vec![],
        initial_marking: vec![],
    };
    assert_eq!(determine_width(&net), TokenWidth::U8);
}

#[test]
fn test_determine_width_no_transitions() {
    let net = PetriNet {
        name: None,
        places: vec![PlaceInfo {
            id: "p0".into(),
            name: None,
        }],
        transitions: vec![],
        initial_marking: vec![42],
    };
    assert_eq!(determine_width(&net), TokenWidth::U8);
}

#[test]
fn test_token_width_bytes() {
    assert_eq!(TokenWidth::U8.bytes(), 1);
    assert_eq!(TokenWidth::U16.bytes(), 2);
    assert_eq!(TokenWidth::U64.bytes(), 8);
}

#[test]
fn test_invariant_width_empty_invariants_falls_back() {
    let net = conserving_net(vec![300, 0]);
    assert_eq!(determine_width_with_invariants(&net, &[]), TokenWidth::U16);
}

#[test]
fn test_invariant_width_tighter_than_total() {
    let net = PetriNet {
        name: None,
        places: vec![
            PlaceInfo {
                id: "p0".into(),
                name: None,
            },
            PlaceInfo {
                id: "p1".into(),
                name: None,
            },
            PlaceInfo {
                id: "p2".into(),
                name: None,
            },
            PlaceInfo {
                id: "p3".into(),
                name: None,
            },
        ],
        transitions: vec![
            TransitionInfo {
                id: "t0".into(),
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
                id: "t1".into(),
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
            TransitionInfo {
                id: "t2".into(),
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
            TransitionInfo {
                id: "t3".into(),
                name: None,
                inputs: vec![Arc {
                    place: PlaceIdx(3),
                    weight: 1,
                }],
                outputs: vec![Arc {
                    place: PlaceIdx(2),
                    weight: 1,
                }],
            },
        ],
        initial_marking: vec![200, 0, 100, 0],
    };
    assert_eq!(determine_width(&net), TokenWidth::U16);

    let invariants = compute_p_invariants(&net);
    assert_eq!(
        determine_width_with_invariants(&net, &invariants),
        TokenWidth::U8
    );
}

#[test]
fn test_invariant_width_uncovered_place_falls_back() {
    let net = PetriNet {
        name: None,
        places: vec![
            PlaceInfo {
                id: "p0".into(),
                name: None,
            },
            PlaceInfo {
                id: "p1".into(),
                name: None,
            },
            PlaceInfo {
                id: "p2".into(),
                name: None,
            },
        ],
        transitions: vec![
            TransitionInfo {
                id: "t0".into(),
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
                id: "t1".into(),
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
            TransitionInfo {
                id: "t2".into(),
                name: None,
                inputs: vec![],
                outputs: vec![Arc {
                    place: PlaceIdx(2),
                    weight: 1,
                }],
            },
        ],
        initial_marking: vec![3, 2, 0],
    };
    assert_eq!(determine_width(&net), TokenWidth::U64);

    let invariants = compute_p_invariants(&net);
    assert_eq!(
        determine_width_with_invariants(&net, &invariants),
        TokenWidth::U64
    );
}

#[test]
fn test_invariant_width_agrees_on_simple_conserving() {
    let net = conserving_net(vec![3, 0]);
    let invariants = compute_p_invariants(&net);
    assert_eq!(determine_width(&net), TokenWidth::U8);
    assert_eq!(
        determine_width_with_invariants(&net, &invariants),
        TokenWidth::U8
    );
}

#[test]
fn test_invariant_width_weighted_invariant_capped_by_conservation() {
    let net = conserving_net(vec![100, 100]);
    assert_eq!(determine_width(&net), TokenWidth::U8);

    let weighted = PInvariant {
        weights: vec![2, 1],
        token_count: 300,
    };
    assert_eq!(
        determine_width_with_invariants(&net, &[weighted]),
        TokenWidth::U8
    );
}

#[test]
fn test_invariant_width_never_looser() {
    let nets = vec![
        conserving_net(vec![3, 0]),
        conserving_net(vec![255, 0]),
        conserving_net(vec![256, 0]),
        conserving_net(vec![70_000, 0]),
        non_conserving_net(),
    ];
    for net in &nets {
        let base = determine_width(net);
        let invariants = compute_p_invariants(net);
        let tight = determine_width_with_invariants(net, &invariants);
        assert!(
            tight.bytes() <= base.bytes(),
            "invariant width ({}) must not exceed base width ({})",
            tight.bytes(),
            base.bytes()
        );
    }
}
