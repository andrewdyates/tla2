// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::invariant::{ImpliedPlace, ImpliedPlaceReconstruction};
use crate::marking::{
    pack_marking_config, reconstruct_implied_places, unpack_marking_config, MarkingConfig,
    PreparedMarking, TokenWidth,
};
use crate::petri_net::{Arc, PetriNet, PlaceIdx, PlaceInfo, TransitionInfo};

#[test]
fn test_marking_config_excluded_smaller_packed_size() {
    let implied = vec![ImpliedPlace {
        place: 1,
        reconstruction: ImpliedPlaceReconstruction {
            constant: 6,
            divisor: 1,
            terms: vec![(0, 1), (2, 1)],
        },
    }];

    let config = MarkingConfig::with_implied(3, TokenWidth::U8, implied);
    assert_eq!(config.packed_len, 2);
    assert!(config.has_exclusions());
    assert_eq!(config.num_excluded(), 1);

    let marking = vec![1, 2, 3];
    let mut buf = Vec::new();
    pack_marking_config(&marking, &config, &mut buf);
    assert_eq!(buf.len(), 2);

    let mut out = Vec::new();
    unpack_marking_config(&buf, &config, &mut out);
    assert_eq!(out, vec![1, 2, 3]);
}

#[test]
fn test_marking_config_roundtrip_u16() {
    let implied = vec![ImpliedPlace {
        place: 2,
        reconstruction: ImpliedPlaceReconstruction {
            constant: 1000,
            divisor: 1,
            terms: vec![(0, 1), (1, 1), (3, 1)],
        },
    }];

    let config = MarkingConfig::with_implied(4, TokenWidth::U16, implied);
    let marking = vec![200, 300, 100, 400];

    let mut buf = Vec::new();
    pack_marking_config(&marking, &config, &mut buf);
    assert_eq!(buf.len(), 6);

    let mut out = Vec::new();
    unpack_marking_config(&buf, &config, &mut out);
    assert_eq!(out, marking);
}

#[test]
fn test_marking_config_weighted_reconstruction() {
    let implied = vec![ImpliedPlace {
        place: 0,
        reconstruction: ImpliedPlaceReconstruction {
            constant: 10,
            divisor: 2,
            terms: vec![(1, 1)],
        },
    }];

    let config = MarkingConfig::with_implied(2, TokenWidth::U8, implied);
    let marking = vec![3, 4];

    let mut buf = Vec::new();
    pack_marking_config(&marking, &config, &mut buf);
    assert_eq!(buf.len(), 1);

    let mut out = Vec::new();
    unpack_marking_config(&buf, &config, &mut out);
    assert_eq!(out, vec![3, 4]);
}

#[test]
fn test_marking_config_multiple_excluded_u64() {
    let implied = vec![
        ImpliedPlace {
            place: 1,
            reconstruction: ImpliedPlaceReconstruction {
                constant: 10,
                divisor: 1,
                terms: vec![(0, 1)],
            },
        },
        ImpliedPlace {
            place: 3,
            reconstruction: ImpliedPlaceReconstruction {
                constant: 15,
                divisor: 1,
                terms: vec![(2, 1), (4, 1)],
            },
        },
    ];

    let config = MarkingConfig::with_implied(5, TokenWidth::U64, implied);
    assert_eq!(config.packed_len, 3);
    assert_eq!(config.num_excluded(), 2);

    let marking = vec![7, 3, 5, 6, 4];
    let mut buf = Vec::new();
    pack_marking_config(&marking, &config, &mut buf);
    assert_eq!(buf.len(), 24);

    let mut out = Vec::new();
    unpack_marking_config(&buf, &config, &mut out);
    assert_eq!(out, marking);
}

#[test]
fn test_reconstruct_implied_places_direct() {
    let implied = vec![ImpliedPlace {
        place: 2,
        reconstruction: ImpliedPlaceReconstruction {
            constant: 100,
            divisor: 1,
            terms: vec![(0, 1), (1, 1)],
        },
    }];

    let mut marking = vec![30, 25, 0];
    reconstruct_implied_places(&mut marking, &implied);
    assert_eq!(marking[2], 45);
}

#[test]
fn test_prepared_marking_analyze_detects_implied_places() {
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
                    place: PlaceIdx(2),
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
                    place: PlaceIdx(0),
                    weight: 1,
                }],
            },
        ],
        initial_marking: vec![1, 0, 0],
    };

    let prepared = PreparedMarking::analyze(&net);
    assert_eq!(prepared.width, TokenWidth::U8);
    assert!(prepared.config.has_exclusions());
    assert_eq!(prepared.config.num_excluded(), 1);
    assert_eq!(prepared.packed_places(), 2);
    assert_eq!(prepared.packed_capacity(), 2);
}
