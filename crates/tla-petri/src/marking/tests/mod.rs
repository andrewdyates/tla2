// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::petri_net::{Arc, PetriNet, PlaceIdx, PlaceInfo, TransitionInfo};

mod codec;
mod layout;
mod width;

pub(super) fn conserving_net(initial: Vec<u64>) -> PetriNet {
    PetriNet {
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
        ],
        transitions: vec![TransitionInfo {
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
        }],
        initial_marking: initial,
    }
}

pub(super) fn non_conserving_net() -> PetriNet {
    PetriNet {
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
        ],
        transitions: vec![TransitionInfo {
            id: "t0".into(),
            name: None,
            inputs: vec![Arc {
                place: PlaceIdx(0),
                weight: 1,
            }],
            outputs: vec![Arc {
                place: PlaceIdx(1),
                weight: 2,
            }],
        }],
        initial_marking: vec![5, 0],
    }
}
