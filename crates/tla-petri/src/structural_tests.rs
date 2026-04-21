// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

pub(super) use super::*;
pub(super) use crate::petri_net::{Arc, PetriNet, PlaceIdx, PlaceInfo, TransitionInfo};

pub(super) fn place(id: &str) -> PlaceInfo {
    PlaceInfo {
        id: id.to_string(),
        name: None,
    }
}

pub(super) fn arc(place: u32, weight: u64) -> Arc {
    Arc {
        place: PlaceIdx(place),
        weight,
    }
}

pub(super) fn trans(id: &str, inputs: Vec<Arc>, outputs: Vec<Arc>) -> TransitionInfo {
    TransitionInfo {
        id: id.to_string(),
        name: None,
        inputs,
        outputs,
    }
}

#[path = "structural_tests/deadlock.rs"]
mod deadlock;
#[path = "structural_tests/live.rs"]
mod live;
#[path = "structural_tests/lp.rs"]
mod lp;
#[path = "structural_tests/set_predicates.rs"]
mod set_predicates;
#[path = "structural_tests/t_semiflow.rs"]
mod t_semiflow;
