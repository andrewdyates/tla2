// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::explorer::ExplorationConfig;
use crate::petri_net::{Arc, PetriNet, PlaceIdx, PlaceInfo, TransitionInfo};

/// P0(1) --T0--> P1: fires once, then P1 is a deadlock (no outgoing transition).
pub(super) fn linear_deadlock_net() -> PetriNet {
    PetriNet {
        name: Some("linear-deadlock".into()),
        places: vec![
            PlaceInfo {
                id: "P0".into(),
                name: None,
            },
            PlaceInfo {
                id: "P1".into(),
                name: None,
            },
        ],
        transitions: vec![TransitionInfo {
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
        }],
        initial_marking: vec![1, 0],
    }
}

/// P0(1) <--T0--> P1 (cycle): no deadlocks, 1-safe.
pub(super) fn cyclic_safe_net() -> PetriNet {
    PetriNet {
        name: Some("cycle-safe".into()),
        places: vec![
            PlaceInfo {
                id: "P0".into(),
                name: None,
            },
            PlaceInfo {
                id: "P1".into(),
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

/// No transitions at all; the initial marking is an immediate deadlock.
pub(super) fn immediate_deadlock_net() -> PetriNet {
    PetriNet {
        name: Some("immediate-deadlock".into()),
        places: vec![PlaceInfo {
            id: "P0".into(),
            name: None,
        }],
        transitions: vec![],
        initial_marking: vec![1],
    }
}

/// P0(2) --T0(weight=1)--> P1: token accumulates in P1, not 1-safe.
pub(super) fn not_safe_net() -> PetriNet {
    PetriNet {
        name: Some("not-safe".into()),
        places: vec![
            PlaceInfo {
                id: "P0".into(),
                name: None,
            },
            PlaceInfo {
                id: "P1".into(),
                name: None,
            },
        ],
        transitions: vec![TransitionInfo {
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
        }],
        initial_marking: vec![2, 0],
    }
}

/// Token-conserving linear drain with 4 states, not 1-safe.
pub(super) fn counting_net() -> PetriNet {
    PetriNet {
        name: Some("counting".into()),
        places: vec![
            PlaceInfo {
                id: "P0".into(),
                name: None,
            },
            PlaceInfo {
                id: "P1".into(),
                name: None,
            },
        ],
        transitions: vec![TransitionInfo {
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
        }],
        initial_marking: vec![3, 0],
    }
}

pub(super) fn default_config() -> ExplorationConfig {
    ExplorationConfig::default()
}
