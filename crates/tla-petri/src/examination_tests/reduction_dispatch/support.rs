// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Reusable synthetic net builders for reduction dispatch tests.

use crate::petri_net::{Arc, PetriNet, PlaceIdx, PlaceInfo, TransitionInfo};

pub(super) fn isolated_place_net(isolated_tokens: u64) -> PetriNet {
    PetriNet {
        name: Some("isolated-place".into()),
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
        initial_marking: vec![1, 0, isolated_tokens],
    }
}

pub(super) fn structurally_dead_transition_net() -> PetriNet {
    PetriNet {
        name: Some("dead-transition".into()),
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
                    place: PlaceIdx(1),
                    weight: 1,
                }],
            },
        ],
        initial_marking: vec![0, 1],
    }
}

pub(super) fn non_free_choice_cycle_net() -> PetriNet {
    PetriNet {
        name: Some("non-free-choice-cycle".into()),
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
            PlaceInfo {
                id: "P3".into(),
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
                    place: PlaceIdx(2),
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
                    place: PlaceIdx(3),
                    weight: 1,
                }],
            },
            TransitionInfo {
                id: "T2".into(),
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
            TransitionInfo {
                id: "T3".into(),
                name: None,
                inputs: vec![Arc {
                    place: PlaceIdx(3),
                    weight: 1,
                }],
                outputs: vec![
                    Arc {
                        place: PlaceIdx(0),
                        weight: 1,
                    },
                    Arc {
                        place: PlaceIdx(1),
                        weight: 1,
                    },
                ],
            },
        ],
        initial_marking: vec![1, 1, 0, 0],
    }
}

/// Chain: p_in(1) →(1) t0 →(1) p_mid(0) →(1) t1 →(1) p_out(0)
///
/// Pre-agglomeration removes t0 and p_mid. Both transitions fire once in the
/// original net (quasi-live). The verdict must NOT short-circuit to FALSE
/// just because a transition was agglomerated. Regression test for the
/// `transitions_removed()` vs `dead_transitions` soundness fix.
pub(super) fn agglomerable_chain_net() -> PetriNet {
    PetriNet {
        name: Some("agg-chain".into()),
        places: vec![
            PlaceInfo {
                id: "P_in".into(),
                name: None,
            },
            PlaceInfo {
                id: "P_mid".into(),
                name: None,
            },
            PlaceInfo {
                id: "P_out".into(),
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
                    place: PlaceIdx(2),
                    weight: 1,
                }],
            },
        ],
        initial_marking: vec![1, 0, 0],
    }
}

pub(super) fn gcd_sensitive_one_safe_net() -> PetriNet {
    PetriNet {
        name: Some("gcd-one-safe".into()),
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
                    weight: 2,
                }],
            },
            TransitionInfo {
                id: "T1".into(),
                name: None,
                inputs: vec![Arc {
                    place: PlaceIdx(1),
                    weight: 2,
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

pub(super) fn gcd_sensitive_state_space_net() -> PetriNet {
    PetriNet {
        name: Some("gcd-state-space".into()),
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
                    weight: 2,
                }],
                outputs: vec![Arc {
                    place: PlaceIdx(1),
                    weight: 2,
                }],
            },
            TransitionInfo {
                id: "T1".into(),
                name: None,
                inputs: vec![Arc {
                    place: PlaceIdx(1),
                    weight: 2,
                }],
                outputs: vec![Arc {
                    place: PlaceIdx(0),
                    weight: 2,
                }],
            },
        ],
        initial_marking: vec![4, 0],
    }
}
