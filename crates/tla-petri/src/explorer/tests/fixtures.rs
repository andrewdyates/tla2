// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

pub(super) fn simple_linear_net() -> PetriNet {
    PetriNet {
        name: Some("linear".into()),
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

pub(super) fn cyclic_net() -> PetriNet {
    PetriNet {
        name: Some("cycle".into()),
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

pub(super) fn deadlock_net() -> PetriNet {
    PetriNet {
        name: Some("deadlock".into()),
        places: vec![PlaceInfo {
            id: "P0".into(),
            name: None,
        }],
        transitions: vec![],
        initial_marking: vec![1],
    }
}

pub(super) fn two_independent_deadlocking_processes() -> PetriNet {
    PetriNet {
        name: Some("two-independent-deadlock".into()),
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

pub(super) struct CountingObserver {
    pub(super) states: usize,
    pub(super) deadlocks: usize,
    pub(super) firings: usize,
    pub(super) merged_summaries: usize,
}

impl CountingObserver {
    pub(super) fn new() -> Self {
        Self {
            states: 0,
            deadlocks: 0,
            firings: 0,
            merged_summaries: 0,
        }
    }
}

impl ExplorationObserver for CountingObserver {
    fn on_new_state(&mut self, _marking: &[u64]) -> bool {
        self.states += 1;
        true
    }

    fn on_transition_fire(&mut self, _trans: TransitionIdx) -> bool {
        self.firings += 1;
        true
    }

    fn on_deadlock(&mut self, _marking: &[u64]) {
        self.deadlocks += 1;
    }

    fn is_done(&self) -> bool {
        false
    }
}

#[derive(Default)]
pub(super) struct CountingSummary {
    states: usize,
    deadlocks: usize,
    firings: usize,
}

impl ParallelExplorationSummary for CountingSummary {
    fn on_new_state(&mut self, _marking: &[u64]) {
        self.states += 1;
    }

    fn on_transition_fire(&mut self, _trans: TransitionIdx) {
        self.firings += 1;
    }

    fn on_deadlock(&mut self, _marking: &[u64]) {
        self.deadlocks += 1;
    }

    fn stop_requested(&self) -> bool {
        false
    }
}

impl ParallelExplorationObserver for CountingObserver {
    type Summary = CountingSummary;

    fn new_summary(&self) -> Self::Summary {
        CountingSummary::default()
    }

    fn merge_summary(&mut self, summary: Self::Summary) {
        self.merged_summaries += 1;
        self.states += summary.states;
        self.deadlocks += summary.deadlocks;
        self.firings += summary.firings;
    }
}

pub(super) fn counting_net(initial_tokens: u64) -> PetriNet {
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
        initial_marking: vec![initial_tokens, 0],
    }
}

pub(super) fn two_component_net() -> PetriNet {
    PetriNet {
        name: Some("two-component".into()),
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
                    weight: 200,
                }],
                outputs: vec![Arc {
                    place: PlaceIdx(1),
                    weight: 200,
                }],
            },
            TransitionInfo {
                id: "T1".into(),
                name: None,
                inputs: vec![Arc {
                    place: PlaceIdx(1),
                    weight: 200,
                }],
                outputs: vec![Arc {
                    place: PlaceIdx(0),
                    weight: 200,
                }],
            },
            TransitionInfo {
                id: "T2".into(),
                name: None,
                inputs: vec![Arc {
                    place: PlaceIdx(2),
                    weight: 200,
                }],
                outputs: vec![Arc {
                    place: PlaceIdx(3),
                    weight: 200,
                }],
            },
            TransitionInfo {
                id: "T3".into(),
                name: None,
                inputs: vec![Arc {
                    place: PlaceIdx(3),
                    weight: 200,
                }],
                outputs: vec![Arc {
                    place: PlaceIdx(2),
                    weight: 200,
                }],
            },
        ],
        initial_marking: vec![200, 0, 200, 0],
    }
}

pub(super) fn ring_net_3() -> PetriNet {
    PetriNet {
        name: Some("ring3".into()),
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
        ],
        initial_marking: vec![1, 0, 0],
    }
}
