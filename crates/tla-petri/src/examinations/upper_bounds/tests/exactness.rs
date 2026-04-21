// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Structural and LP exactness tests for UpperBounds.

use crate::explorer::ExplorationConfig;
use crate::petri_net::{Arc, PetriNet, PlaceIdx, PlaceInfo, TransitionInfo};
use crate::property_xml::{Formula, Property};

use super::super::pipeline::check_upper_bounds_properties;
use super::fixtures::*;

#[test]
fn test_structural_bounds_resolve_at_initial_marking() {
    // Token-conserving net: p0 → t0 → p1 with initial [3, 0].
    // P-invariant [1,1] gives structural bound 3 for both places.
    // p0 initial = 3 = structural bound → confirmed exact.
    // p1 initial = 0 < 3 → needs BFS (not resolved at initial).
    // With max_states=1, BFS is incomplete: p0 resolves, p1 cannot.
    let net = simple_net();
    let props = vec![
        Property {
            id: "test-UpperBounds-00".to_string(),
            formula: Formula::PlaceBound(vec!["p0".to_string()]),
        },
        Property {
            id: "test-UpperBounds-01".to_string(),
            formula: Formula::PlaceBound(vec!["p1".to_string()]),
        },
    ];
    let config = ExplorationConfig::new(1);

    let results = check_upper_bounds_properties(&net, &props, &config);
    // p0: structural bound = 3, initial = 3 → confirmed exact
    assert_eq!(results[0], (String::from("test-UpperBounds-00"), Some(3)));
    // p1: structural bound = 3, initial = 0, BFS incomplete → CANNOT_COMPUTE
    assert_eq!(results[1], (String::from("test-UpperBounds-01"), None));
}

#[test]
fn test_structural_bounds_all_resolve_without_bfs() {
    // When ALL properties are structurally resolved at the initial
    // marking, BFS is skipped entirely (even with max_states=1).
    let net = simple_net(); // p0 → t0 → p1, initial [3, 0]
    let props = vec![Property {
        id: "test-UpperBounds-00".to_string(),
        // Query: bound of p0 alone. Initial = 3 = structural bound.
        formula: Formula::PlaceBound(vec!["p0".to_string()]),
    }];
    let config = ExplorationConfig::new(1);

    let results = check_upper_bounds_properties(&net, &props, &config);
    assert_eq!(
        results,
        vec![(String::from("test-UpperBounds-00"), Some(3))]
    );
}

#[test]
fn test_structural_bounds_sum_property_conserving() {
    // Sum of p0+p1 in conserving net is always 3.
    // Structural bound for the set {p0, p1} is 3.
    // Initial marking sum = 3+0 = 3 = structural bound → resolved.
    let net = simple_net();
    let props = vec![Property {
        id: "test-UpperBounds-00".to_string(),
        formula: Formula::PlaceBound(vec!["p0".to_string(), "p1".to_string()]),
    }];
    let config = ExplorationConfig::new(1);

    let results = check_upper_bounds_properties(&net, &props, &config);
    assert_eq!(
        results,
        vec![(String::from("test-UpperBounds-00"), Some(3))]
    );
}

#[test]
fn test_structural_bounds_with_full_exploration() {
    // Token-conserving net with default config (full exploration).
    // Structural bounds should match BFS-observed bounds exactly.
    let net = simple_net(); // p0 → t0 → p1, initial [3, 0]
    let props = vec![
        Property {
            id: "test-UpperBounds-00".to_string(),
            formula: Formula::PlaceBound(vec!["p0".to_string()]),
        },
        Property {
            id: "test-UpperBounds-01".to_string(),
            formula: Formula::PlaceBound(vec!["p1".to_string()]),
        },
    ];
    let config = default_config();
    let results = check_upper_bounds_properties(&net, &props, &config);

    assert_eq!(
        results,
        vec![
            (String::from("test-UpperBounds-00"), Some(3)),
            (String::from("test-UpperBounds-01"), Some(3)),
        ]
    );
}

#[test]
fn test_structural_bounds_mixed_covered_uncovered() {
    // Net with 3 places: p0 ↔ p1 (conserving), p2 unbounded (source).
    // Structural bound covers p0, p1 but NOT p2.
    let net = PetriNet {
        name: Some("mixed".to_string()),
        places: vec![
            PlaceInfo {
                id: "p0".to_string(),
                name: None,
            },
            PlaceInfo {
                id: "p1".to_string(),
                name: None,
            },
            PlaceInfo {
                id: "p2".to_string(),
                name: None,
            },
        ],
        transitions: vec![
            // T0: p0 → p1 (conserving pair)
            TransitionInfo {
                id: "t0".to_string(),
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
            // T1: → p2 (source, unbounded)
            TransitionInfo {
                id: "t1".to_string(),
                name: None,
                inputs: vec![],
                outputs: vec![Arc {
                    place: PlaceIdx(2),
                    weight: 1,
                }],
            },
        ],
        initial_marking: vec![4, 0, 0],
    };

    let props = vec![
        Property {
            id: "test-UpperBounds-00".to_string(),
            formula: Formula::PlaceBound(vec!["p0".to_string()]),
        },
        Property {
            id: "test-UpperBounds-01".to_string(),
            formula: Formula::PlaceBound(vec!["p2".to_string()]),
        },
    ];
    // Incomplete exploration: p0 gets structural bound, p2 does not.
    let config = ExplorationConfig::new(2);

    let results = check_upper_bounds_properties(&net, &props, &config);
    // p0: structural bound = 4, initial achieves it → resolved
    assert_eq!(results[0], (String::from("test-UpperBounds-00"), Some(4)));
    // p2: no structural bound, incomplete → CANNOT_COMPUTE
    assert_eq!(results[1], (String::from("test-UpperBounds-01"), None));
}

#[test]
fn test_upper_bounds_exact_after_later_witness() {
    // Bidirectional net: t0: p0→p1, t1: p1→p0.
    // Initial [1, 1]. P-invariant [1,1] → structural bound 2 for each.
    // Initial max for p1 = 1 (below cap). BFS discovers [0,2] where
    // p1 = 2 = structural bound → property proven exact mid-exploration.
    // State space: {[1,1], [0,2], [2,0]} — 3 states total.
    let net = PetriNet {
        name: Some("bidir".to_string()),
        places: vec![
            PlaceInfo {
                id: "p0".to_string(),
                name: None,
            },
            PlaceInfo {
                id: "p1".to_string(),
                name: None,
            },
        ],
        transitions: vec![
            TransitionInfo {
                id: "t0".to_string(),
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
                id: "t1".to_string(),
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
        initial_marking: vec![1, 1],
    };

    let props = vec![Property {
        id: "test-UpperBounds-00".to_string(),
        formula: Formula::PlaceBound(vec!["p1".to_string()]),
    }];

    // Full exploration to verify the correct answer.
    let full_results = check_upper_bounds_properties(&net, &props, &default_config());
    assert_eq!(
        full_results,
        vec![(String::from("test-UpperBounds-00"), Some(2))],
        "Full exploration should find max p1 = 2"
    );

    // Now with limited exploration: only the single property tracking p1.
    // Observer's is_done() fires once p1 hits structural cap (2),
    // enabling exact result despite not visiting all states.
    let limited_config = ExplorationConfig::new(2);
    let limited_results = check_upper_bounds_properties(&net, &props, &limited_config);
    assert_eq!(
        limited_results,
        vec![(String::from("test-UpperBounds-00"), Some(2))],
        "Later witness (state [0,2]) should prove p1 exact on incomplete exploration"
    );
}

#[test]
fn test_duplicate_place_counts_do_not_resolve_early() {
    let net = simple_net(); // p0 -> p1, initial [3, 0]
    let props = vec![Property {
        id: "test-UpperBounds-00".to_string(),
        formula: Formula::PlaceBound(vec!["p1".to_string(), "p1".to_string()]),
    }];

    let full_results = check_upper_bounds_properties(&net, &props, &default_config());
    assert_eq!(
        full_results,
        vec![(String::from("test-UpperBounds-00"), Some(6))],
        "Full exploration should count repeated places with multiplicity"
    );

    let limited_config = ExplorationConfig::new(3);
    let limited_results = check_upper_bounds_properties(&net, &props, &limited_config);
    assert_eq!(
        limited_results,
        vec![(String::from("test-UpperBounds-00"), None)],
        "Repeated places must not certify exactness before the true weighted cap is reached"
    );
}

// ── LP-only exactness tests ─────────────────────────────────────────

#[test]
fn test_lp_only_bound_resolves_without_p_invariant() {
    // Cycle-with-sink net: p0 ↔ p1 (cycle) + p0 → sink.
    //
    //   t0: p0 → p1   (move token from p0 to p1)
    //   t1: p1 → p0   (move token from p1 to p0)
    //   t2: p0 → ∅    (drain p0)
    //
    // Initial marking: [1, 1].
    //
    // P-invariant analysis: y·C = 0 where C columns are
    //   t0=[-1,1], t1=[1,-1], t2=[-1,0].
    // From t2: y0 = 0, then y1 = 0. No non-trivial P-invariant.
    // Therefore structural_bound = None for any place set.
    //
    // LP state equation: max(m1) = max(1 + x0 - x1) subject to
    //   1 - x0 + x1 - x2 ≥ 0, x ≥ 0.
    // At x1=0, x2=0: x0 ≤ 1 → max = 2. So lp_bound = Some(2).
    //
    // State space: {[1,1],[0,2],[2,0],[0,1],[1,0],[0,0]}.
    // max(p1) = 2 at [0,2].
    //
    // Both places have initial > 0, so agglomeration is blocked and
    // both survive reduction. The exactness proof comes from lp_bound,
    // NOT structural_bound.
    let net = PetriNet {
        name: Some("cycle-sink".to_string()),
        places: vec![
            PlaceInfo {
                id: "p0".to_string(),
                name: None,
            },
            PlaceInfo {
                id: "p1".to_string(),
                name: None,
            },
        ],
        transitions: vec![
            // t0: p0 → p1
            TransitionInfo {
                id: "t0".to_string(),
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
            // t1: p1 → p0
            TransitionInfo {
                id: "t1".to_string(),
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
            // t2: p0 → (sink)
            TransitionInfo {
                id: "t2".to_string(),
                name: None,
                inputs: vec![Arc {
                    place: PlaceIdx(0),
                    weight: 1,
                }],
                outputs: vec![],
            },
        ],
        initial_marking: vec![1, 1],
    };

    let props = vec![Property {
        id: "test-UpperBounds-00".to_string(),
        formula: Formula::PlaceBound(vec!["p1".to_string()]),
    }];

    // Full exploration: max(p1) = 2 at state [0, 2].
    let full_results = check_upper_bounds_properties(&net, &props, &default_config());
    assert_eq!(
        full_results,
        vec![(String::from("test-UpperBounds-00"), Some(2))],
        "Full exploration: max(p1) = 2"
    );

    // Incomplete exploration (2 states): visits [1,1] then [0,2]
    // (t0 fires first). Observed max = 2. LP cap = 2.
    // Since observed == lp_bound, the property is proven exact
    // even though exploration is incomplete and no P-invariant
    // covers p1.
    let limited_results = check_upper_bounds_properties(&net, &props, &ExplorationConfig::new(2));
    assert_eq!(
        limited_results,
        vec![(String::from("test-UpperBounds-00"), Some(2))],
        "LP cap proves exactness on incomplete exploration without P-invariant"
    );
}
