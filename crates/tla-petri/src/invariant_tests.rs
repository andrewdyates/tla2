// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::petri_net::{Arc, PetriNet, PlaceIdx, PlaceInfo, TransitionInfo};

fn arc(place: u32, weight: u64) -> Arc {
    Arc {
        place: PlaceIdx(place),
        weight,
    }
}

fn place(id: &str) -> PlaceInfo {
    PlaceInfo {
        id: id.to_string(),
        name: None,
    }
}

fn trans(id: &str, inputs: Vec<Arc>, outputs: Vec<Arc>) -> TransitionInfo {
    TransitionInfo {
        id: id.to_string(),
        name: None,
        inputs,
        outputs,
    }
}

// ── Empty / trivial nets ────────────────────────────────────────────

#[test]
fn test_empty_net_no_invariants() {
    let net = PetriNet {
        name: None,
        places: vec![],
        transitions: vec![],
        initial_marking: vec![],
    };
    assert!(compute_p_invariants(&net).is_empty());
}

#[test]
fn test_no_transitions_unit_invariants() {
    let net = PetriNet {
        name: None,
        places: vec![place("p0"), place("p1")],
        transitions: vec![],
        initial_marking: vec![3, 5],
    };
    let invs = compute_p_invariants(&net);
    assert_eq!(invs.len(), 2);
    // Each place has its own unit invariant
    assert_eq!(invs[0].weights, vec![1, 0]);
    assert_eq!(invs[0].token_count, 3);
    assert_eq!(invs[1].weights, vec![0, 1]);
    assert_eq!(invs[1].token_count, 5);
}

// ── Token-conserving 2-place net ────────────────────────────────────

/// Simple conserving net: T0 moves 1 token from p0 to p1.
fn conserving_2place_net(initial: Vec<u64>) -> PetriNet {
    PetriNet {
        name: None,
        places: vec![place("p0"), place("p1")],
        transitions: vec![trans("t0", vec![arc(0, 1)], vec![arc(1, 1)])],
        initial_marking: initial,
    }
}

#[test]
fn test_conserving_2place_finds_invariant() {
    let net = conserving_2place_net(vec![3, 0]);
    let invs = compute_p_invariants(&net);
    // Should find [1, 1] invariant with token_count = 3
    assert!(!invs.is_empty());
    let inv = &invs[0];
    assert_eq!(inv.weights[0], inv.weights[1]); // equal weights
    assert_eq!(inv.token_count, 3 * inv.weights[0]); // 3 * weight
}

#[test]
fn test_conserving_2place_bounds() {
    let net = conserving_2place_net(vec![3, 0]);
    let invs = compute_p_invariants(&net);
    // Each place bounded by 3 (since [1,1] invariant with total = 3)
    assert_eq!(structural_place_bound(&invs, 0), Some(3));
    assert_eq!(structural_place_bound(&invs, 1), Some(3));
}

#[test]
fn test_conserving_2place_set_bound() {
    let net = conserving_2place_net(vec![3, 0]);
    let invs = compute_p_invariants(&net);
    // Sum p0+p1 bounded by 3 (the invariant total)
    assert_eq!(structural_set_bound(&invs, &[0, 1]), Some(3));
}

// ── Token-conserving ring net ───────────────────────────────────────

/// Ring: p0→t0→p1, p1→t1→p2, p2→t2→p0 (3-place token ring).
fn ring_3place_net() -> PetriNet {
    PetriNet {
        name: None,
        places: vec![place("p0"), place("p1"), place("p2")],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t1", vec![arc(1, 1)], vec![arc(2, 1)]),
            trans("t2", vec![arc(2, 1)], vec![arc(0, 1)]),
        ],
        initial_marking: vec![2, 0, 0],
    }
}

#[test]
fn test_ring_3place_invariant() {
    let net = ring_3place_net();
    let invs = compute_p_invariants(&net);
    // Should find [1, 1, 1] invariant with total = 2
    assert!(!invs.is_empty());
    let inv = &invs[0];
    assert!(inv.weights.iter().all(|&w| w == inv.weights[0]));
    assert_eq!(inv.token_count, 2 * inv.weights[0]);
}

#[test]
fn test_ring_3place_structural_bounds() {
    let bounds = structural_place_bounds(&ring_3place_net());
    // Each place bounded by 2
    assert_eq!(bounds, vec![Some(2), Some(2), Some(2)]);
}

// ── Non-conserving net ──────────────────────────────────────────────

/// Non-conserving: T0 consumes 1 from p0, produces 2 to p1.
fn non_conserving_net() -> PetriNet {
    PetriNet {
        name: None,
        places: vec![place("p0"), place("p1")],
        transitions: vec![trans("t0", vec![arc(0, 1)], vec![arc(1, 2)])],
        initial_marking: vec![5, 0],
    }
}

#[test]
#[allow(clippy::needless_range_loop)] // `t` is a column index into row-major c[p][t]
fn test_non_conserving_may_have_no_invariants() {
    let net = non_conserving_net();
    let invs = compute_p_invariants(&net);
    // Non-conserving: might have no semi-positive P-invariants
    // (Specifically, [2, 1] · C = [2*(-1)+1*2] = [0] — this IS an invariant!)
    // Let's verify what we actually find.
    if !invs.is_empty() {
        for inv in &invs {
            // Verify invariant property: y^T · C = 0
            let c = incidence_matrix(&net);
            for t in 0..net.num_transitions() {
                let dot: i64 = inv
                    .weights
                    .iter()
                    .enumerate()
                    .map(|(p, &w)| (w as i64) * c[p][t])
                    .sum();
                assert_eq!(dot, 0, "Invariant violated for transition {t}");
            }
        }
    }
}

#[test]
fn test_non_conserving_2_1_invariant() {
    // For T0: -1 from p0, +2 to p1 → C = [[-1], [2]]
    // P-invariant y: y0*(-1) + y1*2 = 0 → y0 = 2*y1
    // Minimal: y = [2, 1], token_count = 2*5 + 1*0 = 10
    let net = non_conserving_net();
    let invs = compute_p_invariants(&net);
    assert!(!invs.is_empty());
    let inv = &invs[0];
    // Weights should be proportional to [2, 1]
    assert_eq!(inv.weights[0], 2 * inv.weights[1]);
    assert_eq!(inv.token_count, 10 * inv.weights[1] / inv.weights[1]); // = 10
}

// ── Weighted arcs ───────────────────────────────────────────────────

/// Conserving with weight 2: T0 takes 2 from p0, puts 2 to p1.
fn weighted_conserving_net() -> PetriNet {
    PetriNet {
        name: None,
        places: vec![place("p0"), place("p1")],
        transitions: vec![trans("t0", vec![arc(0, 2)], vec![arc(1, 2)])],
        initial_marking: vec![4, 0],
    }
}

#[test]
fn test_weighted_conserving_invariant() {
    let net = weighted_conserving_net();
    let invs = compute_p_invariants(&net);
    assert!(!invs.is_empty());
    // [1, 1] with token_count = 4
    let inv = &invs[0];
    assert_eq!(inv.weights[0], inv.weights[1]);
    assert_eq!(inv.token_count, 4 * inv.weights[0]);
}

// ── Multiple independent subnets (should find multiple invariants) ──

/// Two independent pairs: p0↔p1 and p2↔p3, no interaction.
fn independent_pairs_net() -> PetriNet {
    PetriNet {
        name: None,
        places: vec![place("p0"), place("p1"), place("p2"), place("p3")],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t1", vec![arc(2, 1)], vec![arc(3, 1)]),
        ],
        initial_marking: vec![3, 0, 5, 0],
    }
}

#[test]
fn test_independent_pairs_two_invariants() {
    let net = independent_pairs_net();
    let invs = compute_p_invariants(&net);
    // Should find two independent invariants covering {p0,p1} and {p2,p3}
    assert!(invs.len() >= 2);

    // Verify: at least one invariant covers p0 and p1 but not p2/p3
    let covers_01 = invs.iter().any(|inv| {
        inv.weights[0] > 0 && inv.weights[1] > 0 && inv.weights[2] == 0 && inv.weights[3] == 0
    });
    let covers_23 = invs.iter().any(|inv| {
        inv.weights[0] == 0 && inv.weights[1] == 0 && inv.weights[2] > 0 && inv.weights[3] > 0
    });
    assert!(covers_01, "Should find invariant covering p0,p1");
    assert!(covers_23, "Should find invariant covering p2,p3");
}

#[test]
fn test_independent_pairs_bounds() {
    let bounds = structural_place_bounds(&independent_pairs_net());
    assert_eq!(bounds[0], Some(3));
    assert_eq!(bounds[1], Some(3));
    assert_eq!(bounds[2], Some(5));
    assert_eq!(bounds[3], Some(5));
}

// ── OneSafe structural proof ────────────────────────────────────────

#[test]
fn test_one_safe_structural_proof() {
    // Net with 1 token total: structurally 1-safe
    let net = conserving_2place_net(vec![1, 0]);
    let bounds = structural_place_bounds(&net);
    assert!(bounds.iter().all(|b| b.is_some_and(|v| v <= 1)));
}

#[test]
fn test_not_one_safe_structural() {
    // Net with 3 tokens total: structural bound is 3, not 1-safe
    let net = conserving_2place_net(vec![3, 0]);
    let bounds = structural_place_bounds(&net);
    assert!(bounds.iter().any(|b| b.is_none_or(|v| v > 1)));
}

// ── structural_set_bound edge cases ─────────────────────────────────

#[test]
fn test_set_bound_empty_set() {
    let invs = vec![PInvariant {
        weights: vec![1, 1],
        token_count: 5,
    }];
    assert_eq!(structural_set_bound(&invs, &[]), Some(0));
}

#[test]
fn test_set_bound_no_covering_invariant() {
    let invs = vec![PInvariant {
        weights: vec![1, 0],
        token_count: 5,
    }];
    // No invariant covers both places
    assert_eq!(structural_set_bound(&invs, &[0, 1]), None);
}

#[test]
fn test_set_bound_single_place() {
    let invs = vec![PInvariant {
        weights: vec![2, 1],
        token_count: 10,
    }];
    // Bound for p0: 10/2 = 5
    assert_eq!(structural_set_bound(&invs, &[0]), Some(5));
    // Bound for p1: 10/1 = 10
    assert_eq!(structural_set_bound(&invs, &[1]), Some(10));
}

// ── GCD reduction ───────────────────────────────────────────────────

#[test]
fn test_gcd_basic() {
    assert_eq!(gcd(12, 8), 4);
    assert_eq!(gcd(7, 3), 1);
    assert_eq!(gcd(0, 5), 5);
    assert_eq!(gcd(5, 0), 5);
    assert_eq!(gcd(0, 0), 0);
}

// ── Verify invariant correctness property ───────────────────────────

#[test]
#[allow(clippy::needless_range_loop)] // `t` is a column index into row-major c[p][t]
fn test_all_invariants_satisfy_yt_c_eq_0() {
    let nets = [
        conserving_2place_net(vec![3, 0]),
        ring_3place_net(),
        non_conserving_net(),
        weighted_conserving_net(),
        independent_pairs_net(),
    ];

    for (idx, net) in nets.iter().enumerate() {
        let invs = compute_p_invariants(net);
        let c = incidence_matrix(net);
        for (inv_idx, inv) in invs.iter().enumerate() {
            for t in 0..net.num_transitions() {
                let dot: i64 = inv
                    .weights
                    .iter()
                    .enumerate()
                    .map(|(p, &w)| (w as i64) * c[p][t])
                    .sum();
                assert_eq!(
                    dot, 0,
                    "Net {idx}, invariant {inv_idx}, transition {t}: y^T·C ≠ 0"
                );
            }
        }
    }
}

// ── Mutual exclusion net ────────────────────────────────────────────

/// Classic mutex: two processes sharing one resource.
/// p0 (idle_a), p1 (cs_a), p2 (idle_b), p3 (cs_b), p4 (mutex)
/// T0: p0,p4 → p1  (A enters CS)
/// T1: p1 → p0,p4  (A leaves CS)
/// T2: p2,p4 → p3  (B enters CS)
/// T3: p3 → p2,p4  (B leaves CS)
fn mutex_net() -> PetriNet {
    PetriNet {
        name: None,
        places: vec![
            place("idle_a"),
            place("cs_a"),
            place("idle_b"),
            place("cs_b"),
            place("mutex"),
        ],
        transitions: vec![
            trans("enter_a", vec![arc(0, 1), arc(4, 1)], vec![arc(1, 1)]),
            trans("leave_a", vec![arc(1, 1)], vec![arc(0, 1), arc(4, 1)]),
            trans("enter_b", vec![arc(2, 1), arc(4, 1)], vec![arc(3, 1)]),
            trans("leave_b", vec![arc(3, 1)], vec![arc(2, 1), arc(4, 1)]),
        ],
        initial_marking: vec![1, 0, 1, 0, 1],
    }
}

#[test]
fn test_mutex_structural_bounds() {
    let net = mutex_net();
    let bounds = structural_place_bounds(&net);
    // All places should be bounded by 1 → structurally 1-safe
    assert!(
        bounds.iter().all(|b| b == &Some(1)),
        "Mutex net should be structurally 1-safe, got: {bounds:?}"
    );
}

#[test]
fn test_mutex_mutual_exclusion_invariant() {
    let net = mutex_net();
    let invs = compute_p_invariants(&net);
    // Should find invariant [0, 1, 0, 1, 1] (cs_a + cs_b + mutex = 1)
    // This proves mutual exclusion: cs_a + cs_b ≤ 1
    let me_inv = invs.iter().find(|inv| {
        inv.weights[1] > 0 && inv.weights[3] > 0 && inv.weights[4] > 0 && inv.weights[0] == 0
    });
    assert!(me_inv.is_some(), "Should find mutual exclusion invariant");
    let inv = me_inv.unwrap();
    assert_eq!(inv.token_count, inv.weights[4]); // only mutex has initial token
}

// ── MCC-representative model: Dining Philosophers ────────────────

/// Classic dining philosophers (2 philosophers, 2 shared forks).
/// This pattern is representative of MCC competition models (Kanban,
/// SharedMemory, Peterson) that feature resource competition and
/// conservation invariants.
///
/// Places: think0, eat0, think1, eat1, fork0, fork1
/// Transitions:
///   pickup0:  think0, fork0, fork1 → eat0
///   putdown0: eat0 → think0, fork0, fork1
///   pickup1:  think1, fork0, fork1 → eat1
///   putdown1: eat1 → think1, fork0, fork1
fn dining_philosophers_2() -> PetriNet {
    PetriNet {
        name: None,
        places: vec![
            place("think0"),
            place("eat0"),
            place("think1"),
            place("eat1"),
            place("fork0"),
            place("fork1"),
        ],
        transitions: vec![
            trans(
                "pickup0",
                vec![arc(0, 1), arc(4, 1), arc(5, 1)],
                vec![arc(1, 1)],
            ),
            trans(
                "putdown0",
                vec![arc(1, 1)],
                vec![arc(0, 1), arc(4, 1), arc(5, 1)],
            ),
            trans(
                "pickup1",
                vec![arc(2, 1), arc(4, 1), arc(5, 1)],
                vec![arc(3, 1)],
            ),
            trans(
                "putdown1",
                vec![arc(3, 1)],
                vec![arc(2, 1), arc(4, 1), arc(5, 1)],
            ),
        ],
        initial_marking: vec![1, 0, 1, 0, 1, 1],
    }
}

#[test]
fn test_dining_philosophers_structural_bounds() {
    let net = dining_philosophers_2();
    let bounds = structural_place_bounds(&net);
    // All places bounded by 1 → structurally 1-safe.
    // This matches what MCC's OneSafe examination would verify.
    assert!(
        bounds.iter().all(|b| b == &Some(1)),
        "Dining philosophers should be structurally 1-safe, got: {bounds:?}"
    );
}

#[test]
fn test_dining_philosophers_mutual_exclusion() {
    let net = dining_philosophers_2();
    let invs = compute_p_invariants(&net);
    // The set {eat0, eat1} is bounded by 1: at most one philosopher eats.
    // This is the key safety property for dining philosophers models.
    let bound = structural_set_bound(&invs, &[1, 3]);
    assert_eq!(bound, Some(1), "eat0 + eat1 <= 1 (mutual exclusion)");
}

#[test]
#[allow(clippy::needless_range_loop)] // `t` is a column index into row-major c[p][t]
fn test_dining_philosophers_conservation_laws() {
    let net = dining_philosophers_2();
    let invs = compute_p_invariants(&net);
    let c = incidence_matrix(&net);

    // Verify all discovered invariants satisfy y^T * C = 0.
    for (idx, inv) in invs.iter().enumerate() {
        for t in 0..net.num_transitions() {
            let dot: i64 = inv
                .weights
                .iter()
                .enumerate()
                .map(|(p, &w)| (w as i64) * c[p][t])
                .sum();
            assert_eq!(
                dot, 0,
                "Dining philosophers invariant {idx}, transition {t}: y^T*C != 0"
            );
        }
    }

    // Should find at least 3 independent conservation laws:
    //   think0 + eat0 = 1  (philosopher 0 subprocess)
    //   think1 + eat1 = 1  (philosopher 1 subprocess)
    //   eat0 + eat1 + fork_i = 1  (fork conservation)
    assert!(
        invs.len() >= 3,
        "Should find at least 3 conservation laws, found {}",
        invs.len()
    );
}

// ── Implied place detection ──────────────────────────────────────────

#[test]
fn test_find_implied_places_empty_invariants() {
    assert!(find_implied_places(&[]).is_empty());
}

#[test]
fn test_find_implied_places_ring_removes_one() {
    // Ring: [1,1,1] invariant, 3 places → can remove 1 place
    let net = ring_3place_net();
    let invs = compute_p_invariants(&net);
    let implied = find_implied_places(&invs);
    assert_eq!(
        implied.len(),
        1,
        "Should remove exactly one place from 3-place ring"
    );

    // The removed place should have weight 1 (preferred)
    assert_eq!(implied[0].reconstruction.divisor, 1);

    // Verify reconstruction for initial marking [2,0,0]
    let removed = implied[0].place;
    let r = &implied[0].reconstruction;
    let sum: u64 = r
        .terms
        .iter()
        .map(|&(p, w)| w * net.initial_marking[p])
        .sum();
    let reconstructed = (r.constant - sum) / r.divisor;
    assert_eq!(reconstructed, net.initial_marking[removed]);
}

#[test]
fn test_find_implied_places_independence() {
    // Independent pairs: {p0,p1} and {p2,p3}
    // Can remove one from each pair = 2 implied places
    let net = independent_pairs_net();
    let invs = compute_p_invariants(&net);
    let implied = find_implied_places(&invs);
    assert_eq!(
        implied.len(),
        2,
        "Should remove one place from each independent pair"
    );

    // No implied place should appear in another's reconstruction terms
    let removed_set: std::collections::HashSet<usize> = implied.iter().map(|ip| ip.place).collect();
    for ip in &implied {
        for &(term_place, _) in &ip.reconstruction.terms {
            assert!(
                !removed_set.contains(&term_place),
                "Implied place {} has removed place {} in reconstruction terms",
                ip.place,
                term_place
            );
        }
    }
}

#[test]
fn test_find_implied_places_reconstruction_exactness() {
    // All reachable markings must reconstruct exactly
    let net = conserving_2place_net(vec![5, 0]);
    let invs = compute_p_invariants(&net);
    let implied = find_implied_places(&invs);
    assert_eq!(implied.len(), 1, "2-place conserving net: remove 1 place");

    // Reachable markings for p0↔p1 with total=5
    let markings = vec![
        vec![5, 0],
        vec![4, 1],
        vec![3, 2],
        vec![2, 3],
        vec![1, 4],
        vec![0, 5],
    ];

    for m in &markings {
        let removed = implied[0].place;
        let r = &implied[0].reconstruction;
        let sum: u64 = r.terms.iter().map(|&(p, w)| w * m[p]).sum();
        let reconstructed = (r.constant - sum) / r.divisor;
        assert_eq!(
            reconstructed, m[removed],
            "Reconstruction failed for marking {m:?}"
        );
    }
}

#[test]
fn test_find_implied_places_single_place_invariant_skipped() {
    // Unit invariants with support size 1 → no implied places possible
    let net = PetriNet {
        name: None,
        places: vec![place("p0")],
        transitions: vec![],
        initial_marking: vec![42],
    };
    let invs = compute_p_invariants(&net);
    let implied = find_implied_places(&invs);
    assert!(
        implied.is_empty(),
        "Single-place invariants cannot produce implied places"
    );
}

#[test]
fn test_find_implied_places_mutex_net() {
    let net = mutex_net();
    let invs = compute_p_invariants(&net);
    let implied = find_implied_places(&invs);
    assert!(!implied.is_empty(), "Mutex net should have implied places");

    // Verify reconstruction for initial marking [1, 0, 1, 0, 1]
    for ip in &implied {
        let r = &ip.reconstruction;
        let sum: u64 = r
            .terms
            .iter()
            .map(|&(p, w)| w * net.initial_marking[p])
            .sum();
        let reconstructed = (r.constant - sum) / r.divisor;
        assert_eq!(
            reconstructed, net.initial_marking[ip.place],
            "Reconstruction failed for place {} in mutex net",
            ip.place
        );
    }
}

#[test]
fn test_find_implied_places_no_double_removal() {
    // Verify that no two implied places share reconstruction dependence:
    // for every implied place, its terms reference only kept (non-implied) places.
    let nets: Vec<PetriNet> = vec![
        ring_3place_net(),
        independent_pairs_net(),
        mutex_net(),
        dining_philosophers_2(),
    ];

    for (idx, net) in nets.iter().enumerate() {
        let invs = compute_p_invariants(net);
        let implied = find_implied_places(&invs);
        let removed_set: std::collections::HashSet<usize> =
            implied.iter().map(|ip| ip.place).collect();

        for ip in &implied {
            for &(term_place, _) in &ip.reconstruction.terms {
                assert!(
                    !removed_set.contains(&term_place),
                    "Net {idx}: implied place {} depends on removed place {}",
                    ip.place,
                    term_place
                );
            }
        }
    }
}

// ── T-semiflow tests ────────────────────────────────────────────────

#[test]
fn test_t_semiflow_cycle_net() {
    // Cycle: p0(1) → t0 → p1, p1 → t1 → p0.
    // t0 and t1 form a T-semiflow (firing both returns to initial marking).
    let net = PetriNet {
        name: None,
        places: vec![place("p0"), place("p1")],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t1", vec![arc(1, 1)], vec![arc(0, 1)]),
        ],
        initial_marking: vec![1, 0],
    };
    let result = compute_t_semiflows(&net);
    assert!(result.complete, "cycle net Farkas should complete");
    assert!(
        !result.semiflows.is_empty(),
        "cycle net should have T-semiflows"
    );
    assert!(
        all_transitions_covered(&result.semiflows, net.num_transitions()),
        "both transitions should be covered"
    );
}

#[test]
fn test_t_semiflow_linear_net() {
    // Linear: p0(1) → t0 → p1. No cycle, t0 has no T-semiflow.
    let net = PetriNet {
        name: None,
        places: vec![place("p0"), place("p1")],
        transitions: vec![trans("t0", vec![arc(0, 1)], vec![arc(1, 1)])],
        initial_marking: vec![1, 0],
    };
    let result = compute_t_semiflows(&net);
    assert!(result.complete);
    assert!(
        !all_transitions_covered(&result.semiflows, net.num_transitions()),
        "linear net t0 should be uncovered"
    );
}

#[test]
fn test_t_semiflow_self_loop() {
    // Self-loop: p0(1) → t0 → p0. t0 fires without changing marking.
    let net = PetriNet {
        name: None,
        places: vec![place("p0")],
        transitions: vec![trans("t0", vec![arc(0, 1)], vec![arc(0, 1)])],
        initial_marking: vec![1],
    };
    let result = compute_t_semiflows(&net);
    assert!(result.complete, "self-loop Farkas should complete");
    assert!(
        all_transitions_covered(&result.semiflows, net.num_transitions()),
        "self-loop t0 should be covered"
    );
}

#[test]
fn test_t_semiflow_empty_net() {
    let net = PetriNet {
        name: None,
        places: vec![place("p0")],
        transitions: vec![],
        initial_marking: vec![1],
    };
    let result = compute_t_semiflows(&net);
    assert!(result.complete, "empty net Farkas should complete");
    assert!(result.semiflows.is_empty());
}

#[test]
fn test_t_semiflow_no_places() {
    // Degenerate: transitions exist but no places.
    let net = PetriNet {
        name: None,
        places: vec![],
        transitions: vec![TransitionInfo {
            id: "t0".to_string(),
            name: None,
            inputs: vec![],
            outputs: vec![],
        }],
        initial_marking: vec![],
    };
    let result = compute_t_semiflows(&net);
    assert!(result.complete, "no-places Farkas should complete");
    assert!(
        all_transitions_covered(&result.semiflows, 1),
        "with no places, every transition is a trivial semiflow"
    );
}
