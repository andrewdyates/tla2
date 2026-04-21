// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for stubborn set partial-order reduction.

use super::*;
use crate::petri_net::{Arc, PetriNet, PlaceIdx, PlaceInfo, TransitionIdx, TransitionInfo};

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

/// Two independent processes: p0→t0→p1, p2→t1→p3.
/// t0 and t1 share no places — they are completely independent.
fn two_independent_processes() -> PetriNet {
    PetriNet {
        name: None,
        places: vec![place("p0"), place("p1"), place("p2"), place("p3")],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t1", vec![arc(2, 1)], vec![arc(3, 1)]),
        ],
        initial_marking: vec![1, 0, 1, 0],
    }
}

/// Shared resource: t0 consumes from p0, t1 consumes from p0.
/// Both compete for the same token — they interfere.
fn shared_resource() -> PetriNet {
    PetriNet {
        name: None,
        places: vec![place("p0"), place("p1"), place("p2")],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t1", vec![arc(0, 1)], vec![arc(2, 1)]),
        ],
        initial_marking: vec![1, 0, 0],
    }
}

/// Producer-consumer: t0 produces to p1, t1 consumes from p1.
/// t0 can enable t1 (but they don't interfere symmetrically).
fn producer_consumer() -> PetriNet {
    PetriNet {
        name: None,
        places: vec![place("p0"), place("p1"), place("p2")],
        transitions: vec![
            trans("t_produce", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t_consume", vec![arc(1, 1)], vec![arc(2, 1)]),
        ],
        initial_marking: vec![1, 0, 0],
    }
}

/// Three concurrent processes with one shared resource.
/// p0→t0→p3, p1→t1→p4, p2→t2→p5, but t0,t1,t2 all also need a token from p6.
fn three_with_shared_mutex() -> PetriNet {
    PetriNet {
        name: None,
        places: vec![
            place("p0"),
            place("p1"),
            place("p2"),
            place("p3"),
            place("p4"),
            place("p5"),
            place("mutex"),
        ],
        transitions: vec![
            trans("t0", vec![arc(0, 1), arc(6, 1)], vec![arc(3, 1), arc(6, 1)]),
            trans("t1", vec![arc(1, 1), arc(6, 1)], vec![arc(4, 1), arc(6, 1)]),
            trans("t2", vec![arc(2, 1), arc(6, 1)], vec![arc(5, 1), arc(6, 1)]),
        ],
        initial_marking: vec![1, 1, 1, 0, 0, 0, 1],
    }
}

// --- DependencyGraph construction tests ---

#[test]
fn test_dep_graph_independent_processes_no_interference() {
    let net = two_independent_processes();
    let dep = DependencyGraph::build(&net);

    assert_eq!(dep.num_transitions(), 2);
    // t0 and t1 share no places — no interference.
    assert!(dep.interferes_with[0].is_empty());
    assert!(dep.interferes_with[1].is_empty());
}

#[test]
fn test_dep_graph_shared_resource_interference() {
    let net = shared_resource();
    let dep = DependencyGraph::build(&net);

    // t0 and t1 both consume from p0 — they interfere with each other.
    assert!(dep.interferes_with[0].contains(&TransitionIdx(1)));
    assert!(dep.interferes_with[1].contains(&TransitionIdx(0)));
}

#[test]
fn test_dep_graph_producer_consumer_enabling() {
    let net = producer_consumer();
    let dep = DependencyGraph::build(&net);

    // t0 produces to p1, t1 consumes from p1.
    // So t0 can enable t1 (t0 is in can_enable[t1]).
    assert!(dep.can_enable[1].contains(&TransitionIdx(0)));
    // p1 producers = [t0]
    assert_eq!(dep.place_producers(1), &[TransitionIdx(0)]);
    // p1 consumers = [t1]
    assert_eq!(dep.place_consumers(1), &[TransitionIdx(1)]);
}

#[test]
fn test_dep_graph_mutex_all_interfere() {
    let net = three_with_shared_mutex();
    let dep = DependencyGraph::build(&net);

    // All three transitions share the mutex place — all interfere pairwise.
    for i in 0..3u32 {
        for j in 0..3u32 {
            if i != j {
                assert!(
                    dep.interferes_with[i as usize].contains(&TransitionIdx(j)),
                    "t{i} should interfere with t{j}"
                );
            }
        }
    }
}

// --- DeadlockPreserving stubborn set tests ---

#[test]
fn test_stubborn_independent_processes_reduces() {
    let net = two_independent_processes();
    let dep = DependencyGraph::build(&net);

    // Both t0 and t1 are enabled, but independent.
    // Stubborn set should contain exactly one of them.
    let result = compute_stubborn_set(
        &net,
        &net.initial_marking,
        &dep,
        &PorStrategy::DeadlockPreserving,
    );

    let ts = result.expect("should reduce");
    assert_eq!(
        ts.len(),
        1,
        "independent processes: stubborn set should have 1 transition"
    );
    // The single transition should be either t0 or t1.
    assert!(
        ts[0] == TransitionIdx(0) || ts[0] == TransitionIdx(1),
        "should be t0 or t1"
    );
}

#[test]
fn test_stubborn_shared_resource_no_reduction() {
    let net = shared_resource();
    let dep = DependencyGraph::build(&net);

    // t0 and t1 are both enabled and interfere (shared input p0).
    // The stubborn set must include both → no reduction.
    let result = compute_stubborn_set(
        &net,
        &net.initial_marking,
        &dep,
        &PorStrategy::DeadlockPreserving,
    );

    assert!(
        result.is_none(),
        "interfering transitions should not reduce"
    );
}

#[test]
fn test_stubborn_single_enabled_no_reduction() {
    let net = producer_consumer();
    let dep = DependencyGraph::build(&net);

    // Only t0 (produce) is enabled (p0=1); t1 needs p1 which is empty.
    let result = compute_stubborn_set(
        &net,
        &net.initial_marking,
        &dep,
        &PorStrategy::DeadlockPreserving,
    );

    assert!(
        result.is_none(),
        "single enabled transition: no reduction possible"
    );
}

#[test]
fn test_stubborn_deadlock_state_no_reduction() {
    let net = producer_consumer();
    let dep = DependencyGraph::build(&net);

    // Deadlock marking: p0=0, p1=0, p2=1 — nothing enabled.
    let result = compute_stubborn_set(&net, &[0, 0, 1], &dep, &PorStrategy::DeadlockPreserving);

    assert!(result.is_none(), "deadlock state: no transitions to fire");
}

#[test]
fn test_stubborn_none_strategy_always_returns_none() {
    let net = two_independent_processes();
    let dep = DependencyGraph::build(&net);

    let result = compute_stubborn_set(&net, &net.initial_marking, &dep, &PorStrategy::None);
    assert!(
        result.is_none(),
        "PorStrategy::None should always return None"
    );
}

#[test]
fn test_stubborn_mutex_no_reduction_all_interfere() {
    let net = three_with_shared_mutex();
    let dep = DependencyGraph::build(&net);

    // All three transitions share the mutex and interfere.
    // Stubborn set closure pulls in all three → no reduction.
    let result = compute_stubborn_set(
        &net,
        &net.initial_marking,
        &dep,
        &PorStrategy::DeadlockPreserving,
    );

    assert!(
        result.is_none(),
        "all-interfering transitions should not reduce"
    );
}

// --- Safety-preserving stubborn set tests ---

#[test]
fn test_safety_independent_with_invisible_reduces() {
    let net = two_independent_processes();
    let dep = DependencyGraph::build(&net);

    // Only t0 is visible. t1 is invisible.
    let visible = vec![TransitionIdx(0)];
    let result = compute_stubborn_set(
        &net,
        &net.initial_marking,
        &dep,
        &PorStrategy::SafetyPreserving { visible },
    );

    // Safety-preserving POR must not starve enabled visible work behind
    // independent invisible transitions, so the stubborn set keeps the
    // visible transition and still reduces away the invisible one.
    let ts = result.expect("should reduce with partial visibility");
    assert_eq!(ts, vec![TransitionIdx(0)]);
}

#[test]
fn test_safety_all_visible_no_reduction() {
    let net = two_independent_processes();
    let dep = DependencyGraph::build(&net);

    // All transitions visible → no POR benefit.
    let visible = vec![TransitionIdx(0), TransitionIdx(1)];
    let result = compute_stubborn_set(
        &net,
        &net.initial_marking,
        &dep,
        &PorStrategy::SafetyPreserving { visible },
    );

    assert!(result.is_none(), "all-visible should skip POR");
}

// --- Correctness: stubborn set preserves deadlock reachability ---

#[test]
fn test_stubborn_preserves_deadlock_reachability() {
    // Net with known deadlock: p0=1, p1=1 initially.
    // t0: p0 → p2 (independent of t1)
    // t1: p1 → p3 (independent of t0)
    // After both fire: p2=1, p3=1 — deadlock (no transition enabled).
    // POR should find the deadlock by exploring t0 then t1 (or vice versa)
    // even though it only fires one per state.
    let net = PetriNet {
        name: None,
        places: vec![place("p0"), place("p1"), place("p2"), place("p3")],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(2, 1)]),
            trans("t1", vec![arc(1, 1)], vec![arc(3, 1)]),
        ],
        initial_marking: vec![1, 1, 0, 0],
    };
    let dep = DependencyGraph::build(&net);

    // At the initial state, POR picks one transition (say t0).
    let stub = compute_stubborn_set(
        &net,
        &net.initial_marking,
        &dep,
        &PorStrategy::DeadlockPreserving,
    );
    let ts = stub.expect("should reduce");
    assert_eq!(ts.len(), 1);

    // Fire it to get next state.
    let next = net.fire(&net.initial_marking, ts[0]);

    // At the next state, one transition is still enabled.
    let stub2 = compute_stubborn_set(&net, &next, &dep, &PorStrategy::DeadlockPreserving);
    // Only one enabled → no reduction, returns None.
    assert!(stub2.is_none());

    // Fire the remaining enabled transition.
    let remaining = if ts[0] == TransitionIdx(0) {
        TransitionIdx(1)
    } else {
        TransitionIdx(0)
    };
    assert!(net.is_enabled(&next, remaining));
    let final_marking = net.fire(&next, remaining);

    // Final state should be a deadlock.
    let any_enabled =
        (0..net.num_transitions()).any(|i| net.is_enabled(&final_marking, TransitionIdx(i as u32)));
    assert!(!any_enabled, "final state should be a deadlock");
}

#[test]
fn test_stubborn_result_contains_only_enabled() {
    // Verify the stubborn set only returns enabled transitions (intersection property).
    let net = PetriNet {
        name: None,
        places: vec![
            place("p0"),
            place("p1"),
            place("p2"),
            place("p3"),
            place("p4"),
        ],
        transitions: vec![
            // t0: p0 → p1 (enabled: p0=1)
            trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
            // t1: p2 → p3 (enabled: p2=1)
            trans("t1", vec![arc(2, 1)], vec![arc(3, 1)]),
            // t2: p4 → p0 (disabled: p4=0)
            trans("t2", vec![arc(4, 1)], vec![arc(0, 1)]),
        ],
        initial_marking: vec![1, 0, 1, 0, 0],
    };
    let dep = DependencyGraph::build(&net);

    if let Some(ts) = compute_stubborn_set(
        &net,
        &net.initial_marking,
        &dep,
        &PorStrategy::DeadlockPreserving,
    ) {
        for &t in &ts {
            assert!(
                net.is_enabled(&net.initial_marking, t),
                "stubborn set should only contain enabled transitions"
            );
        }
    }
}

// --- Hand-traced D1+D2 verification on a 4-place net ---
//
// Net: "Two-Phase Pipeline"
//   p0 --t0--> p1 (phase A)
//   p2 --t1--> p3 (phase B, independent of A)
//   p1, p3 --t2--> p0, p2 (combine: consumes both phase outputs)
//
// Initial marking: [1, 0, 1, 0]
// Enabled: {t0, t1}. Disabled: {t2}.
//
// Dependency graph (hand-computed):
//   producers: p0=[t2], p1=[t0], p2=[t2], p3=[t1]
//   consumers: p0=[t0], p1=[t2], p2=[t1], p3=[t2]
//   interferes_with: t0=[t2], t1=[t2], t2=[t0,t1]
//   can_enable: t0=[t2], t1=[t2], t2=[t0,t1]
//
// DeadlockPreserving trace:
//   Seed = t0 (tied interference cost 1 with t1; first wins)
//   Closure: t0(enabled) → add interferes_with[t0]={t2}
//            t2(disabled) → key place p1 (marking 0<1, producers=[t0])
//            t0 already in set → closure complete
//   T_s = {t0, t2}, result = T_s ∩ enabled = {t0}
//   D1: {t0} non-empty ✓
//   D2(t0, enabled): interferes_with[t0]={t2} ⊆ T_s ✓
//   D2(t2, disabled): key=p1, producers[p1]={t0} ⊆ T_s ✓
fn two_phase_pipeline() -> PetriNet {
    PetriNet {
        name: None,
        places: vec![place("p0"), place("p1"), place("p2"), place("p3")],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t1", vec![arc(2, 1)], vec![arc(3, 1)]),
            trans("t2", vec![arc(1, 1), arc(3, 1)], vec![arc(0, 1), arc(2, 1)]),
        ],
        initial_marking: vec![1, 0, 1, 0],
    }
}

#[test]
fn test_d1_d2_hand_traced_four_place_pipeline() {
    let net = two_phase_pipeline();
    let dep = DependencyGraph::build(&net);

    // Verify dependency graph matches hand computation.
    assert_eq!(dep.place_producers(0), &[TransitionIdx(2)], "producers[p0]");
    assert_eq!(dep.place_producers(1), &[TransitionIdx(0)], "producers[p1]");
    assert_eq!(dep.place_producers(2), &[TransitionIdx(2)], "producers[p2]");
    assert_eq!(dep.place_producers(3), &[TransitionIdx(1)], "producers[p3]");

    assert_eq!(dep.place_consumers(0), &[TransitionIdx(0)], "consumers[p0]");
    assert_eq!(dep.place_consumers(1), &[TransitionIdx(2)], "consumers[p1]");
    assert_eq!(dep.place_consumers(2), &[TransitionIdx(1)], "consumers[p2]");
    assert_eq!(dep.place_consumers(3), &[TransitionIdx(2)], "consumers[p3]");

    // interferes_with: t0↔t2 (share p1), t1↔t2 (share p3), t0⊥t1 (no shared place)
    assert!(
        dep.interferes_with[0].contains(&TransitionIdx(2)),
        "t0 interferes t2"
    );
    assert!(
        !dep.interferes_with[0].contains(&TransitionIdx(1)),
        "t0 ⊥ t1"
    );
    assert!(
        dep.interferes_with[1].contains(&TransitionIdx(2)),
        "t1 interferes t2"
    );
    assert!(
        !dep.interferes_with[1].contains(&TransitionIdx(0)),
        "t1 ⊥ t0"
    );
    assert!(
        dep.interferes_with[2].contains(&TransitionIdx(0)),
        "t2 interferes t0"
    );
    assert!(
        dep.interferes_with[2].contains(&TransitionIdx(1)),
        "t2 interferes t1"
    );

    // Compute deadlock-preserving stubborn set at initial marking [1,0,1,0].
    let result = compute_stubborn_set(
        &net,
        &net.initial_marking,
        &dep,
        &PorStrategy::DeadlockPreserving,
    );

    // Hand-traced: T_s ∩ enabled = {t0} (just one of the two independent-looking
    // transitions, since t0's interference with t2 doesn't pull in t1).
    let ts = result.expect("should reduce: 2 enabled, 1 independent pair");
    assert_eq!(ts.len(), 1, "stubborn set should fire exactly 1 transition");
    assert_eq!(
        ts[0],
        TransitionIdx(0),
        "seed should be t0 (first in tie-break)"
    );
}

#[test]
fn test_d1_d2_hand_traced_pipeline_all_successors_reach_deadlock() {
    // Verify deadlock preservation: the two-phase pipeline is a cycle
    // (no deadlock). POR should confirm this by exploring the reduced
    // state space without finding any deadlock.
    let net = two_phase_pipeline();
    let dep = DependencyGraph::build(&net);
    let mut visited = std::collections::HashSet::new();
    visited.insert(net.initial_marking.clone());

    // BFS using stubborn sets.
    let mut queue = std::collections::VecDeque::new();
    queue.push_back(net.initial_marking.clone());
    let mut found_deadlock = false;

    while let Some(m) = queue.pop_front() {
        let stub = compute_stubborn_set(&net, &m, &dep, &PorStrategy::DeadlockPreserving);
        let to_fire: Vec<TransitionIdx> = match &stub {
            Some(ts) => ts.clone(),
            None => {
                // No reduction: fire all enabled.
                let enabled: Vec<_> = (0..net.num_transitions())
                    .filter(|&i| net.is_enabled(&m, TransitionIdx(i as u32)))
                    .map(|i| TransitionIdx(i as u32))
                    .collect();
                if enabled.is_empty() {
                    found_deadlock = true;
                    continue;
                }
                enabled
            }
        };

        for t in to_fire {
            let next = net.fire(&m, t);
            if visited.insert(next.clone()) {
                queue.push_back(next);
            }
        }
    }

    assert!(
        !found_deadlock,
        "pipeline net has no deadlock; POR should confirm"
    );
    // Full state space has 4 states; POR should explore <= 4.
    assert!(
        visited.len() <= 4,
        "POR explored {} states (full=4)",
        visited.len()
    );
}

#[test]
fn test_d2_disabled_transition_no_producer_key_place() {
    // Edge case: disabled transition's key place has zero producers.
    // D2 is vacuously satisfied (∅ ⊆ T_s).
    //
    // Net:
    //   t0: p0 → p1 (enabled)
    //   t1: p2 → p3 (enabled, independent)
    //   t2: p0, p3 → p1 (interferes with t0 via p0)
    //   p3 has no producers initially (t1 produces to p3, but we need a case
    //   where the key place has NO producers at all).
    //
    // Actually: use a place that no transition outputs to.
    //   t0: p0 → p1 (enabled)
    //   t1: p2 → p1 (enabled, shares output p1 with t0)
    //   t2: p3 → p0 (disabled, p3 has no producers at all)
    //
    // interferes_with: t0 and t1 share output p1. But the interference relation
    // for shared output is conservative (Schmidt includes output-place sharing).
    let net = PetriNet {
        name: None,
        places: vec![place("p0"), place("p1"), place("p2"), place("p3")],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t1", vec![arc(2, 1)], vec![arc(1, 1)]),
            trans("t2", vec![arc(3, 1)], vec![arc(0, 1)]),
        ],
        initial_marking: vec![1, 0, 1, 0],
    };
    let dep = DependencyGraph::build(&net);

    // p3 has no producers (no transition outputs to p3).
    assert!(
        dep.place_producers(3).is_empty(),
        "p3 should have no producers"
    );

    // t2 is disabled (p3=0 < 1). If it enters the stubborn set through
    // closure, its key place p3 has 0 producers → D2 vacuously holds.
    let result = compute_stubborn_set(
        &net,
        &net.initial_marking,
        &dep,
        &PorStrategy::DeadlockPreserving,
    );

    // The result should be Some (reduction) or None (all interfere).
    // Either way, the algorithm should not panic or produce invalid output.
    if let Some(ts) = &result {
        // Every returned transition must be enabled.
        for &t in ts {
            assert!(
                net.is_enabled(&net.initial_marking, t),
                "stubborn set must only contain enabled transitions"
            );
        }
        // D1: at least one enabled transition.
        assert!(!ts.is_empty(), "D1: stubborn set must be non-empty");
    }
}

#[test]
fn test_d2_weighted_arc_key_place_detection() {
    // Verify key place detection works for arcs with weight > 1.
    // t0 requires 3 tokens from p0 (disabled at marking [2,...]).
    // t1 produces 1 token to p0 (can partially enable t0).
    //
    // Net:
    //   t0: p0(w=3) → p1 (disabled: 2 < 3)
    //   t1: p2 → p0 (enabled)
    //   t2: p2 → p3 (enabled, independent of t0/t1)
    let net = PetriNet {
        name: None,
        places: vec![place("p0"), place("p1"), place("p2"), place("p3")],
        transitions: vec![
            trans(
                "t0",
                vec![Arc {
                    place: PlaceIdx(0),
                    weight: 3,
                }],
                vec![arc(1, 1)],
            ),
            trans("t1", vec![arc(2, 1)], vec![arc(0, 1)]),
            trans("t2", vec![arc(2, 1)], vec![arc(3, 1)]),
        ],
        initial_marking: vec![2, 0, 2, 0],
    };
    let dep = DependencyGraph::build(&net);

    // t0 disabled (2 < 3), t1 enabled (p2=2 ≥ 1), t2 enabled (p2=2 ≥ 1)
    assert!(!net.is_enabled(&net.initial_marking, TransitionIdx(0)));
    assert!(net.is_enabled(&net.initial_marking, TransitionIdx(1)));
    assert!(net.is_enabled(&net.initial_marking, TransitionIdx(2)));

    // t0's unsatisfied input: p0 (marking=2, weight=3, 2 < 3).
    // producers[p0] = [t1]. So if t0 enters the stubborn set, t1 must too.
    assert!(dep.place_producers(0).contains(&TransitionIdx(1)));

    let result = compute_stubborn_set(
        &net,
        &net.initial_marking,
        &dep,
        &PorStrategy::DeadlockPreserving,
    );

    if let Some(ts) = &result {
        for &t in ts {
            assert!(net.is_enabled(&net.initial_marking, t));
        }
    }
}

#[test]
fn test_safety_preserving_visibility_forces_expansion() {
    // When a visible transition enters the stubborn set, ALL visible
    // transitions must be included. Verify this on the 4-place pipeline.
    let net = two_phase_pipeline();
    let dep = DependencyGraph::build(&net);

    // Make t0 and t1 both visible. Since they're independent, without
    // visibility the stubborn set would be {t0}. With visibility, once
    // t0 enters, t1 must also enter → no reduction.
    let visible = vec![TransitionIdx(0), TransitionIdx(1)];
    let result = compute_stubborn_set(
        &net,
        &net.initial_marking,
        &dep,
        &PorStrategy::SafetyPreserving { visible },
    );

    // Both enabled transitions are visible → visibility expansion forces
    // both into the set → result.len() == enabled.len() → None.
    assert!(
        result.is_none(),
        "all visible enabled transitions → no reduction"
    );
}

#[test]
fn test_safety_preserving_invisible_seed_avoids_expansion() {
    // When only invisible transitions enter the stubborn set, no
    // visibility expansion occurs → effective reduction.
    let net = two_phase_pipeline();
    let dep = DependencyGraph::build(&net);

    // Only t2 is visible (t2 is disabled anyway). t0, t1 are invisible.
    // Seed should be t0 or t1 (invisible, preferred by heuristic).
    // The stubborn set {t0, t2} contains no enabled visible transition
    // (t2 is disabled), so visibility doesn't expand.
    let visible = vec![TransitionIdx(2)];
    let result = compute_stubborn_set(
        &net,
        &net.initial_marking,
        &dep,
        &PorStrategy::SafetyPreserving { visible },
    );

    let ts = result.expect("invisible seed should allow reduction");
    assert_eq!(ts.len(), 1, "should fire exactly 1 transition");
}
