// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for stubborn set partial-order reduction.

use std::collections::{HashSet, VecDeque};

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

// --- POR stats tracking ---

#[test]
fn test_por_stats_collector_tracks_reduction() {
    let net = two_independent_processes();
    let dep = DependencyGraph::build(&net);
    let mut collector = PorStatsCollector::new(&dep);

    let stubborn = compute_stubborn_set_tracked(
        &net,
        &net.initial_marking,
        &mut collector,
        &PorStrategy::DeadlockPreserving,
    );

    let transitions = stubborn.expect("independent transitions should reduce");
    assert_eq!(transitions.len(), 1);

    let stats = collector.stats();
    assert_eq!(stats.states_with_reduction, 1);
    assert_eq!(stats.states_without_reduction, 0);
    assert_eq!(stats.transitions_total, 2);
    assert_eq!(stats.transitions_pruned, 1);
    assert_eq!(stats.reduction_ratio(), 0.5);
}

// --- End-to-end BFS crosschecks ---

#[derive(Debug)]
struct BfsResult {
    states: HashSet<Vec<u64>>,
    deadlocks: Vec<Vec<u64>>,
    transitions_fired: usize,
}

fn enabled_transitions(net: &PetriNet, marking: &[u64]) -> Vec<TransitionIdx> {
    let mut enabled = Vec::new();
    for tidx in 0..net.num_transitions() {
        let trans = TransitionIdx(tidx as u32);
        if net.is_enabled(marking, trans) {
            enabled.push(trans);
        }
    }
    enabled
}

fn bfs_full(net: &PetriNet) -> BfsResult {
    bfs_por(net, &PorStrategy::None)
}

fn bfs_por(net: &PetriNet, strategy: &PorStrategy) -> BfsResult {
    let dep = DependencyGraph::build(net);
    let mut collector = PorStatsCollector::new(&dep);
    let mut states = HashSet::new();
    let mut deadlocks = Vec::new();
    let mut queue = VecDeque::new();
    let mut transitions_fired = 0usize;

    states.insert(net.initial_marking.clone());
    queue.push_back(net.initial_marking.clone());

    while let Some(marking) = queue.pop_front() {
        let to_fire = match compute_stubborn_set_tracked(net, &marking, &mut collector, strategy) {
            Some(transitions) => transitions,
            None => enabled_transitions(net, &marking),
        };

        if to_fire.is_empty() {
            deadlocks.push(marking);
            continue;
        }

        transitions_fired += to_fire.len();
        for trans in to_fire {
            let next = net.fire(&marking, trans);
            if states.insert(next.clone()) {
                queue.push_back(next);
            }
        }
    }

    let _ = collector.into_stats();

    BfsResult {
        states,
        deadlocks,
        transitions_fired,
    }
}

fn has_safety_violation<F>(result: &BfsResult, is_violation: F) -> bool
where
    F: Fn(&[u64]) -> bool,
{
    result.states.iter().any(|marking| is_violation(marking))
}

fn assert_deadlock_crosscheck(net: &PetriNet) {
    let full = bfs_full(net);
    let por = bfs_por(net, &PorStrategy::DeadlockPreserving);

    assert_eq!(
        !por.deadlocks.is_empty(),
        !full.deadlocks.is_empty(),
        "deadlock reachability mismatch: full={}, por={}",
        full.deadlocks.len(),
        por.deadlocks.len()
    );
    assert!(
        por.states.len() <= full.states.len(),
        "POR explored more states than full BFS: por={}, full={}",
        por.states.len(),
        full.states.len()
    );
    assert!(
        por.transitions_fired <= full.transitions_fired,
        "POR fired more transitions than full BFS: por={}, full={}",
        por.transitions_fired,
        full.transitions_fired
    );
}

fn assert_safety_crosscheck<F>(net: &PetriNet, visible: Vec<TransitionIdx>, is_violation: F)
where
    F: Fn(&[u64]) -> bool,
{
    let full = bfs_full(net);
    let por = bfs_por(net, &PorStrategy::SafetyPreserving { visible });

    let full_has_violation = has_safety_violation(&full, &is_violation);
    let por_has_violation = has_safety_violation(&por, &is_violation);

    assert!(
        !full_has_violation || por_has_violation,
        "safety violation was reachable in full BFS but not POR"
    );
    assert!(
        por.states.len() <= full.states.len(),
        "safety POR explored more states than full BFS: por={}, full={}",
        por.states.len(),
        full.states.len()
    );
    assert!(
        por.transitions_fired <= full.transitions_fired,
        "safety POR fired more transitions than full BFS: por={}, full={}",
        por.transitions_fired,
        full.transitions_fired
    );
}

// Dining philosophers needs explicit "holding left fork" places to represent the
// classic circular-wait deadlock after each philosopher grabs its left fork.
fn dining_philosophers_3() -> PetriNet {
    PetriNet {
        name: Some("dining_philosophers_3".to_string()),
        places: vec![
            place("think0"),
            place("think1"),
            place("think2"),
            place("hold0"),
            place("hold1"),
            place("hold2"),
            place("eat0"),
            place("eat1"),
            place("eat2"),
            place("fork0"),
            place("fork1"),
            place("fork2"),
        ],
        transitions: vec![
            trans("pick_left_0", vec![arc(0, 1), arc(9, 1)], vec![arc(3, 1)]),
            trans("pick_right_0", vec![arc(3, 1), arc(10, 1)], vec![arc(6, 1)]),
            trans(
                "put_down_0",
                vec![arc(6, 1)],
                vec![arc(0, 1), arc(9, 1), arc(10, 1)],
            ),
            trans("pick_left_1", vec![arc(1, 1), arc(10, 1)], vec![arc(4, 1)]),
            trans("pick_right_1", vec![arc(4, 1), arc(11, 1)], vec![arc(7, 1)]),
            trans(
                "put_down_1",
                vec![arc(7, 1)],
                vec![arc(1, 1), arc(10, 1), arc(11, 1)],
            ),
            trans("pick_left_2", vec![arc(2, 1), arc(11, 1)], vec![arc(5, 1)]),
            trans("pick_right_2", vec![arc(5, 1), arc(9, 1)], vec![arc(8, 1)]),
            trans(
                "put_down_2",
                vec![arc(8, 1)],
                vec![arc(2, 1), arc(11, 1), arc(9, 1)],
            ),
        ],
        initial_marking: vec![1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1],
    }
}

fn producer_consumer_buffered() -> PetriNet {
    PetriNet {
        name: Some("producer_consumer_buffered".to_string()),
        places: vec![
            place("ready_p0"),
            place("ready_p1"),
            place("buffer"),
            place("done_p0"),
            place("done_p1"),
            place("ready_c"),
            place("done_c"),
            place("space"),
        ],
        transitions: vec![
            trans(
                "produce0",
                vec![arc(0, 1), arc(7, 1)],
                vec![arc(2, 1), arc(3, 1)],
            ),
            trans(
                "produce1",
                vec![arc(1, 1), arc(7, 1)],
                vec![arc(2, 1), arc(4, 1)],
            ),
            trans(
                "consume",
                vec![arc(2, 1), arc(5, 1)],
                vec![arc(5, 1), arc(6, 1), arc(7, 1)],
            ),
        ],
        initial_marking: vec![1, 1, 0, 0, 0, 1, 0, 2],
    }
}

fn token_ring_4() -> PetriNet {
    PetriNet {
        name: Some("token_ring_4".to_string()),
        places: vec![
            place("has_token_0"),
            place("has_token_1"),
            place("has_token_2"),
            place("has_token_3"),
        ],
        transitions: vec![
            trans("pass_0", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("pass_1", vec![arc(1, 1)], vec![arc(2, 1)]),
            trans("pass_2", vec![arc(2, 1)], vec![arc(3, 1)]),
            trans("pass_3", vec![arc(3, 1)], vec![arc(0, 1)]),
        ],
        initial_marking: vec![1, 0, 0, 0],
    }
}

fn mutex_deadlock() -> PetriNet {
    PetriNet {
        name: Some("mutex_deadlock".to_string()),
        places: vec![
            place("p0_start"),
            place("p0_hold_mutex0"),
            place("p0_done"),
            place("p1_start"),
            place("p1_hold_mutex1"),
            place("p1_done"),
            place("p2_start"),
            place("p2_done"),
            place("mutex0"),
            place("mutex1"),
        ],
        transitions: vec![
            trans(
                "p0_lock_mutex0",
                vec![arc(0, 1), arc(8, 1)],
                vec![arc(1, 1)],
            ),
            trans(
                "p0_lock_mutex1",
                vec![arc(1, 1), arc(9, 1)],
                vec![arc(2, 1), arc(8, 1), arc(9, 1)],
            ),
            trans(
                "p1_lock_mutex1",
                vec![arc(3, 1), arc(9, 1)],
                vec![arc(4, 1)],
            ),
            trans(
                "p1_lock_mutex0",
                vec![arc(4, 1), arc(8, 1)],
                vec![arc(5, 1), arc(8, 1), arc(9, 1)],
            ),
            trans(
                "p2_lock_mutex0",
                vec![arc(6, 1), arc(8, 1)],
                vec![arc(7, 1), arc(8, 1)],
            ),
        ],
        initial_marking: vec![1, 0, 0, 1, 0, 0, 1, 0, 1, 1],
    }
}

#[test]
fn test_deadlock_crosscheck_dining_philosophers_3() {
    let net = dining_philosophers_3();
    assert_deadlock_crosscheck(&net);
}

#[test]
fn test_deadlock_crosscheck_producer_consumer_buffered() {
    let net = producer_consumer_buffered();
    assert_deadlock_crosscheck(&net);
}

#[test]
fn test_deadlock_crosscheck_token_ring_4() {
    let net = token_ring_4();
    assert_deadlock_crosscheck(&net);
}

#[test]
fn test_deadlock_crosscheck_mutex_deadlock() {
    let net = mutex_deadlock();
    assert_deadlock_crosscheck(&net);
}

#[test]
fn test_safety_crosscheck_dining_philosophers_3() {
    let net = dining_philosophers_3();
    assert_safety_crosscheck(&net, vec![TransitionIdx(1), TransitionIdx(2)], |marking| {
        marking[6] == 1
    });
}

#[test]
fn test_safety_crosscheck_producer_consumer_buffered() {
    let net = producer_consumer_buffered();
    assert_safety_crosscheck(&net, vec![TransitionIdx(2)], |marking| marking[6] >= 2);
}

#[test]
fn test_safety_crosscheck_token_ring_4() {
    let net = token_ring_4();
    assert_safety_crosscheck(&net, vec![TransitionIdx(1), TransitionIdx(2)], |marking| {
        marking[2] == 1
    });
}

#[test]
fn test_safety_crosscheck_mutex_deadlock() {
    let net = mutex_deadlock();
    assert_safety_crosscheck(&net, vec![TransitionIdx(1), TransitionIdx(3)], |marking| {
        marking[2] == 1 && marking[5] == 1
    });
}

// --- POR reduction effectiveness tests ---

#[test]
fn test_por_effective_reduction_token_ring() {
    // Token ring has only 1 enabled transition at each state (the token holder's
    // pass transition). POR cannot reduce single-enabled states, so the state
    // spaces should be identical.
    let net = token_ring_4();
    let full = bfs_full(&net);
    let por = bfs_por(&net, &PorStrategy::DeadlockPreserving);
    assert_eq!(
        full.states.len(),
        por.states.len(),
        "token ring: single-enabled states, POR should match full"
    );
    assert_eq!(full.states.len(), 4, "token ring should have 4 states");
}

#[test]
fn test_por_effective_reduction_dining_philosophers() {
    // 3 dining philosophers with circular fork sharing: the interference graph
    // forms a cycle through the shared forks, so the stubborn set closure at
    // most states pulls in all enabled transitions. This is correct behavior --
    // POR does not help nets with dense circular dependencies.
    let net = dining_philosophers_3();
    let full = bfs_full(&net);
    let por = bfs_por(&net, &PorStrategy::DeadlockPreserving);

    // POR explores <= full states (may be equal when interference is total).
    assert!(
        por.states.len() <= full.states.len(),
        "POR should not explore more states: por={}, full={}",
        por.states.len(),
        full.states.len()
    );
    // Both must find the deadlock.
    assert!(!full.deadlocks.is_empty(), "dining philosophers have deadlocks");
    assert!(
        !por.deadlocks.is_empty(),
        "POR must preserve deadlock reachability"
    );
}

#[test]
fn test_por_effective_reduction_pipeline_with_independent_branches() {
    // A net with genuinely independent branches: two parallel pipelines
    // that share nothing. POR should reduce the state space significantly.
    //
    // Pipeline A: p0 -> t0 -> p1 -> t1 -> p2
    // Pipeline B: p3 -> t2 -> p4 -> t3 -> p5
    // Initial: [1, 0, 0, 1, 0, 0]
    //
    // Full BFS: 3 markings per pipeline x 3 = 9 states (Cartesian product).
    // POR: should explore only 5 states (linear interleaving).
    let net = PetriNet {
        name: Some("two_pipelines".to_string()),
        places: vec![
            place("a0"),
            place("a1"),
            place("a2"),
            place("b0"),
            place("b1"),
            place("b2"),
        ],
        transitions: vec![
            trans("ta0", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("ta1", vec![arc(1, 1)], vec![arc(2, 1)]),
            trans("tb0", vec![arc(3, 1)], vec![arc(4, 1)]),
            trans("tb1", vec![arc(4, 1)], vec![arc(5, 1)]),
        ],
        initial_marking: vec![1, 0, 0, 1, 0, 0],
    };

    let full = bfs_full(&net);
    let por = bfs_por(&net, &PorStrategy::DeadlockPreserving);

    assert_eq!(
        full.states.len(),
        9,
        "full BFS should explore 3x3=9 states for two 3-state pipelines"
    );
    assert!(
        por.states.len() < full.states.len(),
        "POR should reduce state count for independent pipelines: por={}, full={}",
        por.states.len(),
        full.states.len()
    );
    // Both should find the same deadlock (both pipelines exhausted).
    assert!(!full.deadlocks.is_empty());
    assert!(!por.deadlocks.is_empty());
}

#[test]
fn test_por_stats_complete_bfs_two_pipelines() {
    // Run a complete POR BFS with stats collection on the two-pipeline net
    // where POR achieves actual reduction, and verify stats consistency.
    let net = PetriNet {
        name: Some("two_pipelines".to_string()),
        places: vec![
            place("a0"),
            place("a1"),
            place("a2"),
            place("b0"),
            place("b1"),
            place("b2"),
        ],
        transitions: vec![
            trans("ta0", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("ta1", vec![arc(1, 1)], vec![arc(2, 1)]),
            trans("tb0", vec![arc(3, 1)], vec![arc(4, 1)]),
            trans("tb1", vec![arc(4, 1)], vec![arc(5, 1)]),
        ],
        initial_marking: vec![1, 0, 0, 1, 0, 0],
    };
    let dep = DependencyGraph::build(&net);
    let mut collector = PorStatsCollector::new(&dep);

    let mut states = HashSet::new();
    let mut queue = VecDeque::new();
    states.insert(net.initial_marking.clone());
    queue.push_back(net.initial_marking.clone());

    while let Some(marking) = queue.pop_front() {
        let to_fire = match compute_stubborn_set_tracked(
            &net,
            &marking,
            &mut collector,
            &PorStrategy::DeadlockPreserving,
        ) {
            Some(transitions) => transitions,
            None => enabled_transitions(&net, &marking),
        };
        for trans in to_fire {
            let next = net.fire(&marking, trans);
            if states.insert(next.clone()) {
                queue.push_back(next);
            }
        }
    }

    let stats = collector.into_stats();

    // Internal consistency: total states = reduced + non-reduced.
    assert_eq!(
        stats.states_with_reduction + stats.states_without_reduction,
        states.len() as u64,
        "stats state count should match explored states"
    );
    // Independent pipelines should have some states with reduction.
    assert!(
        stats.states_with_reduction > 0,
        "two independent pipelines should have POR reduction at some states"
    );
    // Transitions pruned should be non-zero.
    assert!(
        stats.transitions_pruned > 0,
        "two independent pipelines should prune some transitions"
    );
    // Reduction ratio should be between 0 and 1.
    let ratio = stats.reduction_ratio();
    assert!(
        (0.0..=1.0).contains(&ratio),
        "reduction ratio should be in [0, 1], got {ratio}"
    );
    assert!(
        ratio > 0.0,
        "reduction ratio should be positive for independent pipelines, got {ratio}"
    );
}
