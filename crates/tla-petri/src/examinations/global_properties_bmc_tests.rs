// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for GlobalProperties BMC + k-induction encoding.

use crate::petri_net::{Arc, PetriNet, PlaceIdx, PlaceInfo, TransitionInfo};

use super::{
    encode_dead_predicate, encode_deadlock_bmc_script, encode_deadlock_kinduction_script,
    encode_not_dead_predicate, encode_one_safe_bmc_script, encode_one_safe_kinduction_script,
    encode_quasi_liveness_bmc_script, encode_stable_marking_bmc_script,
    encode_stable_marking_kinduction_script, encode_transition_disabled_bmc,
    encode_transition_disabled_kinduction,
};

fn place(id: &str) -> PlaceInfo {
    PlaceInfo {
        id: id.to_string(),
        name: None,
    }
}

fn arc(place: u32, weight: u64) -> Arc {
    Arc {
        place: PlaceIdx(place),
        weight,
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

/// p0(1) → [t0] → p1(0): linear net, deadlocks after t0 fires once.
fn linear_net() -> PetriNet {
    PetriNet {
        name: Some("linear".to_string()),
        places: vec![place("p0"), place("p1")],
        transitions: vec![trans("t0", vec![arc(0, 1)], vec![arc(1, 1)])],
        initial_marking: vec![1, 0],
    }
}

/// p0(1) → [t0] → p1(0) → [t1] → p0: cyclic net, never deadlocks.
fn cyclic_net() -> PetriNet {
    PetriNet {
        name: Some("cyclic".to_string()),
        places: vec![place("p0"), place("p1")],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t1", vec![arc(1, 1)], vec![arc(0, 1)]),
        ],
        initial_marking: vec![1, 0],
    }
}

/// p0(2) → [t0] → p1(0): starts with 2 tokens, violates 1-safety at step 0.
fn unsafe_initial_net() -> PetriNet {
    PetriNet {
        name: Some("unsafe-initial".to_string()),
        places: vec![place("p0"), place("p1")],
        transitions: vec![trans("t0", vec![arc(0, 1)], vec![arc(1, 1)])],
        initial_marking: vec![2, 0],
    }
}

/// p0(1) → [t0] → p1(0), p0(1) → [t1] → p1(0): two transitions produce to same place.
fn converging_net() -> PetriNet {
    PetriNet {
        name: Some("converging".to_string()),
        places: vec![place("p0"), place("p1")],
        transitions: vec![
            trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t1", vec![arc(0, 1)], vec![arc(1, 1)]),
        ],
        initial_marking: vec![2, 0],
    }
}

// ── Dead predicate encoding ──────────────────────────────────────────

#[test]
fn test_dead_predicate_linear_net() {
    let net = linear_net();
    let pred = encode_dead_predicate(&net, 0);
    // t0 needs m_0_0 >= 1, so disabled when m_0_0 < 1
    assert_eq!(pred, "(< m_0_0 1)");
}

#[test]
fn test_not_dead_predicate_linear_net() {
    let net = linear_net();
    let pred = encode_not_dead_predicate(&net, 0);
    assert_eq!(pred, "(>= m_0_0 1)");
}

#[test]
fn test_dead_predicate_cyclic_net() {
    let net = cyclic_net();
    let pred = encode_dead_predicate(&net, 2);
    // Two transitions: t0 needs p0>=1, t1 needs p1>=1
    // dead = (p0 < 1) AND (p1 < 1)
    assert_eq!(pred, "(and (< m_2_0 1) (< m_2_1 1))");
}

#[test]
fn test_not_dead_predicate_cyclic_net() {
    let net = cyclic_net();
    let pred = encode_not_dead_predicate(&net, 2);
    assert_eq!(pred, "(or (>= m_2_0 1) (>= m_2_1 1))");
}

#[test]
fn test_dead_predicate_no_transitions() {
    let net = PetriNet {
        name: None,
        places: vec![place("p0")],
        transitions: vec![],
        initial_marking: vec![1],
    };
    assert_eq!(encode_dead_predicate(&net, 0), "true");
    assert_eq!(encode_not_dead_predicate(&net, 0), "false");
}

#[test]
fn test_dead_predicate_source_transition() {
    // Source transition (no inputs) → always enabled → never dead
    let net = PetriNet {
        name: None,
        places: vec![place("p0")],
        transitions: vec![trans("t_src", vec![], vec![arc(0, 1)])],
        initial_marking: vec![0],
    };
    assert_eq!(encode_dead_predicate(&net, 0), "false");
    assert_eq!(encode_not_dead_predicate(&net, 0), "true");
}

#[test]
fn test_dead_predicate_multi_input_transition() {
    // t0 needs p0>=2 AND p1>=3
    let net = PetriNet {
        name: None,
        places: vec![place("p0"), place("p1")],
        transitions: vec![trans("t0", vec![arc(0, 2), arc(1, 3)], vec![])],
        initial_marking: vec![0, 0],
    };
    // disabled = p0 < 2 OR p1 < 3
    assert_eq!(
        encode_dead_predicate(&net, 0),
        "(or (< m_0_0 2) (< m_0_1 3))"
    );
}

// ── Deadlock BMC script structure ────────────────────────────────────

#[test]
fn test_deadlock_bmc_script_contains_initial_marking() {
    let net = linear_net();
    let script = encode_deadlock_bmc_script(&net, 1);
    assert!(script.contains("(assert (= m_0_0 1))"));
    assert!(script.contains("(assert (= m_0_1 0))"));
}

#[test]
fn test_deadlock_bmc_script_contains_dead_goal() {
    let net = linear_net();
    let script = encode_deadlock_bmc_script(&net, 1);
    // Should assert OR of dead at steps 0 and 1
    assert!(script.contains("(assert (or"));
    assert!(script.contains("(< m_0_0 1)")); // dead at step 0
    assert!(script.contains("(< m_1_0 1)")); // dead at step 1
}

#[test]
fn test_deadlock_bmc_script_has_check_sat() {
    let net = linear_net();
    let script = encode_deadlock_bmc_script(&net, 1);
    assert!(script.contains("(check-sat)"));
    assert!(script.contains("(exit)"));
}

// ── Deadlock k-induction script structure ────────────────────────────

#[test]
fn test_deadlock_kinduction_no_initial_marking() {
    let net = linear_net();
    let script = encode_deadlock_kinduction_script(&net, 1);
    // k-induction should NOT fix initial marking
    assert!(!script.contains("(assert (= m_0_0 1))"));
    // But should have state equation (parikh variables)
    assert!(script.contains("parikh_"));
}

#[test]
fn test_deadlock_kinduction_hypothesis_and_check() {
    let net = cyclic_net();
    let script = encode_deadlock_kinduction_script(&net, 2);
    // Hypothesis: NOT dead at steps 0, 1
    let not_dead = encode_not_dead_predicate(&net, 0);
    assert!(
        script.contains(&format!("(assert {})", not_dead)),
        "should assert not-dead at step 0"
    );
    // Check: dead at step 2
    let dead = encode_dead_predicate(&net, 2);
    assert!(
        script.contains(&format!("(assert {})", dead)),
        "should assert dead at final step"
    );
}

// ── OneSafe BMC script structure ─────────────────────────────────────

#[test]
fn test_one_safe_bmc_script_checks_all_places_all_steps() {
    let net = linear_net();
    let script = encode_one_safe_bmc_script(&net, 1);
    // Should check m >= 2 for each place at each step
    assert!(script.contains("(>= m_0_0 2)"));
    assert!(script.contains("(>= m_0_1 2)"));
    assert!(script.contains("(>= m_1_0 2)"));
    assert!(script.contains("(>= m_1_1 2)"));
}

#[test]
fn test_one_safe_bmc_unsafe_initial_should_be_satisfiable_at_step_0() {
    let net = unsafe_initial_net();
    let script = encode_one_safe_bmc_script(&net, 0);
    // Initial marking has p0=2, so (>= m_0_0 2) is satisfiable
    assert!(script.contains("(assert (= m_0_0 2))"));
    assert!(script.contains("(>= m_0_0 2)"));
}

// ── OneSafe k-induction script structure ─────────────────────────────

#[test]
fn test_one_safe_kinduction_hypothesis_constrains_all_places() {
    let net = cyclic_net();
    let script = encode_one_safe_kinduction_script(&net, 2);
    // Hypothesis: all places <= 1 at steps 0, 1
    assert!(script.contains("(assert (<= m_0_0 1))"));
    assert!(script.contains("(assert (<= m_0_1 1))"));
    assert!(script.contains("(assert (<= m_1_0 1))"));
    assert!(script.contains("(assert (<= m_1_1 1))"));
    // Check: some place > 1 at step 2
    assert!(script.contains("(>= m_2_0 2)"));
    assert!(script.contains("(>= m_2_1 2)"));
}

// ── QuasiLiveness BMC script structure ───────────────────────────────

#[test]
fn test_quasi_liveness_bmc_per_transition_push_pop() {
    let net = cyclic_net();
    let pending = vec![0, 1]; // both transitions
    let script = encode_quasi_liveness_bmc_script(&net, &pending, 1);
    // Should have push/pop blocks for each transition
    let push_count = script.matches("(push 1)").count();
    let pop_count = script.matches("(pop 1)").count();
    assert_eq!(push_count, 2, "one push per pending transition");
    assert_eq!(pop_count, 2, "one pop per pending transition");
    // Each transition's enabledness guard
    assert!(script.contains("(>= m_0_0 1)"), "t0 needs p0>=1");
    assert!(script.contains("(>= m_0_1 1)"), "t1 needs p1>=1");
}

#[test]
fn test_quasi_liveness_bmc_single_transition() {
    let net = linear_net();
    let pending = vec![0];
    let script = encode_quasi_liveness_bmc_script(&net, &pending, 2);
    // Should check t0 enabledness at steps 0, 1, 2
    assert!(script.contains("(>= m_0_0 1)"));
    assert!(script.contains("(>= m_1_0 1)"));
    assert!(script.contains("(>= m_2_0 1)"));
}

// ── StableMarking BMC script structure ───────────────────────────────

#[test]
fn test_stable_marking_bmc_checks_deviation_from_initial() {
    let net = linear_net(); // m0 = [1, 0]
    let pending = vec![0, 1];
    let script = encode_stable_marking_bmc_script(&net, &pending, 1);
    // p0 with initial=1: check (not (= m_s_0 1))
    assert!(script.contains("(not (= m_0_0 1))"));
    assert!(script.contains("(not (= m_1_0 1))"));
    // p1 with initial=0: check (not (= m_s_1 0))
    assert!(script.contains("(not (= m_0_1 0))"));
    assert!(script.contains("(not (= m_1_1 0))"));
}

#[test]
fn test_stable_marking_bmc_push_pop_per_place() {
    let net = converging_net();
    let pending = vec![0, 1];
    let script = encode_stable_marking_bmc_script(&net, &pending, 1);
    let push_count = script.matches("(push 1)").count();
    assert_eq!(push_count, 2, "one push per pending place");
}

// ── StableMarking k-induction script structure ───────────────────────

#[test]
fn test_stable_marking_kinduction_hypothesis_and_check() {
    let net = linear_net(); // m0 = [1, 0]
    let candidates = vec![0]; // check if p0 is stable
    let script = encode_stable_marking_kinduction_script(&net, &candidates, 2);
    // Hypothesis: m_0_0 = 1 and m_1_0 = 1
    assert!(script.contains("(assert (= m_0_0 1))"));
    assert!(script.contains("(assert (= m_1_0 1))"));
    // Check: m_2_0 != 1
    assert!(script.contains("(assert (not (= m_2_0 1)))"));
}

#[test]
fn test_stable_marking_kinduction_has_strengthening() {
    let net = cyclic_net();
    let candidates = vec![0];
    let script = encode_stable_marking_kinduction_script(&net, &candidates, 1);
    // Should have state equation strengthening
    assert!(script.contains("parikh_0"));
    assert!(script.contains("parikh_1"));
}

// ── Integration tests (require z4) ──────────────────────────────────

#[test]
fn test_deadlock_bmc_linear_net_finds_deadlock() {
    let net = linear_net();
    match super::run_deadlock_bmc(&net, None) {
        Some(true) => {} // expected: deadlock found
        Some(false) => panic!("linear net DOES deadlock, should not prove freedom"),
        None => eprintln!("z4 not available, skipping integration test"),
    }
}

#[test]
fn test_deadlock_bmc_cyclic_net_proves_freedom() {
    let net = cyclic_net();
    match super::run_deadlock_bmc(&net, None) {
        Some(false) => {} // expected: deadlock-free proved
        Some(true) => panic!("cyclic net does NOT deadlock"),
        None => eprintln!("z4 not available, skipping integration test"),
    }
}

#[test]
fn test_one_safe_bmc_unsafe_initial_finds_violation() {
    let net = unsafe_initial_net();
    match super::run_one_safe_bmc(&net, None) {
        Some(false) => {} // expected: violation found
        Some(true) => panic!("net with p0=2 is NOT 1-safe"),
        None => eprintln!("z4 not available, skipping integration test"),
    }
}

#[test]
fn test_one_safe_bmc_cyclic_1safe_proves_safety() {
    let net = cyclic_net(); // 1 token cycling between 2 places
    match super::run_one_safe_bmc(&net, None) {
        Some(true) => {} // expected: 1-safe proved
        Some(false) => panic!("cyclic net with 1 token IS 1-safe"),
        None => eprintln!("z4 not available, skipping integration test"),
    }
}

#[test]
fn test_quasi_liveness_bmc_cyclic_all_resolved() {
    let net = cyclic_net();
    let resolved = super::run_quasi_liveness_bmc(&net, None);
    if resolved.iter().any(|&r| r) {
        // z4 available: both transitions should be resolved
        assert!(resolved.iter().all(|&r| r), "all transitions should fire");
    } else {
        eprintln!("z4 not available, skipping integration test");
    }
}

#[test]
fn test_stable_marking_bmc_linear_net() {
    let net = linear_net(); // p0 goes 1→0, p1 goes 0→1 → both unstable
    match super::run_stable_marking_bmc(&net, None) {
        Some(result) => match result.verdict {
            Some(false) => {} // expected: all places unstable
            Some(true) => panic!("linear net places are NOT stable"),
            None => {
                // Partial result — at least some places should be unstable
                assert!(result.unstable.iter().any(|&u| u));
            }
        },
        None => eprintln!("z4 not available, skipping integration test"),
    }
}

// ── Deadline handling ────────────────────────────────────────────────

#[test]
fn test_deadlock_bmc_expired_deadline_returns_none() {
    let net = linear_net();
    let expired = Some(std::time::Instant::now() - std::time::Duration::from_secs(1));
    // With expired deadline, should return None (inconclusive)
    assert_eq!(super::run_deadlock_bmc(&net, expired), None);
}

#[test]
fn test_one_safe_bmc_expired_deadline_returns_none() {
    let net = linear_net();
    let expired = Some(std::time::Instant::now() - std::time::Duration::from_secs(1));
    assert_eq!(super::run_one_safe_bmc(&net, expired), None);
}

// ── Liveness BMC encoding ──────────────────────────────────────────────

#[test]
fn test_liveness_bmc_disabled_encoding_linear_net() {
    let net = linear_net();
    // t0: p0 >= 1. disabled = p0 < 1
    let script = encode_transition_disabled_bmc(&net, 0, 1);
    assert!(script.contains("(set-logic QF_LIA)"));
    assert!(script.contains("(< m_0_0 1)") || script.contains("(< m_1_0 1)"));
    assert!(script.contains("(check-sat)"));
}

#[test]
fn test_liveness_bmc_disabled_encoding_cyclic_net() {
    let net = cyclic_net();
    let script = encode_transition_disabled_bmc(&net, 0, 2);
    assert!(script.contains("(< m_0_0 1)"));
    assert!(script.contains("(< m_2_0 1)"));
}

#[test]
fn test_liveness_kinduction_encoding_linear_net() {
    let net = linear_net();
    let script = encode_transition_disabled_kinduction(&net, 0, 1);
    assert!(script.contains("(set-logic QF_LIA)"));
    // Hypothesis: t0 disabled at step 0
    assert!(script.contains("(< m_0_0 1)"));
    // Check: t0 enabled at step 1
    assert!(script.contains("(>= m_1_0 1)"));
}

#[test]
fn test_liveness_kinduction_encoding_source_transition() {
    let net = PetriNet {
        name: None,
        places: vec![place("p0")],
        transitions: vec![trans("t_src", vec![], vec![arc(0, 1)])],
        initial_marking: vec![0],
    };
    let script = encode_transition_disabled_kinduction(&net, 0, 1);
    assert!(script.contains("(assert false)"));
}

// ── Liveness BMC: multi-input transition encoding ─────────────────────

/// t0 needs p0>=2 AND p1>=3 (two input arcs with different weights).
/// Verifies disabled/enabled encoding uses correct OR/AND structure.
fn multi_input_net() -> PetriNet {
    PetriNet {
        name: Some("multi_input".to_string()),
        places: vec![place("p0"), place("p1"), place("p2")],
        transitions: vec![trans("t0", vec![arc(0, 2), arc(1, 3)], vec![arc(2, 1)])],
        initial_marking: vec![2, 3, 0],
    }
}

#[test]
fn test_liveness_bmc_disabled_encoding_multi_input_transition() {
    let net = multi_input_net();
    let script = encode_transition_disabled_bmc(&net, 0, 1);

    // disabled(t0, s) = (or (< m_s_0 2) (< m_s_1 3))
    // The BMC asserts disabled at some step in 0..=depth
    assert!(
        script.contains("(< m_0_0 2)"),
        "should check p0 < 2 at step 0"
    );
    assert!(
        script.contains("(< m_0_1 3)"),
        "should check p1 < 3 at step 0"
    );
    assert!(
        script.contains("(< m_1_0 2)"),
        "should check p0 < 2 at step 1"
    );
    assert!(
        script.contains("(< m_1_1 3)"),
        "should check p1 < 3 at step 1"
    );
    // The disabled predicate for a multi-input transition must use OR (any
    // input insufficient → disabled), not AND.
    assert!(
        script.contains("(or (< m_0_0 2) (< m_0_1 3))"),
        "disabled predicate at step 0 must be OR of input guards"
    );
}

#[test]
fn test_liveness_kinduction_encoding_multi_input_transition() {
    let net = multi_input_net();
    // depth=2: hypothesis at steps 0,1; check enabled at step 2
    let script = encode_transition_disabled_kinduction(&net, 0, 2);

    // Hypothesis: t0 disabled at step 0 — (or (< m_0_0 2) (< m_0_1 3))
    assert!(
        script.contains("(assert (or (< m_0_0 2) (< m_0_1 3)))"),
        "hypothesis: t0 disabled at step 0 via OR"
    );
    // Hypothesis: t0 disabled at step 1
    assert!(
        script.contains("(assert (or (< m_1_0 2) (< m_1_1 3)))"),
        "hypothesis: t0 disabled at step 1 via OR"
    );
    // Check: t0 ENABLED at step 2 — (and (>= m_2_0 2) (>= m_2_1 3))
    assert!(
        script.contains("(assert (and (>= m_2_0 2) (>= m_2_1 3)))"),
        "check: t0 enabled at step 2 via AND"
    );
}

#[test]
fn test_liveness_kinduction_single_vs_multi_input_structure() {
    // Single-input: disabled = bare "(< m_s_p w)", no (or ...) wrapper
    let single_net = linear_net(); // t0: p0>=1
    let single_script = encode_transition_disabled_kinduction(&single_net, 0, 1);
    // Hypothesis at step 0: bare guard, no or
    assert!(
        single_script.contains("(assert (< m_0_0 1))"),
        "single-input hypothesis: bare < guard without or wrapper"
    );
    // Check at step 1: bare guard, no and
    assert!(
        single_script.contains("(assert (>= m_1_0 1))"),
        "single-input check: bare >= guard without and wrapper"
    );

    // Multi-input: disabled = (or ...), enabled = (and ...)
    let multi_script = encode_transition_disabled_kinduction(&multi_input_net(), 0, 1);
    assert!(
        multi_script.contains("(assert (or (< m_0_0 2) (< m_0_1 3)))"),
        "multi-input hypothesis: (or ...) wrapper"
    );
    assert!(
        multi_script.contains("(assert (and (>= m_1_0 2) (>= m_1_1 3)))"),
        "multi-input check: (and ...) wrapper"
    );
}

#[test]
fn test_liveness_kinduction_depth_two_includes_stutter_steps() {
    let script = encode_transition_disabled_kinduction(&cyclic_net(), 0, 2);

    assert!(
        script.contains("(assert (or stay_0 fire_0_0 fire_0_1))"),
        "depth-2 script should allow stuttering before any transition fires"
    );
    assert!(
        script.contains("(assert (=> stay_0 (= m_1_0 m_0_0)))"),
        "stay_0 should preserve the marking into step 1"
    );
    assert!(
        script.contains("(assert (=> stay_1 (= m_2_0 m_1_0)))"),
        "stay_1 should preserve the marking into step 2"
    );
}

#[test]
fn test_liveness_bmc_expired_deadline_returns_none() {
    let net = linear_net();
    let expired = Some(std::time::Instant::now() - std::time::Duration::from_secs(1));
    assert_eq!(super::run_liveness_bmc(&net, expired), None);
}

#[test]
fn test_liveness_bmc_cyclic_net_returns_none() {
    let net = cyclic_net();
    assert_eq!(super::run_liveness_bmc(&net, None), None);
}

#[test]
fn test_liveness_bmc_no_transitions_returns_none() {
    let net = PetriNet {
        name: None,
        places: vec![place("p0")],
        transitions: vec![],
        initial_marking: vec![1],
    };
    assert_eq!(super::run_liveness_bmc(&net, None), None);
}
