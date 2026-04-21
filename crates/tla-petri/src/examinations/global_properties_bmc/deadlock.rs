// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::time::Instant;

use crate::petri_net::PetriNet;

use super::super::bmc_runner::{emit_bmc_preamble, emit_kinduction_preamble};
use super::super::smt_encoding::find_z4;
use super::{run_bmc_and_kinduction, BmcKindConfig};

/// Run BMC + k-induction for the Deadlock examination.
///
/// Returns `Some(true)` if a deadlock is found (BMC witness),
/// `Some(false)` if deadlock-freedom is proved (k-induction),
/// `None` if inconclusive.
pub(crate) fn run_deadlock_bmc(net: &PetriNet, deadline: Option<Instant>) -> Option<bool> {
    let z4_path = find_z4()?;

    // A net with a source transition (no inputs) is never deadlocked.
    if net.transitions.iter().any(|t| t.inputs.is_empty()) {
        return None; // structural check already handles this
    }

    run_bmc_and_kinduction(
        &z4_path,
        net,
        deadline,
        &BmcKindConfig {
            exam_name: "Deadlock",
            bmc_sat_value: true,
            kind_unsat_value: false,
        },
        encode_deadlock_bmc_script,
        encode_deadlock_kinduction_script,
    )
}

/// Encode "exists path from m0 of length depth such that some step is dead".
pub(super) fn encode_deadlock_bmc_script(net: &PetriNet, depth: usize) -> String {
    let mut s = String::with_capacity(4096);
    emit_bmc_preamble(&mut s, net, depth);

    // Goal: OR over steps 0..=depth of dead(step)
    s.push_str("(assert (or");
    for step in 0..=depth {
        s.push_str(&format!(" {}", encode_dead_predicate(net, step)));
    }
    s.push_str("))\n");
    s.push_str("(check-sat)\n(exit)\n");
    s
}

/// Encode k-induction script for deadlock-freedom.
///
/// - No initial marking (arbitrary start via state equation)
/// - Steps 0..depth-1: assert NOT dead (induction hypothesis)
/// - Step depth: assert dead (induction check)
/// - UNSAT = deadlock-freedom is k-inductive
pub(super) fn encode_deadlock_kinduction_script(net: &PetriNet, depth: usize) -> String {
    let mut s = String::with_capacity(4096);
    emit_kinduction_preamble(&mut s, net, depth);

    // Hypothesis: NOT dead at steps 0..depth-1
    for step in 0..depth {
        let not_dead = encode_not_dead_predicate(net, step);
        s.push_str(&format!("(assert {})\n", not_dead));
    }

    // Check: dead at step depth
    s.push_str(&format!("(assert {})\n", encode_dead_predicate(net, depth)));
    s.push_str("(check-sat)\n(exit)\n");
    s
}

/// Encode the "dead" predicate at a given step.
///
/// dead(s) := AND over all transitions t: NOT enabled(t, s)
/// NOT enabled(t, s) := OR over input arcs (p, w): m_s_p < w
pub(super) fn encode_dead_predicate(net: &PetriNet, step: usize) -> String {
    let nt = net.num_transitions();
    if nt == 0 {
        return "true".to_string(); // no transitions = always dead
    }

    let mut transition_disabled: Vec<String> = Vec::with_capacity(nt);
    for t in &net.transitions {
        if t.inputs.is_empty() {
            // Transition with no inputs is always enabled -> NOT enabled = false
            // -> entire conjunction is false -> marking is never dead
            return "false".to_string();
        }
        let guards: Vec<String> = t
            .inputs
            .iter()
            .map(|arc| format!("(< m_{}_{} {})", step, arc.place.0, arc.weight))
            .collect();
        let disabled = if guards.len() == 1 {
            guards[0].clone()
        } else {
            format!("(or {})", guards.join(" "))
        };
        transition_disabled.push(disabled);
    }

    if transition_disabled.len() == 1 {
        transition_disabled[0].clone()
    } else {
        format!("(and {})", transition_disabled.join(" "))
    }
}

/// Encode the "not dead" predicate at a given step.
///
/// not_dead(s) := OR over all transitions t: enabled(t, s)
pub(super) fn encode_not_dead_predicate(net: &PetriNet, step: usize) -> String {
    let nt = net.num_transitions();
    if nt == 0 {
        return "false".to_string();
    }

    let mut transition_enabled: Vec<String> = Vec::with_capacity(nt);
    for t in &net.transitions {
        if t.inputs.is_empty() {
            return "true".to_string();
        }
        let guards: Vec<String> = t
            .inputs
            .iter()
            .map(|arc| format!("(>= m_{}_{} {})", step, arc.place.0, arc.weight))
            .collect();
        let enabled = if guards.len() == 1 {
            guards[0].clone()
        } else {
            format!("(and {})", guards.join(" "))
        };
        transition_enabled.push(enabled);
    }

    if transition_enabled.len() == 1 {
        transition_enabled[0].clone()
    } else {
        format!("(or {})", transition_enabled.join(" "))
    }
}
