// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::time::Instant;

use crate::petri_net::PetriNet;

use super::super::bmc_runner::{
    emit_bmc_preamble, emit_kinduction_preamble, run_depth_ladder, DepthAction, DepthQuery,
};
use super::super::smt_encoding::{find_z4, SolverOutcome, DEPTH_LADDER, PER_DEPTH_TIMEOUT};

/// Run per-transition BMC + k-induction for the Liveness examination (FALSE direction).
///
/// For each transition `t`, attempts to prove that `t` can become permanently
/// disabled from some reachable marking. The approach has two phases:
///
/// 1. **k-induction**: prove that "transition t disabled" is an inductive
///    invariant — once disabled, it stays disabled forever. This holds when
///    no firing sequence from a t-disabled marking can re-enable t.
///
/// 2. **BMC**: find a reachable marking where t is disabled.
///
/// If both phases succeed for any transition, the net is NOT live (L4).
///
/// Returns:
/// - `Some(false)` if a transition is provably permanently disabled → NOT live
/// - `None` if inconclusive (no transition proven permanently disabled)
pub(crate) fn run_liveness_bmc(net: &PetriNet, deadline: Option<Instant>) -> Option<bool> {
    let z4_path = find_z4()?;
    let nt = net.num_transitions();
    if nt == 0 {
        return None;
    }

    // Phase 1: k-induction per transition (depth 1 only).
    // For each transition t, check if "t disabled" is 1-step inductive:
    // from any state where t is disabled, t remains disabled after any
    // single transition firing.
    //
    // Depth 1 is sufficient because the SMT transition relation allows
    // explicit stutter steps (`stay_*`). Once Phase 2 finds one reachable
    // disabled marking, that same marking can be repeated for any number of
    // hypothesis steps by stuttering. Under this stutter-closed relation,
    // any deeper k-induction proof would imply the depth-1 query already
    // succeeds, so only depth 1 is worth asking.
    let mut inductive = vec![false; nt];
    let kinduction_depths: &[usize] = &[1];

    for tidx in 0..nt {
        if deadline.is_some_and(|d| Instant::now() >= d) {
            break;
        }

        let mut found_inductive = false;
        let _ = run_depth_ladder(
            &z4_path,
            kinduction_depths,
            deadline,
            PER_DEPTH_TIMEOUT,
            &mut found_inductive,
            |_, depth| {
                Some(DepthQuery::new(
                    encode_transition_disabled_kinduction(net, tidx, depth),
                    1,
                ))
            },
            |found_inductive, depth, results| match results {
                Some([SolverOutcome::Unsat]) => {
                    eprintln!(
                        "Liveness BMC: transition {tidx} disabled-stays-disabled \
                         k-induction depth {depth} UNSAT (inductive)"
                    );
                    *found_inductive = true;
                    DepthAction::StopDeepening
                }
                Some([SolverOutcome::Unknown]) | None => DepthAction::StopDeepening,
                Some([SolverOutcome::Sat]) => DepthAction::Explored,
                other => {
                    eprintln!("Liveness BMC k-ind unexpected result: {other:?}");
                    DepthAction::StopDeepening
                }
            },
        );
        inductive[tidx] = found_inductive;
    }

    // If no transition has an inductive "disabled" property, BMC can't help.
    if !inductive.iter().any(|&b| b) {
        return None;
    }

    // Phase 2: BMC — for each inductive transition, find a reachable marking
    // where it is disabled.
    for tidx in 0..nt {
        if !inductive[tidx] {
            continue;
        }
        if deadline.is_some_and(|d| Instant::now() >= d) {
            break;
        }

        let mut found_disabled = false;
        let _ = run_depth_ladder(
            &z4_path,
            DEPTH_LADDER,
            deadline,
            PER_DEPTH_TIMEOUT,
            &mut found_disabled,
            |_, depth| {
                Some(DepthQuery::new(
                    encode_transition_disabled_bmc(net, tidx, depth),
                    1,
                ))
            },
            |found_disabled, depth, results| match results {
                Some([SolverOutcome::Sat]) => {
                    eprintln!(
                        "Liveness BMC: transition {tidx} disabled at reachable \
                         marking (BMC depth {depth}) + inductive → permanently dead"
                    );
                    *found_disabled = true;
                    DepthAction::StopDeepening
                }
                Some([SolverOutcome::Unknown]) | None => DepthAction::StopDeepening,
                Some([SolverOutcome::Unsat]) => DepthAction::Explored,
                other => {
                    eprintln!("Liveness BMC unexpected result: {other:?}");
                    DepthAction::StopDeepening
                }
            },
        );

        if found_disabled {
            // Transition tidx is disabled at a reachable marking AND
            // "disabled stays disabled" is inductive → permanently dead → NOT live.
            return Some(false);
        }
    }

    None
}

/// Encode BMC script: "exists reachable marking at some step where transition t is disabled."
///
/// Uses the standard BMC preamble (initial marking + transition relation) and
/// asserts that transition t is disabled at some step 0..=depth.
pub(super) fn encode_transition_disabled_bmc(net: &PetriNet, tidx: usize, depth: usize) -> String {
    let mut s = String::with_capacity(4096);
    emit_bmc_preamble(&mut s, net, depth);

    let transition = &net.transitions[tidx];
    // Assert: transition t is disabled at some step
    s.push_str("(assert (or");
    for step in 0..=depth {
        // disabled(t, step) = OR over input arcs: m_step_p < weight
        let disabled = encode_transition_disabled(transition, step);
        s.push_str(&format!(" {disabled}"));
    }
    s.push_str("))\n");

    s.push_str("(check-sat)\n(exit)\n");
    s
}

/// Encode k-induction script: "if t is disabled at steps 0..k-1, is t disabled at step k?"
///
/// Uses the k-induction preamble (no initial marking, P-invariant strengthening)
/// and asserts the induction hypothesis (t disabled at steps 0..depth-1) and
/// checks if t must be disabled at step depth.
///
/// UNSAT = "disabled stays disabled" is k-inductive for transition t.
pub(super) fn encode_transition_disabled_kinduction(
    net: &PetriNet,
    tidx: usize,
    depth: usize,
) -> String {
    let mut s = String::with_capacity(4096);
    emit_kinduction_preamble(&mut s, net, depth);

    let transition = &net.transitions[tidx];

    // Hypothesis: t is disabled at steps 0..depth-1
    for step in 0..depth {
        let disabled = encode_transition_disabled(transition, step);
        s.push_str(&format!("(assert {disabled})\n"));
    }

    // Check: t is ENABLED at step depth (negation of disabled)
    // If UNSAT: t cannot become enabled → "disabled stays disabled" is inductive
    let enabled = encode_transition_enabled(transition, depth);
    s.push_str(&format!("(assert {enabled})\n"));

    s.push_str("(check-sat)\n(exit)\n");
    s
}

/// Encode "transition t is disabled at step s".
///
/// disabled(t, s) = OR over input arcs (p, w): m_s_p < w
fn encode_transition_disabled(
    transition: &crate::petri_net::TransitionInfo,
    step: usize,
) -> String {
    if transition.inputs.is_empty() {
        return "false".to_string(); // no inputs → always enabled → never disabled
    }

    let guards: Vec<String> = transition
        .inputs
        .iter()
        .map(|arc| format!("(< m_{}_{} {})", step, arc.place.0, arc.weight))
        .collect();

    if guards.len() == 1 {
        guards[0].clone()
    } else {
        format!("(or {})", guards.join(" "))
    }
}

/// Encode "transition t is enabled at step s".
///
/// enabled(t, s) = AND over input arcs (p, w): m_s_p >= w
fn encode_transition_enabled(transition: &crate::petri_net::TransitionInfo, step: usize) -> String {
    if transition.inputs.is_empty() {
        return "true".to_string(); // no inputs → always enabled
    }

    let guards: Vec<String> = transition
        .inputs
        .iter()
        .map(|arc| format!("(>= m_{}_{} {})", step, arc.place.0, arc.weight))
        .collect();

    if guards.len() == 1 {
        guards[0].clone()
    } else {
        format!("(and {})", guards.join(" "))
    }
}
