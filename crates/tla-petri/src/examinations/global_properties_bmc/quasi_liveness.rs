// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::time::Instant;

use crate::petri_net::PetriNet;

use super::super::bmc_runner::{emit_bmc_preamble, run_depth_ladder, DepthAction, DepthQuery};
use super::super::smt_encoding::{find_z4, SolverOutcome, DEPTH_LADDER, PER_DEPTH_TIMEOUT};

/// Run per-transition BMC for QuasiLiveness.
///
/// Returns a vector of booleans parallel to net.transitions:
/// `true` = transition proven quasi-live (BMC found enabling state),
/// `false` = unresolved. Does not attempt k-induction (proving
/// "always enabled" is much stronger than "sometimes enabled").
pub(crate) fn run_quasi_liveness_bmc(net: &PetriNet, deadline: Option<Instant>) -> Vec<bool> {
    let nt = net.num_transitions();
    let mut resolved = vec![false; nt];

    // Transitions with no inputs are always enabled.
    for (i, t) in net.transitions.iter().enumerate() {
        if t.inputs.is_empty() {
            resolved[i] = true;
        }
    }

    let z4_path = match find_z4() {
        Some(p) => p,
        None => return resolved,
    };

    struct QuasiLivenessState<'a> {
        net: &'a PetriNet,
        resolved: &'a mut [bool],
        pending: Vec<usize>,
    }

    let mut state = QuasiLivenessState {
        net,
        resolved: &mut resolved,
        pending: Vec::new(),
    };

    let _ = run_depth_ladder(
        &z4_path,
        DEPTH_LADDER,
        deadline,
        PER_DEPTH_TIMEOUT,
        &mut state,
        |state, depth| {
            state.pending = (0..state.resolved.len())
                .filter(|&transition_idx| !state.resolved[transition_idx])
                .collect();
            if state.pending.is_empty() {
                return None;
            }

            Some(DepthQuery::new(
                encode_quasi_liveness_bmc_script(state.net, &state.pending, depth),
                state.pending.len(),
            ))
        },
        |state, depth, results| match results {
            Some(results) => {
                let mut had_unknown = false;
                for (&transition_idx, outcome) in state.pending.iter().zip(results.iter()) {
                    match outcome {
                        SolverOutcome::Sat => state.resolved[transition_idx] = true,
                        SolverOutcome::Unknown => had_unknown = true,
                        SolverOutcome::Unsat => {}
                    }
                }

                let newly_resolved = state
                    .pending
                    .iter()
                    .filter(|&&transition_idx| state.resolved[transition_idx])
                    .count();
                if newly_resolved > 0 {
                    eprintln!(
                        "QuasiLiveness BMC depth {depth}: {newly_resolved} transitions resolved"
                    );
                }

                if had_unknown {
                    DepthAction::StopDeepening
                } else {
                    DepthAction::Explored
                }
            }
            None => DepthAction::StopDeepening,
        },
    );

    resolved
}

pub(super) fn encode_quasi_liveness_bmc_script(
    net: &PetriNet,
    pending_transitions: &[usize],
    depth: usize,
) -> String {
    let mut s = String::with_capacity(4096);
    emit_bmc_preamble(&mut s, net, depth);

    // Per-transition check: exists step where transition is enabled
    for &tidx in pending_transitions {
        s.push_str("(push 1)\n");

        let transition = &net.transitions[tidx];
        if transition.inputs.is_empty() {
            // Always enabled -- trivially SAT
            s.push_str("(assert true)\n");
        } else {
            s.push_str("(assert (or");
            for step in 0..=depth {
                let guards: Vec<String> = transition
                    .inputs
                    .iter()
                    .map(|arc| format!("(>= m_{}_{} {})", step, arc.place.0, arc.weight))
                    .collect();
                if guards.len() == 1 {
                    s.push_str(&format!(" {}", guards[0]));
                } else {
                    s.push_str(&format!(" (and {})", guards.join(" ")));
                }
            }
            s.push_str("))\n");
        }

        s.push_str("(check-sat)\n(pop 1)\n");
    }

    s.push_str("(exit)\n");
    s
}
