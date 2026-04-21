// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::time::Instant;

use crate::petri_net::PetriNet;

use super::super::bmc_runner::{
    emit_bmc_preamble, emit_kinduction_preamble, run_depth_ladder, DepthAction, DepthQuery,
};
use super::super::smt_encoding::{find_z4, SolverOutcome, DEPTH_LADDER, PER_DEPTH_TIMEOUT};

/// Result of StableMarking BMC analysis.
pub(crate) struct StableMarkingBmcResult {
    /// Definitive verdict if BMC/k-induction fully resolved the examination.
    pub verdict: Option<bool>,
    /// Per-place instability: `true` = proven unstable by BMC.
    /// Available even when `verdict` is `None` (partial results).
    pub unstable: Vec<bool>,
}

/// Run BMC + k-induction for the StableMarking examination.
///
/// Returns a `StableMarkingBmcResult` with:
/// - `verdict = Some(true)` if at least one place is proved stable,
/// - `verdict = Some(false)` if all places are shown unstable,
/// - `verdict = None` if inconclusive (partial `unstable` set still useful).
///
/// Returns `None` if z4 is unavailable.
pub(crate) fn run_stable_marking_bmc(
    net: &PetriNet,
    deadline: Option<Instant>,
) -> Option<StableMarkingBmcResult> {
    let z4_path = find_z4()?;
    let np = net.num_places();
    if np == 0 {
        return None;
    }

    // Track per-place instability: true = proven unstable
    let mut unstable = vec![false; np];

    // Phase 1: BMC -- find instability witnesses per place
    struct StableMarkingBmcState<'a> {
        net: &'a PetriNet,
        unstable: &'a mut [bool],
        pending: Vec<usize>,
    }

    let mut bmc_state = StableMarkingBmcState {
        net,
        unstable: &mut unstable,
        pending: Vec::new(),
    };
    let max_bmc_depth = run_depth_ladder(
        &z4_path,
        DEPTH_LADDER,
        deadline,
        PER_DEPTH_TIMEOUT,
        &mut bmc_state,
        |state, depth| {
            state.pending = (0..state.unstable.len())
                .filter(|&place_idx| !state.unstable[place_idx])
                .collect();
            if state.pending.is_empty() {
                return None;
            }

            Some(DepthQuery::new(
                encode_stable_marking_bmc_script(state.net, &state.pending, depth),
                state.pending.len(),
            ))
        },
        |state, depth, results| match results {
            Some(results) => {
                let mut had_unknown = false;
                for (&place_idx, outcome) in state.pending.iter().zip(results.iter()) {
                    match outcome {
                        SolverOutcome::Sat => state.unstable[place_idx] = true,
                        SolverOutcome::Unknown => had_unknown = true,
                        SolverOutcome::Unsat => {}
                    }
                }

                let newly_unstable = state
                    .pending
                    .iter()
                    .filter(|&&place_idx| state.unstable[place_idx])
                    .count();
                if newly_unstable > 0 {
                    eprintln!(
                        "StableMarking BMC depth {depth}: {newly_unstable} places shown unstable"
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

    // All places unstable -> FALSE
    if unstable.iter().all(|&u| u) {
        return Some(StableMarkingBmcResult {
            verdict: Some(false),
            unstable,
        });
    }

    // Phase 2: k-induction -- prove stability for remaining candidate places
    // Soundness gate: same as deadlock (see run_deadlock_bmc).
    let max_kind_depth = match max_bmc_depth {
        Some(d) => d + 1,
        None => {
            return Some(StableMarkingBmcResult {
                verdict: None,
                unstable,
            });
        }
    };
    let candidates: Vec<usize> = (0..np).filter(|&p| !unstable[p]).collect();
    struct StableMarkingKinductionState<'a> {
        verdict: Option<bool>,
        net: &'a PetriNet,
        candidates: &'a [usize],
    }

    let mut kinduction_state = StableMarkingKinductionState {
        verdict: None,
        net,
        candidates: &candidates,
    };
    let _ = run_depth_ladder(
        &z4_path,
        DEPTH_LADDER,
        deadline,
        PER_DEPTH_TIMEOUT,
        &mut kinduction_state,
        |state, depth| {
            if depth > max_kind_depth {
                None
            } else {
                Some(DepthQuery::new(
                    encode_stable_marking_kinduction_script(state.net, state.candidates, depth),
                    state.candidates.len(),
                ))
            }
        },
        |state, depth, results| match results {
            Some(results) => {
                for (&place_idx, outcome) in state.candidates.iter().zip(results.iter()) {
                    if *outcome == SolverOutcome::Unsat {
                        eprintln!(
                            "StableMarking k-ind depth {depth}: place {place_idx} proved stable"
                        );
                        state.verdict = Some(true);
                        return DepthAction::StopDeepening;
                    }
                }

                if results.contains(&SolverOutcome::Unknown) {
                    DepthAction::StopDeepening
                } else {
                    DepthAction::Explored
                }
            }
            None => DepthAction::StopDeepening,
        },
    );
    if kinduction_state.verdict == Some(true) {
        return Some(StableMarkingBmcResult {
            verdict: Some(true),
            unstable,
        });
    }

    Some(StableMarkingBmcResult {
        verdict: None,
        unstable,
    })
}

pub(super) fn encode_stable_marking_bmc_script(
    net: &PetriNet,
    pending_places: &[usize],
    depth: usize,
) -> String {
    let mut s = String::with_capacity(4096);
    emit_bmc_preamble(&mut s, net, depth);

    // Per-place check: exists step where m_s_p != m0(p)
    for &pidx in pending_places {
        let initial = net.initial_marking[pidx];
        s.push_str("(push 1)\n");
        s.push_str("(assert (or");
        for step in 0..=depth {
            s.push_str(&format!(" (not (= m_{}_{} {}))", step, pidx, initial));
        }
        s.push_str("))\n");
        s.push_str("(check-sat)\n(pop 1)\n");
    }

    s.push_str("(exit)\n");
    s
}

pub(super) fn encode_stable_marking_kinduction_script(
    net: &PetriNet,
    candidate_places: &[usize],
    depth: usize,
) -> String {
    let mut s = String::with_capacity(4096);
    emit_kinduction_preamble(&mut s, net, depth);

    // Per-place k-induction: hypothesis m_s_p = m0(p) at steps 0..depth-1,
    // check m_depth_p != m0(p)
    for &pidx in candidate_places {
        let initial = net.initial_marking[pidx];
        s.push_str("(push 1)\n");
        for step in 0..depth {
            s.push_str(&format!("(assert (= m_{}_{} {}))\n", step, pidx, initial));
        }
        s.push_str(&format!(
            "(assert (not (= m_{}_{} {})))\n",
            depth, pidx, initial
        ));
        s.push_str("(check-sat)\n(pop 1)\n");
    }

    s.push_str("(exit)\n");
    s
}
