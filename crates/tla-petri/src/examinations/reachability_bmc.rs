// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Bounded model checking (BMC) for reachability properties via z4.
//!
//! Encodes Petri net reachability as SMT-LIB queries and runs z4 to find
//! witnesses:
//! - `EF(φ)` → `TRUE` via SAT (witness found)
//! - `AG(φ)` → `FALSE` via SAT (counterexample for ¬φ)
//! - UNSAT, timeout, unknown → inconclusive (falls through to later phases)

use std::time::Instant;

use crate::petri_net::PetriNet;
use crate::property_xml::PathQuantifier;

use super::bmc_runner::{
    emit_bmc_incremental_preamble, run_depth_ladder_incremental, DepthAction, DepthQuery,
    IncrementalPropertyQuery,
};
use super::reachability::{resolve_tracker, PropertyTracker, ReachabilityResolutionSource};
#[cfg(test)]
use super::smt_encoding::encode_int_expr;
use super::smt_encoding::{
    encode_predicate, find_z4, SolverOutcome, DEPTH_LADDER, PER_DEPTH_TIMEOUT,
};

/// Run BMC seeding on pre-resolved trackers.
///
/// For each unresolved property, attempts to find a witness via z4-backed
/// BMC on the original net. Seeds `verdict` on trackers where witnesses
/// are found. Does nothing if z4 is not available.
///
/// Returns the maximum depth at which BMC completed without UNKNOWN results
/// (i.e., all pending properties returned SAT or UNSAT). This is the base-case
/// depth for subsequent k-induction — k-induction at depth k requires the BMC
/// base case to cover at least k states (i.e., `max_bmc_depth + 1 >= k`).
pub(crate) fn run_bmc_seeding(
    net: &PetriNet,
    trackers: &mut [PropertyTracker],
    deadline: Option<Instant>,
) -> Option<usize> {
    let z4_path = match find_z4() {
        Some(path) => path,
        None => {
            eprintln!("BMC: z4 not found, skipping bounded model checking");
            return None;
        }
    };
    run_bmc_seeding_with_solver_path(net, trackers, deadline, &z4_path)
}

/// Run BMC seeding with an explicit solver path.
///
/// Split from [`run_bmc_seeding`] so tests can inject a fake solver without
/// mutating global environment variables.
///
/// Returns the maximum depth at which all pending properties completed
/// without UNKNOWN (the base case for k-induction soundness).
fn run_bmc_seeding_with_solver_path(
    net: &PetriNet,
    trackers: &mut [PropertyTracker],
    deadline: Option<Instant>,
    z4_path: &std::path::Path,
) -> Option<usize> {
    let unresolved: Vec<usize> = trackers
        .iter()
        .enumerate()
        .filter(|(_, tracker)| tracker.verdict.is_none())
        .map(|(index, _)| index)
        .collect();

    if unresolved.is_empty() {
        return None;
    }

    struct ReachabilityBmcState<'a> {
        net: &'a PetriNet,
        trackers: &'a mut [PropertyTracker],
        unresolved: Vec<usize>,
        pending: Vec<usize>,
    }

    let mut state = ReachabilityBmcState {
        net,
        trackers,
        unresolved,
        pending: Vec::new(),
    };

    // Shared result handler — used by both incremental and fallback paths.
    let handle_result = |state: &mut ReachabilityBmcState<'_>,
                         depth: usize,
                         results: Option<&[SolverOutcome]>|
     -> DepthAction {
        match results {
            Some(results) => {
                let mut had_unknown = false;
                for (property_idx, outcome) in state.pending.iter().zip(results.iter()) {
                    match outcome {
                        SolverOutcome::Sat => match state.trackers[*property_idx].quantifier {
                            PathQuantifier::EF => {
                                resolve_tracker(
                                    &mut state.trackers[*property_idx],
                                    true,
                                    ReachabilityResolutionSource::Bmc,
                                    Some(depth),
                                );
                                eprintln!(
                                    "BMC depth {depth}: {} = TRUE (EF witness)",
                                    state.trackers[*property_idx].id
                                );
                            }
                            PathQuantifier::AG => {
                                resolve_tracker(
                                    &mut state.trackers[*property_idx],
                                    false,
                                    ReachabilityResolutionSource::Bmc,
                                    Some(depth),
                                );
                                eprintln!(
                                    "BMC depth {depth}: {} = FALSE (AG counterexample)",
                                    state.trackers[*property_idx].id
                                );
                            }
                        },
                        SolverOutcome::Unsat => {}
                        SolverOutcome::Unknown => had_unknown = true,
                    }
                }

                if had_unknown {
                    eprintln!("BMC depth {depth}: unknown result, stopping BMC");
                    DepthAction::StopDeepening
                } else {
                    DepthAction::Explored
                }
            }
            None => {
                eprintln!("BMC depth {depth}: solver failed, stopping BMC");
                DepthAction::StopDeepening
            }
        }
    };

    // Shared pending-refresh — used by both incremental and fallback query builders.
    let refresh_pending = |state: &mut ReachabilityBmcState<'_>| -> bool {
        state.pending = state
            .unresolved
            .iter()
            .copied()
            .filter(|&index| state.trackers[index].verdict.is_none())
            .collect();
        !state.pending.is_empty()
    };

    run_depth_ladder_incremental(
        z4_path,
        DEPTH_LADDER,
        deadline,
        PER_DEPTH_TIMEOUT,
        net,
        &mut state,
        // One-time preamble (no transition relation — added incrementally).
        emit_bmc_incremental_preamble,
        // Incremental query builder: per-property assertions only.
        |state, depth| {
            if !refresh_pending(state) {
                return None;
            }
            Some(IncrementalPropertyQuery {
                assertions: encode_property_assertions(
                    state.net,
                    state.trackers,
                    &state.pending,
                    depth,
                ),
            })
        },
        // Incremental result handler.
        handle_result,
        // Fallback: batch query builder (full script per depth).
        |state, depth| {
            if !refresh_pending(state) {
                return None;
            }
            Some(DepthQuery::new(
                encode_bmc_script(state.net, state.trackers, &state.pending, depth),
                state.pending.len(),
            ))
        },
        // Fallback: batch result handler.
        handle_result,
    )
}

/// Generate the SMT-LIB script for BMC at a given depth.
///
/// Produces one shared declaration/transition block, then per-property
/// `push/assert/check-sat/pop` blocks. Each step can either fire one
/// transition or stutter (no-op).
fn encode_bmc_script(
    net: &PetriNet,
    trackers: &[PropertyTracker],
    pending: &[usize],
    depth: usize,
) -> String {
    let mut script = String::with_capacity(4096);
    super::bmc_runner::emit_bmc_preamble(&mut script, net, depth);

    for &property_idx in pending {
        let tracker = &trackers[property_idx];
        script.push_str("(push 1)\n");

        let check_negated = tracker.quantifier == PathQuantifier::AG;
        let mut step_assertions = Vec::new();
        for step in 0..=depth {
            let predicate = encode_predicate(&tracker.predicate, step, net);
            if check_negated {
                step_assertions.push(format!("(not {})", predicate));
            } else {
                step_assertions.push(predicate);
            }
        }

        if step_assertions.len() == 1 {
            script.push_str(&format!("(assert {})\n", step_assertions[0]));
        } else {
            script.push_str("(assert (or");
            for assertion in &step_assertions {
                script.push_str(&format!(" {}", assertion));
            }
            script.push_str("))\n");
        }

        script.push_str("(check-sat)\n");
        script.push_str("(pop 1)\n");
    }

    script.push_str("(exit)\n");
    script
}

/// Build per-property assertion strings for incremental BMC at a given depth.
///
/// Each returned string is a self-contained assertion block (without push/pop or
/// check-sat) that the incremental solver wraps in a push/pop scope.
fn encode_property_assertions(
    net: &PetriNet,
    trackers: &[PropertyTracker],
    pending: &[usize],
    depth: usize,
) -> Vec<String> {
    pending
        .iter()
        .map(|&property_idx| {
            let tracker = &trackers[property_idx];
            let check_negated = tracker.quantifier == PathQuantifier::AG;
            let mut step_assertions = Vec::new();
            for step in 0..=depth {
                let predicate = encode_predicate(&tracker.predicate, step, net);
                if check_negated {
                    step_assertions.push(format!("(not {})", predicate));
                } else {
                    step_assertions.push(predicate);
                }
            }

            let mut s = String::new();
            if step_assertions.len() == 1 {
                s.push_str(&format!("(assert {})\n", step_assertions[0]));
            } else {
                s.push_str("(assert (or");
                for assertion in &step_assertions {
                    s.push_str(&format!(" {}", assertion));
                }
                s.push_str("))\n");
            }
            s
        })
        .collect()
}

#[cfg(test)]
#[path = "reachability_bmc_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "reachability_bmc_incremental_tests.rs"]
mod incremental_tests;
