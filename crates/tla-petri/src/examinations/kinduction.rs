// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! k-Induction for reachability properties via z4.

use std::time::Instant;

use crate::petri_net::PetriNet;
use crate::property_xml::PathQuantifier;

use super::bmc_runner::emit_kinduction_preamble;
use super::reachability::{resolve_tracker, PropertyTracker, ReachabilityResolutionSource};
use super::smt_encoding::{
    encode_predicate, find_z4, run_z4, SolverOutcome, DEPTH_LADDER, PER_DEPTH_TIMEOUT,
};

/// k-induction depth ladder.
///
/// Soundness requires the witness-side base case to cover at least the same
/// maximum depth. The `max_bmc_depth` parameter gates which depths are sound.
const KINDUCTION_DEPTH_LADDER: &[usize] = DEPTH_LADDER;

/// Run k-induction seeding on pre-resolved trackers.
///
/// For each unresolved AG property, attempts to prove it by induction:
///   UNSAT at depth k → AG(φ) = TRUE (k-inductive).
/// For each unresolved EF property, attempts to prove `AG(¬φ)` by induction:
///   UNSAT at depth k → EF(φ) = FALSE.
///
/// SAT, unknown, timeout, and process failure are all treated as
/// inconclusive (verdict left as `None`).
///
/// `max_bmc_depth`: the maximum depth at which BMC completed without UNKNOWN
/// for all pending properties. k-induction at depth k requires the base case
/// to cover at least k states, so only depths ≤ `max_bmc_depth + 1` are
/// attempted. Pass `None` to skip k-induction entirely (no base case).
pub(crate) fn run_kinduction_seeding(
    net: &PetriNet,
    trackers: &mut [PropertyTracker],
    deadline: Option<Instant>,
    max_bmc_depth: Option<usize>,
) {
    let max_kind_depth = match max_bmc_depth {
        Some(d) => d + 1,
        None => return, // no base case established by BMC
    };
    let z4_path = match find_z4() {
        Some(path) => path,
        None => return,
    };
    run_kinduction_seeding_with_solver_path(net, trackers, deadline, &z4_path, max_kind_depth);
}

/// Run k-induction seeding with an explicit solver path.
///
/// `max_kind_depth`: maximum k-induction depth that has a sound base case.
/// Only depths ≤ `max_kind_depth` are attempted.
///
/// Runs each property in a separate z4 invocation to avoid a z4 push/pop
/// soundness bug where learned clauses from earlier push/pop blocks can
/// produce incorrect UNSAT results for later properties.
fn run_kinduction_seeding_with_solver_path(
    net: &PetriNet,
    trackers: &mut [PropertyTracker],
    deadline: Option<Instant>,
    z4_path: &std::path::Path,
    max_kind_depth: usize,
) {
    let unresolved: Vec<usize> = trackers
        .iter()
        .enumerate()
        .filter(|(_, tracker)| tracker.verdict.is_none())
        .map(|(index, _)| index)
        .collect();

    if unresolved.is_empty() {
        return;
    }

    for &depth in KINDUCTION_DEPTH_LADDER {
        if depth > max_kind_depth {
            break;
        }
        if deadline.is_some_and(|d| Instant::now() >= d) {
            break;
        }

        let pending: Vec<usize> = unresolved
            .iter()
            .copied()
            .filter(|&index| trackers[index].verdict.is_none())
            .collect();

        if pending.is_empty() {
            break;
        }

        let mut had_unknown = false;
        let mut had_failure = false;

        for &property_idx in &pending {
            if deadline.is_some_and(|d| Instant::now() >= d) {
                break;
            }

            let script = encode_kinduction_script_single(net, trackers, property_idx, depth);
            let timeout = deadline
                .map(|d| PER_DEPTH_TIMEOUT.min(d.saturating_duration_since(Instant::now())))
                .unwrap_or(PER_DEPTH_TIMEOUT);
            let result = run_z4(z4_path, &script, 1, timeout);

            match result.as_deref() {
                Some([SolverOutcome::Unsat]) => match trackers[property_idx].quantifier {
                    PathQuantifier::AG => {
                        resolve_tracker(
                            &mut trackers[property_idx],
                            true,
                            ReachabilityResolutionSource::Kinduction,
                            Some(depth),
                        );
                        eprintln!(
                            "k-ind depth {depth}: {} = TRUE (AG {}-inductive)",
                            trackers[property_idx].id, depth
                        );
                    }
                    PathQuantifier::EF => {
                        resolve_tracker(
                            &mut trackers[property_idx],
                            false,
                            ReachabilityResolutionSource::Kinduction,
                            Some(depth),
                        );
                        eprintln!(
                            "k-ind depth {depth}: {} = FALSE (EF, negation {}-inductive)",
                            trackers[property_idx].id, depth
                        );
                    }
                },
                Some([SolverOutcome::Sat]) => {}
                Some([SolverOutcome::Unknown]) => had_unknown = true,
                _ => had_failure = true,
            }
        }

        if had_unknown {
            eprintln!("k-ind depth {depth}: unknown result, stopping k-induction");
            break;
        }
        if had_failure {
            eprintln!("k-ind depth {depth}: solver failed, stopping k-induction");
            break;
        }
    }
}

/// Generate SMT-LIB script for k-induction of a single property at a given depth.
///
/// No push/pop — one complete script per property, run in its own z4 process.
/// This avoids the z4 push/pop soundness bug where learned clauses from earlier
/// blocks can produce incorrect UNSAT for later properties.
fn encode_kinduction_script_single(
    net: &PetriNet,
    trackers: &[PropertyTracker],
    property_idx: usize,
    depth: usize,
) -> String {
    let mut script = String::with_capacity(4096);

    emit_kinduction_preamble(&mut script, net, depth);

    let tracker = &trackers[property_idx];
    let hypothesis_negated = tracker.quantifier == PathQuantifier::EF;
    for step in 0..depth {
        let predicate = encode_predicate(&tracker.predicate, step, net);
        if hypothesis_negated {
            script.push_str(&format!("(assert (not {}))\n", predicate));
        } else {
            script.push_str(&format!("(assert {})\n", predicate));
        }
    }

    let predicate_at_depth = encode_predicate(&tracker.predicate, depth, net);
    if hypothesis_negated {
        script.push_str(&format!("(assert {})\n", predicate_at_depth));
    } else {
        script.push_str(&format!("(assert (not {}))\n", predicate_at_depth));
    }

    script.push_str("(check-sat)\n");
    script.push_str("(exit)\n");
    script
}

/// Generate SMT-LIB script for k-induction at a given depth (multi-property, push/pop).
///
/// Used only by tests. Production code uses `encode_kinduction_script_single` to
/// avoid the z4 push/pop soundness bug.
#[cfg(test)]
fn encode_kinduction_script(
    net: &PetriNet,
    trackers: &[PropertyTracker],
    pending: &[usize],
    depth: usize,
) -> String {
    encode_kinduction_script_with_strengthening(net, trackers, pending, depth, true)
}

/// Generate SMT-LIB script for k-induction at a given depth.
///
/// Key differences from BMC:
/// - No initial marking constraints (arbitrary start state)
/// - Per-property: assert the property at steps 0..k-1 (induction hypothesis)
/// - Per-property: assert the negation at step k (induction check)
/// - For EF properties: induction is on `¬φ` (proving AG(¬φ))
///
/// When `strengthen_step0` is true, adds state-equation constraints at step 0:
///   M0_model = M0_real + C * parikh  (parikh >= 0)
/// This restricts step-0 markings to those reachable via the state equation,
/// pruning spurious states that would make induction inconclusive.
#[cfg(test)]
fn encode_kinduction_script_with_strengthening(
    net: &PetriNet,
    trackers: &[PropertyTracker],
    pending: &[usize],
    depth: usize,
    strengthen_step0: bool,
) -> String {
    use super::bmc_runner::{emit_marking_vars, emit_non_negativity, emit_step_vars};
    use super::smt_encoding::encode_transition_relation;

    let num_places = net.num_places();
    let num_transitions = net.num_transitions();
    let mut script = String::with_capacity(4096);

    if strengthen_step0 {
        emit_kinduction_preamble(&mut script, net, depth);
    } else {
        // Bare preamble without state-equation or P-invariant strengthening.
        script.push_str("(set-logic QF_LIA)\n");
        emit_marking_vars(&mut script, num_places, depth);
        emit_step_vars(&mut script, num_transitions, depth);
        emit_non_negativity(&mut script, num_places, depth);
        encode_transition_relation(&mut script, net, num_places, num_transitions, depth);
    }

    for &property_idx in pending {
        let tracker = &trackers[property_idx];
        script.push_str("(push 1)\n");

        let hypothesis_negated = tracker.quantifier == PathQuantifier::EF;
        for step in 0..depth {
            let predicate = encode_predicate(&tracker.predicate, step, net);
            if hypothesis_negated {
                script.push_str(&format!("(assert (not {}))\n", predicate));
            } else {
                script.push_str(&format!("(assert {})\n", predicate));
            }
        }

        let predicate_at_depth = encode_predicate(&tracker.predicate, depth, net);
        if hypothesis_negated {
            script.push_str(&format!("(assert {})\n", predicate_at_depth));
        } else {
            script.push_str(&format!("(assert (not {}))\n", predicate_at_depth));
        }

        script.push_str("(check-sat)\n");
        script.push_str("(pop 1)\n");
    }

    script.push_str("(exit)\n");
    script
}

#[cfg(test)]
#[path = "kinduction_tests.rs"]
mod tests;
