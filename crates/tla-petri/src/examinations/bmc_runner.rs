// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared BMC and k-induction script-building helpers.
//!
//! Extracted from `global_properties_bmc.rs` to eliminate duplicated
//! SMT-LIB preamble code across `reachability_bmc.rs`, `kinduction.rs`,
//! and `global_properties_bmc.rs`.

use std::path::Path;
use std::time::{Duration, Instant};

use crate::invariant::compute_p_invariants;
use crate::petri_net::PetriNet;

use super::incremental_solver::IncrementalSolver;
use super::smt_encoding::encode_transition_relation;
use super::smt_encoding::{encode_transition_relation_steps, run_z4, SolverOutcome};

/// Per-depth solver query constructed by a BMC depth-ladder caller.
pub(super) struct DepthQuery {
    /// SMT-LIB script to send to z4 for this depth.
    pub script: String,
    /// Number of `(check-sat)` results expected back from z4.
    pub num_checks: usize,
}

impl DepthQuery {
    pub(super) fn new(script: String, num_checks: usize) -> Self {
        Self { script, num_checks }
    }
}

/// Control flow after handling a solver result for one ladder depth.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum DepthAction {
    /// This depth completed normally and deeper levels remain sound to try.
    Explored,
    /// Stop deepening after this depth.
    StopDeepening,
}

/// Run a shared BMC or k-induction depth ladder.
///
/// The caller provides a mutable state object plus two closures:
/// - `build_query` prepares the SMT script for the current depth, or returns
///   `None` when there is no more work (for example, no pending properties or a
///   depth cap has been reached).
/// - `handle_result` routes the solver outcome into caller-specific state and
///   decides whether deepening should continue.
///
/// Returns the last depth whose result was marked [`DepthAction::Explored`].
pub(super) fn run_depth_ladder<T>(
    z4_path: &Path,
    depths: &[usize],
    deadline: Option<Instant>,
    per_depth_timeout: Duration,
    state: &mut T,
    mut build_query: impl FnMut(&mut T, usize) -> Option<DepthQuery>,
    mut handle_result: impl FnMut(&mut T, usize, Option<&[SolverOutcome]>) -> DepthAction,
) -> Option<usize> {
    let mut max_explored_depth = None;

    for &depth in depths {
        if deadline.is_some_and(|global_deadline| Instant::now() >= global_deadline) {
            break;
        }

        let Some(query) = build_query(state, depth) else {
            break;
        };

        let timeout = deadline
            .map(|global_deadline| {
                per_depth_timeout.min(global_deadline.saturating_duration_since(Instant::now()))
            })
            .unwrap_or(per_depth_timeout);
        let results = run_z4(z4_path, &query.script, query.num_checks, timeout);

        match handle_result(state, depth, results.as_deref()) {
            DepthAction::Explored => max_explored_depth = Some(depth),
            DepthAction::StopDeepening => break,
        }
    }

    max_explored_depth
}

/// Per-depth property query for the incremental solver.
///
/// Unlike [`DepthQuery`], this contains only the per-property assertion strings
/// (without preamble or transition relation — those are sent incrementally).
pub(super) struct IncrementalPropertyQuery {
    /// SMT-LIB assertion strings, one per property (sent inside push/pop).
    pub assertions: Vec<String>,
}

/// Run a BMC depth ladder using a persistent incremental z4 process.
///
/// The solver is spawned once and kept alive across all depths.
/// Transition-relation assertions accumulate (z4 retains learned clauses).
/// Per-property queries use push/pop scoping.
///
/// The caller provides:
/// - `emit_preamble`: one-time preamble (logic, vars for max depth, initial marking,
///   non-negativity) — called once before the ladder starts.
/// - `build_queries`: returns per-property assertion strings for the current depth,
///   or `None` when there is no more work.
/// - `handle_result`: routes solver outcomes and decides whether to continue.
///
/// Falls back to [`run_depth_ladder`] if the incremental solver cannot be spawned.
pub(super) fn run_depth_ladder_incremental<T>(
    z4_path: &Path,
    depths: &[usize],
    deadline: Option<Instant>,
    per_depth_timeout: Duration,
    net: &PetriNet,
    state: &mut T,
    emit_preamble: impl FnOnce(&mut String, &PetriNet, usize),
    mut build_queries: impl FnMut(&mut T, usize) -> Option<IncrementalPropertyQuery>,
    mut handle_result: impl FnMut(&mut T, usize, Option<&[SolverOutcome]>) -> DepthAction,
    // Fallback closures — used only if incremental solver spawn fails.
    fallback_build_query: impl FnMut(&mut T, usize) -> Option<DepthQuery>,
    fallback_handle_result: impl FnMut(&mut T, usize, Option<&[SolverOutcome]>) -> DepthAction,
) -> Option<usize> {
    let mut solver = match IncrementalSolver::new(z4_path) {
        Some(s) => s,
        None => {
            eprintln!("Incremental solver spawn failed, falling back to batch mode");
            return run_depth_ladder(
                z4_path,
                depths,
                deadline,
                per_depth_timeout,
                state,
                fallback_build_query,
                fallback_handle_result,
            );
        }
    };

    let np = net.num_places();
    let nt = net.num_transitions();
    let max_depth = match depths.last() {
        Some(&d) => d,
        None => return None,
    };

    // One-time preamble: logic, ALL vars for max depth, initial marking, non-negativity.
    let mut preamble = String::with_capacity(4096);
    emit_preamble(&mut preamble, net, max_depth);
    if !solver.send(&preamble) {
        eprintln!("Incremental preamble failed, falling back to batch mode");
        return run_depth_ladder(
            z4_path,
            depths,
            deadline,
            per_depth_timeout,
            state,
            fallback_build_query,
            fallback_handle_result,
        );
    }

    let mut prev_depth = 0;
    let mut max_explored_depth = None;

    for &depth in depths {
        if deadline.is_some_and(|d| Instant::now() >= d) {
            break;
        }

        let Some(query) = build_queries(state, depth) else {
            break;
        };

        if query.assertions.is_empty() {
            break;
        }

        // Incrementally add transition relation for new steps only.
        let mut tr = String::new();
        encode_transition_relation_steps(&mut tr, net, np, nt, prev_depth..depth);
        if !tr.is_empty() && !solver.send(&tr) {
            break;
        }

        let timeout = deadline
            .map(|global_deadline| {
                per_depth_timeout.min(global_deadline.saturating_duration_since(Instant::now()))
            })
            .unwrap_or(per_depth_timeout);
        if timeout.is_zero() {
            break;
        }
        let depth_deadline = Instant::now() + timeout;

        // Check each property with push/pop.
        let mut outcomes = Vec::with_capacity(query.assertions.len());
        let mut session_failed = false;
        for assertion in &query.assertions {
            let remaining = depth_deadline.saturating_duration_since(Instant::now());
            if remaining.is_zero() {
                session_failed = true;
                break;
            }
            if !solver.push() || !solver.send(assertion) {
                session_failed = true;
                break;
            }
            outcomes.push(solver.check_sat(remaining));
            if !solver.pop() {
                session_failed = true;
                break;
            }
        }

        if outcomes.len() < query.assertions.len() {
            outcomes.resize(query.assertions.len(), SolverOutcome::Unknown);
        }

        match handle_result(state, depth, Some(&outcomes)) {
            DepthAction::Explored => max_explored_depth = Some(depth),
            DepthAction::StopDeepening => break,
        }

        if session_failed {
            break;
        }

        prev_depth = depth;
    }

    max_explored_depth
}

/// Emit the BMC incremental preamble (no transition relation — added incrementally).
///
/// Writes: logic declaration, marking variables for max depth, step variables for
/// max depth, initial marking, and non-negativity.
pub(crate) fn emit_bmc_incremental_preamble(s: &mut String, net: &PetriNet, max_depth: usize) {
    let np = net.num_places();
    let nt = net.num_transitions();
    s.push_str("(set-logic QF_LIA)\n");
    emit_marking_vars(s, np, max_depth);
    emit_step_vars(s, nt, max_depth);
    emit_initial_marking(s, net);
    emit_non_negativity(s, np, max_depth);
}

/// Emit the BMC script preamble for a bounded model check from the initial marking.
///
/// Writes: logic declaration, marking variables, step variables, initial marking,
/// non-negativity constraints, and the transition relation.
pub(crate) fn emit_bmc_preamble(s: &mut String, net: &PetriNet, depth: usize) {
    let np = net.num_places();
    let nt = net.num_transitions();
    s.push_str("(set-logic QF_LIA)\n");
    emit_marking_vars(s, np, depth);
    emit_step_vars(s, nt, depth);
    emit_initial_marking(s, net);
    emit_non_negativity(s, np, depth);
    encode_transition_relation(s, net, np, nt, depth);
}

/// Emit the k-induction script preamble (no initial marking, state-equation
/// strengthening + P-invariants instead).
///
/// Writes: logic declaration, marking variables, step variables, state-equation
/// constraints at step 0, non-negativity, transition relation, and P-invariant
/// equalities at every step.
pub(crate) fn emit_kinduction_preamble(s: &mut String, net: &PetriNet, depth: usize) {
    let np = net.num_places();
    let nt = net.num_transitions();
    s.push_str("(set-logic QF_LIA)\n");
    emit_marking_vars(s, np, depth);
    emit_step_vars(s, nt, depth);
    emit_state_equation_strengthening(s, net, np, nt);
    emit_non_negativity(s, np, depth);
    encode_transition_relation(s, net, np, nt, depth);
    emit_p_invariant_strengthening(s, net, depth);
}

/// Declare marking variables `m_{step}_{place}` for steps 0..=depth.
pub(crate) fn emit_marking_vars(s: &mut String, np: usize, depth: usize) {
    for step in 0..=depth {
        for place in 0..np {
            s.push_str(&format!("(declare-const m_{}_{} Int)\n", step, place));
        }
    }
}

/// Declare step decision variables (stay + fire) for steps 0..depth.
pub(crate) fn emit_step_vars(s: &mut String, nt: usize, depth: usize) {
    for step in 0..depth {
        s.push_str(&format!("(declare-const stay_{step} Bool)\n"));
        for transition in 0..nt {
            s.push_str(&format!(
                "(declare-const fire_{}_{} Bool)\n",
                step, transition
            ));
        }
    }
}

/// Assert initial marking constraints at step 0.
pub(crate) fn emit_initial_marking(s: &mut String, net: &PetriNet) {
    for (place, &tokens) in net.initial_marking.iter().enumerate() {
        s.push_str(&format!("(assert (= m_0_{} {}))\n", place, tokens));
    }
}

/// Assert non-negativity for all marking variables.
pub(crate) fn emit_non_negativity(s: &mut String, np: usize, depth: usize) {
    for step in 0..=depth {
        for place in 0..np {
            s.push_str(&format!("(assert (>= m_{}_{} 0))\n", step, place));
        }
    }
}

/// Add state-equation constraints at step 0 (for k-induction).
///
/// `m_0_p = initial_p + sum(delta_p_t * parikh_t)` with `parikh_t >= 0`.
pub(crate) fn emit_state_equation_strengthening(
    s: &mut String,
    net: &PetriNet,
    np: usize,
    nt: usize,
) {
    for transition in 0..nt {
        s.push_str(&format!("(declare-const parikh_{} Int)\n", transition));
    }
    for transition in 0..nt {
        s.push_str(&format!("(assert (>= parikh_{} 0))\n", transition));
    }

    for place in 0..np {
        let initial_tokens = net.initial_marking[place] as i64;
        let mut terms: Vec<(usize, i64)> = Vec::new();
        for (tidx, t) in net.transitions.iter().enumerate() {
            let mut delta = 0_i64;
            for arc in &t.inputs {
                if arc.place.0 as usize == place {
                    delta -= arc.weight as i64;
                }
            }
            for arc in &t.outputs {
                if arc.place.0 as usize == place {
                    delta += arc.weight as i64;
                }
            }
            if delta != 0 {
                terms.push((tidx, delta));
            }
        }

        let rhs = if terms.is_empty() {
            format!("{initial_tokens}")
        } else {
            let mut parts = Vec::with_capacity(terms.len() + 1);
            parts.push(format!("{initial_tokens}"));
            for &(tidx, delta) in &terms {
                if delta == 1 {
                    parts.push(format!("parikh_{tidx}"));
                } else if delta == -1 {
                    parts.push(format!("(- parikh_{tidx})"));
                } else {
                    parts.push(format!("(* {} parikh_{})", delta, tidx));
                }
            }
            format!("(+ {})", parts.join(" "))
        };
        s.push_str(&format!("(assert (= m_0_{} {}))\n", place, rhs));
    }
}

/// Add P-invariant equalities at every step (for k-induction).
pub(crate) fn emit_p_invariant_strengthening(s: &mut String, net: &PetriNet, depth: usize) {
    let invariants = compute_p_invariants(net);
    let max_invariants = 50;
    let invariants = &invariants[..invariants.len().min(max_invariants)];
    for inv in invariants {
        for step in 0..=depth {
            let terms: Vec<String> = inv
                .weights
                .iter()
                .enumerate()
                .filter(|(_, &w)| w > 0)
                .map(|(p, &w)| {
                    if w == 1 {
                        format!("m_{}_{}", step, p)
                    } else {
                        format!("(* {} m_{}_{})", w, step, p)
                    }
                })
                .collect();
            if !terms.is_empty() {
                let lhs = if terms.len() == 1 {
                    terms[0].clone()
                } else {
                    format!("(+ {})", terms.join(" "))
                };
                s.push_str(&format!("(assert (= {} {}))\n", lhs, inv.token_count));
            }
        }
    }
}

#[cfg(test)]
#[path = "bmc_runner_tests.rs"]
mod tests;
