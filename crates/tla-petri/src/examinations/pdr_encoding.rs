// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! PDR/IC3 encoding for Petri net safety verification via z4-chc.
//!
//! Encodes a Petri net and a safety property as a Constrained Horn Clause (CHC)
//! problem and solves it with z4-chc's [`AdaptivePortfolio`]. The encoding uses
//! one uninterpreted predicate `Inv(m_0, ..., m_{P-1})` over integer marking
//! variables, with:
//!
//! - **Init clause**: `m_0 = init[0] /\ ... => Inv(m_0, ...)`
//! - **Consecution**: For each transition `t`: `Inv(m) /\ guard_t(m) /\ effect_t(m, m') => Inv(m')`
//! - **Stuttering**: `Inv(m) /\ m' = m => Inv(m')` (identity transition)
//! - **Query**: `Inv(m) /\ NOT safety(m) => false`
//! - **Strengthening** (optional): P-invariant equalities as additional constraints
//!
//! This is a sound reduction for Petri net safety. When the CHC solver finds
//! an inductive invariant, the property is proved for all reachable markings;
//! otherwise the result may remain `Unknown`. Because the state is encoded as
//! integer markings, the technique also applies to unbounded nets without
//! requiring explicit-state exploration.

use std::time::Duration;

use z4_chc::{
    AdaptiveConfig, AdaptivePortfolio, ChcExpr, ChcProblem, ChcSort, ChcVar, ClauseBody,
    ClauseHead, HornClause, VerifiedChcResult,
};

use crate::invariant::{compute_p_invariants, PInvariant};
use crate::petri_net::PetriNet;
use crate::resolved_predicate::{ResolvedIntExpr, ResolvedPredicate};

/// Configuration for PDR-based Petri net verification.
#[derive(Debug, Clone)]
pub(crate) struct PdrConfig {
    /// Time budget for the adaptive portfolio solver (default: 30s).
    pub time_budget: Duration,
    /// Whether to add P-invariant strengthening clauses.
    pub use_p_invariants: bool,
    /// Whether to add a stuttering (identity) transition clause.
    pub add_stuttering: bool,
    /// Enable verbose output from the CHC solver.
    pub verbose: bool,
}

impl Default for PdrConfig {
    fn default() -> Self {
        Self {
            time_budget: Duration::from_secs(30),
            use_p_invariants: true,
            add_stuttering: true,
            verbose: false,
        }
    }
}

/// Result of PDR-based safety verification.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PdrCheckResult {
    /// Property holds: an inductive invariant was found.
    Safe,
    /// Property violated: a counterexample trace exists.
    Unsafe,
    /// Solver could not determine the result within the budget.
    Unknown,
}

// ── Variable naming helpers ─────────────────────────────────────────

/// Create a marking variable for the current state: `m_<place_idx>`.
fn make_var(place_idx: usize) -> ChcVar {
    ChcVar::new(format!("m_{place_idx}"), ChcSort::Int)
}

/// Create a marking variable for the next state: `m_<place_idx>'`.
fn make_primed_var(place_idx: usize) -> ChcVar {
    ChcVar::new(format!("m_{place_idx}'"), ChcSort::Int)
}

/// Create a `ChcExpr::Var` for the current-state marking of a place.
fn var_expr(place_idx: usize) -> ChcExpr {
    ChcExpr::var(make_var(place_idx))
}

/// Create a `ChcExpr::Var` for the next-state marking of a place.
fn primed_var_expr(place_idx: usize) -> ChcExpr {
    ChcExpr::var(make_primed_var(place_idx))
}

// ── CHC encoding ────────────────────────────────────────────────────

/// Encode a Petri net and safety property as a CHC problem.
///
/// The returned `ChcProblem` has a single predicate `Inv` with `P` integer
/// arguments (one per place), plus clauses for initialization, transition
/// consecution, and the safety query.
pub(crate) fn encode_petri_net_pdr(
    net: &PetriNet,
    property: &ResolvedPredicate,
    config: &PdrConfig,
) -> ChcProblem {
    let np = net.num_places();

    let mut problem = ChcProblem::new();

    // Declare Inv(m_0: Int, m_1: Int, ..., m_{P-1}: Int)
    let arg_sorts: Vec<ChcSort> = (0..np).map(|_| ChcSort::Int).collect();
    let inv = problem.declare_predicate("Inv", arg_sorts);

    // Current-state and next-state argument vectors for Inv
    let current_args: Vec<ChcExpr> = (0..np).map(var_expr).collect();
    let primed_args: Vec<ChcExpr> = (0..np).map(primed_var_expr).collect();

    // ── Init clause ──────────────────────────────────────────────
    // m_0 = init[0] /\ m_1 = init[1] /\ ... => Inv(m_0, m_1, ...)
    let init_conjuncts: Vec<ChcExpr> = (0..np)
        .map(|p| ChcExpr::eq(var_expr(p), ChcExpr::int(net.initial_marking[p] as i64)))
        .collect();
    let init_constraint = ChcExpr::and_all(init_conjuncts);
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(init_constraint),
        ClauseHead::Predicate(inv, current_args.clone()),
    ));

    // ── Non-negativity constraints ──────────────────────────────
    // PDR synthesises over-approximating invariants.  Without explicit
    // non-negativity bounds the solver may include states with negative
    // token counts, slowing convergence.  We add m_p' >= 0 to every
    // consecution clause to keep the abstraction tight.
    let nonneg_primed: Vec<ChcExpr> = (0..np)
        .map(|p| ChcExpr::ge(primed_var_expr(p), ChcExpr::int(0)))
        .collect();

    // ── Consecution clauses (one per transition) ─────────────────
    // For each transition t:
    //   Inv(m) /\ guard_t(m) /\ effect_t(m, m') /\ m' >= 0 => Inv(m')
    for transition in &net.transitions {
        // Guard: all input places have enough tokens
        let guard_conjuncts: Vec<ChcExpr> = transition
            .inputs
            .iter()
            .map(|arc| {
                ChcExpr::ge(
                    var_expr(arc.place.0 as usize),
                    ChcExpr::int(arc.weight as i64),
                )
            })
            .collect();

        // Effect: compute deltas for each place
        let mut deltas = vec![0_i64; np];
        let mut affected = vec![false; np];
        for arc in &transition.inputs {
            let p = arc.place.0 as usize;
            deltas[p] -= arc.weight as i64;
            affected[p] = true;
        }
        for arc in &transition.outputs {
            let p = arc.place.0 as usize;
            deltas[p] += arc.weight as i64;
            affected[p] = true;
        }

        // Build effect constraints: m_p' = m_p + delta_p for affected places,
        // m_p' = m_p for frame (unaffected) places.
        let mut effect_conjuncts: Vec<ChcExpr> = Vec::with_capacity(np);
        for p in 0..np {
            if !affected[p] || deltas[p] == 0 {
                effect_conjuncts.push(ChcExpr::eq(primed_var_expr(p), var_expr(p)));
            } else {
                effect_conjuncts.push(ChcExpr::eq(
                    primed_var_expr(p),
                    ChcExpr::add(var_expr(p), ChcExpr::int(deltas[p])),
                ));
            }
        }

        // Combine guard + effect + non-negativity into the transition constraint
        let mut all_conjuncts = guard_conjuncts;
        all_conjuncts.extend(effect_conjuncts);
        all_conjuncts.extend(nonneg_primed.clone());
        let transition_constraint = ChcExpr::and_all(all_conjuncts);

        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(inv, current_args.clone())],
                Some(transition_constraint),
            ),
            ClauseHead::Predicate(inv, primed_args.clone()),
        ));
    }

    // ── Stuttering clause (optional) ─────────────────────────────
    // Inv(m) /\ m' = m => Inv(m')
    if config.add_stuttering {
        let stutter_conjuncts: Vec<ChcExpr> = (0..np)
            .map(|p| ChcExpr::eq(primed_var_expr(p), var_expr(p)))
            .collect();
        let stutter_constraint = ChcExpr::and_all(stutter_conjuncts);
        problem.add_clause(HornClause::new(
            ClauseBody::new(vec![(inv, current_args.clone())], Some(stutter_constraint)),
            ClauseHead::Predicate(inv, primed_args.clone()),
        ));
    }

    // ── P-invariant strengthening (optional) ─────────────────────
    // For each P-invariant y: sum(y[p] * m[p]) = y^T * m0.
    // Added as: Inv(m) /\ sum(y[p] * m'[p]) = constant /\ frame => Inv(m')
    // Actually, we add them as additional constraints on the init and query
    // to strengthen the invariant discovery.
    let query_strengthening = if config.use_p_invariants {
        let invariants = compute_p_invariants(net);
        p_invariant_constraints(&invariants, np)
    } else {
        Vec::new()
    };

    // ── Query clause ─────────────────────────────────────────────
    // Inv(m) /\ NOT safety(m) => false
    let mut query_conjuncts = Vec::with_capacity(1 + query_strengthening.len());
    query_conjuncts.push(encode_negated_predicate(property, net));
    query_conjuncts.extend(query_strengthening);
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, current_args)],
            Some(ChcExpr::and_all(query_conjuncts)),
        ),
        ClauseHead::False,
    ));

    problem
}

/// Solve a Petri net safety property using PDR/IC3 via z4-chc.
///
/// Returns `Safe` if an inductive invariant is found proving the property,
/// `Unsafe` if a counterexample is found, or `Unknown` if the solver
/// cannot determine the result within the time budget.
pub(crate) fn solve_petri_net_pdr(
    net: &PetriNet,
    property: &ResolvedPredicate,
    config: &PdrConfig,
) -> PdrCheckResult {
    let problem = encode_petri_net_pdr(net, property, config);

    let adaptive_config = AdaptiveConfig::with_budget(config.time_budget, config.verbose);
    let solver = AdaptivePortfolio::new(problem, adaptive_config);
    let result = solver.solve();

    match result {
        VerifiedChcResult::Safe(_) => PdrCheckResult::Safe,
        VerifiedChcResult::Unsafe(_) => PdrCheckResult::Unsafe,
        VerifiedChcResult::Unknown(_) => PdrCheckResult::Unknown,
        _ => PdrCheckResult::Unknown,
    }
}

// ── Predicate encoding ──────────────────────────────────────────────

/// Encode a resolved predicate as a `ChcExpr` over current-state marking
/// variables (`m_0`, `m_1`, ...).
fn encode_predicate_expr(pred: &ResolvedPredicate, net: &PetriNet) -> ChcExpr {
    match pred {
        ResolvedPredicate::True => ChcExpr::Bool(true),
        ResolvedPredicate::False => ChcExpr::Bool(false),
        ResolvedPredicate::And(children) => {
            let exprs: Vec<ChcExpr> = children
                .iter()
                .map(|c| encode_predicate_expr(c, net))
                .collect();
            ChcExpr::and_all(exprs)
        }
        ResolvedPredicate::Or(children) => {
            let exprs: Vec<ChcExpr> = children
                .iter()
                .map(|c| encode_predicate_expr(c, net))
                .collect();
            ChcExpr::or_all(exprs)
        }
        ResolvedPredicate::Not(inner) => ChcExpr::not(encode_predicate_expr(inner, net)),
        ResolvedPredicate::IntLe(left, right) => {
            ChcExpr::le(encode_int_expr(left), encode_int_expr(right))
        }
        ResolvedPredicate::IsFireable(transitions) => {
            let disjuncts: Vec<ChcExpr> = transitions
                .iter()
                .map(|t_idx| {
                    let transition = &net.transitions[t_idx.0 as usize];
                    if transition.inputs.is_empty() {
                        return ChcExpr::Bool(true);
                    }
                    let guards: Vec<ChcExpr> = transition
                        .inputs
                        .iter()
                        .map(|arc| {
                            ChcExpr::ge(
                                var_expr(arc.place.0 as usize),
                                ChcExpr::int(arc.weight as i64),
                            )
                        })
                        .collect();
                    ChcExpr::and_all(guards)
                })
                .collect();
            ChcExpr::or_all(disjuncts)
        }
    }
}

/// Encode a resolved integer expression as a `ChcExpr`.
fn encode_int_expr(expr: &ResolvedIntExpr) -> ChcExpr {
    match expr {
        ResolvedIntExpr::Constant(value) => ChcExpr::int(*value as i64),
        ResolvedIntExpr::TokensCount(places) => {
            if places.is_empty() {
                ChcExpr::int(0)
            } else if places.len() == 1 {
                var_expr(places[0].0 as usize)
            } else {
                let terms: Vec<ChcExpr> = places.iter().map(|p| var_expr(p.0 as usize)).collect();
                // Build a left-associative sum via repeated add
                terms
                    .into_iter()
                    .reduce(ChcExpr::add)
                    .unwrap_or_else(|| ChcExpr::int(0))
            }
        }
    }
}

/// Encode the negation of a safety predicate as a `ChcExpr`.
///
/// The query clause asserts `Inv(m) /\ NOT safety(m) => false`, so we need
/// the negation of the property.
fn encode_negated_predicate(pred: &ResolvedPredicate, net: &PetriNet) -> ChcExpr {
    ChcExpr::not(encode_predicate_expr(pred, net))
}

// ── P-invariant strengthening ───────────────────────────────────────

/// Encode current-state P-invariant equalities as query-strengthening facts.
///
/// Every reachable marking satisfies these equalities, so adding them to the
/// safety query only prunes unreachable over-approximation states from `Inv`.
fn p_invariant_constraints(invariants: &[PInvariant], num_places: usize) -> Vec<ChcExpr> {
    invariants
        .iter()
        .filter_map(|inv| {
            // Build the P-invariant expression: sum(y[p] * m[p])
            let terms: Vec<ChcExpr> = (0..num_places)
                .filter(|&p| inv.weights[p] > 0)
                .map(|p| {
                    if inv.weights[p] == 1 {
                        var_expr(p)
                    } else {
                        ChcExpr::mul(ChcExpr::int(inv.weights[p] as i64), var_expr(p))
                    }
                })
                .collect();

            if terms.is_empty() {
                return None;
            }

            let sum = terms
                .into_iter()
                .reduce(ChcExpr::add)
                .expect("non-empty terms");

            Some(ChcExpr::eq(sum, ChcExpr::int(inv.token_count as i64)))
        })
        .collect()
}

#[cfg(test)]
#[path = "pdr_encoding_tests.rs"]
mod tests;
