// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! LP relaxation of the Petri net state equation for structural analysis.
//!
//! The state equation M = M0 + C*x (where C is the incidence matrix,
//! x >= 0 is a firing count vector, and M >= 0 is the target marking)
//! is a *necessary* condition for reachability. If the LP is infeasible
//! under added constraints, the target marking is provably unreachable.
//!
//! Two capabilities:
//!
//! 1. **Reachability pruning**: encode a predicate as LP constraints.
//!    If infeasible, the predicate is unreachable (EF = FALSE).
//!
//! 2. **Upper bound tightening**: maximize token sum for a place set
//!    subject to the state equation. At least as tight as P-invariant
//!    bounds (P-invariants are the LP dual).
//!
//! Reference: Murata (1989) "Petri nets: Properties, analysis and
//! applications." Proc. IEEE 77(4).

use minilp::{ComparisonOp, OptimizationDirection, Problem, Variable};

use crate::petri_net::{PetriNet, PlaceIdx};
use crate::resolved_predicate::{ResolvedIntExpr, ResolvedPredicate};

/// Maximum LP variables before skipping (prevents pathological nets).
const MAX_LP_VARIABLES: usize = 50_000;

/// Add state equation constraints to an LP problem.
///
/// Given firing count variables `x_vars` and marking variables `m_vars`,
/// adds: m[p] - sum_t C[p][t]*x[t] = m0[p] for each place p.
fn add_state_equation(
    problem: &mut Problem,
    net: &PetriNet,
    x_vars: &[Variable],
    m_vars: &[Variable],
) {
    let np = net.num_places();
    for p in 0..np {
        let mut row = Vec::new();
        row.push((m_vars[p], 1.0));
        for (t, transition) in net.transitions.iter().enumerate() {
            // -C[p][t] = input_weight - output_weight
            let mut coeff = 0.0_f64;
            for arc in &transition.inputs {
                if arc.place.0 as usize == p {
                    coeff += arc.weight as f64;
                }
            }
            for arc in &transition.outputs {
                if arc.place.0 as usize == p {
                    coeff -= arc.weight as f64;
                }
            }
            if coeff.abs() > f64::EPSILON {
                row.push((x_vars[t], coeff));
            }
        }
        problem.add_constraint(&row, ComparisonOp::Eq, net.initial_marking[p] as f64);
    }
}

/// Accumulate an integer expression into a linear constraint row.
///
/// `variable_coeff` scales marking-variable terms, while `constant_coeff`
/// contributes to the scalar right-hand side.
fn accumulate_int_expr(
    expr: &ResolvedIntExpr,
    coefficients: &mut [f64],
    rhs: &mut f64,
    variable_coeff: f64,
    constant_coeff: f64,
) {
    match expr {
        ResolvedIntExpr::Constant(c) => *rhs += constant_coeff * (*c as f64),
        ResolvedIntExpr::TokensCount(places) => {
            for place in places {
                coefficients[place.0 as usize] += variable_coeff;
            }
        }
    }
}

/// Build the linear constraint row for `lhs <= rhs`.
fn build_int_le_constraint(
    lhs: &ResolvedIntExpr,
    rhs: &ResolvedIntExpr,
    m_vars: &[Variable],
) -> (Vec<(Variable, f64)>, f64) {
    let mut coefficients = vec![0.0_f64; m_vars.len()];
    let mut rhs_bound = 0.0_f64;
    accumulate_int_expr(lhs, &mut coefficients, &mut rhs_bound, 1.0, -1.0);
    accumulate_int_expr(rhs, &mut coefficients, &mut rhs_bound, -1.0, 1.0);
    let row = coefficients
        .into_iter()
        .enumerate()
        .filter_map(|(index, coefficient)| {
            (coefficient.abs() > f64::EPSILON).then_some((m_vars[index], coefficient))
        })
        .collect();
    (row, rhs_bound)
}

/// Check if a predicate is LP-amenable (pure conjunctions of IntLe).
///
/// The LP encodes conjunctions of linear inequalities over marking
/// variables. Or, Not, and IsFireable require case analysis.
fn is_lp_amenable(pred: &ResolvedPredicate) -> bool {
    match pred {
        ResolvedPredicate::And(children) => children.iter().all(is_lp_amenable),
        ResolvedPredicate::IntLe(_, _) | ResolvedPredicate::True | ResolvedPredicate::False => true,
        ResolvedPredicate::Or(_) | ResolvedPredicate::Not(_) | ResolvedPredicate::IsFireable(_) => {
            false
        }
    }
}

/// Add LP constraints encoding a resolved predicate.
///
/// Returns `false` if the predicate is `False` (trivially infeasible).
fn add_predicate_constraints(
    problem: &mut Problem,
    pred: &ResolvedPredicate,
    m_vars: &[Variable],
) -> bool {
    match pred {
        ResolvedPredicate::And(children) => {
            for child in children {
                if !add_predicate_constraints(problem, child, m_vars) {
                    return false;
                }
            }
            true
        }
        ResolvedPredicate::IntLe(left, right) => {
            let (row, rhs_bound) = build_int_le_constraint(left, right, m_vars);
            problem.add_constraint(&row, ComparisonOp::Le, rhs_bound);
            true
        }
        ResolvedPredicate::True => true,
        ResolvedPredicate::False => false,
        _ => true,
    }
}

/// Check if a place set forms a trap.
///
/// A trap T satisfies: for every transition t that consumes from T
/// (has an input arc from some place in T), t also produces into T
/// (has an output arc to some place in T). Key property: once marked,
/// a trap stays marked forever.
fn is_trap(net: &PetriNet, places: &[bool]) -> bool {
    for transition in &net.transitions {
        let consumes_from_set = transition
            .inputs
            .iter()
            .any(|arc| places[arc.place.0 as usize]);
        if consumes_from_set
            && !transition
                .outputs
                .iter()
                .any(|arc| places[arc.place.0 as usize])
        {
            return false;
        }
    }
    true
}

/// Compute the siphon closure of an initial place set.
///
/// A siphon S satisfies: every transition producing into S also consumes
/// from S. This function grows the initial set until the siphon property
/// holds by adding input places of transitions that produce into the set
/// but do not yet consume from it.
fn siphon_closure(net: &PetriNet, initial: &[bool]) -> Vec<bool> {
    let mut set = initial.to_vec();
    loop {
        let mut changed = false;
        for transition in &net.transitions {
            let produces_into_set = transition
                .outputs
                .iter()
                .any(|arc| set[arc.place.0 as usize]);
            if !produces_into_set {
                continue;
            }

            let consumes_from_set = transition
                .inputs
                .iter()
                .any(|arc| set[arc.place.0 as usize]);
            if consumes_from_set {
                continue;
            }

            for arc in &transition.inputs {
                let place = arc.place.0 as usize;
                if !set[place] {
                    set[place] = true;
                    changed = true;
                }
            }
        }

        if !changed {
            break;
        }
    }
    set
}

/// Extract the maximal trap contained within a siphon.
///
/// Every siphon contains a (possibly empty) maximal trap. This function
/// iteratively removes places that violate the trap property until a
/// fixed point is reached. The result is guaranteed to be a trap (or empty).
fn maximal_trap_within_siphon(net: &PetriNet, siphon: &[bool]) -> Vec<bool> {
    let mut trap_candidate = siphon.to_vec();
    loop {
        let mut changed = false;
        for place in 0..trap_candidate.len() {
            if !trap_candidate[place] {
                continue;
            }

            let place_is_valid = net.transitions.iter().all(|transition| {
                let consumes_place = transition
                    .inputs
                    .iter()
                    .any(|arc| arc.place.0 as usize == place);
                !consumes_place
                    || transition
                        .outputs
                        .iter()
                        .any(|arc| trap_candidate[arc.place.0 as usize])
            });

            if !place_is_valid {
                trap_candidate[place] = false;
                changed = true;
            }
        }

        if !changed {
            break;
        }
    }
    debug_assert!(!trap_candidate.iter().any(|&in_trap| in_trap) || is_trap(net, &trap_candidate));
    trap_candidate
}

/// Minimize a trap by greedily removing places.
///
/// Tries to remove each place one at a time; if the remaining set is
/// still a non-empty trap, the removal is kept. Produces a minimal
/// (not necessarily minimum) trap.
fn minimize_trap(net: &PetriNet, trap: &[bool]) -> Vec<bool> {
    let mut result = trap.to_vec();
    loop {
        let mut changed = false;
        for place in 0..result.len() {
            if !result[place] {
                continue;
            }

            result[place] = false;
            if result.iter().any(|&in_trap| in_trap) && is_trap(net, &result) {
                changed = true;
            } else {
                result[place] = true;
            }
        }

        if !changed {
            break;
        }
    }
    result
}

/// Enumerate all distinct minimal traps that are initially marked.
///
/// For each place, computes the siphon closure, extracts the maximal
/// trap within, minimizes it, and keeps it if at least one place in
/// the trap has tokens in the initial marking. Deduplicates results.
/// These traps generate valid LP constraints: sum of marking >= 1.
pub(crate) fn find_initially_marked_traps(net: &PetriNet) -> Vec<Vec<bool>> {
    let num_places = net.num_places();
    let mut traps = Vec::new();

    for seed_place in 0..num_places {
        let mut initial = vec![false; num_places];
        initial[seed_place] = true;

        let closure = siphon_closure(net, &initial);
        if !closure.iter().any(|&in_set| in_set) {
            continue;
        }

        let maximal_trap = maximal_trap_within_siphon(net, &closure);
        if !maximal_trap.iter().any(|&in_set| in_set) {
            continue;
        }

        let minimal_trap = minimize_trap(net, &maximal_trap);
        if !minimal_trap.iter().any(|&in_set| in_set) {
            continue;
        }

        let initially_marked = minimal_trap
            .iter()
            .enumerate()
            .any(|(place, &in_trap)| in_trap && net.initial_marking[place] > 0);
        if !initially_marked {
            continue;
        }

        if !traps.iter().any(|trap| trap == &minimal_trap) {
            traps.push(minimal_trap);
        }
    }

    traps
}

/// Check unreachability using the LP state equation with iterative trap tightening.
///
/// Solves M = M0 + C*x with the predicate constraints, then iteratively
/// adds trap invariants (sum of marking in trap >= 1) for initially-marked
/// traps whose LP solution violates the invariant. If adding these
/// constraints makes the LP infeasible, the predicate marking is provably
/// unreachable. This is a key SMPT technique that strengthens the basic
/// state equation overapproximation.
pub(crate) fn lp_unreachable_with_traps(net: &PetriNet, predicate: &ResolvedPredicate) -> bool {
    if !is_lp_amenable(predicate) {
        return false;
    }

    let np = net.num_places();
    let nt = net.num_transitions();

    if np + nt > MAX_LP_VARIABLES {
        return false;
    }

    let traps = find_initially_marked_traps(net);

    let mut problem = Problem::new(OptimizationDirection::Minimize);

    let x_vars: Vec<_> = (0..nt)
        .map(|_| problem.add_var(0.0, (0.0, f64::INFINITY)))
        .collect();
    let m_vars: Vec<_> = (0..np)
        .map(|_| problem.add_var(0.0, (0.0, f64::INFINITY)))
        .collect();

    add_state_equation(&mut problem, net, &x_vars, &m_vars);

    if !add_predicate_constraints(&mut problem, predicate, &m_vars) {
        return true;
    }

    let mut solution = match problem.solve() {
        Ok(solution) => solution,
        Err(minilp::Error::Infeasible) => return true,
        Err(minilp::Error::Unbounded) => return false,
    };

    let mut added_constraints = vec![false; traps.len()];
    for _ in 0..100 {
        let violated_traps: Vec<_> = traps
            .iter()
            .enumerate()
            .filter_map(|(trap_idx, trap)| {
                if added_constraints[trap_idx] {
                    return None;
                }

                let trap_sum: f64 = trap
                    .iter()
                    .enumerate()
                    .filter_map(|(place, &in_trap)| {
                        in_trap.then_some(*solution.var_value(m_vars[place]))
                    })
                    .sum();

                (trap_sum < 0.5).then_some(trap_idx)
            })
            .collect();

        if violated_traps.is_empty() {
            return false;
        }

        for trap_idx in violated_traps {
            added_constraints[trap_idx] = true;
            let constraint: Vec<_> = traps[trap_idx]
                .iter()
                .enumerate()
                .filter_map(|(place, &in_trap)| in_trap.then_some((m_vars[place], 1.0)))
                .collect();

            solution = match solution.add_constraint(constraint, ComparisonOp::Ge, 1.0) {
                Ok(solution) => solution,
                Err(minilp::Error::Infeasible) => return true,
                Err(minilp::Error::Unbounded) => return false,
            };
        }
    }

    false
}

/// Check if a target predicate is LP-infeasible under the state equation.
///
/// Returns `true` if the LP {M = M0 + C*x, x >= 0, M >= 0, phi(M)} is
/// infeasible, meaning no marking satisfying phi is reachable.
///
/// Returns `false` if the LP is feasible (inconclusive) or if the
/// predicate is not LP-encodable.
pub(crate) fn lp_unreachable(net: &PetriNet, predicate: &ResolvedPredicate) -> bool {
    lp_unreachable_with_traps(net, predicate)
}

/// Check whether the strict inequality `lhs > rhs` is LP-infeasible.
///
/// Over the integer Petri-net domain, `lhs > rhs` is equivalent to
/// `rhs + 1 <= lhs`. If the LP relaxation is infeasible under that
/// constraint, no reachable marking can violate `lhs <= rhs`.
pub(crate) fn lp_strictly_greater_unreachable(
    net: &PetriNet,
    lhs: &ResolvedIntExpr,
    rhs: &ResolvedIntExpr,
) -> bool {
    let np = net.num_places();
    let nt = net.num_transitions();

    if np + nt > MAX_LP_VARIABLES {
        return false;
    }

    let mut problem = Problem::new(OptimizationDirection::Minimize);

    let x_vars: Vec<_> = (0..nt)
        .map(|_| problem.add_var(0.0, (0.0, f64::INFINITY)))
        .collect();
    let m_vars: Vec<_> = (0..np)
        .map(|_| problem.add_var(0.0, (0.0, f64::INFINITY)))
        .collect();

    add_state_equation(&mut problem, net, &x_vars, &m_vars);

    let (row, rhs_bound) = build_int_le_constraint(rhs, lhs, &m_vars);
    problem.add_constraint(&row, ComparisonOp::Le, rhs_bound - 1.0);

    matches!(problem.solve(), Err(minilp::Error::Infeasible))
}

/// Compute an LP upper bound on the sum of tokens at specified places.
///
/// Solves: maximize sum(M[p] for p in places)
/// subject to: M = M0 + C*x, x >= 0, M >= 0.
///
/// Returns `Some(bound)` if the LP has a finite optimum, `None` if
/// unbounded or the net is too large.
pub(crate) fn lp_upper_bound(net: &PetriNet, places: &[PlaceIdx]) -> Option<u64> {
    if places.is_empty() {
        return Some(0);
    }

    let np = net.num_places();
    let nt = net.num_transitions();

    if np + nt > MAX_LP_VARIABLES {
        return None;
    }

    let mut problem = Problem::new(OptimizationDirection::Maximize);

    let x_vars: Vec<_> = (0..nt)
        .map(|_| problem.add_var(0.0, (0.0, f64::INFINITY)))
        .collect();

    // Objective coefficients: multiplicity-aware for repeated places.
    let mut obj_coeffs = vec![0.0_f64; np];
    for place in places {
        obj_coeffs[place.0 as usize] += 1.0;
    }
    let m_vars: Vec<_> = (0..np)
        .map(|p| problem.add_var(obj_coeffs[p], (0.0, f64::INFINITY)))
        .collect();

    add_state_equation(&mut problem, net, &x_vars, &m_vars);

    match problem.solve() {
        Ok(solution) => {
            let obj = solution.objective();
            // minilp may return a very large finite value instead of
            // Unbounded for effectively unconstrained problems. Treat
            // values above 1e15 as unbounded (no Petri net in MCC has
            // token counts anywhere near this).
            if obj > 1e15 {
                return None;
            }
            // ceil() is sound: ceil(LP_max) >= LP_max >= true_max.
            // floor() is theoretically tighter (floor(1.5)=1 is correct
            // since LP over-approximates), but floating-point error in
            // the simplex solver can push a true-integer optimum below
            // the integer boundary (e.g., 0.9999 instead of 1.0), and
            // floor(0.9999) = 0 is unsound. This caused wrong answers
            // on NQueens-PT-30 and IBM5964-PT-none. (#1501)
            let bound = obj.ceil() as u64;
            Some(bound)
        }
        // Infeasible should never occur (x=0, m=m0 is always feasible for
        // valid Petri nets). If minilp reports it, treat as numerical
        // instability → unknown. Returning Some(0) here was unsound: it
        // overrode correct P-invariant bounds (NQueens-PT-30 #1501).
        Err(minilp::Error::Infeasible) => None,
        Err(minilp::Error::Unbounded) => None,
    }
}

/// Determine the truth value of an individual resolved predicate atom via LP.
///
/// Returns:
/// - `Some(false)` if LP proves the atom is unreachable (never satisfiable)
/// - `Some(true)` if LP proves the atom always holds
/// - `None` if LP is inconclusive or the atom is not LP-amenable
///
/// Only `IntLe`, `True`, and `False` atoms produce definite results.
/// Compound shapes (`And`, `Or`, `Not`) and `IsFireable` return `None`.
pub(crate) fn lp_atom_truth(net: &PetriNet, atom: &ResolvedPredicate) -> Option<bool> {
    match atom {
        ResolvedPredicate::True => Some(true),
        ResolvedPredicate::False => Some(false),
        ResolvedPredicate::IntLe(lhs, rhs) => {
            let singleton = ResolvedPredicate::IntLe(lhs.clone(), rhs.clone());
            if lp_unreachable(net, &singleton) {
                return Some(false);
            }
            if lp_strictly_greater_unreachable(net, lhs, rhs) {
                return Some(true);
            }
            None
        }
        _ => None,
    }
}

/// Check if a predicate holds in ALL reachable markings using LP.
///
/// Returns `true` when every LP-checkable violating branch is infeasible,
/// meaning the predicate can never be violated. Only handles conjunctions
/// of `IntLe` atoms; returns `false` for non-amenable shapes (`Or`, `Not`,
/// `IsFireable`).
///
/// This is the shared dual of [`lp_unreachable`]: where `lp_unreachable`
/// proves `φ` NEVER holds, this proves `φ` ALWAYS holds.
pub(crate) fn lp_always_true(net: &PetriNet, predicate: &ResolvedPredicate) -> bool {
    match predicate {
        ResolvedPredicate::And(children) => children.iter().all(|child| lp_always_true(net, child)),
        ResolvedPredicate::IntLe(lhs, rhs) => lp_strictly_greater_unreachable(net, lhs, rhs),
        ResolvedPredicate::True => true,
        ResolvedPredicate::False => false,
        ResolvedPredicate::Or(_) | ResolvedPredicate::Not(_) | ResolvedPredicate::IsFireable(_) => {
            false
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::petri_net::{Arc, PetriNet, PlaceInfo, TransitionInfo};

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

    fn conserving_net() -> PetriNet {
        PetriNet {
            name: None,
            places: vec![place("p0"), place("p1")],
            transitions: vec![trans("t0", vec![arc(0, 1)], vec![arc(1, 1)])],
            initial_marking: vec![3, 0],
        }
    }

    fn dual_kill_trap_net() -> PetriNet {
        PetriNet {
            name: None,
            places: vec![place("p0"), place("p1")],
            transitions: vec![
                trans("t0", vec![arc(0, 1), arc(1, 1)], vec![arc(0, 1)]),
                trans("t1", vec![arc(0, 1), arc(1, 1)], vec![arc(1, 1)]),
                trans("t2", vec![arc(1, 1)], vec![arc(0, 1)]),
            ],
            initial_marking: vec![1, 1],
        }
    }

    fn basic_lp_unreachable_without_traps(net: &PetriNet, predicate: &ResolvedPredicate) -> bool {
        if !is_lp_amenable(predicate) {
            return false;
        }

        let np = net.num_places();
        let nt = net.num_transitions();

        if np + nt > MAX_LP_VARIABLES {
            return false;
        }

        let mut problem = Problem::new(OptimizationDirection::Minimize);

        let x_vars: Vec<_> = (0..nt)
            .map(|_| problem.add_var(0.0, (0.0, f64::INFINITY)))
            .collect();
        let m_vars: Vec<_> = (0..np)
            .map(|_| problem.add_var(0.0, (0.0, f64::INFINITY)))
            .collect();

        add_state_equation(&mut problem, net, &x_vars, &m_vars);

        if !add_predicate_constraints(&mut problem, predicate, &m_vars) {
            return true;
        }

        matches!(problem.solve(), Err(minilp::Error::Infeasible))
    }

    #[test]
    fn test_lp_upper_bound_conserving_net() {
        let net = conserving_net();
        assert_eq!(lp_upper_bound(&net, &[PlaceIdx(0)]), Some(3));
        assert_eq!(lp_upper_bound(&net, &[PlaceIdx(1)]), Some(3));
        assert_eq!(lp_upper_bound(&net, &[PlaceIdx(0), PlaceIdx(1)]), Some(3));
    }

    #[test]
    fn test_lp_upper_bound_unbounded_net() {
        let net = PetriNet {
            name: None,
            places: vec![place("p0")],
            transitions: vec![trans("t0", vec![], vec![arc(0, 1)])],
            initial_marking: vec![0],
        };
        assert_eq!(lp_upper_bound(&net, &[PlaceIdx(0)]), None);
    }

    #[test]
    fn test_lp_upper_bound_empty_places() {
        let net = conserving_net();
        assert_eq!(lp_upper_bound(&net, &[]), Some(0));
    }

    #[test]
    fn test_lp_unreachable_impossible_marking() {
        let net = conserving_net();
        // p0 >= 5 is unreachable (p0 + p1 = 3, p1 >= 0 => p0 <= 3).
        let pred = ResolvedPredicate::IntLe(
            ResolvedIntExpr::Constant(5),
            ResolvedIntExpr::TokensCount(vec![PlaceIdx(0)]),
        );
        assert!(lp_unreachable(&net, &pred));
    }

    #[test]
    fn test_lp_unreachable_possible_marking() {
        let net = conserving_net();
        // p1 >= 2 is reachable (fire t0 twice).
        let pred = ResolvedPredicate::IntLe(
            ResolvedIntExpr::Constant(2),
            ResolvedIntExpr::TokensCount(vec![PlaceIdx(1)]),
        );
        assert!(!lp_unreachable(&net, &pred));
    }

    #[test]
    fn test_lp_unreachable_conjunction() {
        let net = conserving_net();
        // p0 >= 2 AND p1 >= 2 is impossible (sum = 3).
        let pred = ResolvedPredicate::And(vec![
            ResolvedPredicate::IntLe(
                ResolvedIntExpr::Constant(2),
                ResolvedIntExpr::TokensCount(vec![PlaceIdx(0)]),
            ),
            ResolvedPredicate::IntLe(
                ResolvedIntExpr::Constant(2),
                ResolvedIntExpr::TokensCount(vec![PlaceIdx(1)]),
            ),
        ]);
        assert!(lp_unreachable(&net, &pred));
    }

    #[test]
    fn test_lp_unreachable_trivially_false() {
        let net = conserving_net();
        assert!(lp_unreachable(&net, &ResolvedPredicate::False));
    }

    #[test]
    fn test_lp_unreachable_trivially_true() {
        let net = conserving_net();
        assert!(!lp_unreachable(&net, &ResolvedPredicate::True));
    }

    #[test]
    fn test_lp_unreachable_non_amenable_skipped() {
        let net = conserving_net();
        let pred = ResolvedPredicate::Or(vec![
            ResolvedPredicate::IntLe(
                ResolvedIntExpr::Constant(5),
                ResolvedIntExpr::TokensCount(vec![PlaceIdx(0)]),
            ),
            ResolvedPredicate::True,
        ]);
        assert!(!lp_unreachable(&net, &pred));
    }

    #[test]
    fn test_find_initially_marked_traps_dual_kill_net() {
        let net = dual_kill_trap_net();
        assert_eq!(find_initially_marked_traps(&net), vec![vec![true, true]]);
    }

    #[test]
    fn test_lp_unreachable_with_traps_closes_feasible_basic_lp() {
        let net = dual_kill_trap_net();
        let pred = ResolvedPredicate::IntLe(
            ResolvedIntExpr::TokensCount(vec![PlaceIdx(0), PlaceIdx(1)]),
            ResolvedIntExpr::Constant(0),
        );

        assert!(
            !basic_lp_unreachable_without_traps(&net, &pred),
            "basic state-equation LP admits the empty-trap marking"
        );
        assert!(lp_unreachable_with_traps(&net, &pred));
        assert!(lp_unreachable(&net, &pred));
    }

    #[test]
    fn test_lp_unreachable_with_traps_stays_feasible_when_traps_do_not_help() {
        let net = dual_kill_trap_net();
        let pred = ResolvedPredicate::And(vec![
            ResolvedPredicate::IntLe(
                ResolvedIntExpr::Constant(1),
                ResolvedIntExpr::TokensCount(vec![PlaceIdx(0)]),
            ),
            ResolvedPredicate::IntLe(
                ResolvedIntExpr::TokensCount(vec![PlaceIdx(1)]),
                ResolvedIntExpr::Constant(0),
            ),
        ]);

        assert!(!basic_lp_unreachable_without_traps(&net, &pred));
        assert!(!lp_unreachable_with_traps(&net, &pred));
    }

    #[test]
    fn test_lp_unreachable_with_traps_preserves_basic_infeasibility() {
        let net = conserving_net();
        let pred = ResolvedPredicate::IntLe(
            ResolvedIntExpr::Constant(5),
            ResolvedIntExpr::TokensCount(vec![PlaceIdx(0)]),
        );

        assert!(basic_lp_unreachable_without_traps(&net, &pred));
        assert!(lp_unreachable_with_traps(&net, &pred));
    }

    #[test]
    fn test_lp_strictly_greater_unreachable_token_rhs() {
        let net = conserving_net();
        assert!(lp_strictly_greater_unreachable(
            &net,
            &ResolvedIntExpr::TokensCount(vec![PlaceIdx(0)]),
            &ResolvedIntExpr::TokensCount(vec![PlaceIdx(0), PlaceIdx(1)]),
        ));
    }

    #[test]
    fn test_lp_strictly_greater_unreachable_feasible_violation() {
        let net = conserving_net();
        assert!(!lp_strictly_greater_unreachable(
            &net,
            &ResolvedIntExpr::TokensCount(vec![PlaceIdx(0)]),
            &ResolvedIntExpr::TokensCount(vec![PlaceIdx(1)]),
        ));
    }

    #[test]
    fn test_lp_upper_bound_weighted_net() {
        // p0(4) -2-> t0 -1-> p1. m0 = 4-2x, m1 = x, x <= 2.
        let net = PetriNet {
            name: None,
            places: vec![place("p0"), place("p1")],
            transitions: vec![trans("t0", vec![arc(0, 2)], vec![arc(1, 1)])],
            initial_marking: vec![4, 0],
        };
        assert_eq!(lp_upper_bound(&net, &[PlaceIdx(1)]), Some(2));
        assert_eq!(lp_upper_bound(&net, &[PlaceIdx(0)]), Some(4));
    }

    #[test]
    fn test_lp_upper_bound_with_multiplicity() {
        let net = conserving_net();
        // max(2*p1) = 2*3 = 6
        assert_eq!(lp_upper_bound(&net, &[PlaceIdx(1), PlaceIdx(1)]), Some(6));
    }
}
