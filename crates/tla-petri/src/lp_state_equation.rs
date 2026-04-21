// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
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

/// Check if a target predicate is LP-infeasible under the state equation.
///
/// Returns `true` if the LP {M = M0 + C*x, x >= 0, M >= 0, phi(M)} is
/// infeasible, meaning no marking satisfying phi is reachable.
///
/// Returns `false` if the LP is feasible (inconclusive) or if the
/// predicate is not LP-encodable.
pub(crate) fn lp_unreachable(net: &PetriNet, predicate: &ResolvedPredicate) -> bool {
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
        return true; // Predicate is trivially False
    }

    matches!(problem.solve(), Err(minilp::Error::Infeasible))
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
