// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::conjoin;
use crate::expr::evaluate::evaluate_expr;
use crate::pdr::model::InvariantModel;
use crate::smt::SmtResult;
use crate::{ChcExpr, ChcProblem, ChcVar, ClauseHead, PredicateId, SmtValue};
use rustc_hash::{FxHashMap, FxHashSet};

/// Result of algebraic model validation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum AlgebraicValidationResult {
    /// Model is valid: all clauses satisfied.
    Valid,
    /// Model is invalid but concrete evaluation proved the system is UNSAFE:
    /// the algebraically-derived invariant admits bad states.
    UnsafeDetected,
    /// Model is invalid for other reasons.
    Invalid,
}

/// Validate the model against all CHC clauses using SMT.
#[cfg(test)]
pub(super) fn validate_model(problem: &ChcProblem, model: &InvariantModel) -> bool {
    matches!(
        validate_model_with_algebraic_fallback(problem, model, &FxHashSet::default(), false),
        AlgebraicValidationResult::Valid,
    )
}

pub(super) fn validate_model_with_algebraic_fallback(
    problem: &ChcProblem,
    model: &InvariantModel,
    algebraic_self_loop_preds: &FxHashSet<PredicateId>,
    verbose: bool,
) -> AlgebraicValidationResult {
    let mut smt = problem.make_smt_context();

    // SOUNDNESS FIX (#7986): Detect BvToInt-abstracted problems by checking
    // for mod/div operations in clause constraints. When BvToInt abstraction
    // is active, the "constructive proof" argument for accepting Unknown on
    // self-loop transitions is INVALID: the algebraic invariant was derived
    // in unbounded integers, but modular wrapping can make the invariant
    // false in the BV domain. For example, x >= 1 is valid for x = 1,2,4,...
    // in integers, but x = 1 * 2^16 = 0 (mod 2^16) violates it in BV16.
    let has_mod_div = problem.clauses().iter().any(|c| {
        c.body
            .constraint
            .as_ref()
            .is_some_and(ChcExpr::contains_mod_or_div)
            || c.body
                .predicates
                .iter()
                .any(|(_, args)| args.iter().any(ChcExpr::contains_mod_or_div))
            || match &c.head {
                ClauseHead::Predicate(_, args) => {
                    args.iter().any(ChcExpr::contains_mod_or_div)
                }
                ClauseHead::False => false,
            }
    });

    for clause in problem.clauses() {
        let mut body_conjuncts: Vec<ChcExpr> = Vec::new();

        for (pred_id, args) in &clause.body.predicates {
            if let Some(interp) = model.get(pred_id) {
                let substitution: Vec<(ChcVar, ChcExpr)> = interp
                    .vars
                    .iter()
                    .zip(args.iter())
                    .map(|(v, a)| (v.clone(), a.clone()))
                    .collect();
                body_conjuncts.push(interp.formula.substitute(&substitution));
            }
        }

        if let Some(constraint) = &clause.body.constraint {
            body_conjuncts.push(constraint.clone());
        }

        let body_formula = conjoin(body_conjuncts);

        let head_formula = match &clause.head {
            ClauseHead::Predicate(pred_id, args) => {
                if let Some(interp) = model.get(pred_id) {
                    let substitution: Vec<(ChcVar, ChcExpr)> = interp
                        .vars
                        .iter()
                        .zip(args.iter())
                        .map(|(v, a)| (v.clone(), a.clone()))
                        .collect();
                    interp.formula.substitute(&substitution)
                } else {
                    ChcExpr::Bool(true)
                }
            }
            ClauseHead::False => ChcExpr::Bool(false),
        };

        // Check: body AND NOT(head) is UNSAT
        let check = ChcExpr::and(body_formula.clone(), ChcExpr::not(head_formula.clone()));

        smt.reset();
        match smt.check_sat(&check) {
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {}
            SmtResult::Unknown
                if algebraic_self_loop_clause(clause, algebraic_self_loop_preds)
                    && !has_mod_div =>
            {
                // Accept Unknown on algebraic self-loop (transition) clauses
                // only when no BvToInt abstraction (mod/div) is present.
                // The algebraic solver has a constructive proof of
                // inductiveness (closed-form derivation), so Unknown from
                // SMT incompleteness (NIA) is acceptable for transitions
                // in the ORIGINAL integer domain.
                //
                // SOUNDNESS FIX (#7986): When BvToInt abstraction is active
                // (has_mod_div = true), Unknown must NOT be accepted. The
                // algebraic invariant was derived in unbounded integers but
                // modular wrapping can invalidate it. Example: bv_wide_mul_unsafe
                // where x >= 1 holds in Z but x = 2^16 mod 2^16 = 0 in BV16.
                if verbose {
                    safe_eprintln!(
                        "Algebraic: accepting SMT Unknown on self-loop transition clause {:?}",
                        clause
                    );
                }
            }
            SmtResult::Unknown
                if algebraic_query_clause(clause, algebraic_self_loop_preds)
                    && !has_mod_div =>
            {
                // #7688: Query clause returned Unknown (NIA). Before
                // accepting, try concrete evaluation: substitute small
                // integer values for all free variables and check if the
                // formula is satisfiable. If a concrete satisfying
                // assignment is found, the invariant does NOT exclude
                // bad states and must be rejected.
                //
                // SOUNDNESS FIX (#7986): Same as above -- when BvToInt
                // abstraction is active, concrete checks are insufficient
                // (BV overflow values like 2^16 exceed the concrete range).
                if concrete_query_check_sat(&check) {
                    if verbose {
                        safe_eprintln!(
                            "Algebraic: query clause Unknown but concrete check found SAT \
                             (invariant does not exclude bad states) (#7688)"
                        );
                    }
                    return AlgebraicValidationResult::UnsafeDetected;
                }
                // No concrete counterexample found. Accept the invariant:
                // the algebraic derivation provides a constructive proof,
                // and no concrete evidence contradicts it.
                if verbose {
                    safe_eprintln!(
                        "Algebraic: accepting SMT Unknown on query clause (no concrete counterexample)"
                    );
                }
            }
            result => {
                if verbose {
                    safe_eprintln!(
                        "Algebraic: validation failed on clause {:?} with result {:?}",
                        clause,
                        result
                    );
                }
                return AlgebraicValidationResult::Invalid;
            }
        }
    }

    AlgebraicValidationResult::Valid
}

fn algebraic_self_loop_clause(
    clause: &crate::HornClause,
    algebraic_self_loop_preds: &FxHashSet<PredicateId>,
) -> bool {
    let ClauseHead::Predicate(head_pred, _) = &clause.head else {
        return false;
    };
    clause.body.predicates.len() == 1
        && clause.body.predicates[0].0 == *head_pred
        && algebraic_self_loop_preds.contains(head_pred)
}

fn algebraic_query_clause(
    clause: &crate::HornClause,
    algebraic_self_loop_preds: &FxHashSet<PredicateId>,
) -> bool {
    matches!(clause.head, ClauseHead::False)
        && clause.body.predicates.len() == 1
        && algebraic_self_loop_preds.contains(&clause.body.predicates[0].0)
}

/// Try concrete integer evaluation to check satisfiability of a formula.
///
/// Evaluates the formula at integer points in a bounded range for each
/// variable. This catches cases where the SMT solver returns Unknown on NIA
/// formulas but concrete counterexamples exist (e.g., accumulator_unsafe
/// where x=11, y=55 satisfies the query).
///
/// Returns true if a satisfying assignment is found.
fn concrete_query_check_sat(formula: &ChcExpr) -> bool {
    let vars: Vec<ChcVar> = formula.vars().into_iter().collect();
    if vars.is_empty() || vars.len() > 4 {
        return false;
    }

    // Sample ranges scaled by dimensionality to stay fast.
    let range: Vec<i64> = match vars.len() {
        1 | 2 => (-10..=200).collect(),
        3 => (-5..=50).collect(),
        4 => (-3..=20).collect(),
        _ => return false,
    };

    concrete_check_recursive(formula, &vars, 0, &mut FxHashMap::default(), &range)
}

fn concrete_check_recursive(
    formula: &ChcExpr,
    vars: &[ChcVar],
    idx: usize,
    model: &mut FxHashMap<String, SmtValue>,
    range: &[i64],
) -> bool {
    if idx == vars.len() {
        matches!(evaluate_expr(formula, model), Some(SmtValue::Bool(true)))
    } else {
        for &val in range {
            model.insert(vars[idx].name.clone(), SmtValue::Int(val));
            if concrete_check_recursive(formula, vars, idx + 1, model, range) {
                return true;
            }
        }
        model.remove(&vars[idx].name);
        false
    }
}
