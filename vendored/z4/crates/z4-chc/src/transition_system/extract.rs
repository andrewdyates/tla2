// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! CHC problem extraction: convert a linear CHC problem into a transition system.

use super::TransitionSystem;
use crate::{ChcExpr, ChcProblem, ChcVar, ClauseHead, PredicateId};
use rustc_hash::FxHashSet;

impl TransitionSystem {
    /// Extract a transition system from a CHC problem.
    ///
    /// The problem must be a single-predicate linear CHC problem:
    /// - Exactly one predicate
    /// - At most one predicate in each clause body
    /// - At least one fact clause (init), one transition clause, and one query clause
    ///
    /// Part of #1032 (TPA engine).
    pub(crate) fn from_chc_problem(problem: &ChcProblem) -> Result<Self, String> {
        // Check: exactly one predicate
        if problem.predicates().len() != 1 {
            return Err(format!(
                "Expected 1 predicate, found {}",
                problem.predicates().len()
            ));
        }

        let pred = &problem.predicates()[0];
        let pred_id = pred.id;

        // Check: all clauses are linear (at most one predicate in body)
        for clause in problem.clauses() {
            if clause.body.predicates.len() > 1 {
                return Err("Non-linear clause: multiple predicates in body".to_string());
            }
        }

        // Create canonical variables
        let vars: Vec<ChcVar> = pred
            .arg_sorts
            .iter()
            .enumerate()
            .map(|(i, sort)| ChcVar::new(format!("v{i}"), sort.clone()))
            .collect();

        // Extract init constraint from fact clauses
        let init = Self::extract_init_constraint(problem, pred_id, &vars)
            .ok_or_else(|| "No fact clause found".to_string())?;

        // Extract transition constraint from transition clauses
        let transition = Self::extract_transition_constraint(problem, pred_id, &vars)
            .ok_or_else(|| "No transition clause found".to_string())?;

        // Extract query constraint from query clauses
        let query = Self::extract_query_constraint(problem, pred_id, &vars)
            .ok_or_else(|| "No query clause found".to_string())?;

        Ok(Self::new(pred_id, vars, init, transition, query))
    }

    /// Substitute clause arguments to canonical variables in a constraint.
    ///
    /// For each argument in `args`:
    /// - If it's a variable, substitute it in `constraint` with the canonical var.
    /// - If it's an expression, add an equality: `canonical_var = substituted_expr`.
    ///
    /// Returns the modified constraint, extra equalities, and the substitution map
    /// (needed by callers that do a second pass, e.g., transition head args).
    ///
    /// Uses the #2508 flatten pattern to avoid deep right-skewed binary And trees.
    fn substitute_args_to_canonical_vars(
        constraint: ChcExpr,
        args: &[ChcExpr],
        canonical_vars: &[ChcVar],
    ) -> (ChcExpr, Vec<ChcExpr>, Vec<(ChcVar, ChcExpr)>) {
        let subst_map: Vec<(ChcVar, ChcExpr)> = args
            .iter()
            .enumerate()
            .filter_map(|(i, arg)| {
                if let ChcExpr::Var(v) = arg {
                    Some((v.clone(), ChcExpr::var(canonical_vars[i].clone())))
                } else {
                    None
                }
            })
            .collect();

        let mut result = constraint;
        let mut extra_eqs = Vec::new();
        for (i, arg) in args.iter().enumerate() {
            if let ChcExpr::Var(v) = arg {
                result = result.substitute(&[(v.clone(), ChcExpr::var(canonical_vars[i].clone()))]);
            } else {
                let substituted_arg = arg.substitute(&subst_map);
                extra_eqs.push(ChcExpr::eq(
                    ChcExpr::var(canonical_vars[i].clone()),
                    substituted_arg,
                ));
            }
        }

        (result, extra_eqs, subst_map)
    }

    /// Combine a constraint with extra equalities using and_all (#2508 flatten pattern).
    fn finalize_constraint(constraint: ChcExpr, extra_eqs: Vec<ChcExpr>) -> ChcExpr {
        if extra_eqs.is_empty() {
            constraint
        } else {
            let mut all = extra_eqs;
            all.insert(0, constraint);
            ChcExpr::and_all(all)
        }
    }

    /// Rename local (non-canonical) variables in a constraint to avoid collisions.
    ///
    /// After substituting predicate arguments to canonical variables (v0..vN,
    /// v0_next..vN_next), any remaining free variables are clause-local
    /// existentials. Different clauses may reuse the same variable names for
    /// their locals. When init, transition, and query constraints are conjoined
    /// (e.g., `init ∧ Tr ∧ query`), these same-named locals accidentally merge,
    /// adding spurious constraints that make satisfiable formulas appear UNSAT.
    ///
    /// This function renames all non-canonical variables by prefixing them with
    /// a unique clause tag (e.g., `__init0_`, `__tr0_`, `__qry0_`).
    ///
    /// Fixes #6789: Kind engine false-Safe caused by local variable collision.
    fn rename_local_vars(
        constraint: ChcExpr,
        canonical_vars: &[ChcVar],
        next_vars: Option<&[ChcVar]>,
        prefix: &str,
    ) -> ChcExpr {
        // Collect all variables in the constraint
        let all_vars = constraint.vars();

        // Build set of canonical var names to exclude from renaming
        let mut canonical_names: FxHashSet<String> =
            canonical_vars.iter().map(|v| v.name.clone()).collect();
        if let Some(nvars) = next_vars {
            for v in nvars {
                canonical_names.insert(v.name.clone());
            }
        }

        // Build substitution for local vars only
        let substitutions: Vec<(ChcVar, ChcExpr)> = all_vars
            .into_iter()
            .filter(|v| !canonical_names.contains(&v.name))
            .map(|v| {
                let renamed = ChcVar::new(format!("{}{}", prefix, v.name), v.sort.clone());
                (v, ChcExpr::var(renamed))
            })
            .collect();

        if substitutions.is_empty() {
            constraint
        } else {
            constraint.substitute(&substitutions)
        }
    }

    /// Extract init constraint: maps fact clauses to constraint on canonical vars.
    fn extract_init_constraint(
        problem: &ChcProblem,
        pred_id: PredicateId,
        vars: &[ChcVar],
    ) -> Option<ChcExpr> {
        let mut init_disjuncts = Vec::new();

        for (idx, fact) in problem.facts().enumerate() {
            if fact.head.predicate_id() != Some(pred_id) {
                continue;
            }

            // Get head arguments
            let head_args = match &fact.head {
                ClauseHead::Predicate(_, args) => args,
                _ => continue,
            };

            let constraint = fact.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));
            let (constraint, extra_eqs, _) =
                Self::substitute_args_to_canonical_vars(constraint, head_args, vars);
            let combined = Self::finalize_constraint(constraint, extra_eqs);
            // Rename local variables to avoid collisions with transition/query locals (#6789)
            let prefix = format!("__init{idx}_");
            init_disjuncts.push(Self::rename_local_vars(combined, vars, None, &prefix));
        }

        if init_disjuncts.is_empty() {
            None
        } else {
            Some(ChcExpr::or_all(init_disjuncts))
        }
    }

    /// Extract transition constraint from transition clauses.
    fn extract_transition_constraint(
        problem: &ChcProblem,
        pred_id: PredicateId,
        vars: &[ChcVar],
    ) -> Option<ChcExpr> {
        let mut trans_disjuncts = Vec::new();

        // Create "next" variables
        let next_vars: Vec<ChcVar> = vars
            .iter()
            .map(|v| ChcVar::new(format!("{}_next", v.name), v.sort.clone()))
            .collect();

        for (idx, trans) in problem.transitions().enumerate() {
            // Body should have the predicate
            let (body_pred, body_args) = trans.body.predicates.first()?;
            if *body_pred != pred_id {
                continue;
            }

            // Head should also be the predicate
            let head_args = match &trans.head {
                ClauseHead::Predicate(p, args) if *p == pred_id => args,
                _ => continue,
            };

            // Substitute body args with current canonical vars
            let constraint = trans.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));
            let (mut constraint, mut extra_eqs, body_subst) =
                Self::substitute_args_to_canonical_vars(constraint, body_args, vars);

            // Substitute head args with next vars
            for (i, head_arg) in head_args.iter().enumerate() {
                if let ChcExpr::Var(v) = head_arg {
                    // Check if this variable was already substituted by the body pass.
                    // This happens when the same variable appears as both a body arg and
                    // a head arg (e.g., inv(B,C,F,A) → inv(D,E,F,G) where F is at
                    // position 2 in both). After body substitution, F no longer exists
                    // in the constraint (replaced by v2), so substituting F→v2_next
                    // would be a no-op, leaving v2_next unconstrained.
                    // Fix: add explicit equality next_var[i] = canonical_var.
                    if let Some((_, canonical_expr)) = body_subst.iter().find(|(bv, _)| bv == v) {
                        extra_eqs.push(ChcExpr::eq(
                            ChcExpr::var(next_vars[i].clone()),
                            canonical_expr.clone(),
                        ));
                    } else {
                        constraint = constraint
                            .substitute(&[(v.clone(), ChcExpr::var(next_vars[i].clone()))]);
                    }
                } else {
                    // Apply body substitution to head_arg before adding equality
                    // This ensures variables like `x` in `x + 1` get mapped to canonical vars
                    // Fixes #1102: head arg expressions must use canonical variables
                    let substituted_head_arg = head_arg.substitute(&body_subst);
                    extra_eqs.push(ChcExpr::eq(
                        ChcExpr::var(next_vars[i].clone()),
                        substituted_head_arg,
                    ));
                }
            }
            let combined = Self::finalize_constraint(constraint, extra_eqs);
            // Rename local variables to avoid collisions with init/query locals (#6789)
            let prefix = format!("__tr{idx}_");
            trans_disjuncts.push(Self::rename_local_vars(
                combined,
                vars,
                Some(&next_vars),
                &prefix,
            ));
        }

        if trans_disjuncts.is_empty() {
            None
        } else {
            Some(ChcExpr::or_all(trans_disjuncts))
        }
    }

    /// Extract query constraint from query clauses.
    fn extract_query_constraint(
        problem: &ChcProblem,
        pred_id: PredicateId,
        vars: &[ChcVar],
    ) -> Option<ChcExpr> {
        let mut query_disjuncts = Vec::new();

        for (idx, query) in problem.queries().enumerate() {
            // Body should have the predicate
            let (body_pred, body_args) = query.body.predicates.first()?;
            if *body_pred != pred_id {
                continue;
            }

            let constraint = query.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));
            let (constraint, extra_eqs, _) =
                Self::substitute_args_to_canonical_vars(constraint, body_args, vars);
            let combined = Self::finalize_constraint(constraint, extra_eqs);
            // Rename local variables to avoid collisions with init/transition locals (#6789)
            let prefix = format!("__qry{idx}_");
            query_disjuncts.push(Self::rename_local_vars(combined, vars, None, &prefix));
        }

        if query_disjuncts.is_empty() {
            None
        } else {
            Some(ChcExpr::or_all(query_disjuncts))
        }
    }
}
