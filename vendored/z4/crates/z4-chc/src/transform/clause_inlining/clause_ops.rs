// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Clause-level inlining operations.
//!
//! Contains the low-level functions that perform actual clause inlining:
//! applying definitions, substituting variables, and handling fresh variable
//! generation for capture avoidance.

use crate::{ChcExpr, ChcVar, ClauseBody, ClauseHead, HornClause, PredicateId};
use rustc_hash::{FxHashMap, FxHashSet};

use super::{fresh_var_name, ClauseInliner};

impl ClauseInliner {
    /// Apply definitions to inline predicates in a clause.
    ///
    /// This function recursively inlines all predicates that are in the defs map,
    /// including predicates introduced by other inlined definitions.
    pub(super) fn apply_defs(
        &self,
        clause: &HornClause,
        defs: &FxHashMap<PredicateId, HornClause>,
    ) -> HornClause {
        let mut pending_preds = clause.body.predicates.clone();
        let mut final_preds: Vec<(PredicateId, Vec<ChcExpr>)> = Vec::new();
        let mut constraints: Vec<ChcExpr> = clause.body.constraint.iter().cloned().collect();

        // Recursively inline predicates until no more can be inlined
        while let Some((pred_id, args)) = pending_preds.pop() {
            if let Some(def_clause) = defs.get(&pred_id) {
                // Inline this predicate - its body predicates go back into pending
                let (inlined_preds, inlined_constraint) = self.inline_clause(def_clause, &args);
                pending_preds.extend(inlined_preds);
                if let Some(c) = inlined_constraint {
                    constraints.push(c);
                }
            } else {
                // Keep this predicate as-is
                final_preds.push((pred_id, args));
            }
        }

        let final_constraint = if constraints.is_empty() {
            None
        } else {
            Some(
                constraints
                    .into_iter()
                    .reduce(ChcExpr::and)
                    .expect("constraints is non-empty after is_empty check"),
            )
        };

        HornClause::new(
            ClauseBody::new(final_preds, final_constraint),
            clause.head.clone(),
        )
    }

    /// Inline a clause definition with the given arguments.
    ///
    /// Given defining clause `H(x, y) ⇐ B₁(x), B₂(y), φ(x, y)` and call `H(a, b)`:
    /// 1. Create fresh variables x', y' to avoid capture
    /// 2. Add constraint `x' = a ∧ y' = b`
    /// 3. Return body `B₁(x'), B₂(y')` and constraint `φ(x', y') ∧ x' = a ∧ y' = b`
    pub(super) fn inline_clause(
        &self,
        def_clause: &HornClause,
        call_args: &[ChcExpr],
    ) -> (Vec<(PredicateId, Vec<ChcExpr>)>, Option<ChcExpr>) {
        // Get head arguments (formal parameters)
        let head_args: &[ChcExpr] = match &def_clause.head {
            ClauseHead::Predicate(_, args) => args,
            ClauseHead::False => return (Vec::new(), None),
        };

        // Optimization: when all head args are plain Vars and there are no
        // body-local variables, substitute directly (head_var → call_arg)
        // without introducing fresh variables. This avoids polluting PDR's
        // model with auxiliary variables that don't exist in the original problem.
        let all_head_vars = head_args.iter().all(|a| matches!(a, ChcExpr::Var(_)));
        let has_body_local_vars = if all_head_vars {
            let head_var_names: FxHashSet<&str> = head_args
                .iter()
                .filter_map(|a| match a {
                    ChcExpr::Var(v) => Some(v.name.as_str()),
                    _ => None,
                })
                .collect();
            let body_vars = def_clause.body.vars();
            body_vars
                .iter()
                .any(|v| !head_var_names.contains(v.name.as_str()))
        } else {
            true // Complex head args always need fresh variables
        };

        if all_head_vars && !has_body_local_vars {
            return self.inline_clause_direct(def_clause, head_args, call_args);
        }

        // Fallback: fresh variable approach for complex cases
        self.inline_clause_with_fresh_vars(def_clause, head_args, call_args)
    }

    /// Direct substitution: map each head Var directly to the corresponding call arg.
    /// Safe when there are no body-local variables to capture.
    fn inline_clause_direct(
        &self,
        def_clause: &HornClause,
        head_args: &[ChcExpr],
        call_args: &[ChcExpr],
    ) -> (Vec<(PredicateId, Vec<ChcExpr>)>, Option<ChcExpr>) {
        let subst: Vec<(ChcVar, ChcExpr)> = head_args
            .iter()
            .zip(call_args.iter())
            .filter_map(|(head_arg, call_arg)| {
                if let ChcExpr::Var(v) = head_arg {
                    Some((v.clone(), call_arg.clone()))
                } else {
                    None // Shouldn't happen (caller checks all_head_vars)
                }
            })
            .collect();

        let new_body_preds: Vec<(PredicateId, Vec<ChcExpr>)> = def_clause
            .body
            .predicates
            .iter()
            .map(|(pred_id, args)| {
                let new_args: Vec<ChcExpr> =
                    args.iter().map(|arg| arg.substitute(&subst)).collect();
                (*pred_id, new_args)
            })
            .collect();

        let subst_constraint = def_clause
            .body
            .constraint
            .as_ref()
            .map(|c| c.substitute(&subst));

        (new_body_preds, subst_constraint)
    }

    /// Fresh variable approach: create fresh variables and add equality constraints.
    /// Required when body-local variables exist or head args are complex expressions.
    fn inline_clause_with_fresh_vars(
        &self,
        def_clause: &HornClause,
        head_args: &[ChcExpr],
        call_args: &[ChcExpr],
    ) -> (Vec<(PredicateId, Vec<ChcExpr>)>, Option<ChcExpr>) {
        // Create fresh variables for each head argument position
        let fresh_vars: Vec<ChcVar> = head_args
            .iter()
            .enumerate()
            .map(|(i, arg)| {
                let sort = arg.sort();
                let prefix = if let ChcExpr::Var(v) = arg {
                    v.name.clone()
                } else {
                    format!("arg{i}")
                };
                ChcVar::new(fresh_var_name(&prefix), sort)
            })
            .collect();

        // Build substitution in two passes to handle shared variables correctly.
        // A variable like `A` can appear both as a plain Var head arg AND inside
        // an expression head arg (e.g., `f(1+A, A)`). Processing Var args first
        // establishes canonical fresh names, then expression args reuse them (#5523).
        let mut subst: Vec<(ChcVar, ChcExpr)> = Vec::new();
        let mut expr_equalities: Vec<ChcExpr> = Vec::new();

        // Pass 1: Var head args → canonical substitutions.
        for (i, arg) in head_args.iter().enumerate() {
            if let ChcExpr::Var(v) = arg {
                if !subst.iter().any(|(sv, _)| sv.name == v.name) {
                    subst.push((v.clone(), ChcExpr::var(fresh_vars[i].clone())));
                }
            }
        }

        // Pass 2: Expression head args → freshen remaining constituent vars
        // and build equality constraints. Variables already in subst (from Var
        // head args) are reused, keeping a single canonical fresh name.
        for (i, arg) in head_args.iter().enumerate() {
            if !matches!(arg, ChcExpr::Var(_)) {
                // #2660: Expression head arg — freshen constituent vars to
                // avoid capture, then add equality fresh_pos = expr[freshened].
                for v in arg.vars() {
                    if !subst.iter().any(|(sv, _)| sv.name == v.name) {
                        let fresh = ChcVar::new(fresh_var_name(&v.name), v.sort.clone());
                        subst.push((v, ChcExpr::var(fresh)));
                    }
                }
                // Apply freshening to the expression using all substitutions
                let freshened_expr = arg.substitute(&subst);
                expr_equalities.push(ChcExpr::eq(
                    ChcExpr::var(fresh_vars[i].clone()),
                    freshened_expr,
                ));
            }
        }

        // Freshen body-local variables to avoid capture with the calling clause's
        // variables (#5523). A body-local variable is any variable in the body
        // (predicates or constraint) that was not already freshened above (i.e.,
        // not a head variable or expression-head constituent).
        let already_freshened: FxHashSet<String> =
            subst.iter().map(|(v, _)| v.name.clone()).collect();
        for v in def_clause.body.vars() {
            if !already_freshened.contains(&v.name) {
                let fresh = ChcVar::new(fresh_var_name(&v.name), v.sort.clone());
                subst.push((v, ChcExpr::var(fresh)));
            }
        }

        // Apply substitution to body predicates
        let new_body_preds: Vec<(PredicateId, Vec<ChcExpr>)> = def_clause
            .body
            .predicates
            .iter()
            .map(|(pred_id, args)| {
                let new_args: Vec<ChcExpr> =
                    args.iter().map(|arg| arg.substitute(&subst)).collect();
                (*pred_id, new_args)
            })
            .collect();

        // Apply substitution to constraint
        let subst_constraint = def_clause
            .body
            .constraint
            .as_ref()
            .map(|c| c.substitute(&subst));

        // Build equalities: canonical_fresh = call_arg.
        // SOUNDNESS FIX (#7897): When a Var appears at multiple head positions
        // (e.g., `Post(1, v, v)`), each position gets its own fresh_vars[i],
        // but the substitution maps `v` to only ONE canonical fresh variable
        // (from Pass 1). We must use the canonical variable for the equality,
        // not the position-specific one, so that call_args at shared positions
        // are correctly linked through the same fresh variable.
        let arg_equalities: Vec<ChcExpr> = head_args
            .iter()
            .enumerate()
            .zip(call_args.iter())
            .map(|((i, head_arg), actual)| {
                let canonical_fresh = if let ChcExpr::Var(v) = head_arg {
                    // Look up the canonical fresh variable from subst
                    subst
                        .iter()
                        .find(|(sv, _)| sv.name == v.name)
                        .map(|(_, expr)| expr.clone())
                        .unwrap_or_else(|| ChcExpr::var(fresh_vars[i].clone()))
                } else {
                    ChcExpr::var(fresh_vars[i].clone())
                };
                ChcExpr::eq(canonical_fresh, actual.clone())
            })
            .collect();

        // Combine all constraints: arg equalities + expression head equalities + original
        let all_constraints: Vec<ChcExpr> = arg_equalities
            .into_iter()
            .chain(expr_equalities)
            .chain(subst_constraint)
            .collect();

        let final_constraint = if all_constraints.is_empty() {
            None
        } else {
            Some(
                all_constraints
                    .into_iter()
                    .reduce(ChcExpr::and)
                    .expect("all_constraints is non-empty after is_empty check"),
            )
        };

        (new_body_preds, final_constraint)
    }

    /// Compute the size of an expression (number of nodes).
    pub(super) fn expr_size(expr: &ChcExpr) -> usize {
        crate::expr::maybe_grow_expr_stack(|| match expr {
            ChcExpr::Bool(_)
            | ChcExpr::Int(_)
            | ChcExpr::Real(_, _)
            | ChcExpr::BitVec(_, _)
            | ChcExpr::Var(_) => 1,
            ChcExpr::Op(_, args) => 1 + args.iter().map(|a| Self::expr_size(a)).sum::<usize>(),
            ChcExpr::PredicateApp(_, _, args) => {
                1 + args.iter().map(|a| Self::expr_size(a)).sum::<usize>()
            }
            ChcExpr::ConstArrayMarker(_) => 1,
            ChcExpr::IsTesterMarker(_) => 1,
            ChcExpr::FuncApp(_, _, args) => {
                1 + args.iter().map(|a| Self::expr_size(a)).sum::<usize>()
            }
            ChcExpr::ConstArray(_ks, val) => 1 + Self::expr_size(val),
        })
    }

    /// Normalize a defining clause so all head arguments are plain variables.
    ///
    /// For `P(x+1, y) <= C(x, y)`, rewrites to
    /// `P(f0, f1) <= (f0 = x'+1) ∧ (f1 = y') ∧ C(x', y')`
    /// so `synthesize_interpretation` can extract formal parameters. (#5295)
    pub(super) fn normalize_head_for_back_translation(clause: &HornClause) -> HornClause {
        let head_args = match &clause.head {
            ClauseHead::Predicate(_, args) => args,
            ClauseHead::False => return clause.clone(),
        };

        let needs_normalization = head_args.iter().any(|a| !matches!(a, ChcExpr::Var(_)));
        if !needs_normalization {
            return clause.clone();
        }

        let pred_id = clause.head.predicate_id().expect("checked above");
        let (fresh_vars, equalities, subst) = Self::build_head_normalization(head_args);

        let new_body_preds: Vec<(PredicateId, Vec<ChcExpr>)> = clause
            .body
            .predicates
            .iter()
            .map(|(pid, args)| {
                let new_args = args.iter().map(|a| a.substitute(&subst)).collect();
                (*pid, new_args)
            })
            .collect();

        let subst_constraint = clause
            .body
            .constraint
            .as_ref()
            .map(|c| c.substitute(&subst));
        let mut all_constraints: Vec<ChcExpr> = equalities;
        if let Some(c) = subst_constraint {
            all_constraints.push(c);
        }

        let final_constraint = all_constraints.into_iter().reduce(ChcExpr::and);

        let new_head = ClauseHead::Predicate(
            pred_id,
            fresh_vars.iter().map(|v| ChcExpr::var(v.clone())).collect(),
        );

        HornClause::new(ClauseBody::new(new_body_preds, final_constraint), new_head)
    }

    /// Build fresh variables and substitution for normalizing complex head args.
    ///
    /// Returns `(fresh_vars, equalities, substitution)` where:
    /// - `fresh_vars[i]` is a fresh variable replacing `head_args[i]`
    /// - `equalities` are `fresh_i = expr_i` for non-Var head args
    /// - `substitution` maps original vars to fresh vars
    fn build_head_normalization(
        head_args: &[ChcExpr],
    ) -> (Vec<ChcVar>, Vec<ChcExpr>, Vec<(ChcVar, ChcExpr)>) {
        let fresh_vars: Vec<ChcVar> = head_args
            .iter()
            .enumerate()
            .map(|(i, arg)| {
                let sort = arg.sort();
                let prefix = if let ChcExpr::Var(v) = arg {
                    v.name.clone()
                } else {
                    format!("bt_arg{i}")
                };
                ChcVar::new(fresh_var_name(&prefix), sort)
            })
            .collect();

        let mut equalities: Vec<ChcExpr> = Vec::new();
        let mut subst: Vec<(ChcVar, ChcExpr)> = Vec::new();
        for (i, arg) in head_args.iter().enumerate() {
            match arg {
                ChcExpr::Var(v) => {
                    subst.push((v.clone(), ChcExpr::var(fresh_vars[i].clone())));
                }
                expr => {
                    for v in expr.vars() {
                        if !subst.iter().any(|(sv, _)| sv.name == v.name) {
                            let fresh = ChcVar::new(fresh_var_name(&v.name), v.sort.clone());
                            subst.push((v, ChcExpr::var(fresh)));
                        }
                    }
                    let freshened_expr = expr.substitute(&subst);
                    equalities.push(ChcExpr::eq(
                        ChcExpr::var(fresh_vars[i].clone()),
                        freshened_expr,
                    ));
                }
            }
        }
        (fresh_vars, equalities, subst)
    }
}
