// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Back-translation for clause inlining.
//!
//! Synthesizes interpretations for predicates that were removed by inlining,
//! reconstructing their definitions from the original clause bodies.

use crate::{
    mbp::Mbp,
    smt::{SmtContext, SmtResult},
    ChcExpr, ChcOp, ChcSort, ChcVar, ClauseHead, HornClause, PredicateId, PredicateInterpretation,
};
use rustc_hash::{FxHashMap, FxHashSet};
use std::sync::Arc;

use super::super::{BackTranslator, InvalidityWitness, ValidityWitness};

/// Cap AllSAT+MBP existential projection during back-translation.
///
/// If the cap is hit before the exact projection is covered, synthesis fails
/// closed and portfolio validation rejects the Safe result.
const MAX_EXISTENTIAL_QE_ITERS: usize = 100;

/// Back-translator that synthesizes interpretations for predicates removed by inlining.
///
/// When ClauseInliner eliminates a predicate P with defining clause
/// `P(x1,...,xn) ⇐ C(x1,...,xn) ∧ Q1(a1) ∧ ...`, the solver's model
/// will not contain an interpretation for P. This translator reconstructs
/// P's interpretation from its defining clause body so that the model
/// validates against the original (pre-inlining) problem.
pub(super) struct InliningBackTranslator {
    /// Defining clauses for each inlined predicate, in inlining order.
    /// Later entries may have body predicates already substituted from earlier rounds.
    /// PredicateIds are from the **original** (pre-compaction) problem.
    pub(super) inlined_defs: Vec<(PredicateId, HornClause)>,
    /// Mapping from compacted (engine) predicate IDs to original predicate IDs.
    /// Empty if no compaction was performed.
    pub(super) new_to_old: FxHashMap<PredicateId, PredicateId>,
}

impl InliningBackTranslator {
    fn vars_are_closed(formula: &ChcExpr, allowed: &FxHashSet<ChcVar>) -> bool {
        formula.vars().into_iter().all(|var| allowed.contains(&var))
    }

    /// Substitute Int variables pinned by matching lower/upper constant bounds.
    ///
    /// This is especially important for inlined loop-exit clauses where a guard
    /// like `B >= 16` combines with the body invariant `B <= 16`, making the
    /// existential witness effectively constant before projection.
    fn propagate_tight_bound_constants(formula: &ChcExpr) -> ChcExpr {
        let conjuncts = formula.collect_conjuncts();
        let mut lower: FxHashMap<String, i64> = FxHashMap::default();
        let mut upper: FxHashMap<String, i64> = FxHashMap::default();

        for conj in &conjuncts {
            if let ChcExpr::Op(ChcOp::Ge, args) = conj {
                if args.len() == 2 {
                    if let (ChcExpr::Var(v), ChcExpr::Int(c)) = (args[0].as_ref(), args[1].as_ref())
                    {
                        if matches!(v.sort, ChcSort::Int) {
                            lower
                                .entry(v.name.clone())
                                .and_modify(|old| *old = (*old).max(*c))
                                .or_insert(*c);
                        }
                    }
                }
            }
            if let ChcExpr::Op(ChcOp::Le, args) = conj {
                if args.len() == 2 {
                    if let (ChcExpr::Var(v), ChcExpr::Int(c)) = (args[0].as_ref(), args[1].as_ref())
                    {
                        if matches!(v.sort, ChcSort::Int) {
                            upper
                                .entry(v.name.clone())
                                .and_modify(|old| *old = (*old).min(*c))
                                .or_insert(*c);
                        }
                    }
                }
            }
        }

        let subst: Vec<(ChcVar, ChcExpr)> = lower
            .iter()
            .filter_map(|(name, lb)| {
                (upper.get(name) == Some(lb))
                    .then(|| (ChcVar::new(name.clone(), ChcSort::Int), ChcExpr::Int(*lb)))
            })
            .collect();

        if subst.is_empty() {
            return formula.clone();
        }

        let mut equalities: Vec<ChcExpr> = subst
            .iter()
            .map(|(var, val)| ChcExpr::eq(ChcExpr::var(var.clone()), val.clone()))
            .collect();
        let simplified = formula.substitute(&subst).simplify_constants();
        if matches!(simplified, ChcExpr::Bool(true)) {
            ChcExpr::and_all(equalities)
        } else {
            equalities.push(simplified);
            ChcExpr::and_all(equalities)
        }
    }

    fn solve_local_from_head_equality(
        equality: &ChcExpr,
        keep_names: &FxHashSet<&str>,
    ) -> Option<(ChcVar, ChcExpr)> {
        fn local_affine_rhs(expr: &ChcExpr) -> Option<(ChcVar, i64, bool)> {
            match expr {
                ChcExpr::Var(v) if matches!(v.sort, ChcSort::Int) => Some((v.clone(), 0, true)),
                ChcExpr::Op(ChcOp::Add, args) if args.len() == 2 => {
                    match (args[0].as_ref(), args[1].as_ref()) {
                        (ChcExpr::Var(v), ChcExpr::Int(c)) if matches!(v.sort, ChcSort::Int) => {
                            Some((v.clone(), *c, true))
                        }
                        (ChcExpr::Int(c), ChcExpr::Var(v)) if matches!(v.sort, ChcSort::Int) => {
                            Some((v.clone(), *c, true))
                        }
                        _ => None,
                    }
                }
                ChcExpr::Op(ChcOp::Sub, args) if args.len() == 2 => {
                    match (args[0].as_ref(), args[1].as_ref()) {
                        (ChcExpr::Var(v), ChcExpr::Int(c)) if matches!(v.sort, ChcSort::Int) => {
                            Some((v.clone(), *c, true))
                        }
                        (ChcExpr::Int(c), ChcExpr::Var(v)) if matches!(v.sort, ChcSort::Int) => {
                            Some((v.clone(), *c, false))
                        }
                        _ => None,
                    }
                }
                _ => None,
            }
        }

        let ChcExpr::Op(ChcOp::Eq, args) = equality else {
            return None;
        };
        if args.len() != 2 {
            return None;
        }

        let (keep_var, other_side) = match (args[0].as_ref(), args[1].as_ref()) {
            (ChcExpr::Var(v), rhs) if keep_names.contains(v.name.as_str()) => (v.clone(), rhs),
            (lhs, ChcExpr::Var(v)) if keep_names.contains(v.name.as_str()) => (v.clone(), lhs),
            _ => return None,
        };

        let (local_var, constant, positive_local) = local_affine_rhs(other_side)?;
        if keep_names.contains(local_var.name.as_str()) {
            return None;
        }

        let rhs = if positive_local {
            if constant == 0 {
                ChcExpr::var(keep_var)
            } else if matches!(other_side, ChcExpr::Op(ChcOp::Sub, _)) {
                ChcExpr::add(ChcExpr::var(keep_var), ChcExpr::int(constant))
            } else {
                ChcExpr::sub(ChcExpr::var(keep_var), ChcExpr::int(constant))
            }
        } else {
            ChcExpr::sub(ChcExpr::int(constant), ChcExpr::var(keep_var))
        };

        Some((local_var, rhs))
    }

    fn substitute_head_affine_locals(formula: &ChcExpr, keep_vars: &[ChcVar]) -> ChcExpr {
        let keep_names: FxHashSet<&str> = keep_vars.iter().map(|v| v.name.as_str()).collect();
        let mut current = Self::propagate_tight_bound_constants(formula).simplify_constants();

        loop {
            let subst = current
                .collect_conjuncts()
                .into_iter()
                .find_map(|conj| Self::solve_local_from_head_equality(&conj, &keep_names));
            let Some((local, replacement)) = subst else {
                break;
            };
            current = current
                .substitute(&[(local, replacement)])
                .simplify_constants();
        }

        current
    }

    fn propagate_non_keep_constants(formula: &ChcExpr, keep_vars: &[ChcVar]) -> ChcExpr {
        let keep_names: FxHashSet<&str> = keep_vars.iter().map(|v| v.name.as_str()).collect();
        let subst: Vec<(ChcVar, ChcExpr)> = formula
            .collect_conjuncts()
            .into_iter()
            .filter_map(|conj| {
                let ChcExpr::Op(ChcOp::Eq, args) = conj else {
                    return None;
                };
                if args.len() != 2 {
                    return None;
                }
                match (args[0].as_ref(), args[1].as_ref()) {
                    (ChcExpr::Var(v), ChcExpr::Int(c)) | (ChcExpr::Int(c), ChcExpr::Var(v))
                        if !keep_names.contains(v.name.as_str())
                            && matches!(v.sort, ChcSort::Int) =>
                    {
                        Some((v.clone(), ChcExpr::Int(*c)))
                    }
                    _ => None,
                }
            })
            .collect();

        if subst.is_empty() {
            formula.clone()
        } else {
            formula.substitute(&subst).simplify_constants()
        }
    }

    fn normalize_shifted_keep_constraints(formula: &ChcExpr, keep_vars: &[ChcVar]) -> ChcExpr {
        let keep_names: FxHashSet<&str> = keep_vars.iter().map(|v| v.name.as_str()).collect();
        let rewrite = |conj: &ChcExpr| -> ChcExpr {
            match conj {
                ChcExpr::Op(ChcOp::Le, args) if args.len() == 2 => {
                    match (args[0].as_ref(), args[1].as_ref()) {
                        (ChcExpr::Op(ChcOp::Sub, sub_args), ChcExpr::Int(k))
                            if sub_args.len() == 2 =>
                        {
                            if let (ChcExpr::Var(v), ChcExpr::Int(c)) =
                                (sub_args[0].as_ref(), sub_args[1].as_ref())
                            {
                                if keep_names.contains(v.name.as_str()) {
                                    return ChcExpr::le(
                                        ChcExpr::var(v.clone()),
                                        ChcExpr::int(k.saturating_add(*c)),
                                    );
                                }
                            }
                        }
                        _ => {}
                    }
                    conj.clone()
                }
                ChcExpr::Op(ChcOp::Ge, args) if args.len() == 2 => {
                    match (args[0].as_ref(), args[1].as_ref()) {
                        (ChcExpr::Op(ChcOp::Sub, sub_args), ChcExpr::Int(k))
                            if sub_args.len() == 2 =>
                        {
                            if let (ChcExpr::Var(v), ChcExpr::Int(c)) =
                                (sub_args[0].as_ref(), sub_args[1].as_ref())
                            {
                                if keep_names.contains(v.name.as_str()) {
                                    return ChcExpr::ge(
                                        ChcExpr::var(v.clone()),
                                        ChcExpr::int(k.saturating_add(*c)),
                                    );
                                }
                            }
                        }
                        _ => {}
                    }
                    conj.clone()
                }
                ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => {
                    if let ChcExpr::Op(ChcOp::Le, inner) = args[0].as_ref() {
                        if inner.len() == 2 {
                            match (inner[0].as_ref(), inner[1].as_ref()) {
                                (ChcExpr::Int(k), ChcExpr::Op(ChcOp::Sub, sub_args))
                                    if sub_args.len() == 2 =>
                                {
                                    if let (ChcExpr::Var(v), ChcExpr::Int(c)) =
                                        (sub_args[0].as_ref(), sub_args[1].as_ref())
                                    {
                                        if keep_names.contains(v.name.as_str()) {
                                            return ChcExpr::le(
                                                ChcExpr::var(v.clone()),
                                                ChcExpr::int(
                                                    k.saturating_add(*c).saturating_sub(1),
                                                ),
                                            );
                                        }
                                    }
                                }
                                (ChcExpr::Int(k), ChcExpr::Var(v))
                                    if keep_names.contains(v.name.as_str()) =>
                                {
                                    return ChcExpr::le(
                                        ChcExpr::var(v.clone()),
                                        ChcExpr::int(k.saturating_sub(1)),
                                    );
                                }
                                _ => {}
                            }
                        }
                    }
                    conj.clone()
                }
                ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                    let rewrite_mod = |expr: &ChcExpr| -> Option<ChcExpr> {
                        let ChcExpr::Op(ChcOp::Mod, mod_args) = expr else {
                            return None;
                        };
                        if mod_args.len() != 2 {
                            return None;
                        }
                        let ChcExpr::Int(modulus) = mod_args[1].as_ref() else {
                            return None;
                        };
                        match mod_args[0].as_ref() {
                            ChcExpr::Op(ChcOp::Sub, sub_args) if sub_args.len() == 2 => {
                                if let (ChcExpr::Var(v), ChcExpr::Int(c)) =
                                    (sub_args[0].as_ref(), sub_args[1].as_ref())
                                {
                                    if keep_names.contains(v.name.as_str())
                                        && c.rem_euclid(*modulus) == 0
                                    {
                                        return Some(ChcExpr::mod_op(
                                            ChcExpr::var(v.clone()),
                                            ChcExpr::int(*modulus),
                                        ));
                                    }
                                }
                                None
                            }
                            _ => None,
                        }
                    };

                    match (rewrite_mod(args[0].as_ref()), rewrite_mod(args[1].as_ref())) {
                        (Some(lhs), _) => ChcExpr::eq(lhs, args[1].as_ref().clone()),
                        (_, Some(rhs)) => ChcExpr::eq(args[0].as_ref().clone(), rhs),
                        _ => conj.clone(),
                    }
                }
                _ => conj.clone(),
            }
        };

        if let ChcExpr::Op(ChcOp::And, _) = formula {
            ChcExpr::and_all(
                formula
                    .collect_conjuncts()
                    .into_iter()
                    .map(|conj| rewrite(&conj)),
            )
            .simplify_constants()
        } else {
            rewrite(formula).simplify_constants()
        }
    }

    fn compress_closed_keep_constraints(formula: &ChcExpr, keep_vars: &[ChcVar]) -> ChcExpr {
        let [keep] = keep_vars else {
            return formula.clone();
        };
        if !matches!(keep.sort, ChcSort::Int) {
            return formula.clone();
        }

        let mut lower: Option<i64> = None;
        let mut upper: Option<i64> = None;
        let mut best_mod_zero: Option<i64> = None;
        let mut rest = Vec::new();

        for conj in formula.collect_conjuncts() {
            match &conj {
                ChcExpr::Op(ChcOp::Ge, args)
                    if args.len() == 2
                        && matches!(args[0].as_ref(), ChcExpr::Var(v) if v == keep)
                        && matches!(args[1].as_ref(), ChcExpr::Int(_)) =>
                {
                    if let ChcExpr::Int(c) = args[1].as_ref() {
                        lower = Some(lower.map_or(*c, |old| old.max(*c)));
                    }
                }
                ChcExpr::Op(ChcOp::Le, args)
                    if args.len() == 2
                        && matches!(args[0].as_ref(), ChcExpr::Var(v) if v == keep)
                        && matches!(args[1].as_ref(), ChcExpr::Int(_)) =>
                {
                    if let ChcExpr::Int(c) = args[1].as_ref() {
                        upper = Some(upper.map_or(*c, |old| old.min(*c)));
                    }
                }
                ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                    let matches_mod_zero = |lhs: &ChcExpr, rhs: &ChcExpr| -> Option<i64> {
                        let ChcExpr::Op(ChcOp::Mod, mod_args) = lhs else {
                            return None;
                        };
                        if mod_args.len() != 2 {
                            return None;
                        }
                        match (mod_args[0].as_ref(), mod_args[1].as_ref(), rhs) {
                            (ChcExpr::Var(v), ChcExpr::Int(m), ChcExpr::Int(0)) if v == keep => {
                                Some(*m)
                            }
                            _ => None,
                        }
                    };
                    if let Some(m) = matches_mod_zero(args[0].as_ref(), args[1].as_ref())
                        .or_else(|| matches_mod_zero(args[1].as_ref(), args[0].as_ref()))
                    {
                        best_mod_zero = Some(best_mod_zero.map_or(m, |old| old.max(m)));
                    } else {
                        rest.push(conj);
                    }
                }
                _ => rest.push(conj),
            }
        }

        if let Some(lb) = lower {
            rest.push(ChcExpr::ge(ChcExpr::var(keep.clone()), ChcExpr::int(lb)));
        }
        if let Some(ub) = upper {
            rest.push(ChcExpr::le(ChcExpr::var(keep.clone()), ChcExpr::int(ub)));
        }
        if let Some(m) = best_mod_zero {
            rest.push(ChcExpr::eq(
                ChcExpr::mod_op(ChcExpr::var(keep.clone()), ChcExpr::int(m)),
                ChcExpr::int(0),
            ));
        }

        ChcExpr::and_all(rest).simplify_constants()
    }

    /// Existentially eliminate clause-local variables from a synthesized
    /// interpretation, keeping only the predicate's formal parameters.
    ///
    /// Uses AllSAT+MBP enumeration to build a candidate projection and then
    /// validates completeness with `formula ∧ ¬projection`. If any models remain,
    /// the projection is incomplete and we fail closed.
    fn existentially_project_to_head_vars(
        formula: &ChcExpr,
        keep_vars: &[ChcVar],
    ) -> Option<ChcExpr> {
        let formula = Self::propagate_non_keep_constants(
            &Self::substitute_head_affine_locals(formula, keep_vars),
            keep_vars,
        );
        let formula = Self::normalize_shifted_keep_constraints(&formula, keep_vars);
        let formula = Self::compress_closed_keep_constraints(&formula, keep_vars);
        let keep_set: FxHashSet<ChcVar> = keep_vars.iter().cloned().collect();
        if Self::vars_are_closed(&formula, &keep_set) {
            return Some(formula);
        }

        let mbp = Mbp::new();
        let mut smt = SmtContext::new();
        let mut projections = Vec::new();
        let mut blocking = formula.clone();

        for _ in 0..MAX_EXISTENTIAL_QE_ITERS {
            match smt.check_sat_with_executor_fallback(&blocking) {
                SmtResult::Sat(model) => {
                    let projection = mbp
                        .keep_only(&formula, keep_vars, &model)
                        .simplify_constants();
                    if !Self::vars_are_closed(&projection, &keep_set) {
                        return None;
                    }
                    projections.push(projection.clone());
                    blocking =
                        ChcExpr::and(blocking, ChcExpr::not(projection)).simplify_constants();
                }
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                    break
                }
                SmtResult::Unknown => {
                    if projections.is_empty() {
                        return None;
                    }
                    break;
                }
            }
        }

        let projected = if projections.is_empty() {
            ChcExpr::Bool(false)
        } else {
            ChcExpr::or_all(projections).simplify_constants()
        };

        if !Self::vars_are_closed(&projected, &keep_set) {
            return None;
        }

        let mut exactness = SmtContext::new();
        let missing_region =
            ChcExpr::and(formula.clone(), ChcExpr::not(projected.clone())).simplify_constants();
        match exactness.check_sat_with_executor_fallback(&missing_region) {
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {}
            SmtResult::Sat(_) => return None,
            SmtResult::Unknown => {}
        }

        Some(projected)
    }

    fn close_synthesized_interpretation(
        interp: PredicateInterpretation,
    ) -> Option<PredicateInterpretation> {
        let formula = Self::existentially_project_to_head_vars(&interp.formula, &interp.vars)?;
        Some(PredicateInterpretation::new(interp.vars, formula))
    }

    /// Synthesize interpretation for an inlined predicate from its defining clause.
    ///
    /// For a fact clause `P(x1,...,xn) ⇐ C`: P's interpretation is C with
    /// the head variables as formal parameters.
    ///
    /// For a clause with body predicates `P(x1,...,xn) ⇐ C ∧ Q(a1,...,am)`:
    /// P's interpretation is C ∧ Q_interp(a1,...,am) where Q_interp substitutes
    /// Q's model interpretation applied to the body predicate's arguments.
    fn synthesize_interpretation(
        clause: &HornClause,
        model: &ValidityWitness,
    ) -> Option<PredicateInterpretation> {
        // Extract formal parameter variables from the head
        let head_vars = match &clause.head {
            ClauseHead::Predicate(_, args) => {
                let mut vars = Vec::new();
                for arg in args {
                    if let ChcExpr::Var(v) = arg {
                        vars.push(v.clone());
                    } else {
                        // After normalize_head_for_back_translation (#5295), all
                        // head args should be plain variables. This is a safety net.
                        debug_assert!(
                            false,
                            "BUG #5295: defining clause should be normalized before \
                             storing in inlined_defs — got complex head arg: {arg:?}"
                        );
                        return None;
                    }
                }
                vars
            }
            ClauseHead::False => return None,
        };

        // Start with the body constraint
        let constraint = clause
            .body
            .constraint
            .clone()
            .unwrap_or(ChcExpr::Bool(true));

        if clause.body.predicates.is_empty() {
            // Fact clause: interpretation is just the body constraint
            return Self::close_synthesized_interpretation(PredicateInterpretation::new(
                head_vars, constraint,
            ));
        }

        // Clause has body predicates — substitute each with its model interpretation
        let mut conjuncts = vec![Arc::new(constraint)];
        for (body_pred_id, body_args) in &clause.body.predicates {
            let Some(body_interp) = model.get(body_pred_id) else {
                // Body predicate has no interpretation — can't synthesize
                return None;
            };
            // Build substitution: body_interp.vars[i] → body_args[i]
            let subst: Vec<(ChcVar, ChcExpr)> = body_interp
                .vars
                .iter()
                .zip(body_args.iter())
                .map(|(formal, actual)| (formal.clone(), actual.clone()))
                .collect();
            let applied = body_interp.formula.substitute(&subst);
            conjuncts.push(Arc::new(applied));
        }

        let formula = if conjuncts.len() == 1 {
            Arc::unwrap_or_clone(conjuncts.pop().unwrap())
        } else {
            ChcExpr::Op(ChcOp::And, conjuncts)
        };
        Self::close_synthesized_interpretation(PredicateInterpretation::new(head_vars, formula))
    }

    /// Group inlined definitions by predicate ID, preserving insertion order.
    fn group_defs_by_predicate(
        inlined_defs: &[(PredicateId, HornClause)],
    ) -> Vec<(PredicateId, Vec<&HornClause>)> {
        let mut grouped: Vec<(PredicateId, Vec<&HornClause>)> = Vec::new();
        let mut group_idx: FxHashMap<PredicateId, usize> = FxHashMap::default();
        for (pred_id, defining_clause) in inlined_defs {
            if let Some(&idx) = group_idx.get(pred_id) {
                grouped[idx].1.push(defining_clause);
            } else {
                let idx = grouped.len();
                group_idx.insert(*pred_id, idx);
                grouped.push((*pred_id, vec![defining_clause]));
            }
        }
        grouped
    }

    /// Synthesize a disjunctive interpretation for a multi-definition predicate.
    ///
    /// Returns `OR(body1, body2, ...)` where each body_i comes from one defining
    /// clause. All definitions share the same formal parameters; we rename vars
    /// to match the first definition's variable names.
    fn synthesize_disjunctive(
        clauses: &[&HornClause],
        model: &ValidityWitness,
    ) -> Option<PredicateInterpretation> {
        let mut disjuncts: Vec<Arc<ChcExpr>> = Vec::new();
        let mut shared_vars: Option<Vec<ChcVar>> = None;
        for (def_idx, clause) in clauses.iter().enumerate() {
            let interp = Self::synthesize_interpretation(clause, model)?;
            if shared_vars.is_none() {
                shared_vars = Some(interp.vars.clone());
            }
            // Rename interp vars to match the first definition's vars.
            let formula = if let Some(ref sv) = shared_vars {
                let head_subst: Vec<(ChcVar, ChcExpr)> = interp
                    .vars
                    .iter()
                    .zip(sv.iter())
                    .filter(|(a, b)| a.name != b.name)
                    .map(|(from, to)| (from.clone(), ChcExpr::var(to.clone())))
                    .collect();
                if head_subst.is_empty() {
                    interp.formula
                } else {
                    // Alpha-rename free body vars that collide with target
                    // shared_vars names before renaming head vars.
                    let head_var_names: FxHashSet<&str> =
                        interp.vars.iter().map(|v| v.name.as_str()).collect();
                    let target_names: FxHashSet<&str> =
                        sv.iter().map(|v| v.name.as_str()).collect();
                    let mut alpha_subst: Vec<(ChcVar, ChcExpr)> = Vec::new();
                    for fv in interp.formula.vars() {
                        if head_var_names.contains(fv.name.as_str()) {
                            continue;
                        }
                        if target_names.contains(fv.name.as_str()) {
                            let fresh =
                                ChcVar::new(format!("_bt{}_{}", def_idx, fv.name), fv.sort.clone());
                            alpha_subst.push((fv, ChcExpr::var(fresh)));
                        }
                    }
                    let formula = if alpha_subst.is_empty() {
                        interp.formula
                    } else {
                        interp.formula.substitute(&alpha_subst)
                    };
                    formula.substitute(&head_subst)
                }
            } else {
                interp.formula
            };
            disjuncts.push(Arc::new(formula));
        }
        let vars = shared_vars?;
        let formula = if disjuncts.len() == 1 {
            Arc::unwrap_or_clone(disjuncts.pop().unwrap())
        } else {
            ChcExpr::Op(ChcOp::Or, disjuncts)
        };
        let allowed: FxHashSet<ChcVar> = vars.iter().cloned().collect();
        if !Self::vars_are_closed(&formula, &allowed) {
            return None;
        }
        Some(PredicateInterpretation::new(vars, formula))
    }

    /// Remap witness PredicateIds from compacted space to original space.
    fn remap_witness(
        witness: ValidityWitness,
        new_to_old: &FxHashMap<PredicateId, PredicateId>,
    ) -> ValidityWitness {
        let mut remapped = ValidityWitness::new();
        remapped.verification_method = witness.verification_method;
        for (new_id, interp) in witness.iter() {
            let old_id = new_to_old.get(new_id).copied().unwrap_or(*new_id);
            remapped.set(old_id, interp.clone());
        }
        remapped
    }
}

impl BackTranslator for InliningBackTranslator {
    fn translate_validity(&self, mut witness: ValidityWitness) -> ValidityWitness {
        // Step 1: Remap engine witness from compacted IDs to original IDs.
        // The engine produced interpretations keyed by new (compacted) PredicateIds;
        // we need them keyed by original IDs for back-translation to work.
        if !self.new_to_old.is_empty() {
            witness = Self::remap_witness(witness, &self.new_to_old);
        }

        // Step 2: Synthesize interpretations for inlined predicates.
        // inlined_defs uses original PredicateIds, so after remapping the
        // engine witness, all IDs are in the original space.
        let grouped = Self::group_defs_by_predicate(&self.inlined_defs);
        let mut changed = true;
        while changed {
            changed = false;
            for (pred_id, clauses) in &grouped {
                if witness.get(pred_id).is_some() {
                    continue;
                }

                let synthesized = if clauses.len() == 1 {
                    Self::synthesize_interpretation(clauses[0], &witness)
                } else {
                    Self::synthesize_disjunctive(clauses, &witness)
                };

                if let Some(interp) = synthesized {
                    witness.set(*pred_id, interp);
                    changed = true;
                }
            }
        }
        witness
    }

    fn translate_invalidity(&self, witness: InvalidityWitness) -> InvalidityWitness {
        // Counterexamples don't need predicate interpretation synthesis
        witness
    }
}
