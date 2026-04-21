// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared inductive-blocking checks for lemma admission.
//!
//! This keeps the public `PdrSolver` method surface in `inductiveness/mod.rs`
//! while isolating the cached wrapper, uncached transition checks, and
//! hyperedge incremental helper into one focused module.

use super::super::PdrSolver;
use crate::smt::SmtResult;
use crate::{ChcExpr, PredicateId};

pub(super) fn check_hyperedge_inductive_query(
    solver: &mut PdrSolver,
    predicate: PredicateId,
    clause_index: usize,
    hyperedge_query: &super::super::hyperedge::HyperedgeInductiveQuery,
) -> SmtResult {
    if super::super::INCREMENTAL_PDR_ENABLED && solver.problem_is_integer_arithmetic {
        let seg_key = super::super::prop_solver::SegmentKey::Inductiveness { clause_index };
        let prop = super::super::core::ensure_prop_solver_split(
            &mut solver.prop_solvers,
            &solver.frames,
            predicate,
        );
        prop.register_segment(seg_key, &hyperedge_query.clause_constraint);
        let check_timeout = solver
            .smt
            .current_timeout()
            .or(Some(std::time::Duration::from_secs(2)));
        let assumptions = [
            hyperedge_query.candidate_on_body.clone(),
            hyperedge_query.violated_on_head.clone(),
        ];
        match prop.check_inductiveness(
            solver.frames.len(),
            clause_index,
            &assumptions,
            check_timeout,
            None,
        ) {
            crate::smt::IncrementalCheckResult::Unsat => SmtResult::Unsat,
            crate::smt::IncrementalCheckResult::Sat(model) => SmtResult::Sat(model),
            crate::smt::IncrementalCheckResult::Unknown
            | crate::smt::IncrementalCheckResult::RetryFresh(_) => SmtResult::Unknown,
        }
    } else {
        solver.smt.check_sat(&hyperedge_query.query)
    }
}

pub(super) fn is_inductive_blocking(
    solver: &mut PdrSolver,
    blocking_formula: &ChcExpr,
    predicate: PredicateId,
    level: usize,
) -> bool {
    // Cache lookup: (predicate, level, formula_hash) -> (frame_lemma_count, result)
    // Level 0 results are stable (init facts don't change).
    // Level > 0 results are valid if frame hasn't grown (or if result was true).
    let cache_key = (predicate, level, blocking_formula.structural_hash());
    let current_frame_count = if level > 0 && level <= solver.frames.len() {
        solver.frames[level - 1].lemmas.len()
    } else {
        0
    };

    if let Some((cached_expr, cached_frame_count, cached_result)) =
        solver.caches.inductive_blocking_cache.get(&cache_key)
    {
        // Collision safety (#2860): verify expression matches before using cached result.
        if cached_expr == blocking_formula {
            // Cache hit: return if result is stable
            // - Level 0: always stable (init facts don't change)
            // - Level > 0, true result: stable (inductiveness preserved under frame growth)
            // - Level > 0, false result: stable only if frame hasn't grown
            if level == 0 || *cached_result || *cached_frame_count == current_frame_count {
                return *cached_result;
            }
        }
        // Expression mismatch (collision) or frame grew with false result - recompute
    }

    let result = is_inductive_blocking_uncached(solver, blocking_formula, predicate, level);

    // Store with expression for collision detection (#2860)
    solver.insert_inductive_blocking_cache_entry(
        cache_key,
        (blocking_formula.clone(), current_frame_count, result),
    );
    result
}

pub(super) fn is_inductive_blocking_uncached(
    solver: &mut PdrSolver,
    blocking_formula: &ChcExpr,
    predicate: PredicateId,
    level: usize,
) -> bool {
    // Fast path: check if any cached countermodel satisfies blocking_formula (#2126)
    if solver.caches.implication_cache.blocking_rejected_by_cache(
        predicate.index(),
        level,
        blocking_formula,
    ) {
        if solver.config.verbose {
            safe_eprintln!(
                "PDR: is_inductive_blocking fast reject via cached model for pred {} level {}",
                predicate.index(),
                level
            );
        }
        return false;
    }

    // Require that the lemma (NOT of blocking_formula) holds for ALL initial states.
    //
    // Many predicates have multiple initial states (e.g., array-typed init that only
    // constrains a few indices). If we only ensure the lemma is consistent with *some*
    // init state, PDR can learn lemmas that exclude legitimate init states and become
    // unsound (and will later fail model verification).
    let lemma = ChcExpr::not(blocking_formula.clone());
    if solver.predicate_has_facts(predicate) {
        let neg_lemma = ChcExpr::not(lemma);
        if !solver.blocks_initial_states(predicate, &neg_lemma) {
            if solver.config.verbose {
                safe_eprintln!(
                    "PDR: is_inductive_blocking rejecting at level {}: blocking formula {} is consistent with init (would block init states)",
                    level, blocking_formula
                );
            }
            return false;
        }
    }

    if level == 0 {
        return level_zero_inductive_blocking(solver, blocking_formula, predicate);
    }

    for (clause_index, clause) in solver.problem.clauses_defining_with_index(predicate) {
        // #2901: Check cancellation between SMT queries in clause loop.
        if solver.is_cancelled() {
            return false;
        }
        if clause.body.predicates.is_empty() {
            continue;
        }
        let head_args = match &clause.head {
            crate::ClauseHead::Predicate(_, a) => a.as_slice(),
            crate::ClauseHead::False => continue,
        };
        let clause_constraint = clause
            .body
            .constraint
            .clone()
            .unwrap_or(ChcExpr::Bool(true));
        let blocking_on_head = match solver.apply_to_args(predicate, blocking_formula, head_args) {
            Some(e) => e,
            None => return false,
        };
        let guarded = solver.clause_guarded_constraint(predicate, clause_index, head_args, level);
        let incr_clause_bg = clause_constraint.clone();
        let incr_blocking_on_head = blocking_on_head.clone();
        let incr_guarded = guarded.clone();
        let base = ChcExpr::and_all([clause_constraint, blocking_on_head, guarded]);

        if clause.body.predicates.len() > 1 {
            if level - 1 == 0 {
                if solver.config.verbose {
                    safe_eprintln!(
                        "PDR: is_inductive_blocking being conservative for hyperedge at level 1"
                    );
                }
                return false;
            }

            let mut body_constraints = Vec::with_capacity(clause.body.predicates.len());
            for (body_pred, body_args) in &clause.body.predicates {
                let frame_constraint = solver
                    .cumulative_frame_constraint(level - 1, *body_pred)
                    .unwrap_or(ChcExpr::Bool(true));
                match solver.apply_to_args(*body_pred, &frame_constraint, body_args) {
                    Some(e) => body_constraints.push(e),
                    None => return false,
                }
            }
            let all_body_constraints = ChcExpr::and_all(body_constraints);
            let query = solver.bound_int_vars(ChcExpr::and_all([base, all_body_constraints]));

            let simplified = query.propagate_equalities();
            if matches!(simplified, ChcExpr::Bool(false)) {
                continue;
            }

            let (result, _) = PdrSolver::check_sat_with_ite_case_split(
                &mut solver.smt,
                solver.config.verbose,
                &simplified,
            );
            match result {
                SmtResult::Sat(ref model) => {
                    solver
                        .caches
                        .implication_cache
                        .record_blocking_countermodel(predicate.index(), level, model);
                    return false;
                }
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                    continue
                }
                SmtResult::Unknown => return false,
            }
        }

        let (body_pred, body_args) = &clause.body.predicates[0];
        if level - 1 == 0 {
            for fact in solver
                .problem
                .facts()
                .filter(|f| f.head.predicate_id() == Some(*body_pred))
            {
                let fact_constraint = fact.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));
                let fact_head_args = match &fact.head {
                    crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                    crate::ClauseHead::False => continue,
                };
                if fact_head_args.len() != body_args.len() {
                    continue;
                }

                let (renamed_fact_constraint, renamed_fact_args) =
                    PdrSolver::rename_fact_variables(&fact_constraint, fact_head_args, "__fact_");

                let eqs: Vec<ChcExpr> = body_args
                    .iter()
                    .cloned()
                    .zip(renamed_fact_args.iter().cloned())
                    .map(|(a, b)| ChcExpr::eq(a, b))
                    .collect();
                let init_match = ChcExpr::and_all(eqs);
                let query = solver.bound_int_vars(ChcExpr::and_all([
                    base.clone(),
                    renamed_fact_constraint,
                    init_match,
                ]));

                let simplified = query.propagate_equalities();
                if matches!(simplified, ChcExpr::Bool(false)) {
                    continue;
                }

                let (result, _) = PdrSolver::check_sat_with_ite_case_split(
                    &mut solver.smt,
                    solver.config.verbose,
                    &simplified,
                );
                match result {
                    SmtResult::Sat(_) => return false,
                    SmtResult::Unsat
                    | SmtResult::UnsatWithCore(_)
                    | SmtResult::UnsatWithFarkas(_) => continue,
                    SmtResult::Unknown => return false,
                }
            }
        } else {
            let frame_constraint = solver
                .cumulative_frame_constraint(level - 1, *body_pred)
                .unwrap_or(ChcExpr::Bool(true));
            let frame_on_body = match solver.apply_to_args(*body_pred, &frame_constraint, body_args)
            {
                Some(e) => e,
                None => return false,
            };

            if super::super::INCREMENTAL_PDR_ENABLED && solver.problem_is_integer_arithmetic {
                let check_timeout = solver.smt.current_timeout();
                let seg_key = super::super::prop_solver::SegmentKey::Inductiveness { clause_index };
                let prop = super::super::core::ensure_prop_solver_split(
                    &mut solver.prop_solvers,
                    &solver.frames,
                    predicate,
                );
                prop.register_segment(seg_key, &incr_clause_bg);
                let assumptions = [incr_blocking_on_head, incr_guarded, frame_on_body.clone()];
                let incr_result = prop.check_inductiveness(
                    solver.frames.len(),
                    clause_index,
                    &assumptions,
                    check_timeout,
                    None,
                );
                match incr_result {
                    crate::smt::IncrementalCheckResult::Unsat => {
                        continue;
                    }
                    crate::smt::IncrementalCheckResult::Sat(ref model) => {
                        solver
                            .caches
                            .implication_cache
                            .record_blocking_countermodel(predicate.index(), level, model);
                        return false;
                    }
                    crate::smt::IncrementalCheckResult::Unknown
                    | crate::smt::IncrementalCheckResult::RetryFresh(_) => {}
                }
            }

            let query = solver.bound_int_vars(ChcExpr::and_all([base, frame_on_body]));

            let simplified = query.propagate_equalities();
            if matches!(simplified, ChcExpr::Bool(false)) {
                continue;
            }

            let (result, _) = PdrSolver::check_sat_with_ite_case_split(
                &mut solver.smt,
                solver.config.verbose,
                &simplified,
            );
            match result {
                SmtResult::Sat(ref model) => {
                    solver
                        .caches
                        .implication_cache
                        .record_blocking_countermodel(predicate.index(), level, model);
                    return false;
                }
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                    continue
                }
                SmtResult::Unknown => return false,
            }
        }
    }

    true
}

fn level_zero_inductive_blocking(
    solver: &mut PdrSolver,
    blocking_formula: &ChcExpr,
    predicate: PredicateId,
) -> bool {
    if !solver.predicate_has_facts(predicate) {
        return true;
    }
    if !solver.blocks_initial_states(predicate, blocking_formula) {
        return false;
    }

    for (clause_index, clause) in solver.problem.clauses_defining_with_index(predicate) {
        if solver.is_cancelled() {
            return false;
        }
        if clause.body.predicates.is_empty() {
            continue;
        }
        let head_args = match &clause.head {
            crate::ClauseHead::Predicate(_, a) => a.as_slice(),
            crate::ClauseHead::False => continue,
        };
        let clause_constraint = clause
            .body
            .constraint
            .clone()
            .unwrap_or(ChcExpr::Bool(true));
        let blocking_on_head = match solver.apply_to_args(predicate, blocking_formula, head_args) {
            Some(e) => e,
            None => return false,
        };
        let guarded = solver.clause_guarded_constraint(predicate, clause_index, head_args, 1);
        let base = ChcExpr::and_all([
            clause_constraint.clone(),
            blocking_on_head.clone(),
            guarded.clone(),
        ]);

        if clause.body.predicates.len() == 1 {
            let (body_pred, body_args) = &clause.body.predicates[0];
            for (fact_index, fact) in solver
                .problem
                .clauses()
                .iter()
                .enumerate()
                .filter(|(_, f)| f.is_fact() && f.head.predicate_id() == Some(*body_pred))
            {
                let fact_constraint = fact.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));
                let fact_head_args = match &fact.head {
                    crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                    crate::ClauseHead::False => continue,
                };
                if fact_head_args.len() != body_args.len() {
                    continue;
                }

                let (renamed_fact_constraint, renamed_fact_args) =
                    PdrSolver::rename_fact_variables(&fact_constraint, fact_head_args, "__fact_");

                let eqs: Vec<ChcExpr> = body_args
                    .iter()
                    .cloned()
                    .zip(renamed_fact_args.iter().cloned())
                    .map(|(a, b)| ChcExpr::eq(a, b))
                    .collect();
                let init_match = ChcExpr::and_all(eqs);

                if super::super::INCREMENTAL_PDR_ENABLED
                    && solver.problem_is_integer_arithmetic
                    && !solver.uses_arrays
                {
                    let check_timeout = solver.smt.current_timeout();
                    let seg_key = super::super::prop_solver::SegmentKey::InitInductiveness {
                        clause_index,
                        fact_index,
                    };
                    let prop = super::super::core::ensure_prop_solver_split(
                        &mut solver.prop_solvers,
                        &solver.frames,
                        predicate,
                    );
                    prop.register_segment_multi(
                        seg_key,
                        &[
                            clause_constraint.clone(),
                            renamed_fact_constraint.clone(),
                            init_match.clone(),
                        ],
                    );
                    let incr_assumptions = [blocking_on_head.clone(), guarded.clone()];
                    let incr_result = prop.check_init_inductiveness(
                        solver.frames.len(),
                        clause_index,
                        fact_index,
                        &incr_assumptions,
                        check_timeout,
                    );
                    match incr_result {
                        crate::smt::IncrementalCheckResult::Unsat => {
                            continue;
                        }
                        crate::smt::IncrementalCheckResult::Sat(_) => {
                            if solver.config.verbose {
                                safe_eprintln!(
                                    "PDR: is_inductive_blocking at level 0: incr SAT — transition from init reaches blocked state"
                                );
                            }
                            return false;
                        }
                        crate::smt::IncrementalCheckResult::Unknown
                        | crate::smt::IncrementalCheckResult::RetryFresh(_) => {}
                    }
                }

                let query = solver.bound_int_vars(ChcExpr::and_all([
                    base.clone(),
                    renamed_fact_constraint,
                    init_match,
                ]));

                let simplified = query.propagate_equalities();
                if matches!(simplified, ChcExpr::Bool(false)) {
                    continue;
                }

                let (result, _) = PdrSolver::check_sat_with_ite_case_split(
                    &mut solver.smt,
                    solver.config.verbose,
                    &simplified,
                );
                match result {
                    SmtResult::Sat(_) => {
                        if solver.config.verbose {
                            safe_eprintln!(
                                "PDR: is_inductive_blocking at level 0: transition from init reaches blocked state"
                            );
                        }
                        return false;
                    }
                    SmtResult::Unsat
                    | SmtResult::UnsatWithCore(_)
                    | SmtResult::UnsatWithFarkas(_) => continue,
                    SmtResult::Unknown => return false,
                }
            }
        }
    }
    true
}
