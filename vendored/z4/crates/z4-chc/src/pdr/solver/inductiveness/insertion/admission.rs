// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::{ChcExpr, ChcOp, ChcSort, FxHashMap, Lemma, PdrSolver, PredicateId, SmtResult};

pub(super) fn add_discovered_invariant(
    solver: &mut PdrSolver,
    pred: PredicateId,
    formula: ChcExpr,
    level: usize,
) -> bool {
    add_discovered_invariant_impl(solver, pred, formula, level, false)
}

pub(super) fn add_discovered_invariant_algebraic(
    solver: &mut PdrSolver,
    pred: PredicateId,
    formula: ChcExpr,
    level: usize,
) -> bool {
    add_discovered_invariant_impl(solver, pred, formula, level, true)
}

pub(super) fn add_discovered_invariant_impl(
    solver: &mut PdrSolver,
    pred: PredicateId,
    formula: ChcExpr,
    level: usize,
    algebraically_verified: bool,
) -> bool {
    if formula.contains_array_ops() && !formula.is_bool_sorted_top_level() {
        return false;
    }

    if !algebraically_verified
        && solver
            .rejected_invariants
            .contains(&(pred, formula.clone()))
    {
        return false;
    }

    let target_level = level.min(solver.frames.len().saturating_sub(1)).max(1);

    if solver.frames[target_level].contains_lemma(pred, &formula) {
        if algebraically_verified {
            solver.frames[target_level].add_lemma(
                Lemma::new(pred, formula, target_level).with_algebraically_verified(true),
            );
        }
        return true;
    }

    if !algebraically_verified {
        if let Some((parity_var, k, c)) = solver.extract_simple_parity_equality(pred, &formula) {
            if !solver.is_parity_preserved_by_transitions(pred, &parity_var, k, c) {
                if solver.config.verbose {
                    safe_eprintln!(
                        "PDR: Rejecting discovered parity invariant for pred {} (not transition-preserved): {}",
                        pred.index(),
                        formula
                    );
                }
                cache_rejected_invariant(solver, pred, &formula);
                return false;
            }
        }
    }

    if solver.predicate_has_facts(pred) && !algebraically_verified {
        let blocking = ChcExpr::not(formula.clone());
        if !solver.blocks_initial_states(pred, &blocking) {
            if solver.config.verbose {
                safe_eprintln!(
                    "PDR: Rejecting non-init-valid discovered invariant for pred {}: {}",
                    pred.index(),
                    formula
                );
            }
            cache_rejected_invariant(solver, pred, &formula);
            return false;
        }
    } else if !solver.has_any_incoming_inter_predicate_transitions(pred) {
        let init_values = solver.get_init_values(pred);
        if !init_values.is_empty() {
            if let Some(init_constraint) =
                solver.build_init_constraint_from_bounds(pred, &init_values)
            {
                let query = ChcExpr::and(init_constraint, formula.clone());
                solver.smt.reset();
                if matches!(
                    solver.smt.check_sat(&query),
                    SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
                ) {
                    if solver.config.verbose {
                        safe_eprintln!(
                            "PDR: Rejecting non-init-valid invariant for pred {} (propagated bounds): {}",
                            pred.index(),
                            formula
                        );
                    }
                    cache_rejected_invariant(solver, pred, &formula);
                    return false;
                }
            }
        }
    }

    if solver.is_cancelled() {
        return false;
    }

    if let Some(&scc_idx) = solver.scc_info.predicate_to_scc.get(&pred) {
        let scc = &solver.scc_info.sccs[scc_idx];
        if scc.is_cyclic && scc.predicates.len() > 1 {
            let mut invariants: FxHashMap<PredicateId, ChcExpr> = FxHashMap::default();
            let scc_predicates = scc.predicates.clone();
            let mut translation_failed = false;
            for scc_pred in &scc_predicates {
                if *scc_pred == pred {
                    invariants.insert(pred, formula.clone());
                } else if let Some(translated) = solver.translate_lemma(&formula, pred, *scc_pred) {
                    invariants.insert(*scc_pred, translated);
                } else {
                    if solver.config.verbose {
                        safe_eprintln!(
                            "PDR: Cannot translate discovered invariant to SCC pred {} (skipping joint SCC check): {}",
                            scc_pred.index(),
                            formula
                        );
                    }
                    translation_failed = true;
                    break;
                }
            }

            if !translation_failed && !solver.verify_scc_lemmas(&scc_predicates, &invariants, level)
            {
                if solver.config.verbose {
                    safe_eprintln!(
                        "PDR: Rejecting non-inductive discovered invariant for SCC pred {}: {}",
                        pred.index(),
                        formula
                    );
                }
                cache_rejected_invariant(solver, pred, &formula);
                return false;
            }
        }
    }

    if solver.has_any_incoming_inter_predicate_transitions(pred)
        && !solver.is_entry_inductive(&formula, pred, target_level)
    {
        if is_equality_formula(&formula) {
            let strengthened =
                solver.try_strengthen_predecessors_for_entry(pred, &formula, target_level);
            if strengthened && solver.is_entry_inductive(&formula, pred, target_level) {
                if solver.config.verbose {
                    safe_eprintln!(
                        "PDR: Entry-inductiveness succeeded after predecessor strengthening for pred {}: {}",
                        pred.index(),
                        formula
                    );
                }
            } else {
                if strengthened && solver.config.verbose {
                    safe_eprintln!(
                        "PDR: Predecessor strengthening insufficient for pred {}: {}",
                        pred.index(),
                        formula
                    );
                }
                let mut any_weakened_added = false;
                let mut failed_weakened = Vec::new();
                if let Some(weakened) = try_weaken_equality_to_inequality(&formula) {
                    for weak_formula in weakened {
                        if solver.config.verbose {
                            safe_eprintln!(
                                "PDR: Equality {} failed entry-inductiveness, trying weakened: {}",
                                formula,
                                weak_formula
                            );
                        }
                        if add_discovered_invariant_impl(
                            solver,
                            pred,
                            weak_formula.clone(),
                            level,
                            algebraically_verified,
                        ) {
                            any_weakened_added = true;
                        } else {
                            failed_weakened.push(weak_formula);
                        }
                    }
                }
                if !failed_weakened.is_empty() && solver.deferred_entry_invariants.len() < 64 {
                    for weak_formula in failed_weakened {
                        if !solver.frames[target_level].contains_lemma(pred, &weak_formula) {
                            solver.deferred_entry_invariants.push((
                                pred,
                                weak_formula,
                                target_level,
                                0,
                            ));
                        }
                    }
                }
                if any_weakened_added {
                    return true;
                }
                if solver.config.verbose {
                    safe_eprintln!(
                        "PDR: Rejecting discovered invariant for pred {} (not entry-inductive): {}",
                        pred.index(),
                        formula
                    );
                }
                return false;
            }
        } else {
            if solver.config.verbose {
                safe_eprintln!(
                    "PDR: Rejecting discovered invariant for pred {} (not entry-inductive): {}",
                    pred.index(),
                    formula
                );
            }
            return false;
        }
    }

    if !algebraically_verified {
        let blocking_formula = ChcExpr::not(formula.clone());
        let passes_self_inductive = if solver.predicate_has_facts(pred) {
            solver.is_self_inductive_blocking(&blocking_formula, pred)
        } else if let Some(entry_domain) = solver.entry_domain_constraint(pred, target_level) {
            solver.is_self_inductive_blocking_with_entry_domain(
                &blocking_formula,
                pred,
                Some(&entry_domain),
            )
        } else {
            solver.is_self_inductive_blocking(&blocking_formula, pred)
        };

        if !passes_self_inductive {
            if solver.deferred_self_inductive_invariants.len() < 64 {
                if !solver.frames[target_level].contains_lemma(pred, &formula) {
                    solver.deferred_self_inductive_invariants.push((
                        pred,
                        formula.clone(),
                        target_level,
                        0,
                    ));
                    if solver.config.verbose {
                        safe_eprintln!(
                            "PDR: Deferring discovered invariant for pred {} (not self-inductive, will retry with frame): {}",
                            pred.index(),
                            formula
                        );
                    }
                }
            } else if solver.config.verbose {
                safe_eprintln!(
                    "PDR: Rejecting discovered invariant for pred {} (not self-inductive, defer queue full): {}",
                    pred.index(),
                    formula
                );
            }
            cache_rejected_invariant(solver, pred, &formula);
            return false;
        }
    } else if solver.config.verbose {
        safe_eprintln!(
            "PDR: Accepting algebraically-verified invariant for pred {} (bypassing SMT check): {}",
            pred.index(),
            formula
        );
    }

    solver.add_lemma_to_frame(
        Lemma::new(pred, formula, target_level).with_algebraically_verified(algebraically_verified),
        target_level,
    );
    true
}

pub(super) fn try_weaken_equality_to_inequality(formula: &ChcExpr) -> Option<Vec<ChcExpr>> {
    if let ChcExpr::Op(ChcOp::Eq, args) = formula {
        if args.len() == 2 {
            let lhs = args[0].as_ref().clone();
            let rhs = args[1].as_ref().clone();
            if matches!(lhs.sort(), ChcSort::Int) && matches!(rhs.sort(), ChcSort::Int) {
                return Some(vec![
                    ChcExpr::ge(lhs.clone(), rhs.clone()),
                    ChcExpr::le(lhs, rhs),
                ]);
            }
        }
    }
    None
}

pub(super) fn add_discovered_invariant_with_weakening(
    solver: &mut PdrSolver,
    pred: PredicateId,
    formula: ChcExpr,
    level: usize,
) -> bool {
    if solver.add_discovered_invariant(pred, formula.clone(), level) {
        return true;
    }

    if !solver.has_any_incoming_inter_predicate_transitions(pred) {
        return false;
    }

    if let Some(weakened_forms) = try_weaken_equality_to_inequality(&formula) {
        if solver.config.verbose {
            safe_eprintln!(
                "PDR: Equality {} failed for pred {}, trying weakened forms",
                formula,
                pred.index()
            );
        }

        for weakened in weakened_forms {
            if solver.add_discovered_invariant(pred, weakened.clone(), level) {
                if solver.config.verbose {
                    safe_eprintln!(
                        "PDR: Weakened equality to {} for pred {}",
                        weakened,
                        pred.index()
                    );
                }
                return true;
            }
        }
    }

    false
}

pub(super) fn is_equality_formula(formula: &ChcExpr) -> bool {
    if let ChcExpr::Op(ChcOp::Eq, args) = formula {
        if args.len() == 2 {
            return matches!(args[0].sort(), ChcSort::Int)
                && matches!(args[1].sort(), ChcSort::Int);
        }
    }
    false
}

pub(super) fn cache_rejected_invariant(
    solver: &mut PdrSolver,
    pred: PredicateId,
    formula: &ChcExpr,
) {
    if solver.rejected_invariants.len() < 512 {
        solver.rejected_invariants.insert((pred, formula.clone()));
    }
}
