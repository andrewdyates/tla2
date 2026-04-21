// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

pub(super) fn generalize_bv_inductive(
    solver: &mut PdrSolver,
    state: &ChcExpr,
    predicate: PredicateId,
    level: usize,
) -> ChcExpr {
    let conjuncts = state.collect_conjuncts();
    if conjuncts.is_empty() {
        return state.clone();
    }

    if solver.config.verbose {
        safe_eprintln!(
            "PDR: #5877 BV inductive generalization: {} conjuncts at level {}",
            conjuncts.len(),
            level
        );
    }

    let mut current = conjuncts;
    if current.len() >= 2 {
        if let Some(shrunk) =
            solver.try_shrink_blocking_conjuncts_with_iuc(&current, predicate, level)
        {
            if shrunk.len() < current.len() {
                let candidate = PdrSolver::build_conjunction(&shrunk);
                if solver.is_inductive_blocking(&candidate, predicate, level) {
                    if solver.config.verbose {
                        safe_eprintln!(
                            "PDR: BV IUC shrunk {} -> {} conjuncts",
                            current.len(),
                            shrunk.len()
                        );
                    }
                    current = shrunk;
                }
            }
        }
    }

    let mut weakened = Vec::with_capacity(current.len());
    let mut any_weakened = false;
    for c in &current {
        if let Some(replacement) = try_weaken_bv_equality_to_nonzero(c) {
            weakened.push(replacement);
            any_weakened = true;
        } else {
            weakened.push(c.clone());
        }
    }
    if solver.config.verbose && any_weakened {
        let weakenable_count = current
            .iter()
            .filter(|c| try_weaken_bv_equality_to_nonzero(c).is_some())
            .count();
        safe_eprintln!(
            "PDR: BV Phase 0: {} of {} conjuncts are BV equalities (weakenable)",
            weakenable_count,
            current.len()
        );
    }
    if any_weakened {
        let blocking = PdrSolver::build_conjunction(&weakened);
        if solver.is_inductive_blocking(&blocking, predicate, level) {
            if solver.config.verbose {
                safe_eprintln!(
                    "PDR: BV Phase 0a: weakened ALL BV equalities to nonzero checks ({} conjuncts)",
                    weakened.len()
                );
            }
            current = weakened;
        } else {
            if solver.config.verbose {
                safe_eprintln!(
                    "PDR: BV Phase 0a FAILED (all-at-once not inductive), trying Phase 0b (individual)"
                );
            }
            let mut individual_weakened = current.clone();
            let mut individual_count = 0;
            for idx in 0..individual_weakened.len() {
                if let Some(replacement) =
                    try_weaken_bv_equality_to_nonzero(&individual_weakened[idx])
                {
                    let mut candidate = individual_weakened.clone();
                    candidate[idx] = replacement;
                    let blocking = PdrSolver::build_conjunction(&candidate);
                    if solver.is_inductive_blocking(&blocking, predicate, level) {
                        individual_weakened = candidate;
                        individual_count += 1;
                    }
                }
            }
            if individual_count > 0 {
                if solver.config.verbose {
                    safe_eprintln!(
                        "PDR: BV Phase 0b: individually weakened {} BV equalities to nonzero checks",
                        individual_count
                    );
                }
                current = individual_weakened;
            } else if solver.config.verbose {
                safe_eprintln!("PDR: BV Phase 0b: no individual weakenings succeeded either");
            }
        }
    }

    let use_self_ind = level <= 1;
    let mut changed = true;
    while changed && current.len() > 1 {
        changed = false;
        let mut i = current.len();
        while i > 0 {
            i -= 1;
            if current.len() <= 1 {
                break;
            }

            if atom_contains_bv_constant(&current[i]) {
                if let Some(weakened_lit) = try_weaken_bv_equality_to_nonzero(&current[i]) {
                    let mut candidate = current.clone();
                    candidate[i] = weakened_lit;
                    let blocking = PdrSolver::build_conjunction(&candidate);
                    let check = if use_self_ind {
                        solver.is_inductive_blocking(&blocking, predicate, level)
                            && solver.is_self_inductive_blocking(&blocking, predicate)
                    } else {
                        solver.is_inductive_blocking(&blocking, predicate, level)
                    };
                    if check {
                        if solver.config.verbose {
                            safe_eprintln!(
                                "PDR: BV weakened literal {}: {} -> {}",
                                i,
                                current[i],
                                candidate[i]
                            );
                        }
                        current = candidate;
                        changed = true;
                        continue;
                    }
                }
            }

            let mut candidate: Vec<ChcExpr> = Vec::with_capacity(current.len() - 1);
            for (j, c) in current.iter().enumerate() {
                if j != i {
                    candidate.push(c.clone());
                }
            }
            let blocking = PdrSolver::build_conjunction(&candidate);
            let check = if use_self_ind {
                solver.is_inductive_blocking(&blocking, predicate, level)
                    && solver.is_self_inductive_blocking(&blocking, predicate)
            } else {
                solver.is_inductive_blocking(&blocking, predicate, level)
            };
            if check {
                if solver.config.verbose {
                    safe_eprintln!("PDR: BV dropped literal {}: {}", i, current[i]);
                }
                current = candidate;
                changed = true;
            }
        }
    }

    if solver.config.verbose {
        safe_eprintln!(
            "PDR: BV inductive generalization result: {} literals",
            current.len()
        );
    }

    PdrSolver::build_conjunction(&current)
}
