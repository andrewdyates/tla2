// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SCORR (Sequential Combinational Redundancy Removal) and forward reduction.
//!
//! SCORR merges latches that are provably equivalent (or complementary) using
//! simulation-based candidate generation followed by SAT-based verification.
//! Forward reduction does the same for combinational AND gate outputs.
//!
//! Candidate generation uses three simulation modes for maximum coverage:
//! 1. **Random simulation** — pure random patterns for broad coverage.
//! 2. **Init-seeded simulation** — first round uses known init values from
//!    unit clauses, catching init-equivalent latches.
//! 3. **SAT-seeded simulation** — z4-sat enumerates valid init states,
//!    then forward-simulates for N steps. Catches equivalences from non-unit
//!    init constraints and reachable-state patterns.
//!
//! Reference: rIC3 `transys/scorr.rs` uses `init_simulation(1)` +
//! `rt_simulation(&init, 10)` + `solve_with_restart_limit([], ..., 10)`.

use rustc_hash::FxHashMap;

use crate::sat_types::{Lit, SatResult, SatSolver, SolverBackend, Var, Z4SatCdclSolver};
use crate::transys::Transys;

use super::simulation::{
    build_candidates, gate_signatures, latch_signatures, latch_signatures_init_seeded,
};
use super::simulation_sat::latch_signatures_sat_seeded;
use super::substitution::{apply_substitution, subst_lit};

/// Maximum number of forward-reduce candidate pairs to verify via SAT.
const FORWARD_REDUCE_VERIFY_LIMIT: usize = 512;

fn make_solver(ts: &Transys, backend: SolverBackend) -> Box<dyn SatSolver> {
    match backend {
        SolverBackend::Z4Sat => Box::new(Z4SatCdclSolver::new(ts.max_var + 1)),
        _ => backend.make_solver(ts.max_var + 1),
    }
}

fn build_init_solver(ts: &Transys) -> Box<dyn SatSolver> {
    let mut solver = make_solver(ts, SolverBackend::Z4Sat);
    solver.ensure_vars(ts.max_var);
    for clause in &ts.init_clauses {
        solver.add_clause(&clause.lits);
    }
    solver
}

fn build_trans_solver(ts: &Transys) -> Box<dyn SatSolver> {
    let mut solver = make_solver(ts, SolverBackend::Z4Sat);
    solver.ensure_vars(ts.max_var);
    for clause in &ts.trans_clauses {
        solver.add_clause(&clause.lits);
    }
    for &constraint in &ts.constraint_lits {
        solver.add_clause(&[constraint]);
    }
    solver
}

#[inline]
fn relation_cases(a: Lit, b: Lit, negated: bool) -> [(Lit, Lit); 2] {
    if negated {
        [(a, !b), (!a, b)]
    } else {
        [(a, b), (!a, !b)]
    }
}

#[inline]
fn mismatch_cases(a: Lit, b: Lit, negated: bool) -> [(Lit, Lit); 2] {
    if negated {
        [(a, b), (!a, !b)]
    } else {
        [(a, !b), (!a, b)]
    }
}

fn relation_implied(solver: &mut dyn SatSolver, a: Lit, b: Lit, negated: bool) -> bool {
    for (lhs, rhs) in mismatch_cases(a, b, negated) {
        match solver.solve(&[lhs, rhs]) {
            SatResult::Unsat => {}
            SatResult::Sat | SatResult::Unknown => return false,
        }
    }
    true
}

/// Check if the relation holds inductively, using a conflict budget.
///
/// Uses `solve_with_budget` with a limit of 10 conflicts per SAT query,
/// matching rIC3's `solve_with_restart_limit(..., 10)`. This keeps SCORR
/// fast: each equivalence check is bounded, and hard-to-verify pairs are
/// skipped (treated as non-equivalent).
fn relation_inductive_budgeted(
    solver: &mut dyn SatSolver,
    curr_a: Lit,
    curr_b: Lit,
    next_a: Lit,
    next_b: Lit,
    negated: bool,
) -> Option<bool> {
    for (curr0, curr1) in relation_cases(curr_a, curr_b, negated) {
        for (next0, next1) in mismatch_cases(next_a, next_b, negated) {
            match solver.solve_with_budget(&[curr0, curr1, next0, next1], 1000) {
                SatResult::Unsat => {}
                SatResult::Sat => return Some(false),
                SatResult::Unknown => return None,
            }
        }
    }
    Some(true)
}

fn relation_inductive(
    solver: &mut dyn SatSolver,
    curr_a: Lit,
    curr_b: Lit,
    next_a: Lit,
    next_b: Lit,
    negated: bool,
) -> bool {
    for (curr0, curr1) in relation_cases(curr_a, curr_b, negated) {
        for (next0, next1) in mismatch_cases(next_a, next_b, negated) {
            match solver.solve(&[curr0, curr1, next0, next1]) {
                SatResult::Unsat => {}
                SatResult::Sat | SatResult::Unknown => return false,
            }
        }
    }
    true
}

fn combinational_equiv(solver: &mut dyn SatSolver, a: Lit, b: Lit, negated: bool) -> bool {
    for (lhs, rhs) in mismatch_cases(a, b, negated) {
        match solver.solve(&[lhs, rhs]) {
            SatResult::Unsat => {}
            SatResult::Sat | SatResult::Unknown => return false,
        }
    }
    true
}

/// Merge two sorted candidate lists, deduplicating by (x, y, negated).
fn merge_candidates(
    a: Vec<(Var, Var, bool)>,
    b: Vec<(Var, Var, bool)>,
) -> Vec<(Var, Var, bool)> {
    use rustc_hash::FxHashSet;
    let mut seen: FxHashSet<(u32, u32, bool)> = FxHashSet::default();
    let mut merged = Vec::with_capacity(a.len() + b.len());

    for (x, y, neg) in a.into_iter().chain(b) {
        if seen.insert((x.0, y.0, neg)) {
            merged.push((x, y, neg));
        }
    }

    merged.sort_unstable_by_key(|(x, y, negated)| (y.0, x.0, *negated as u8));
    merged
}

/// Merge three candidate lists.
fn merge_candidates_3(
    a: Vec<(Var, Var, bool)>,
    b: Vec<(Var, Var, bool)>,
    c: Vec<(Var, Var, bool)>,
) -> Vec<(Var, Var, bool)> {
    merge_candidates(merge_candidates(a, b), c)
}

/// Sequential combinational redundancy removal for latches.
///
/// Uses three simulation modes for candidate generation:
/// 1. Random simulation — broad coverage of equivalence patterns.
/// 2. Init-seeded simulation (unit-clause) — catches init-equivalent latches.
/// 3. SAT-seeded simulation — z4-sat enumerates full init states and
///    forward-simulates, finding equivalences from non-unit constraints
///    and reachable-state patterns.
///
/// Candidates from all three modes are merged and deduplicated before
/// SAT-based verification. For circuits with >= 10 latches, the inductiveness
/// check uses a conflict budget (matching rIC3's restart_limit=10) to keep
/// SCORR fast on large circuits.
pub(crate) fn scorr(ts: &Transys) -> (Transys, usize) {
    if ts.latch_vars.len() < 2 {
        return (ts.clone(), 0);
    }

    // Generate candidates from three simulation modes, then merge.
    let random_candidates = build_candidates(&latch_signatures(ts));
    let init_candidates = build_candidates(&latch_signatures_init_seeded(ts));
    let sat_candidates = build_candidates(&latch_signatures_sat_seeded(ts));
    let candidates = merge_candidates_3(random_candidates, init_candidates, sat_candidates);
    if candidates.is_empty() {
        return (ts.clone(), 0);
    }

    let mut init_solver = build_init_solver(ts);
    let mut trans_solver = build_trans_solver(ts);
    let mut subst = FxHashMap::default();

    // Use budgeted inductiveness check for larger circuits.
    let use_budget = ts.latch_vars.len() >= 10;

    for (x, y, negated) in candidates {
        if subst.contains_key(&y) {
            continue;
        }

        let (Some(&next_x), Some(&next_y)) = (ts.next_state.get(&x), ts.next_state.get(&y)) else {
            continue;
        };

        if !relation_implied(&mut *init_solver, Lit::pos(x), Lit::pos(y), negated) {
            continue;
        }

        let inductive = if use_budget {
            // Use budgeted check: Unknown means skip this pair (too hard).
            relation_inductive_budgeted(
                &mut *trans_solver,
                Lit::pos(x),
                Lit::pos(y),
                next_x,
                next_y,
                negated,
            )
            .unwrap_or(false)
        } else {
            relation_inductive(
                &mut *trans_solver,
                Lit::pos(x),
                Lit::pos(y),
                next_x,
                next_y,
                negated,
            )
        };

        if !inductive {
            continue;
        }

        let representative = subst_lit(Lit::pos(x), &subst);
        let replacement = if negated {
            !representative
        } else {
            representative
        };
        if replacement != Lit::pos(y) {
            subst.insert(y, replacement);
        }
    }

    let eliminated = subst.len();
    if eliminated == 0 {
        (ts.clone(), 0)
    } else {
        (apply_substitution(ts, &subst), eliminated)
    }
}

/// Forward reduction for equivalent AND-gate outputs.
pub(crate) fn forward_reduce(ts: &Transys) -> Transys {
    if ts.and_defs.len() < 2 {
        return ts.clone();
    }

    let mut candidates = build_candidates(&gate_signatures(ts));
    if candidates.is_empty() {
        return ts.clone();
    }

    // The SAT API does not expose restart budgeting, so keep this pass light by
    // bounding the number of verified pairs.
    if candidates.len() > FORWARD_REDUCE_VERIFY_LIMIT {
        candidates.truncate(FORWARD_REDUCE_VERIFY_LIMIT);
    }

    let mut solver = build_trans_solver(ts);
    let mut subst = FxHashMap::default();

    for (x, y, negated) in candidates {
        if subst.contains_key(&y) {
            continue;
        }
        if !combinational_equiv(&mut *solver, Lit::pos(x), Lit::pos(y), negated) {
            continue;
        }

        let representative = subst_lit(Lit::pos(x), &subst);
        let replacement = if negated {
            !representative
        } else {
            representative
        };
        if replacement != Lit::pos(y) {
            subst.insert(y, replacement);
        }
    }

    if subst.is_empty() {
        ts.clone()
    } else {
        apply_substitution(ts, &subst)
    }
}
