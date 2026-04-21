// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded Variable Elimination (BVE) for AND gate output variables.
//!
//! Eliminates an AND gate variable `g` when:
//! 1. `g` is not a latch, input, bad, or constraint variable (i.e. "internal").
//! 2. `g` has low occurrence count in the transition clauses (bounded by the
//!    product of positive and negative occurrence counts).
//!
//! Elimination works by resolving all clauses containing `g` against each
//! other and removing the original clauses. This is standard SAT preprocessing
//! (Een & Biere, SAT 2005). For AND gates in Tseitin form, each gate produces
//! exactly 3 clauses: 2 binary + 1 ternary. The resolution product is bounded.
//!
//! Reference: rIC3's `bve_simplify()` in its DAG-CNF simplifier does this
//! after COI refinement. ABC's `dc2`/`resyn2` also uses BVE-like rewrites.

use rustc_hash::{FxHashMap, FxHashSet};

use crate::sat_types::{Clause, Lit, Var};
use crate::transys::Transys;

use super::substitution::{cleanup_ts, simplify_clause_lits};

/// Maximum number of BVE elimination attempts per pass.
const BVE_MAX_ELIMINATIONS: usize = 10_000;

/// Perform bounded variable elimination on internal AND gate variables.
pub(crate) fn bounded_variable_elimination(ts: &Transys) -> (Transys, usize) {
    if ts.and_defs.is_empty() {
        return (ts.clone(), 0);
    }

    // Build the set of "frozen" variables: latches, inputs, bad/constraint references,
    // and next-state targets. These cannot be eliminated.
    let mut frozen = FxHashSet::default();
    frozen.insert(Var(0));
    for &v in &ts.latch_vars {
        frozen.insert(v);
    }
    for &v in &ts.input_vars {
        frozen.insert(v);
    }
    for &lit in &ts.bad_lits {
        frozen.insert(lit.var());
    }
    for &lit in &ts.constraint_lits {
        frozen.insert(lit.var());
    }
    for &next_lit in ts.next_state.values() {
        frozen.insert(next_lit.var());
    }
    // AND gate inputs that are themselves latch/input are already frozen.
    // Additionally freeze any variable referenced in init clauses.
    for clause in &ts.init_clauses {
        for &lit in &clause.lits {
            frozen.insert(lit.var());
        }
    }

    // Build occurrence lists: for each variable, which clause indices contain it.
    let mut pos_occ: FxHashMap<Var, Vec<usize>> = FxHashMap::default();
    let mut neg_occ: FxHashMap<Var, Vec<usize>> = FxHashMap::default();

    for (idx, clause) in ts.trans_clauses.iter().enumerate() {
        for &lit in &clause.lits {
            if lit.is_positive() {
                pos_occ.entry(lit.var()).or_default().push(idx);
            } else {
                neg_occ.entry(lit.var()).or_default().push(idx);
            }
        }
    }

    // Find eliminable AND gate variables: internal, non-frozen, low occurrence.
    // BVE bound: #resolvents = |pos_occ| * |neg_occ|. We only eliminate if
    // the number of resolvents is <= the number of removed clauses
    // (= |pos_occ| + |neg_occ|), which guarantees the clause count doesn't grow.
    let mut eliminate_vars: Vec<Var> = Vec::new();
    for &gate_var in ts.and_defs.keys() {
        if frozen.contains(&gate_var) {
            continue;
        }
        let np = pos_occ.get(&gate_var).map_or(0, |v| v.len());
        let nn = neg_occ.get(&gate_var).map_or(0, |v| v.len());
        let total = np + nn;
        let product = np * nn;

        // Only eliminate if resolution doesn't increase clause count.
        // Also skip variables with zero occurrences (already dead).
        if total > 0 && product <= total {
            eliminate_vars.push(gate_var);
        }
    }

    eliminate_vars.sort_by_key(|v| {
        let np = pos_occ.get(v).map_or(0, |v| v.len());
        let nn = neg_occ.get(v).map_or(0, |v| v.len());
        np * nn // eliminate cheapest first
    });

    if eliminate_vars.is_empty() {
        return (ts.clone(), 0);
    }

    eliminate_vars.truncate(BVE_MAX_ELIMINATIONS);

    // Perform elimination: for each variable, resolve pos and neg clauses,
    // add resolvents, mark originals for deletion.
    let mut deleted = vec![false; ts.trans_clauses.len()];
    let mut new_clauses: Vec<Clause> = Vec::new();
    let mut eliminated = 0usize;
    let elim_set: FxHashSet<Var> = eliminate_vars.iter().copied().collect();

    for &var in &eliminate_vars {
        let pos_indices = pos_occ.get(&var).cloned().unwrap_or_default();
        let neg_indices = neg_occ.get(&var).cloned().unwrap_or_default();

        // Check that none of the clauses have been previously deleted.
        let pos_alive: Vec<usize> = pos_indices.iter().copied().filter(|&i| !deleted[i]).collect();
        let neg_alive: Vec<usize> = neg_indices.iter().copied().filter(|&i| !deleted[i]).collect();

        if pos_alive.is_empty() && neg_alive.is_empty() {
            continue;
        }

        // Recheck bound with alive counts.
        if pos_alive.len() * neg_alive.len() > pos_alive.len() + neg_alive.len() {
            continue;
        }

        // Generate resolvents.
        let mut resolvents = Vec::new();
        for &pi in &pos_alive {
            for &ni in &neg_alive {
                // Resolve: combine lits from both clauses, dropping the pivot variable.
                let mut res_lits: Vec<Lit> = Vec::new();
                for &lit in &ts.trans_clauses[pi].lits {
                    if lit.var() != var {
                        res_lits.push(lit);
                    }
                }
                for &lit in &ts.trans_clauses[ni].lits {
                    if lit.var() != var {
                        res_lits.push(lit);
                    }
                }
                // Simplify the resolvent.
                if let Some(simplified) = simplify_clause_lits(res_lits) {
                    resolvents.push(simplified);
                }
                // If simplification returns None, the clause is a tautology -- skip it.
            }
        }

        // Mark original clauses as deleted.
        for &i in &pos_alive {
            deleted[i] = true;
        }
        for &i in &neg_alive {
            deleted[i] = true;
        }

        new_clauses.extend(resolvents);
        eliminated += 1;
    }

    if eliminated == 0 {
        return (ts.clone(), 0);
    }

    // Build new transition system with surviving clauses + resolvents.
    let mut surviving_clauses: Vec<Clause> = ts
        .trans_clauses
        .iter()
        .enumerate()
        .filter(|(i, _)| !deleted[*i])
        .map(|(_, c)| c.clone())
        .collect();
    surviving_clauses.extend(new_clauses);

    // Remove eliminated gates from and_defs.
    let mut and_defs = ts.and_defs.clone();
    for &var in &eliminate_vars {
        if elim_set.contains(&var) {
            and_defs.remove(&var);
        }
    }

    let provisional = Transys {
        max_var: ts.max_var,
        num_latches: ts.latch_vars.len(),
        num_inputs: ts.input_vars.len(),
        latch_vars: ts.latch_vars.clone(),
        input_vars: ts.input_vars.clone(),
        next_state: ts.next_state.clone(),
        init_clauses: ts.init_clauses.clone(),
        trans_clauses: surviving_clauses,
        bad_lits: ts.bad_lits.clone(),
        constraint_lits: ts.constraint_lits.clone(),
        and_defs,
        internal_signals: Vec::new(),
    };

    (cleanup_ts(provisional), eliminated)
}
