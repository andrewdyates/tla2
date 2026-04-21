// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Substitution utilities for AIGER preprocessing.
//!
//! Provides literal substitution, AND gate folding, clause simplification,
//! and the core `apply_substitution` transform that rewrites a transition
//! system according to a variable-to-literal mapping.

use rustc_hash::{FxHashMap, FxHashSet};

use crate::sat_types::{Clause, Lit, Var};
use crate::transys::Transys;

#[inline]
fn subst_lit_once(lit: Lit, subst: &FxHashMap<Var, Lit>) -> Lit {
    if let Some(&replacement) = subst.get(&lit.var()) {
        if lit.is_negated() {
            !replacement
        } else {
            replacement
        }
    } else {
        lit
    }
}

#[inline]
pub(crate) fn subst_lit(lit: Lit, subst: &FxHashMap<Var, Lit>) -> Lit {
    let mut current = lit;
    let mut steps = 0usize;
    let max_steps = subst.len().saturating_add(1);
    while steps <= max_steps {
        let next = subst_lit_once(current, subst);
        if next == current {
            break;
        }
        current = next;
        steps += 1;
    }
    current
}

pub(crate) fn canonicalize_subst(subst: &FxHashMap<Var, Lit>) -> FxHashMap<Var, Lit> {
    let mut resolved = FxHashMap::default();
    for &var in subst.keys() {
        resolved.insert(var, subst_lit(Lit::pos(var), subst));
    }
    resolved
}

#[inline]
pub(crate) fn fold_and(rhs0: Lit, rhs1: Lit) -> Option<Lit> {
    if rhs0 == Lit::FALSE || rhs1 == Lit::FALSE {
        return Some(Lit::FALSE);
    }
    if rhs0 == Lit::TRUE {
        return Some(rhs1);
    }
    if rhs1 == Lit::TRUE {
        return Some(rhs0);
    }
    if rhs0 == rhs1 {
        return Some(rhs0);
    }
    if rhs0 == !rhs1 {
        return Some(Lit::FALSE);
    }
    None
}

pub(crate) fn sorted_and_defs(ts: &Transys) -> Vec<(Var, Lit, Lit)> {
    let mut gates: Vec<(Var, Lit, Lit)> = ts
        .and_defs
        .iter()
        .map(|(&out, &(rhs0, rhs1))| (out, rhs0, rhs1))
        .collect();
    gates.sort_unstable_by_key(|(out, _, _)| out.0);
    gates
}

pub(crate) fn rebuild_trans_clauses(and_defs: &FxHashMap<Var, (Lit, Lit)>) -> Vec<Clause> {
    let mut gates: Vec<(Var, Lit, Lit)> = and_defs
        .iter()
        .map(|(&out, &(rhs0, rhs1))| (out, rhs0, rhs1))
        .collect();
    gates.sort_unstable_by_key(|(out, _, _)| out.0);

    let mut clauses = Vec::with_capacity(gates.len() * 3);
    for (out_var, rhs0, rhs1) in gates {
        let out = Lit::pos(out_var);
        clauses.push(Clause::binary(!out, rhs0));
        clauses.push(Clause::binary(!out, rhs1));
        clauses.push(Clause::new(vec![!rhs0, !rhs1, out]));
    }
    clauses
}

pub(crate) fn simplify_clause_lits<I>(lits: I) -> Option<Clause>
where
    I: IntoIterator<Item = Lit>,
{
    let mut seen = FxHashSet::default();
    let mut simplified = Vec::new();

    for lit in lits {
        if lit == Lit::TRUE {
            return None;
        }
        if lit == Lit::FALSE {
            continue;
        }
        if seen.contains(&!lit) {
            return None;
        }
        if seen.insert(lit) {
            simplified.push(lit);
        }
    }

    if simplified.is_empty() {
        None
    } else {
        Some(Clause::new(simplified))
    }
}

fn simplify_or_lits<I>(lits: I) -> Vec<Lit>
where
    I: IntoIterator<Item = Lit>,
{
    let mut seen = FxHashSet::default();
    let mut simplified = Vec::new();

    for lit in lits {
        if lit == Lit::TRUE {
            return vec![Lit::TRUE];
        }
        if lit == Lit::FALSE {
            continue;
        }
        if seen.contains(&!lit) {
            return vec![Lit::TRUE];
        }
        if seen.insert(lit) {
            simplified.push(lit);
        }
    }

    if simplified.is_empty() {
        vec![Lit::FALSE]
    } else {
        simplified
    }
}

fn simplify_and_lits<I>(lits: I) -> Vec<Lit>
where
    I: IntoIterator<Item = Lit>,
{
    let mut seen = FxHashSet::default();
    let mut simplified = Vec::new();

    for lit in lits {
        if lit == Lit::FALSE {
            return vec![Lit::FALSE];
        }
        if lit == Lit::TRUE {
            continue;
        }
        if seen.contains(&!lit) {
            return vec![Lit::FALSE];
        }
        if seen.insert(lit) {
            simplified.push(lit);
        }
    }

    simplified
}

fn max_used_var(ts: &Transys) -> u32 {
    let mut max_var = 0u32;

    let mut observe_var = |var: Var| {
        if var.0 > max_var {
            max_var = var.0;
        }
    };

    for &var in &ts.latch_vars {
        observe_var(var);
    }
    for &var in &ts.input_vars {
        observe_var(var);
    }
    for &lit in &ts.bad_lits {
        observe_var(lit.var());
    }
    for &lit in &ts.constraint_lits {
        observe_var(lit.var());
    }
    for clause in &ts.init_clauses {
        for &lit in &clause.lits {
            observe_var(lit.var());
        }
    }
    for clause in &ts.trans_clauses {
        for &lit in &clause.lits {
            observe_var(lit.var());
        }
    }
    for (&out, &(rhs0, rhs1)) in &ts.and_defs {
        observe_var(out);
        observe_var(rhs0.var());
        observe_var(rhs1.var());
    }
    for (&latch, &next_lit) in &ts.next_state {
        observe_var(latch);
        observe_var(next_lit.var());
    }

    max_var
}

pub(crate) fn cleanup_ts(ts: Transys) -> Transys {
    let mut reduced = ts.coi_reduce();
    reduced.max_var = max_used_var(&reduced);
    reduced.num_latches = reduced.latch_vars.len();
    reduced.num_inputs = reduced.input_vars.len();
    reduced.internal_signals.clear();
    reduced
}

/// Apply a variable substitution map throughout a transition system.
pub(crate) fn apply_substitution(ts: &Transys, subst: &FxHashMap<Var, Lit>) -> Transys {
    let mut combined = canonicalize_subst(subst);
    let mut and_defs = FxHashMap::default();

    for (out, raw_rhs0, raw_rhs1) in sorted_and_defs(ts) {
        if combined.contains_key(&out) {
            continue;
        }

        let rhs0 = subst_lit(raw_rhs0, &combined);
        let rhs1 = subst_lit(raw_rhs1, &combined);

        if let Some(folded) = fold_and(rhs0, rhs1) {
            combined.insert(out, folded);
        } else {
            and_defs.insert(out, (rhs0, rhs1));
        }
    }

    let mut init_clauses = Vec::with_capacity(ts.init_clauses.len());
    for clause in &ts.init_clauses {
        if let Some(simplified) =
            simplify_clause_lits(clause.lits.iter().map(|&lit| subst_lit(lit, &combined)))
        {
            init_clauses.push(simplified);
        }
    }

    let mut latch_vars = Vec::with_capacity(ts.latch_vars.len());
    let mut next_state = FxHashMap::default();
    for &latch in &ts.latch_vars {
        if combined.contains_key(&latch) {
            continue;
        }
        latch_vars.push(latch);
        if let Some(&next_lit) = ts.next_state.get(&latch) {
            next_state.insert(latch, subst_lit(next_lit, &combined));
        }
    }

    let input_vars: Vec<Var> = ts
        .input_vars
        .iter()
        .copied()
        .filter(|var| !combined.contains_key(var))
        .collect();

    let bad_lits = simplify_or_lits(ts.bad_lits.iter().map(|&lit| subst_lit(lit, &combined)));
    let constraint_lits = simplify_and_lits(
        ts.constraint_lits
            .iter()
            .map(|&lit| subst_lit(lit, &combined)),
    );

    let provisional = Transys {
        max_var: ts.max_var,
        num_latches: latch_vars.len(),
        num_inputs: input_vars.len(),
        latch_vars,
        input_vars,
        next_state,
        init_clauses,
        trans_clauses: rebuild_trans_clauses(&and_defs),
        bad_lits,
        constraint_lits,
        and_defs,
        internal_signals: Vec::new(),
    };

    cleanup_ts(provisional)
}
