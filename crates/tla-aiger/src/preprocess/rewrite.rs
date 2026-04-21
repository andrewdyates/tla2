// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Local AIG rewriting for arithmetic-heavy transition systems.
//!
//! This pass performs a single round of local rewrites over the AND network:
//! - reassociation / shared-input extraction via small conjunction flattening
//! - idempotence and contradiction detection across one local AND cone
//! - direct self-negating gate elimination (`g = AND(!g, x)`)

use rustc_hash::FxHashMap;

use crate::sat_types::{Lit, Var};
use crate::transys::Transys;

use super::substitution::{apply_substitution, fold_and, sorted_and_defs};

type PairKey = (u32, u32);
type TriadKey = (u32, u32, u32);

#[derive(Clone, Copy)]
enum NormalizedAnd {
    Lit(Lit),
    Pair(PairKey),
    Triad(TriadKey),
}

#[inline]
fn subst_lit(lit: Lit, subst: &FxHashMap<Var, Lit>) -> Lit {
    let mut current = lit;
    let mut steps = 0usize;
    let max_steps = subst.len().saturating_add(1);

    while steps <= max_steps {
        let Some(&replacement) = subst.get(&current.var()) else {
            break;
        };

        let next = if current.is_negated() {
            !replacement
        } else {
            replacement
        };

        if next == current {
            break;
        }

        current = next;
        steps += 1;
    }

    current
}

#[inline]
fn canonical_pair(lhs0: Lit, lhs1: Lit) -> (Lit, Lit) {
    if lhs0.code() <= lhs1.code() {
        (lhs0, lhs1)
    } else {
        (lhs1, lhs0)
    }
}

#[inline]
fn pair_key(lhs0: Lit, lhs1: Lit) -> PairKey {
    let (lhs0, lhs1) = canonical_pair(lhs0, lhs1);
    (lhs0.code(), lhs1.code())
}

fn collect_local_conjuncts(
    lit: Lit,
    and_defs: &FxHashMap<Var, (Lit, Lit)>,
    leaves: &mut Vec<Lit>,
) -> bool {
    if lit == Lit::TRUE {
        return true;
    }

    if lit.is_positive() {
        if let Some(&(rhs0, rhs1)) = and_defs.get(&lit.var()) {
            if !collect_local_conjuncts(rhs0, and_defs, leaves) {
                return false;
            }
            if !collect_local_conjuncts(rhs1, and_defs, leaves) {
                return false;
            }
            return leaves.len() <= 4;
        }
    }

    leaves.push(lit);
    leaves.len() <= 4
}

fn normalize_local_and(
    rhs0: Lit,
    rhs1: Lit,
    and_defs: &FxHashMap<Var, (Lit, Lit)>,
) -> Option<NormalizedAnd> {
    let mut leaves = Vec::with_capacity(4);
    if !collect_local_conjuncts(rhs0, and_defs, &mut leaves)
        || !collect_local_conjuncts(rhs1, and_defs, &mut leaves)
    {
        return None;
    }

    let mut simplified = Vec::with_capacity(leaves.len());
    for lit in leaves {
        if lit == Lit::FALSE {
            return Some(NormalizedAnd::Lit(Lit::FALSE));
        }
        if lit == Lit::TRUE {
            continue;
        }
        if simplified.contains(&lit) {
            continue;
        }
        if simplified.contains(&!lit) {
            return Some(NormalizedAnd::Lit(Lit::FALSE));
        }
        simplified.push(lit);
    }

    simplified.sort_unstable_by_key(|lit| lit.code());

    match simplified.as_slice() {
        [] => Some(NormalizedAnd::Lit(Lit::TRUE)),
        [lit] => Some(NormalizedAnd::Lit(*lit)),
        [lhs0, lhs1] => Some(NormalizedAnd::Pair((lhs0.code(), lhs1.code()))),
        [lhs0, lhs1, lhs2] => Some(NormalizedAnd::Triad((
            lhs0.code(),
            lhs1.code(),
            lhs2.code(),
        ))),
        _ => None,
    }
}

fn simplify_self_negating_gate(out: Var, rhs0: Lit, rhs1: Lit) -> Option<(Lit, Lit)> {
    let neg_out = Lit::neg(out);

    if rhs0 == neg_out {
        return Some((Lit::FALSE, !rhs1));
    }
    if rhs1 == neg_out {
        return Some((Lit::FALSE, !rhs0));
    }

    None
}

/// Apply one round of local AIG rewriting rules.
///
/// Returns the rewritten transition system and the number of eliminated or
/// substituted gate definitions.
pub(crate) fn local_rewrite(ts: &Transys) -> (Transys, usize) {
    if ts.and_defs.is_empty() {
        return (ts.clone(), 0);
    }

    let mut subst: FxHashMap<Var, Lit> = FxHashMap::default();
    let mut extra_constraints = Vec::new();
    let mut live_defs: FxHashMap<Var, (Lit, Lit)> = FxHashMap::default();
    let mut binary_defs: FxHashMap<PairKey, Var> = FxHashMap::default();
    let mut triad_defs: FxHashMap<TriadKey, Var> = FxHashMap::default();
    let mut rewrites = 0usize;

    for (out, raw_rhs0, raw_rhs1) in sorted_and_defs(ts) {
        let rhs0 = subst_lit(raw_rhs0, &subst);
        let rhs1 = subst_lit(raw_rhs1, &subst);
        let (rhs0, rhs1) = canonical_pair(rhs0, rhs1);

        if let Some((replacement, forced_constraint)) = simplify_self_negating_gate(out, rhs0, rhs1)
        {
            subst.insert(out, replacement);
            extra_constraints.push(forced_constraint);
            rewrites += 1;
            continue;
        }

        if let Some(folded) = fold_and(rhs0, rhs1) {
            if folded != Lit::pos(out) {
                subst.insert(out, folded);
                rewrites += 1;
                continue;
            }
        }

        let normalized = normalize_local_and(rhs0, rhs1, &live_defs);
        match normalized {
            Some(NormalizedAnd::Lit(lit)) if lit != Lit::pos(out) => {
                subst.insert(out, lit);
                rewrites += 1;
                continue;
            }
            Some(NormalizedAnd::Pair(key)) => {
                if let Some(&rep) = binary_defs.get(&key) {
                    let replacement = Lit::pos(rep);
                    if replacement != Lit::pos(out) {
                        subst.insert(out, replacement);
                        rewrites += 1;
                        continue;
                    }
                }
            }
            Some(NormalizedAnd::Triad(key)) => {
                if let Some(&rep) = triad_defs.get(&key) {
                    let replacement = Lit::pos(rep);
                    if replacement != Lit::pos(out) {
                        subst.insert(out, replacement);
                        rewrites += 1;
                        continue;
                    }
                }
            }
            Some(NormalizedAnd::Lit(_)) | None => {}
        }

        live_defs.insert(out, (rhs0, rhs1));
        binary_defs.entry(pair_key(rhs0, rhs1)).or_insert(out);
        if let Some(NormalizedAnd::Triad(key)) = normalized {
            triad_defs.entry(key).or_insert(out);
        }
    }

    if subst.is_empty() && extra_constraints.is_empty() {
        return (ts.clone(), 0);
    }

    let mut augmented = ts.clone();
    augmented.constraint_lits.extend(extra_constraints);

    (apply_substitution(&augmented, &subst), rewrites)
}

#[cfg(test)]
mod tests {
    use rustc_hash::{FxHashMap, FxHashSet};

    use crate::sat_types::{Clause, Lit, Var};
    use crate::transys::Transys;

    use super::local_rewrite;
    use super::super::substitution::rebuild_trans_clauses;

    fn build_ts(
        max_var: u32,
        latch_vars: Vec<Var>,
        input_vars: Vec<Var>,
        next_state: FxHashMap<Var, Lit>,
        init_clauses: Vec<Clause>,
        bad_lits: Vec<Lit>,
        constraint_lits: Vec<Lit>,
        and_defs: FxHashMap<Var, (Lit, Lit)>,
    ) -> Transys {
        Transys {
            max_var,
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
        }
    }

    fn assert_valid_ts(ts: &Transys) {
        assert_eq!(ts.num_latches, ts.latch_vars.len());
        assert_eq!(ts.num_inputs, ts.input_vars.len());
        assert!(ts.internal_signals.is_empty());

        let expected_trans: FxHashSet<Clause> =
            rebuild_trans_clauses(&ts.and_defs).into_iter().collect();
        let actual_trans: FxHashSet<Clause> = ts.trans_clauses.iter().cloned().collect();
        assert!(
            expected_trans.is_subset(&actual_trans),
            "all live AND definitions must remain encoded in trans_clauses"
        );

        let latch_set: FxHashSet<Var> = ts.latch_vars.iter().copied().collect();
        let input_set: FxHashSet<Var> = ts.input_vars.iter().copied().collect();
        assert_eq!(latch_set.len(), ts.latch_vars.len());
        assert_eq!(input_set.len(), ts.input_vars.len());
        assert!(latch_set.is_disjoint(&input_set));

        for &latch in &ts.latch_vars {
            assert!(latch.0 <= ts.max_var);
            assert!(ts.next_state.contains_key(&latch));
        }

        for &input in &ts.input_vars {
            assert!(input.0 <= ts.max_var);
        }

        for (&out, &(rhs0, rhs1)) in &ts.and_defs {
            assert!(out.0 <= ts.max_var);
            assert!(rhs0.var().0 <= ts.max_var);
            assert!(rhs1.var().0 <= ts.max_var);
        }

        for clause in &ts.init_clauses {
            for &lit in &clause.lits {
                assert!(lit.var().0 <= ts.max_var);
            }
        }

        for clause in &ts.trans_clauses {
            for &lit in &clause.lits {
                assert!(lit.var().0 <= ts.max_var);
            }
        }

        for &lit in &ts.bad_lits {
            assert!(lit.var().0 <= ts.max_var);
        }

        for &lit in &ts.constraint_lits {
            assert!(lit.var().0 <= ts.max_var);
        }
    }

    #[test]
    fn test_local_rewrite_extracts_shared_input() {
        let a = Var(1);
        let b = Var(2);
        let c = Var(3);
        let ab = Var(4);
        let ac = Var(5);
        let bc = Var(6);
        let left = Var(7);
        let right = Var(8);

        let mut and_defs = FxHashMap::default();
        and_defs.insert(ab, (Lit::pos(a), Lit::pos(b)));
        and_defs.insert(ac, (Lit::pos(a), Lit::pos(c)));
        and_defs.insert(bc, (Lit::pos(b), Lit::pos(c)));
        and_defs.insert(left, (Lit::pos(ab), Lit::pos(ac)));
        and_defs.insert(right, (Lit::pos(a), Lit::pos(bc)));

        let ts = build_ts(
            8,
            Vec::new(),
            vec![a, b, c],
            FxHashMap::default(),
            Vec::new(),
            vec![Lit::pos(left), Lit::pos(right)],
            Vec::new(),
            and_defs,
        );

        let (rewritten, rewrites) = local_rewrite(&ts);
        assert_eq!(rewrites, 1);
        assert!(rewritten.and_defs.contains_key(&left));
        assert!(!rewritten.and_defs.contains_key(&right));
        assert_eq!(rewritten.bad_lits, vec![Lit::pos(left)]);
        assert_valid_ts(&rewritten);
    }

    #[test]
    fn test_local_rewrite_eliminates_self_negating_gate() {
        let x = Var(1);
        let g = Var(2);

        let mut and_defs = FxHashMap::default();
        and_defs.insert(g, (Lit::neg(g), Lit::pos(x)));

        let ts = build_ts(
            2,
            Vec::new(),
            vec![x],
            FxHashMap::default(),
            Vec::new(),
            vec![Lit::pos(g)],
            Vec::new(),
            and_defs,
        );

        let (rewritten, rewrites) = local_rewrite(&ts);
        assert_eq!(rewrites, 1);
        assert!(rewritten.and_defs.is_empty());
        assert_eq!(rewritten.bad_lits, vec![Lit::FALSE]);
        assert_eq!(rewritten.constraint_lits, vec![Lit::neg(x)]);
        assert_valid_ts(&rewritten);
    }
}
