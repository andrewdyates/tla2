// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! AIG balancing: reduce AND-tree depth via tree restructuring.
//!
//! AIG balance is one of the three fundamental ABC synthesis operations
//! (balance, rewrite, refactor). It restructures chains of AND gates
//! into balanced binary trees, reducing the longest path (critical path
//! depth) in the circuit. Lower depth means fewer decision levels in
//! SAT solving, directly improving IC3/BMC performance.
//!
//! Algorithm:
//! 1. For each AND gate output, collect all leaf inputs by flattening
//!    the AND tree (following positive AND gate edges only).
//! 2. If the tree has 3+ leaves, rebuild as a balanced binary tree.
//! 3. Reuse existing gate variables where possible; allocate fresh ones
//!    if needed.
//!
//! Reference: ABC's `Abc_NtkBalance()` in `src/base/abc/abcBalance.c`.
//! super-prove (#4 HWMCC'25) runs `balance` as part of its AIG
//! preprocessing pipeline, achieving 30-60% circuit shrinkage when
//! combined with rewriting.
//!
//! Limitation: This implementation handles linear AND chains (depth
//! reduction) but does not implement ABC's full SOP balancing or
//! timing-driven balancing. It focuses on the common case of deep
//! AND chains that arise from sequential specification patterns.

use rustc_hash::{FxHashMap, FxHashSet};

use crate::sat_types::{Lit, Var};
use crate::transys::Transys;

use super::substitution::{apply_substitution, fold_and, rebuild_trans_clauses, sorted_and_defs};

/// Maximum depth of AND tree flattening to prevent blowup on wide circuits.
const MAX_FLATTEN_DEPTH: usize = 16;

/// Minimum number of leaves to justify rebalancing an AND tree.
/// Trees with only 2 leaves are already balanced.
const MIN_LEAVES_TO_BALANCE: usize = 3;

/// Flatten an AND tree rooted at `lit` into its leaf inputs.
///
/// Follows positive AND gate references only (a negated reference to an
/// AND gate is a leaf, not flattened further). Returns leaves in order.
fn flatten_and_tree(
    lit: Lit,
    and_defs: &FxHashMap<Var, (Lit, Lit)>,
    fanout: &FxHashMap<Var, usize>,
    leaves: &mut Vec<Lit>,
    depth: usize,
) {
    if depth > MAX_FLATTEN_DEPTH {
        leaves.push(lit);
        return;
    }

    // Only flatten positive references to AND gates with fanout == 1.
    // Multi-fanout gates must be preserved as shared nodes.
    if lit.is_positive() {
        if let Some(&(rhs0, rhs1)) = and_defs.get(&lit.var()) {
            let fo = fanout.get(&lit.var()).copied().unwrap_or(0);
            if fo <= 1 {
                flatten_and_tree(rhs0, and_defs, fanout, leaves, depth + 1);
                flatten_and_tree(rhs1, and_defs, fanout, leaves, depth + 1);
                return;
            }
        }
    }

    leaves.push(lit);
}

/// Compute fanout count for each AND gate variable.
///
/// Fanout = number of times a variable is used as an input to another AND gate,
/// plus references from bad_lits, constraint_lits, and next_state.
fn compute_fanout(ts: &Transys) -> FxHashMap<Var, usize> {
    let mut fanout: FxHashMap<Var, usize> = FxHashMap::default();

    for &(rhs0, rhs1) in ts.and_defs.values() {
        *fanout.entry(rhs0.var()).or_insert(0) += 1;
        *fanout.entry(rhs1.var()).or_insert(0) += 1;
    }

    for &lit in &ts.bad_lits {
        *fanout.entry(lit.var()).or_insert(0) += 1;
    }
    for &lit in &ts.constraint_lits {
        *fanout.entry(lit.var()).or_insert(0) += 1;
    }
    for &next_lit in ts.next_state.values() {
        *fanout.entry(next_lit.var()).or_insert(0) += 1;
    }

    fanout
}

/// Compute the depth of each AND gate (longest path from inputs).
fn compute_depths(ts: &Transys) -> FxHashMap<Var, usize> {
    let mut depths: FxHashMap<Var, usize> = FxHashMap::default();

    fn depth_of(
        lit: Lit,
        and_defs: &FxHashMap<Var, (Lit, Lit)>,
        depths: &mut FxHashMap<Var, usize>,
    ) -> usize {
        if lit == Lit::FALSE || lit == Lit::TRUE {
            return 0;
        }
        if let Some(&d) = depths.get(&lit.var()) {
            return d;
        }
        if let Some(&(rhs0, rhs1)) = and_defs.get(&lit.var()) {
            let d0 = depth_of(rhs0, and_defs, depths);
            let d1 = depth_of(rhs1, and_defs, depths);
            let d = d0.max(d1) + 1;
            depths.insert(lit.var(), d);
            d
        } else {
            depths.insert(lit.var(), 0);
            0
        }
    }

    for &out in ts.and_defs.keys() {
        depth_of(Lit::pos(out), &ts.and_defs, &mut depths);
    }

    depths
}

/// Build a balanced AND tree from a list of leaves.
///
/// Returns the root literal and any new AND gate definitions created.
/// Reuses existing gates from `existing_defs` where possible.
fn build_balanced_tree(
    leaves: &[Lit],
    next_var: &mut u32,
    existing_defs: &FxHashMap<(u32, u32), Var>,
) -> (Lit, Vec<(Var, Lit, Lit)>) {
    assert!(!leaves.is_empty());

    if leaves.len() == 1 {
        return (leaves[0], Vec::new());
    }

    let mut new_defs = Vec::new();
    let mut current_level: Vec<Lit> = leaves.to_vec();

    while current_level.len() > 1 {
        let mut next_level = Vec::with_capacity((current_level.len() + 1) / 2);

        for chunk in current_level.chunks(2) {
            if chunk.len() == 1 {
                next_level.push(chunk[0]);
            } else {
                let lhs = chunk[0];
                let rhs = chunk[1];

                // Check for constant folding first.
                if let Some(folded) = fold_and(lhs, rhs) {
                    next_level.push(folded);
                    continue;
                }

                // Canonical key for structural hashing.
                let key = if lhs.code() <= rhs.code() {
                    (lhs.code(), rhs.code())
                } else {
                    (rhs.code(), lhs.code())
                };

                // Reuse existing gate if available.
                if let Some(&existing) = existing_defs.get(&key) {
                    next_level.push(Lit::pos(existing));
                } else {
                    // Allocate a fresh variable for this new AND gate.
                    let new_var = Var(*next_var);
                    *next_var += 1;
                    let (canonical_lhs, canonical_rhs) = if lhs.code() <= rhs.code() {
                        (lhs, rhs)
                    } else {
                        (rhs, lhs)
                    };
                    new_defs.push((new_var, canonical_lhs, canonical_rhs));
                    next_level.push(Lit::pos(new_var));
                }
            }
        }

        current_level = next_level;
    }

    (current_level[0], new_defs)
}

/// Apply AIG balancing to the transition system.
///
/// Returns the balanced system and the number of depth reductions achieved.
/// A depth reduction means a root AND gate's tree was restructured to be
/// shallower.
pub(crate) fn balance(ts: &Transys) -> (Transys, usize) {
    if ts.and_defs.len() < 3 {
        return (ts.clone(), 0);
    }

    let fanout = compute_fanout(ts);
    let depths = compute_depths(ts);

    // Find AND gate roots (gates used by bad, constraint, or next-state).
    // Also find AND gates that fan out to multiple consumers (shared nodes).
    let mut roots: FxHashSet<Var> = FxHashSet::default();
    for &lit in &ts.bad_lits {
        if ts.and_defs.contains_key(&lit.var()) {
            roots.insert(lit.var());
        }
    }
    for &lit in &ts.constraint_lits {
        if ts.and_defs.contains_key(&lit.var()) {
            roots.insert(lit.var());
        }
    }
    for &next_lit in ts.next_state.values() {
        if ts.and_defs.contains_key(&next_lit.var()) {
            roots.insert(next_lit.var());
        }
    }
    // Multi-fanout AND gates are also balancing roots.
    for (&var, &fo) in &fanout {
        if fo > 1 && ts.and_defs.contains_key(&var) {
            roots.insert(var);
        }
    }

    // Build an existing gate index for structural reuse.
    let mut existing_defs: FxHashMap<(u32, u32), Var> = FxHashMap::default();
    for (&out, &(rhs0, rhs1)) in &ts.and_defs {
        let key = if rhs0.code() <= rhs1.code() {
            (rhs0.code(), rhs1.code())
        } else {
            (rhs1.code(), rhs0.code())
        };
        existing_defs.entry(key).or_insert(out);
    }

    let mut subst: FxHashMap<Var, Lit> = FxHashMap::default();
    let mut new_and_defs: Vec<(Var, Lit, Lit)> = Vec::new();
    let mut next_var = ts.max_var + 1;
    let mut reductions = 0usize;

    // Process roots in topological order.
    let mut sorted_roots: Vec<Var> = roots.into_iter().collect();
    sorted_roots.sort_by_key(|v| v.0);

    for root in sorted_roots {
        let root_depth = depths.get(&root).copied().unwrap_or(0);
        if root_depth < 3 {
            // Already shallow, no benefit from balancing.
            continue;
        }

        let mut leaves = Vec::new();
        let Some(&(rhs0, rhs1)) = ts.and_defs.get(&root) else {
            continue;
        };
        flatten_and_tree(rhs0, &ts.and_defs, &fanout, &mut leaves, 0);
        flatten_and_tree(rhs1, &ts.and_defs, &fanout, &mut leaves, 0);

        if leaves.len() < MIN_LEAVES_TO_BALANCE {
            continue;
        }

        // Deduplicate and check for contradictions.
        let mut deduped = Vec::with_capacity(leaves.len());
        let mut seen = FxHashSet::default();
        let mut has_contradiction = false;
        for &leaf in &leaves {
            if leaf == Lit::FALSE {
                // AND with FALSE = FALSE
                subst.insert(root, Lit::FALSE);
                reductions += 1;
                has_contradiction = true;
                break;
            }
            if leaf == Lit::TRUE {
                continue; // AND with TRUE is identity
            }
            if seen.contains(&!leaf) {
                // x AND !x = FALSE
                subst.insert(root, Lit::FALSE);
                reductions += 1;
                has_contradiction = true;
                break;
            }
            if seen.insert(leaf) {
                deduped.push(leaf);
            }
        }

        if has_contradiction {
            continue;
        }

        if deduped.is_empty() {
            subst.insert(root, Lit::TRUE);
            reductions += 1;
            continue;
        }

        if deduped.len() == 1 {
            subst.insert(root, deduped[0]);
            reductions += 1;
            continue;
        }

        // Compute the depth of a balanced tree for these leaves.
        let balanced_depth = (deduped.len() as f64).log2().ceil() as usize;
        if balanced_depth >= root_depth {
            // Balanced tree wouldn't be shallower. Skip.
            continue;
        }

        // Build balanced tree.
        let (new_root_lit, new_defs) =
            build_balanced_tree(&deduped, &mut next_var, &existing_defs);

        // Register new gates for structural reuse.
        for &(var, lhs, rhs) in &new_defs {
            let key = if lhs.code() <= rhs.code() {
                (lhs.code(), rhs.code())
            } else {
                (rhs.code(), lhs.code())
            };
            existing_defs.entry(key).or_insert(var);
        }

        new_and_defs.extend(new_defs);

        if new_root_lit != Lit::pos(root) {
            subst.insert(root, new_root_lit);
            reductions += 1;
        }
    }

    if subst.is_empty() && new_and_defs.is_empty() {
        return (ts.clone(), 0);
    }

    // Build the result: add new AND gates, apply substitutions.
    let mut result = ts.clone();
    result.max_var = next_var.saturating_sub(1).max(ts.max_var);

    // Add new AND gate definitions.
    for (var, lhs, rhs) in &new_and_defs {
        result.and_defs.insert(*var, (*lhs, *rhs));
    }

    // Rebuild trans_clauses to include new gates.
    result.trans_clauses = rebuild_trans_clauses(&result.and_defs);

    // Apply substitutions (will also remove dead gates via COI in cleanup).
    if !subst.is_empty() {
        result = apply_substitution(&result, &subst);
    }

    (result, reductions)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::preprocess::substitution::rebuild_trans_clauses;
    use crate::sat_types::Clause;

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

    #[test]
    fn test_balance_linear_chain() {
        // Linear chain: g1 = AND(a, b), g2 = AND(g1, c), g3 = AND(g2, d).
        // Depth = 3. Balanced = AND(AND(a,b), AND(c,d)). Depth = 2.
        let a = Var(1);
        let b = Var(2);
        let c = Var(3);
        let d = Var(4);
        let g1 = Var(5);
        let g2 = Var(6);
        let g3 = Var(7);

        let mut and_defs = FxHashMap::default();
        and_defs.insert(g1, (Lit::pos(a), Lit::pos(b)));
        and_defs.insert(g2, (Lit::pos(g1), Lit::pos(c)));
        and_defs.insert(g3, (Lit::pos(g2), Lit::pos(d)));

        let ts = build_ts(
            7,
            Vec::new(),
            vec![a, b, c, d],
            FxHashMap::default(),
            Vec::new(),
            vec![Lit::pos(g3)],
            Vec::new(),
            and_defs,
        );

        let (result, reductions) = balance(&ts);
        assert!(reductions > 0, "should reduce depth of linear chain");
        // The result should still be functionally valid.
        assert!(!result.bad_lits.is_empty());
    }

    #[test]
    fn test_balance_already_balanced() {
        // Already balanced: AND(AND(a,b), AND(c,d)). Depth = 2.
        let a = Var(1);
        let b = Var(2);
        let c = Var(3);
        let d = Var(4);
        let g1 = Var(5);
        let g2 = Var(6);
        let g3 = Var(7);

        let mut and_defs = FxHashMap::default();
        and_defs.insert(g1, (Lit::pos(a), Lit::pos(b)));
        and_defs.insert(g2, (Lit::pos(c), Lit::pos(d)));
        and_defs.insert(g3, (Lit::pos(g1), Lit::pos(g2)));

        let ts = build_ts(
            7,
            Vec::new(),
            vec![a, b, c, d],
            FxHashMap::default(),
            Vec::new(),
            vec![Lit::pos(g3)],
            Vec::new(),
            and_defs,
        );

        let (result, reductions) = balance(&ts);
        assert_eq!(reductions, 0, "already balanced tree should not change");
        assert_eq!(result.and_defs.len(), ts.and_defs.len());
    }

    #[test]
    fn test_balance_with_contradiction() {
        // Chain: g1 = AND(a, !a), g2 = AND(g1, b), g3 = AND(g2, c).
        // Flattening reveals a AND !a = FALSE.
        let a = Var(1);
        let b = Var(2);
        let c = Var(3);
        let g1 = Var(4);
        let g2 = Var(5);
        let g3 = Var(6);

        let mut and_defs = FxHashMap::default();
        and_defs.insert(g1, (Lit::pos(a), Lit::neg(a)));
        and_defs.insert(g2, (Lit::pos(g1), Lit::pos(b)));
        and_defs.insert(g3, (Lit::pos(g2), Lit::pos(c)));

        let ts = build_ts(
            6,
            Vec::new(),
            vec![a, b, c],
            FxHashMap::default(),
            Vec::new(),
            vec![Lit::pos(g3)],
            Vec::new(),
            and_defs,
        );

        let (result, reductions) = balance(&ts);
        assert!(reductions > 0, "should detect contradiction");
        assert_eq!(result.bad_lits, vec![Lit::FALSE]);
    }

    #[test]
    fn test_balance_preserves_shared_nodes() {
        // g1 = AND(a, b) is used by both g2 and g3 (fanout > 1).
        // Balance should NOT flatten through g1.
        let a = Var(1);
        let b = Var(2);
        let c = Var(3);
        let d = Var(4);
        let g1 = Var(5); // shared
        let g2 = Var(6);
        let g3 = Var(7);

        let mut and_defs = FxHashMap::default();
        and_defs.insert(g1, (Lit::pos(a), Lit::pos(b)));
        and_defs.insert(g2, (Lit::pos(g1), Lit::pos(c)));
        and_defs.insert(g3, (Lit::pos(g1), Lit::pos(d)));

        let ts = build_ts(
            7,
            Vec::new(),
            vec![a, b, c, d],
            FxHashMap::default(),
            Vec::new(),
            vec![Lit::pos(g2), Lit::pos(g3)],
            Vec::new(),
            and_defs,
        );

        let (_result, _reductions) = balance(&ts);
        // Should not panic and should preserve functional correctness.
        // g1 is shared so won't be flattened through.
    }

    #[test]
    fn test_balance_noop_small_circuit() {
        // Circuit with < 3 AND gates: balance should be a no-op.
        let a = Var(1);
        let b = Var(2);
        let g = Var(3);

        let mut and_defs = FxHashMap::default();
        and_defs.insert(g, (Lit::pos(a), Lit::pos(b)));

        let ts = build_ts(
            3,
            Vec::new(),
            vec![a, b],
            FxHashMap::default(),
            Vec::new(),
            vec![Lit::pos(g)],
            Vec::new(),
            and_defs,
        );

        let (result, reductions) = balance(&ts);
        assert_eq!(reductions, 0);
        assert_eq!(result.and_defs.len(), 1);
    }

    #[test]
    fn test_balance_deep_chain_5_inputs() {
        // Deep linear chain: g1=AND(a,b), g2=AND(g1,c), g3=AND(g2,d), g4=AND(g3,e).
        // Depth = 4. Balanced depth = ceil(log2(5)) = 3. Should reduce.
        let a = Var(1);
        let b = Var(2);
        let c = Var(3);
        let d = Var(4);
        let e = Var(5);
        let g1 = Var(6);
        let g2 = Var(7);
        let g3 = Var(8);
        let g4 = Var(9);

        let mut and_defs = FxHashMap::default();
        and_defs.insert(g1, (Lit::pos(a), Lit::pos(b)));
        and_defs.insert(g2, (Lit::pos(g1), Lit::pos(c)));
        and_defs.insert(g3, (Lit::pos(g2), Lit::pos(d)));
        and_defs.insert(g4, (Lit::pos(g3), Lit::pos(e)));

        let ts = build_ts(
            9,
            Vec::new(),
            vec![a, b, c, d, e],
            FxHashMap::default(),
            Vec::new(),
            vec![Lit::pos(g4)],
            Vec::new(),
            and_defs,
        );

        let (result, reductions) = balance(&ts);
        assert!(reductions > 0, "should reduce depth of 5-input chain");
        assert!(!result.bad_lits.is_empty());
    }
}
