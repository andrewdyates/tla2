// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Constant latch elimination for AIGER preprocessing.
//!
//! Detects latches stuck at a constant value by inductive reasoning:
//! if a latch's initial value is a known constant and its next-state
//! function evaluates to the same constant (using only proven-constant
//! substitutions), the latch is constant forever.

use rustc_hash::FxHashMap;

use crate::sat_types::{Lit, Var};
use crate::transys::Transys;

use super::substitution::{apply_substitution, subst_lit};

/// Detect latches stuck at a constant value and eliminate them.
///
/// A latch is "stuck-at-constant" if:
/// 1. Its initial value is a known constant (unit init clause: 0 or 1).
/// 2. Its next-state function evaluates to the same constant after
///    substituting all known constant latches.
///
/// This is done iteratively to fixpoint: eliminating one stuck latch may
/// reveal that another latch's next-state function now reduces to a constant.
///
/// Reference: rIC3 `src/transys/simp.rs` performs iterative constant
/// propagation through `init` and `next` during its `simplify` pass.
/// ABC's `abc_NtkDarLcorr` also eliminates constant latches before IC3.
pub(crate) fn eliminate_constant_latches(ts: &Transys) -> (Transys, usize) {
    let mut subst: FxHashMap<Var, Lit> = FxHashMap::default();
    let mut changed = true;
    let mut total_eliminated = 0usize;

    // Build initial constant map from unit init clauses.
    // Maps latch_var -> constant Lit (TRUE or FALSE).
    let mut known_constants: FxHashMap<Var, Lit> = FxHashMap::default();
    for clause in &ts.init_clauses {
        if clause.lits.len() == 1 {
            let lit = clause.lits[0];
            let var = lit.var();
            if var != Var(0) {
                let val = if lit.is_positive() {
                    Lit::TRUE
                } else {
                    Lit::FALSE
                };
                known_constants.insert(var, val);
            }
        }
    }

    // Iterative fixpoint: keep finding constant latches until none remain.
    let max_iters = ts.latch_vars.len().saturating_add(1);
    let mut iter = 0;
    while changed && iter < max_iters {
        changed = false;
        iter += 1;

        for &latch_var in &ts.latch_vars {
            if subst.contains_key(&latch_var) {
                continue;
            }

            // Check if latch has a known initial constant value.
            let Some(&init_val) = known_constants.get(&latch_var) else {
                continue;
            };

            // Check if next-state function evaluates to the same constant.
            // Use an extended substitution that includes the latch's own init
            // value. This handles self-referencing next-state functions like
            // next(a) = AND(a, input) where a=0 initially.
            let Some(&next_lit) = ts.next_state.get(&latch_var) else {
                continue;
            };

            // Build a temporary evaluation context: subst (already-eliminated
            // constant latches) + this latch's own init value.
            //
            // IMPORTANT: We must NOT substitute other non-eliminated latches'
            // init values here. The next-state function computes the value at
            // step k+1 based on step k. Just because latch B starts at 0 does
            // NOT mean B is still 0 at step k -- B might change. Only latches
            // already proven constant (in `subst`) are safe to substitute.
            //
            // Adding the latch's own init value IS correct: it creates an
            // inductive argument. If latch A=c initially, and next(A)=c
            // whenever A=c (plus only proven-constant substitutions), then
            // A=c forever by induction.
            let mut eval_subst = subst.clone();
            eval_subst.entry(latch_var).or_insert(init_val);

            let resolved_next = subst_lit(next_lit, &eval_subst);
            let next_val = eval_to_constant(resolved_next, &ts.and_defs, &eval_subst);

            if let Some(const_val) = next_val {
                if const_val == init_val {
                    // Latch is stuck at this constant forever.
                    subst.insert(latch_var, const_val);
                    total_eliminated += 1;
                    changed = true;
                }
            }
        }
    }

    if total_eliminated == 0 {
        return (ts.clone(), 0);
    }

    (apply_substitution(ts, &subst), total_eliminated)
}

/// Try to evaluate a literal to a constant (TRUE or FALSE) given known
/// constant substitutions and AND gate definitions.
///
/// Walks through AND gates recursively (with depth limit) to determine
/// if a signal is provably constant.
fn eval_to_constant(
    lit: Lit,
    and_defs: &FxHashMap<Var, (Lit, Lit)>,
    subst: &FxHashMap<Var, Lit>,
) -> Option<Lit> {
    eval_to_constant_inner(lit, and_defs, subst, 0, 64)
}

fn eval_to_constant_inner(
    lit: Lit,
    and_defs: &FxHashMap<Var, (Lit, Lit)>,
    subst: &FxHashMap<Var, Lit>,
    depth: usize,
    max_depth: usize,
) -> Option<Lit> {
    // Check if already a constant.
    if lit == Lit::TRUE {
        return Some(Lit::TRUE);
    }
    if lit == Lit::FALSE {
        return Some(Lit::FALSE);
    }

    // Check if variable is in the substitution map.
    if let Some(&replacement) = subst.get(&lit.var()) {
        let resolved = if lit.is_negated() {
            !replacement
        } else {
            replacement
        };
        if resolved == Lit::TRUE || resolved == Lit::FALSE {
            return Some(resolved);
        }
        // Substitution resolved to another non-constant -- don't recurse further.
        return None;
    }

    if depth >= max_depth {
        return None;
    }

    // Check if it's an AND gate and try to evaluate.
    if let Some(&(rhs0, rhs1)) = and_defs.get(&lit.var()) {
        let resolved_rhs0 = subst_lit(rhs0, subst);
        let resolved_rhs1 = subst_lit(rhs1, subst);

        let val0 = eval_to_constant_inner(resolved_rhs0, and_defs, subst, depth + 1, max_depth);
        let val1 = eval_to_constant_inner(resolved_rhs1, and_defs, subst, depth + 1, max_depth);

        // AND gate short-circuit: if either input is FALSE, output is FALSE.
        if val0 == Some(Lit::FALSE) || val1 == Some(Lit::FALSE) {
            let gate_val = Lit::FALSE;
            return Some(if lit.is_negated() {
                !gate_val
            } else {
                gate_val
            });
        }
        // If both are TRUE, output is TRUE.
        if val0 == Some(Lit::TRUE) && val1 == Some(Lit::TRUE) {
            let gate_val = Lit::TRUE;
            return Some(if lit.is_negated() {
                !gate_val
            } else {
                gate_val
            });
        }
    }

    None
}
