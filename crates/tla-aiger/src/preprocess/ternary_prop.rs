// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Ternary constant propagation for AIGER preprocessing.
//!
//! Detects AND gate outputs that are structurally constant (0 or 1) by
//! propagating ternary values (0, 1, X=unknown) through the gate network.
//!
//! SOUNDNESS NOTE: This pass treats ALL latches and inputs as X (unknown).
//! It does NOT seed from init-state values because latches change over time.
//! Only Var(0) (the structural constant FALSE) is seeded. This means this
//! pass only detects gates that are constant purely from the circuit's
//! combinational structure (e.g., AND(x, !x) = 0, or chains thereof).
//!
//! For init-value-dependent constant detection, use `eliminate_constant_latches`
//! which does a proper inductive argument (init + next-state fixpoint).
//!
//! Reference: rIC3's ternary simulation in preprocessing. ABC's `ternary_sim`.

use rustc_hash::FxHashMap;

use crate::sat_types::{Lit, Var};
use crate::transys::Transys;

use super::substitution::{apply_substitution, sorted_and_defs};

/// Ternary constant propagation: detect AND gate outputs that are structurally
/// constant by propagating ternary values through the gate network.
pub(crate) fn ternary_constant_propagation(ts: &Transys) -> Transys {
    if ts.and_defs.is_empty() {
        return ts.clone();
    }

    // Ternary values: Some(true) = 1, Some(false) = 0, None = X (unknown).
    let mut ternary: Vec<Option<bool>> = vec![None; ts.max_var as usize + 1];

    // Var(0) is constant false -- the only structural constant.
    if !ternary.is_empty() {
        ternary[0] = Some(false);
    }

    // DO NOT seed from init clauses! Latches change over time and their init
    // values are not invariant. Using init values here caused false UNSAT
    // results on SAT benchmarks (e.g., microban_44, microban_1).

    // Evaluate AND gates in topological order.
    // This detects gates that are structurally constant regardless of inputs,
    // e.g., AND(x, FALSE) = FALSE, AND(x, !x) = FALSE.
    for (out, rhs0, rhs1) in sorted_and_defs(ts) {
        let val0 = ternary_eval_lit(rhs0, &ternary);
        let val1 = ternary_eval_lit(rhs1, &ternary);

        let result = match (val0, val1) {
            (Some(false), _) | (_, Some(false)) => Some(false), // AND with 0 = 0
            (Some(true), Some(true)) => Some(true),             // 1 AND 1 = 1
            (Some(true), None) | (None, Some(true)) => None,    // 1 AND X = X
            (None, None) => None,                               // X AND X = X
        };

        if out.index() < ternary.len() {
            ternary[out.index()] = result;
        }
    }

    // Build substitution for all variables determined to be constant.
    let mut subst = FxHashMap::default();
    for (idx, val) in ternary.iter().enumerate() {
        if let Some(is_true) = val {
            let var = Var(idx as u32);
            if var == Var(0) {
                continue; // Var(0) already is constant false
            }
            // Only substitute AND gate outputs (combinational nodes).
            if ts.and_defs.contains_key(&var) {
                let const_lit = if *is_true { Lit::TRUE } else { Lit::FALSE };
                subst.insert(var, const_lit);
            }
        }
    }

    if subst.is_empty() {
        ts.clone()
    } else {
        apply_substitution(ts, &subst)
    }
}

/// Evaluate a literal in ternary domain.
#[inline]
fn ternary_eval_lit(lit: Lit, ternary: &[Option<bool>]) -> Option<bool> {
    let val = ternary.get(lit.var().index()).copied().flatten();
    match val {
        Some(v) => {
            if lit.is_negated() {
                Some(!v)
            } else {
                Some(v)
            }
        }
        None => None,
    }
}
