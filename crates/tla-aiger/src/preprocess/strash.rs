// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Structural hashing for AIGER AND gates.
//!
//! Detects AND gates that have become structurally identical after
//! substitution and merges them, reducing the number of gates and
//! Tseitin clauses.
//!
//! Reference: ABC's `strash` (structural hashing) is a fundamental AIG
//! optimization. rIC3 relies on ABC for this via its `preprocess` pipeline.

use rustc_hash::FxHashMap;

use crate::sat_types::{Lit, Var};
use crate::transys::Transys;

use super::substitution::{apply_substitution, fold_and, sorted_and_defs, subst_lit};

/// Perform structural hashing: detect AND gates that have become structurally
/// identical after substitution and merge them.
///
/// After constant propagation and SCORR, AND gates may end up with the same
/// pair of inputs. Merging these reduces the number of gates and Tseitin
/// clauses, improving SAT solver performance.
pub(crate) fn structural_hash(ts: &Transys) -> Transys {
    if ts.and_defs.len() < 2 {
        return ts.clone();
    }

    // Build a map from canonical (rhs0, rhs1) pairs to the first gate var seen.
    // Canonical form: order inputs by literal code so (a, b) == (b, a).
    let mut canonical_map: FxHashMap<(u32, u32), Var> = FxHashMap::default();
    let mut subst: FxHashMap<Var, Lit> = FxHashMap::default();

    // Process gates in topological order (sorted by output var).
    for (out, rhs0, rhs1) in sorted_and_defs(ts) {
        let r0 = subst_lit(rhs0, &subst);
        let r1 = subst_lit(rhs1, &subst);

        // First check if the gate folds to a constant.
        if let Some(folded) = fold_and(r0, r1) {
            subst.insert(out, folded);
            continue;
        }

        // Canonical form: lower literal code first.
        let key = if r0.code() <= r1.code() {
            (r0.code(), r1.code())
        } else {
            (r1.code(), r0.code())
        };

        if let Some(&existing_var) = canonical_map.get(&key) {
            // This gate is structurally identical to an existing one.
            subst.insert(out, Lit::pos(existing_var));
        } else {
            canonical_map.insert(key, out);
        }
    }

    if subst.is_empty() {
        ts.clone()
    } else {
        apply_substitution(ts, &subst)
    }
}
