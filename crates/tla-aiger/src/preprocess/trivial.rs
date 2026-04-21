// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Trivial constant propagation for AIGER preprocessing.
//!
//! Folds AND gates with constant or complementary inputs, propagating
//! the resulting constants through the transition system.

use rustc_hash::FxHashMap;

use crate::transys::Transys;

use super::substitution::{apply_substitution, fold_and, sorted_and_defs, subst_lit};

/// Trivial constant propagation and clause cleanup.
pub(crate) fn trivial_simplify(ts: &Transys) -> Transys {
    let mut subst = FxHashMap::default();

    for (out, raw_rhs0, raw_rhs1) in sorted_and_defs(ts) {
        let rhs0 = subst_lit(raw_rhs0, &subst);
        let rhs1 = subst_lit(raw_rhs1, &subst);
        if let Some(folded) = fold_and(rhs0, rhs1) {
            subst.insert(out, folded);
        }
    }

    apply_substitution(ts, &subst)
}
