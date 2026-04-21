// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// A lemma blocking states at some frame level
#[derive(Debug, Clone)]
pub(crate) struct Lemma {
    /// Predicate this lemma is about
    pub(crate) predicate: PredicateId,
    /// The invariant formula (states that satisfy this predicate's constraint).
    /// Despite the old comment saying "blocking formula", this is actually the invariant:
    /// - Created via `NOT(generalized)` at lemma construction
    /// - cumulative_frame_constraint returns AND of these formulas
    /// - The blocking formula is NOT(formula)
    pub(crate) formula: ChcExpr,
    /// Cached structural hash of `formula` for fast deduplication (#1037).
    pub(crate) formula_hash: u64,
    /// Frame level where this lemma was learned
    pub(crate) level: usize,
    /// If true, this lemma was verified algebraically and should bypass SMT checks
    /// in `is_self_inductive_blocking`. Used for sum invariants discovered via
    /// `is_sum_preserved_by_transitions` with algebraic verification. (#955)
    pub(crate) algebraically_verified: bool,
}

impl Lemma {
    pub(crate) fn new(predicate: PredicateId, formula: ChcExpr, level: usize) -> Self {
        let formula_hash = formula.structural_hash();

        let lemma = Self {
            predicate,
            formula,
            formula_hash,
            level,
            algebraically_verified: false,
        };

        // Postcondition: cached hash is consistent with formula (#4757).
        debug_assert_eq!(
            lemma.formula_hash,
            lemma.formula.structural_hash(),
            "BUG: Lemma hash mismatch immediately after construction"
        );
        lemma
    }

    pub(crate) fn with_algebraically_verified(mut self, value: bool) -> Self {
        self.algebraically_verified = value;
        self
    }
}
