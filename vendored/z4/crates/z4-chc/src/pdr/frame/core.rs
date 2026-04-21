// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Frame containing lemmas at a given level
#[derive(Debug, Clone)]
pub(crate) struct Frame {
    pub(crate) lemmas: Vec<Lemma>,
    pub(super) lemma_revisions: FxHashMap<PredicateId, u64>,
    /// O(1) lookup map for duplicate detection: (predicate_index, formula_hash) -> formula.
    /// Uses precomputed hash from Lemma for fast lookup without string allocation.
    /// Performance: Eliminates O(L) scan in add_lemma and push_lemmas (#1036, #1121).
    ///
    /// Collision safety (#2860): Stores the full `ChcExpr` in the value. On lookup,
    /// we verify the stored expression matches the query. Hash collisions become
    /// cache misses (the second lemma is correctly added, not rejected).
    pub(super) lemma_keys: FxHashMap<(usize, u64), ChcExpr>,
    /// Cached per-predicate conjunction of lemma formulas (#2815).
    /// Key: PredicateId, Value: (revision_when_cached, conjunction).
    /// Invalidated via `lemma_revisions`: stale entries are recomputed on access.
    predicate_constraint_cache: RefCell<FxHashMap<PredicateId, (u64, ChcExpr)>>,
}

impl Default for Frame {
    fn default() -> Self {
        Self {
            lemmas: Vec::new(),
            lemma_revisions: FxHashMap::default(),
            lemma_keys: FxHashMap::default(),
            predicate_constraint_cache: RefCell::new(FxHashMap::default()),
        }
    }
}

impl Frame {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    pub(crate) fn predicate_lemma_revision(&self, pred: PredicateId) -> u64 {
        self.lemma_revisions.get(&pred).copied().unwrap_or(0)
    }

    /// Debug-only frame consistency check (#4757).
    ///
    /// Verifies structural invariants that must hold after every mutation:
    /// 1. Every lemma's cached `formula_hash` matches `formula.structural_hash()`
    /// 2. Every `lemma_keys` entry is backed by a lemma in the vec
    /// 3. `lemma_keys` size does not exceed `lemmas` size
    /// 4. No duplicate `(predicate, formula)` pairs exist in the lemma vec
    ///
    /// Cost: O(N^2) in the number of lemmas, so only runs in debug builds.
    pub(super) fn debug_assert_frame_invariants(&self) {
        // (1) Hash consistency: cached hash matches formula
        for (i, lemma) in self.lemmas.iter().enumerate() {
            let cached = lemma.formula_hash;
            let actual = lemma.formula.structural_hash();
            debug_assert_eq!(
                cached, actual,
                "BUG: Lemma {i} has stale formula_hash (cached={cached:#x}, actual={actual:#x})",
            );
        }

        // (2) Every lemma_keys entry is backed by at least one lemma
        for ((pred_idx, hash), cached_expr) in &self.lemma_keys {
            let has_backing = self.lemmas.iter().any(|l| {
                l.predicate.index() == *pred_idx
                    && l.formula_hash == *hash
                    && l.formula == *cached_expr
            });
            debug_assert!(
                has_backing,
                "BUG: lemma_keys has orphaned entry (pred_idx={pred_idx}, hash={hash:#x}) with no backing lemma",
            );
        }

        // (3) Key index cannot exceed lemma count
        let keys_len = self.lemma_keys.len();
        let lemmas_len = self.lemmas.len();
        debug_assert!(
            keys_len <= lemmas_len,
            "BUG: lemma_keys ({keys_len}) exceeds lemmas vec ({lemmas_len})",
        );

        // (4) No duplicate (predicate, formula) pairs — the dedup guarantee.
        // Only check small frames to avoid quadratic blowup on large frames.
        if self.lemmas.len() <= 200 {
            for i in 0..self.lemmas.len() {
                for j in (i + 1)..self.lemmas.len() {
                    let a = &self.lemmas[i];
                    let b = &self.lemmas[j];
                    let pred = &a.predicate;
                    debug_assert!(
                        !(a.predicate == b.predicate && a.formula == b.formula),
                        "BUG: Duplicate lemma at indices {i} and {j} (pred={pred:?})",
                    );
                }
            }
        }
    }

    pub(crate) fn add_lemma(&mut self, lemma: Lemma) {
        // O(1) duplicate check with collision safety (#1036, #1121, #2860)
        let key = (lemma.predicate.index(), lemma.formula_hash);
        match self.lemma_keys.entry(key) {
            std::collections::hash_map::Entry::Occupied(entry) => {
                // Key exists: verify expression matches to handle hash collisions (#2860).
                // If expressions match, it's a true duplicate — skip.
                // If they differ, it's a hash collision — allow the add.
                if *entry.get() == lemma.formula {
                    // Upgrade: if the new lemma is algebraically_verified but
                    // the existing one isn't, promote the existing lemma. This
                    // handles the case where a propagated (non-algebraic) lemma
                    // is already in the frame and parity/sum discovery later
                    // algebraically verifies the same formula.
                    if lemma.algebraically_verified {
                        if let Some(existing) = self
                            .lemmas
                            .iter_mut()
                            .find(|l| l.predicate == lemma.predicate && l.formula == lemma.formula)
                        {
                            if !existing.algebraically_verified {
                                existing.algebraically_verified = true;
                                let pred = lemma.predicate;
                                *self.lemma_revisions.entry(pred).or_default() += 1;
                            }
                        }
                    }
                    return;
                }
                // Hash collision: different formula with same hash. Allow addition.
            }
            std::collections::hash_map::Entry::Vacant(entry) => {
                entry.insert(lemma.formula.clone());
            }
        }
        let pred = lemma.predicate;
        self.lemmas.push(lemma);
        *self.lemma_revisions.entry(pred).or_default() += 1;
        self.debug_assert_frame_invariants();
    }

    /// Rebuild the duplicate-detection cache from the surviving lemmas.
    ///
    /// This keeps `lemma_keys` correct after bulk retain/remove passes without
    /// depending on incremental key bookkeeping across multiple deletions.
    pub(super) fn rebuild_lemma_keys(&mut self) {
        self.lemma_keys.clear();
        for lemma in &self.lemmas {
            self.lemma_keys.insert(
                (lemma.predicate.index(), lemma.formula_hash),
                lemma.formula.clone(),
            );
        }
    }

    /// Truncate the lemma list and rebuild all derived indexes.
    ///
    /// Some callers roll back speculative lemma discovery by restoring the
    /// frame's previous length. The duplicate cache and predicate constraint
    /// cache must be kept in sync with that rollback.
    pub(crate) fn truncate_lemmas(&mut self, new_len: usize) {
        if new_len >= self.lemmas.len() {
            return;
        }

        let removed_preds: FxHashSet<PredicateId> = self.lemmas[new_len..]
            .iter()
            .map(|lemma| lemma.predicate)
            .collect();
        self.lemmas.truncate(new_len);
        self.rebuild_lemma_keys();
        for pred in removed_preds {
            *self.lemma_revisions.entry(pred).or_default() += 1;
            self.predicate_constraint_cache.borrow_mut().remove(&pred);
        }
        self.debug_assert_frame_invariants();
    }

    /// Check if a lemma with given predicate and formula exists (O(1))
    /// Used by push_lemmas for fast duplicate checking (#1036, #1121).
    pub(crate) fn contains_lemma(&self, predicate: PredicateId, formula: &ChcExpr) -> bool {
        self.contains_lemma_with_hash(predicate, formula, formula.structural_hash())
    }

    /// Check if a lemma exists using a precomputed formula hash.
    ///
    /// Avoids redundant O(|formula|) `structural_hash()` tree walk when the
    /// caller already has the hash (e.g., from `Lemma.formula_hash`).
    /// Used by `push_lemmas` which indexes into `Lemma.formula_hash` directly.
    pub(crate) fn contains_lemma_with_hash(
        &self,
        predicate: PredicateId,
        formula: &ChcExpr,
        formula_hash: u64,
    ) -> bool {
        let key = (predicate.index(), formula_hash);
        // Collision safety (#2860): verify expression matches, not just hash.
        self.lemma_keys
            .get(&key)
            .is_some_and(|cached_expr| cached_expr == formula)
    }

    /// Get the conjunction of all lemmas for a predicate (from this frame only).
    ///
    /// Cached per-predicate with revision-based invalidation (#2815). Eliminates
    /// O(L) linear scan on repeated calls for the same predicate. Cache entries
    /// become stale when `lemma_revisions` for that predicate is bumped (on add
    /// or remove), and are recomputed lazily on next access.
    pub(crate) fn get_predicate_constraint(&self, pred: PredicateId) -> Option<ChcExpr> {
        let current_rev = self.lemma_revisions.get(&pred).copied().unwrap_or(0);

        // Fast path: return cached result if revision matches
        if let Some((cached_rev, cached_formula)) =
            self.predicate_constraint_cache.borrow().get(&pred)
        {
            if *cached_rev == current_rev {
                return Some(cached_formula.clone());
            }
        }

        // Cache miss or stale: recompute from lemmas
        let pred_lemmas: Vec<_> = self.lemmas.iter().filter(|l| l.predicate == pred).collect();

        if pred_lemmas.is_empty() {
            // Remove stale cache entry if present
            self.predicate_constraint_cache.borrow_mut().remove(&pred);
            None
        } else {
            let formula = ChcExpr::and_all(pred_lemmas.into_iter().map(|l| l.formula.clone()));
            self.predicate_constraint_cache
                .borrow_mut()
                .insert(pred, (current_rev, formula.clone()));
            Some(formula)
        }
    }

    // remove_blocking_lemmas_excluding_state and remove_lemmas_excluding_state
    // removed in #5653 Phase 1 (frame convergence trust). Re-implement for
    // Phase 2 (model refinement) from git history if needed.
}
