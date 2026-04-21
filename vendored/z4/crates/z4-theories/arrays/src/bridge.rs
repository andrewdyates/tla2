// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Cross-theory bridge helpers for `ArraySolver`.
//!
//! Extracted from `lib.rs` to reduce crate root size.
//! Contains: `SelectResolution`, `UndecidedIndexPair`, `undecided_index_pairs`,
//! external equality/disequality injection, `notify_equality`, and
//! `set_defer_expensive_checks`.

use super::*;

/// A pair of array index terms whose equality/disequality is undecided.
///
/// Result of relaxed store chain resolution for equality propagation (#5086).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SelectResolution {
    /// Resolved to a concrete value via ROW1 or const-array.
    Value(TermId),
    /// Reached a base array (not a store) — `select(base, index)` is the result.
    Base(TermId),
    /// Could not resolve (unknown index relationships or iteration limit).
    Unresolved,
}

/// When the array solver encounters `select(store(a, i, v), j)` and
/// cannot determine whether `i = j` or `i ≠ j`, it reports this pair
/// so the combined solver can consult arithmetic theories (#4665).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct UndecidedIndexPair {
    /// First index (store index)
    pub idx1: TermId,
    /// Second index (select index)
    pub idx2: TermId,
}

impl ArraySolver<'_> {
    /// Return index pairs from `select(store(a, i, v), j)` patterns where
    /// neither `i = j` nor `i ≠ j` is known to this solver.
    ///
    /// The combined solver (e.g., AufLiaSolver) uses these to query LIA
    /// for arithmetic-derived disequalities and propagate them back (#4665).
    pub fn undecided_index_pairs(&mut self) -> Vec<UndecidedIndexPair> {
        self.populate_caches();
        let mut pairs = Vec::new();
        let mut seen = HashSet::new();

        for &(array, index) in self.select_cache.values() {
            // Walk through store chains looking for undecided index pairs.
            // Limit must accommodate the longest store chain in the formula
            // (storecomm benchmarks have 60+ stores) (#5086).
            let mut current = array;
            let mut iterations = 0;
            const MAX_ITERATIONS: usize = 200;

            loop {
                iterations += 1;
                if iterations > MAX_ITERATIONS {
                    break;
                }

                if let Some(&(base, store_idx, _)) = self.store_cache.get(&current) {
                    if !self.known_equal(index, store_idx) && !self.known_distinct(index, store_idx)
                    {
                        let key = if index.0 <= store_idx.0 {
                            (index, store_idx)
                        } else {
                            (store_idx, index)
                        };
                        if seen.insert(key) {
                            pairs.push(UndecidedIndexPair {
                                idx1: store_idx,
                                idx2: index,
                            });
                        }
                    }
                    current = base;
                    continue;
                }

                // Also check through equality-linked store terms
                if let Some(neighbors) = self.eq_adj.get(&current) {
                    let mut found_store = false;
                    for &(other, _) in neighbors {
                        if let Some(&(base, store_idx, _)) = self.store_cache.get(&other) {
                            if !self.known_equal(index, store_idx)
                                && !self.known_distinct(index, store_idx)
                            {
                                let key = if index.0 <= store_idx.0 {
                                    (index, store_idx)
                                } else {
                                    (store_idx, index)
                                };
                                if seen.insert(key) {
                                    pairs.push(UndecidedIndexPair {
                                        idx1: store_idx,
                                        idx2: index,
                                    });
                                }
                            }
                            current = base;
                            found_store = true;
                            break;
                        }
                    }
                    if !found_store {
                        break;
                    }
                } else {
                    break;
                }
            }
        }

        pairs
    }

    /// Inject an external disequality `t1 ≠ t2` learned from another theory.
    ///
    /// This is used by the combined solver when LIA determines that two
    /// array indices are distinct (e.g., from `y = x + 1`). The disequality
    /// is persisted across `rebuild_assign_indices()` calls (#4665).
    ///
    /// Returns `true` if the disequality was new (not already known).
    pub fn assert_external_disequality(&mut self, t1: TermId, t2: TermId) -> bool {
        let key = Self::ordered_pair(t1, t2);
        let is_new = self.external_diseqs.insert(key);
        self.diseq_set.insert(key);
        is_new
    }

    /// Inject a reason-carrying external disequality `t1 ≠ t2` (#6546).
    ///
    /// Unlike `assert_external_disequality`, this stores the `TheoryLit` reasons
    /// from the arithmetic solver's tight bounds. `explain_distinct_if_provable()`
    /// can then use these reasons to justify ROW2 store-chain skips and conflict
    /// clauses, which is required for lazy ROW on AUFLIA paths.
    ///
    /// Returns `true` if the disequality was new (not already known).
    pub fn assert_external_disequality_with_reasons(
        &mut self,
        t1: TermId,
        t2: TermId,
        reasons: Vec<TheoryLit>,
    ) -> bool {
        let key = Self::ordered_pair(t1, t2);
        let is_new = self.external_diseqs.insert(key);
        self.diseq_set.insert(key);
        if !reasons.is_empty() {
            self.external_diseq_reasons.insert(key, reasons);
        }
        is_new
    }

    /// Check if a model equality for this index pair was already requested
    /// by `propagate_array_index_info` (#6546 Packet 4).
    ///
    /// Used to prevent the N-O fixpoint from re-requesting the same
    /// unresolved pairs when the LIA trivial model assigns all indices
    /// to the same value.
    pub fn model_equality_already_requested(&self, t1: TermId, t2: TermId) -> bool {
        let key = Self::ordered_pair(t1, t2);
        self.requested_model_eqs.contains(&key)
    }

    /// Mark a model equality for this index pair as requested (#6546 Packet 4).
    pub fn mark_model_equality_requested(&mut self, t1: TermId, t2: TermId) {
        let key = Self::ordered_pair(t1, t2);
        self.requested_model_eqs.insert(key);
    }

    /// Inject an external equality `t1 = t2` learned from another theory.
    ///
    /// This is used by the combined solver when LIA or EUF determines that
    /// two array-relevant terms are equal. The equality is added to the
    /// internal adjacency list so that `known_equal()` returns true (#4665).
    pub fn assert_external_equality(&mut self, t1: TermId, t2: TermId) {
        // Persist so it survives rebuild_assign_indices() calls
        self.external_eqs.push((t1, t2));
        let sentinel = TermId::SENTINEL;
        self.eq_adj.entry(t1).or_default().push((t2, sentinel));
        self.eq_adj.entry(t2).or_default().push((t1, sentinel));
        self.note_eq_graph_changed();
    }

    /// Notify the array solver that two terms have become equal.
    ///
    /// If both terms have associated `ArrayVarData`, cross-products their
    /// stores × selects and queues ROW2 axioms into `pending_axioms` (with
    /// fingerprint dedup). This is Z4's equivalent of Z3's `merge_eh` →
    /// `add_parent_select` / `add_store` pipeline (#6546 Approach B).
    ///
    /// The queued axioms are returned as `NeedLemmas` from the next `check()`.
    pub fn notify_equality(&mut self, a: TermId, b: TermId) {
        // Ensure term caches are populated so array_vars are current.
        self.populate_caches();

        if a == b {
            return;
        }

        let a_data = self.array_vars.get(&a).cloned();
        let b_data = self.array_vars.get(&b).cloned();

        // Cross-product: stores from a × selects from b, and vice versa.
        // Enqueue both ROW2 down axioms and ROW1 candidates (#6546 event-driven).
        // ROW1 is queued on stores_as_result × parent_selects only (not
        // parent_stores), because ROW1 requires the select to read from the
        // store result, not from the store's base array.
        if let (Some(ref ad), Some(ref bd)) = (&a_data, &b_data) {
            for &store in &ad.stores_as_result {
                for &select in &bd.parent_selects {
                    self.queue_row2_down_axiom(store, select);
                    self.pending_row1.push((select, store));
                }
            }
            for &store in &bd.stores_as_result {
                for &select in &ad.parent_selects {
                    self.queue_row2_down_axiom(store, select);
                    self.pending_row1.push((select, store));
                }
            }
            // Also cross parent_stores (upward direction): stores whose base
            // is a × selects from b, and vice versa. ROW2 only — NOT ROW1.
            // parent_stores are stores whose BASE is this array. The select reads
            // from the base, not from the store result.
            for &store in &ad.parent_stores {
                for &select in &bd.parent_selects {
                    self.queue_row2_down_axiom(store, select);
                    // ROW2 upward: select on base, store on base (#6820).
                    self.pending_row2_upward.push((select, store));
                }
            }
            for &store in &bd.parent_stores {
                for &select in &ad.parent_selects {
                    self.queue_row2_down_axiom(store, select);
                    // ROW2 upward: select on base, store on base (#6820).
                    self.pending_row2_upward.push((select, store));
                }
            }
        }

        // Event-driven const-array reads: if a or b is a const-array,
        // selects on the other now see it through the equality.
        if self.const_array_cache.contains_key(&a) {
            if let Some(ref bd) = b_data {
                for &select in &bd.parent_selects {
                    self.pending_const_reads.push((select, a));
                }
            }
        }
        if self.const_array_cache.contains_key(&b) {
            if let Some(ref ad) = a_data {
                for &select in &ad.parent_selects {
                    self.pending_const_reads.push((select, b));
                }
            }
        }

        // Merge b's data into a's ArrayVarData (append-only).
        if b_data.is_some() {
            self.array_var_merge_log.push((a, b));
            Self::merge_array_var_data(&mut self.array_vars, a, b);
        }
    }

    /// Enable deferred expensive checks mode (#6282 Packet 2).
    ///
    /// When enabled, `check()` skips O(n²) checks (ROW2 upward, ROW2 extended,
    /// nested select conflicts). The combined solver must call `final_check()`
    /// after the N-O fixpoint converges to run these deferred checks.
    pub fn set_defer_expensive_checks(&mut self, defer: bool) {
        self.defer_expensive_checks = defer;
    }
}
