// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Incremental cache registration and queue maintenance for `ArraySolver`.
//!
//! Extracted from `lib.rs` to reduce crate root size.
//! Contains: `clear_term_caches`, `row2_fingerprint_seen`, `queue_row2_down_axiom`,
//! `register_select`, `register_store`, `merge_array_var_data`, `register_term`,
//! `debug_array_var_data_matches_caches`, and `populate_caches`.

use super::*;

impl ArraySolver<'_> {
    pub(crate) fn clear_term_caches(&mut self) {
        self.select_cache.clear();
        self.select_pair_index.clear();
        self.store_cache.clear();
        self.const_array_cache.clear();
        self.equality_cache.clear();
        self.term_to_equalities.clear();
        self.eq_pair_index.clear();
        self.array_vars.clear();
        self.array_var_merge_log.clear();
        self.affine_int_expr_cache.borrow_mut().clear();
        // axiom_fingerprints / row2_fingerprint_indices are NOT cleared here.
        // They track which exact `(store, select_index)` pairs have already had
        // ROW2 work queued. Since the resulting SAT clauses are permanent
        // (survive push/pop), re-queuing the same exact axiom after a dirty
        // rebuild causes infinite NeedLemmas cycling in the DPLL(T) refinement
        // loop (#6703). Cleared indirectly via reset().
        self.pending_axioms.clear();
        self.blocked_axioms.clear();
        self.blocked_axiom_term_gen = 0;
        self.pending_const_reads.clear();
        self.pending_row1.clear();
        self.pending_row2_upward.clear();
        self.pending_self_store.clear();
        self.pending_registered_equalities.clear();
        self.populated_terms = 0;
    }

    pub(crate) fn row2_fingerprint_seen(&self, store: TermId, select_index: TermId) -> bool {
        self.axiom_fingerprints.contains(&(store, select_index))
            || self
                .row2_fingerprint_indices
                .get(&store)
                .is_some_and(|indices| {
                    indices
                        .iter()
                        .copied()
                        .any(|existing_index| self.known_equal(existing_index, select_index))
                })
    }

    pub(crate) fn queue_row2_down_axiom(&mut self, store: TermId, select: TermId) {
        let Some(&(_, select_index)) = self.select_cache.get(&select) else {
            return;
        };
        if self.row2_fingerprint_seen(store, select_index) {
            return;
        }

        self.axiom_fingerprints.insert((store, select_index));
        self.row2_fingerprint_indices
            .entry(store)
            .or_default()
            .push(select_index);
        self.pending_axioms
            .push(PendingAxiom::Row2Down { store, select });
    }

    pub(crate) fn register_select(&mut self, select_term: TermId, array: TermId) {
        let (stores_as_result, parent_stores) = {
            let data = self.array_vars.entry(array).or_default();
            data.parent_selects.push(select_term);
            data.prop_upward |= !data.parent_stores.is_empty();
            (data.stores_as_result.clone(), data.parent_stores.clone())
        };

        for store in &stores_as_result {
            self.queue_row2_down_axiom(*store, select_term);
            // ROW1: select reads from an array that IS a store result.
            // Queue for event-driven check_row1 (#6546 revised ROW1 design).
            self.pending_row1.push((select_term, *store));
        }

        // ROW2 upward: select on base array A, stores whose base is A.
        // Queue (select, store) for event-driven check_row2_upward (#6820).
        for &store in &parent_stores {
            self.pending_row2_upward.push((select_term, store));
        }

        // Event-driven const-array reads (#6546 Step 1): if the select's
        // array is a const-array, enqueue for check_const_array_read().
        if self.const_array_cache.contains_key(&array) {
            self.pending_const_reads.push((select_term, array));
        }
    }

    pub(crate) fn register_store(&mut self, store_term: TermId, base_array: TermId) {
        let base_parent_selects = {
            let base_data = self.array_vars.entry(base_array).or_default();
            base_data.parent_stores.push(store_term);
            base_data.prop_upward |= !base_data.parent_selects.is_empty();
            base_data.parent_selects.clone()
        };

        let result_parent_selects = {
            let result_data = self.array_vars.entry(store_term).or_default();
            result_data.stores_as_result.push(store_term);
            result_data.parent_selects.clone()
        };

        for select in result_parent_selects {
            self.queue_row2_down_axiom(store_term, select);
            // ROW1: existing selects now read from this store (#6546 revised design).
            self.pending_row1.push((select, store_term));
        }

        // ROW2 upward: new store on base array A, existing selects on A.
        // Queue (select, store) for event-driven check_row2_upward (#6820).
        for &select in &base_parent_selects {
            self.pending_row2_upward.push((select, store_term));
        }

        // Event-driven self-store (#6820): check if any existing equality
        // involving this store term is already assigned true.
        // Uses the reverse index for O(eq_count) lookup instead of O(|equality_cache|).
        if let Some(eq_terms) = self.term_to_equalities.get(&store_term) {
            for &eq_term in eq_terms {
                if self.assigns.get(&eq_term) == Some(&true) {
                    self.pending_self_store.push((eq_term, store_term));
                }
            }
        }
    }

    pub(crate) fn merge_array_var_data(
        array_vars: &mut HashMap<TermId, ArrayVarData>,
        target: TermId,
        source: TermId,
    ) {
        let Some(source_data) = array_vars.get(&source).cloned() else {
            return;
        };

        let target_data = array_vars.entry(target).or_default();
        for store in source_data.stores_as_result {
            if !target_data.stores_as_result.contains(&store) {
                target_data.stores_as_result.push(store);
            }
        }
        for select in source_data.parent_selects {
            if !target_data.parent_selects.contains(&select) {
                target_data.parent_selects.push(select);
            }
        }
        for store in source_data.parent_stores {
            if !target_data.parent_stores.contains(&store) {
                target_data.parent_stores.push(store);
            }
        }
        target_data.prop_upward =
            !target_data.parent_selects.is_empty() && !target_data.parent_stores.is_empty();
    }

    pub(crate) fn register_term(&mut self, term_id: TermId) {
        if let TermData::App(sym, args) = self.terms.get(term_id) {
            match sym.name() {
                "select" if args.len() == 2 => {
                    self.select_cache.insert(term_id, (args[0], args[1]));
                    let previous = self.select_pair_index.insert((args[0], args[1]), term_id);
                    debug_assert!(
                        previous.is_none() || previous == Some(term_id),
                        "arrays: duplicate exact select lookup for ({}, {})",
                        args[0],
                        args[1]
                    );
                    self.register_select(term_id, args[0]);
                }
                "store" if args.len() == 3 => {
                    self.store_cache
                        .insert(term_id, (args[0], args[1], args[2]));
                    self.register_store(term_id, args[0]);
                }
                "const-array" if args.len() == 1 => {
                    self.const_array_cache.insert(term_id, args[0]);
                }
                "=" if args.len() == 2 => {
                    self.equality_cache.insert(term_id, (args[0], args[1]));
                    self.term_to_equalities
                        .entry(args[0])
                        .or_default()
                        .push(term_id);
                    self.term_to_equalities
                        .entry(args[1])
                        .or_default()
                        .push(term_id);
                    let key = Self::ordered_pair(args[0], args[1]);
                    self.eq_pair_index.insert(key, term_id);
                    if self.assigns.get(&term_id) == Some(&true) {
                        if self.store_cache.contains_key(&args[0]) {
                            self.pending_self_store.push((term_id, args[0]));
                        }
                        if self.store_cache.contains_key(&args[1]) {
                            self.pending_self_store.push((term_id, args[1]));
                        }
                    }
                }
                _ => {}
            }
        }
    }

    #[cfg(debug_assertions)]
    pub(crate) fn debug_array_var_data_matches_caches(&self) -> bool {
        let mut expected: HashMap<TermId, ArrayVarData> = HashMap::new();

        for (&store_term, &(base_array, _, _)) in &self.store_cache {
            expected
                .entry(base_array)
                .or_default()
                .parent_stores
                .push(store_term);
            expected
                .entry(store_term)
                .or_default()
                .stores_as_result
                .push(store_term);
        }

        for (&select_term, &(array, _)) in &self.select_cache {
            expected
                .entry(array)
                .or_default()
                .parent_selects
                .push(select_term);
        }

        for data in expected.values_mut() {
            data.stores_as_result.sort_unstable_by_key(|term| term.0);
            data.parent_selects.sort_unstable_by_key(|term| term.0);
            data.parent_stores.sort_unstable_by_key(|term| term.0);
            data.prop_upward = !data.parent_selects.is_empty() && !data.parent_stores.is_empty();
        }

        for &(target, source) in &self.array_var_merge_log {
            Self::merge_array_var_data(&mut expected, target, source);
        }

        // Re-sort after merge replay (merge appends items that break sort order).
        for data in expected.values_mut() {
            data.stores_as_result.sort_unstable_by_key(|term| term.0);
            data.parent_selects.sort_unstable_by_key(|term| term.0);
            data.parent_stores.sort_unstable_by_key(|term| term.0);
        }

        let mut actual = self.array_vars.clone();
        for data in actual.values_mut() {
            data.stores_as_result.sort_unstable_by_key(|term| term.0);
            data.parent_selects.sort_unstable_by_key(|term| term.0);
            data.parent_stores.sort_unstable_by_key(|term| term.0);
        }

        expected == actual
    }

    #[cfg(not(debug_assertions))]
    pub(crate) fn debug_array_var_data_matches_caches(&self) -> bool {
        true
    }

    /// Populate caches by incrementally scanning new terms.
    pub(crate) fn populate_caches(&mut self) {
        if self.dirty {
            self.clear_term_caches();
            self.dirty = false;
        }

        if self.populated_terms < self.terms.len() {
            for idx in self.populated_terms..self.terms.len() {
                self.register_term(TermId(idx as u32));
            }
            self.populated_terms = self.terms.len();
            self.apply_pending_registered_equalities();
        }

        debug_assert!(
            self.debug_array_var_data_matches_caches(),
            "arrays: incremental array_vars tracking diverged from caches"
        );
        self.rebuild_assign_indices();
    }
}
