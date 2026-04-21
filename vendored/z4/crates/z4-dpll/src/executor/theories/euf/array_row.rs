// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Read-over-write (ROW/ROW2b) array axiom generation.
//!
//! Extracted from `array_patterns.rs` as part of code-health module split.
//! ROW (downward): `select(store(A,i,v), k)` decomposes by index equality.
//! ROW2b (upward): `select(A, j)` propagates to `select(store(A,i,v), j)`.

use super::super::super::Executor;
#[cfg(not(kani))]
use hashbrown::HashMap;
#[cfg(kani)]
use z4_core::kani_compat::DetHashMap as HashMap;
use z4_core::{TermData, TermId};

impl Executor {
    /// Collect `select(store(a, i, v), k)` patterns that participate in ROW.
    #[allow(clippy::type_complexity)]
    fn collect_array_row_patterns(&self) -> Vec<(TermId, TermId, TermId, TermId, TermId)> {
        let mut patterns = Vec::new();
        for idx in 0..self.ctx.terms.len() {
            let select_term = TermId(idx as u32);
            if !self.term_in_array_scope(select_term) {
                continue;
            }

            let (array, sel_index) =
                if let TermData::App(ref sym, ref args) = self.ctx.terms.get(select_term).clone() {
                    if sym.name() == "select" && args.len() == 2 {
                        (args[0], args[1])
                    } else {
                        continue;
                    }
                } else {
                    continue;
                };

            let (base_array, store_index, store_value) =
                if let TermData::App(ref sym, ref args) = self.ctx.terms.get(array).clone() {
                    if sym.name() == "store" && args.len() == 3 {
                        (args[0], args[1], args[2])
                    } else {
                        continue;
                    }
                } else {
                    continue;
                };

            if store_index == sel_index {
                continue;
            }

            patterns.push((select_term, base_array, store_index, store_value, sel_index));
        }
        patterns
    }

    pub(in crate::executor) fn seed_array_row_terms(&mut self) -> bool {
        let before = self.ctx.terms.len();
        for (_, base_array, _, _, sel_index) in self.collect_array_row_patterns() {
            let _ = self.ctx.terms.mk_select(base_array, sel_index);
        }
        self.ctx.terms.len() != before
    }

    /// Add eager read-over-write clauses for already-seeded ROW patterns.
    pub(in crate::executor) fn add_array_row_clauses(&mut self) {
        let top_level_disequalities = self.collect_top_level_disequalities();
        for (select_term, base_array, store_index, store_value, sel_index) in
            self.collect_array_row_patterns()
        {
            let indices_provably_distinct = self.are_terms_provably_distinct_from_assertions(
                store_index,
                sel_index,
                &top_level_disequalities,
            );

            let base_select = self.ctx.terms.mk_select(base_array, sel_index);
            let row2_eq = self.ctx.terms.mk_eq(select_term, base_select);

            if indices_provably_distinct {
                // If `i != k` is already established, ROW1 is tautological and
                // ROW2 collapses to a unit equality.
                self.push_array_axiom_assertion(row2_eq);
                continue;
            }

            // Create (= store_index sel_index)
            let idx_eq = self.ctx.terms.mk_eq(store_index, sel_index);
            let not_idx_eq = self.ctx.terms.mk_not(idx_eq);

            // ROW1 clause: ¬(= i k) ∨ (= select_term v)
            // "If the indices are equal, the select returns the stored value"
            let row1_eq = self.ctx.terms.mk_eq(select_term, store_value);
            let row1_clause = self.ctx.terms.mk_or(vec![not_idx_eq, row1_eq]);
            self.push_array_axiom_assertion(row1_clause);

            // ROW2 clause: (= i k) ∨ (= select_term (select base_array sel_index))
            // "If the indices differ, the select passes through to the base array"
            // Note: mk_select may simplify if base_array is also a store with known index
            let row2_clause = self.ctx.terms.mk_or(vec![idx_eq, row2_eq]);
            self.push_array_axiom_assertion(row2_clause);
        }
    }

    pub(in crate::executor) fn add_array_row_lemmas(&mut self) {
        while self.seed_array_row_terms() {}
        self.add_array_row_clauses();
    }

    /// Add Axiom 2b (upward select propagation through store parents).
    ///
    /// Z3 reference: `theory_array.cpp:212-221`, `instantiate_axiom2b`.
    ///
    /// For every `select(A, j)` where `A` is the base array of some store term
    /// `B = store(A, i, v)`, asserts:
    ///   `(= i j) ∨ (= (select A j) (select B j))`
    ///
    /// This "upward" propagation complements the existing "downward" propagation
    /// in `add_array_row_lemmas` (which handles `select(store(A,i,v), j)` → `select(A,j)`).
    /// For deeply nested `_nf_` store expressions where intermediate stores are
    /// subterms (not named variables with explicit equality assertions), the downward
    /// propagation alone cannot create the select terms needed to chain through
    /// multiple nesting levels.
    ///
    /// Upward propagation ensures that a select on a base array is connected to
    /// the same index on all store results built from that base, enabling the
    /// fixpoint loop to fully resolve through nested store chains (#6282).
    ///
    /// Returns the number of axioms added (for budget tracking).
    /// Duplicate axioms across rounds are harmless — the caller deduplicates
    /// assertions after the fixpoint loop completes.
    #[allow(clippy::type_complexity)]
    fn collect_array_row2b_context(
        &self,
    ) -> (
        HashMap<TermId, Vec<(TermId, TermId, TermId, Option<TermId>)>>,
        HashMap<TermId, (TermId, Option<TermId>)>,
        Vec<(TermId, TermId, TermId)>,
    ) {
        // Build parent-stores index: base_array -> [(store, index, value, guard)].
        // The guard is present for non-definitional aliases so ROW2b only fires
        // when the store equality itself is active.
        let mut parent_stores: HashMap<TermId, Vec<(TermId, TermId, TermId, Option<TermId>)>> =
            HashMap::new();
        // Store-alias map: for equalities (= X store(...)), map
        // store_term -> (alias, optional guard equality).
        let mut store_aliases: HashMap<TermId, (TermId, Option<TermId>)> = HashMap::new();
        for idx in 0..self.ctx.terms.len() {
            let term_id = TermId(idx as u32);
            if !self.term_in_array_scope(term_id) {
                continue;
            }
            match self.ctx.terms.get(term_id).clone() {
                TermData::App(ref sym, ref args) if sym.name() == "store" && args.len() == 3 => {
                    parent_stores
                        .entry(args[0])
                        .or_default()
                        .push((term_id, args[1], args[2], None));
                }
                TermData::App(ref sym, ref args) if sym.name() == "=" && args.len() == 2 => {
                    let (lhs, rhs) = (args[0], args[1]);
                    let lhs_is_store = matches!(
                        self.ctx.terms.get(lhs),
                        TermData::App(ref s, ref a) if s.name() == "store" && a.len() == 3
                    );
                    let rhs_is_store = matches!(
                        self.ctx.terms.get(rhs),
                        TermData::App(ref s, ref a) if s.name() == "store" && a.len() == 3
                    );
                    if rhs_is_store {
                        let guard = if lhs_is_store { Some(term_id) } else { None };
                        store_aliases.insert(rhs, (lhs, guard));
                    }
                    if lhs_is_store {
                        let guard = if rhs_is_store { Some(term_id) } else { None };
                        store_aliases.insert(lhs, (rhs, guard));
                    }
                }
                _ => {}
            }
        }

        // Extend parent_stores for store aliases. Definitional aliases are
        // unconditional; store-store equalities are guarded by the equality atom.
        for (&store_term, &(alias, guard)) in &store_aliases {
            if let TermData::App(ref sym, ref args) = self.ctx.terms.get(store_term).clone() {
                if sym.name() == "store" && args.len() == 3 {
                    parent_stores
                        .entry(alias)
                        .or_default()
                        .push((store_term, args[1], args[2], guard));
                }
            }
        }

        if parent_stores.is_empty() {
            return (parent_stores, store_aliases, Vec::new());
        }

        // Collect select terms: (select_term, array, index)
        let mut selects: Vec<(TermId, TermId, TermId)> = Vec::new();
        for idx in 0..self.ctx.terms.len() {
            let term_id = TermId(idx as u32);
            if !self.term_in_array_scope(term_id) {
                continue;
            }
            if let TermData::App(ref sym, ref args) = self.ctx.terms.get(term_id).clone() {
                if sym.name() == "select" && args.len() == 2 {
                    selects.push((term_id, args[0], args[1]));
                }
            }
        }

        (parent_stores, store_aliases, selects)
    }

    pub(in crate::executor) fn seed_array_row2b_terms(&mut self, budget: usize) -> usize {
        let (parent_stores, store_aliases, selects) = self.collect_array_row2b_context();
        if parent_stores.is_empty() {
            return 0;
        }

        let mut seeded = 0_usize;
        for (_, array, sel_index) in &selects {
            let Some(stores) = parent_stores.get(array) else {
                continue;
            };
            for &(store_term, store_index, _store_value, _guard) in stores {
                if seeded >= budget {
                    return seeded;
                }
                if store_index == *sel_index {
                    continue;
                }

                let before = self.ctx.terms.len();
                let upward_select = self.ctx.terms.mk_select(store_term, *sel_index);
                if self.ctx.terms.len() != before {
                    seeded += 1;
                    if seeded >= budget {
                        return seeded;
                    }
                }

                if let Some(&(alias, _alias_guard)) = store_aliases.get(&store_term) {
                    let before = self.ctx.terms.len();
                    let alias_select = self.ctx.terms.mk_select(alias, *sel_index);
                    if alias_select != upward_select && self.ctx.terms.len() != before {
                        seeded += 1;
                    }
                }
            }
        }
        seeded
    }

    #[allow(clippy::type_complexity)]
    pub(in crate::executor) fn add_array_row2b_clauses(&mut self, budget: usize) -> usize {
        let (parent_stores, store_aliases, selects) = self.collect_array_row2b_context();
        if parent_stores.is_empty() {
            return 0;
        }

        // For each select(A, j), check if A is the base of any store(A, i, v) = B.
        // Budget prevents O(selects × stores) blowup on large formulas (#6282).
        let mut added = 0_usize;
        for (select_term, array, sel_index) in &selects {
            let Some(stores) = parent_stores.get(array) else {
                continue;
            };
            for &(store_term, store_index, _store_value, guard) in stores {
                if added >= budget {
                    return added;
                }
                // Skip if indices are syntactically identical (ROW1 handles this via mk_select)
                if store_index == *sel_index {
                    continue;
                }

                let idx_eq = self.ctx.terms.mk_eq(store_index, *sel_index);
                let upward_select = self.ctx.terms.mk_select(store_term, *sel_index);

                let sel_eq = self.ctx.terms.mk_eq(*select_term, upward_select);
                let axiom = if let Some(eq_term) = guard {
                    let neg_guard = self.ctx.terms.mk_not(eq_term);
                    self.ctx.terms.mk_or(vec![neg_guard, idx_eq, sel_eq])
                } else {
                    self.ctx.terms.mk_or(vec![idx_eq, sel_eq])
                };
                self.push_array_axiom_assertion(axiom);
                added += 1;

                if let Some(&(alias, alias_guard)) = store_aliases.get(&store_term) {
                    if added >= budget {
                        return added;
                    }
                    let alias_select = self.ctx.terms.mk_select(alias, *sel_index);
                    if alias_select != upward_select {
                        let alias_sel_eq = self.ctx.terms.mk_eq(*select_term, alias_select);
                        let alias_axiom = if let Some(alias_eq) = alias_guard {
                            let neg = self.ctx.terms.mk_not(alias_eq);
                            self.ctx.terms.mk_or(vec![neg, idx_eq, alias_sel_eq])
                        } else {
                            self.ctx.terms.mk_or(vec![idx_eq, alias_sel_eq])
                        };
                        self.push_array_axiom_assertion(alias_axiom);
                        added += 1;
                    }
                }
            }
        }
        added
    }

    pub(in crate::executor) fn add_array_row2b_upward_lemmas(&mut self, budget: usize) -> usize {
        let _ = self.seed_array_row2b_terms(budget);
        self.add_array_row2b_clauses(budget)
    }
}
