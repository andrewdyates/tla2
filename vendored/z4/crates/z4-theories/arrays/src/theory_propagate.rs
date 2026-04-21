// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Array theory ROW2 propagation implementation.
//!
//! Propagates `select(store(a, i, v), j) = select(a, j)` when `i ≠ j`.
//! Extracted from `theory_impl.rs` to keep each file under 500 lines.

use super::*;

impl ArraySolver<'_> {
    /// ROW2 propagation: `i ≠ j → select(store(a, i, v), j) = select(a, j)`.
    ///
    /// Scans equality terms for unassigned `(= select_a select_b)` atoms where
    /// one side reads through a store with a provably different index.
    pub(crate) fn propagate_impl(&mut self) -> Vec<TheoryPropagation> {
        self.populate_caches();

        #[derive(Clone)]
        struct SelectView {
            array: TermId,
            index: TermId,
            reason: Vec<TheoryLit>,
        }

        #[derive(Clone)]
        struct StoreView {
            base_array: TermId,
            store_index: TermId,
            reason: Vec<TheoryLit>,
        }

        // Use pre-built indices (eq_pair_index and eq_adj) instead of rebuilding per call
        let require_equal = |reasons: &mut Vec<TheoryLit>, t1: TermId, t2: TermId| -> bool {
            if t1 == t2 {
                return true;
            }
            let key = Self::ordered_pair(t1, t2);
            if let Some(&eq_term) = self.eq_pair_index.get(&key) {
                if self.assigns.get(&eq_term) == Some(&true) {
                    reasons.push(TheoryLit::new(eq_term, true));
                    return true;
                }
            }
            false
        };

        let require_distinct = |reasons: &mut Vec<TheoryLit>, t1: TermId, t2: TermId| -> bool {
            if t1 == t2 {
                return false;
            }
            let key = Self::ordered_pair(t1, t2);
            if let Some(&eq_term) = self.eq_pair_index.get(&key) {
                if self.assigns.get(&eq_term) == Some(&false) {
                    reasons.push(TheoryLit::new(eq_term, false));
                    return true;
                }
            }
            // Tautological: distinct constants or affine offsets (#5086).
            let t1_is_const = matches!(self.terms.get(t1), TermData::Const(_));
            let t2_is_const = matches!(self.terms.get(t2), TermData::Const(_));
            if t1_is_const && t2_is_const && t1 != t2 {
                return true;
            }
            // O(1) tautological affine offset (i vs i+1)
            if self.distinct_by_affine_offset(t1, t2) {
                return true;
            }
            // Do NOT fall through to diseq_set: external disequalities have no
            // reason terms and would produce incomplete justifications (#5086).
            false
        };

        let select_views_for = |term: TermId| -> Vec<SelectView> {
            let mut views = Vec::new();

            if let Some(&(array, index)) = self.select_cache.get(&term) {
                views.push(SelectView {
                    array,
                    index,
                    reason: Vec::new(),
                });
            }

            if let Some(neighbors) = self.eq_adj.get(&term) {
                for &(other, eq_term) in neighbors {
                    if let Some(&(array, index)) = self.select_cache.get(&other) {
                        let reason = if eq_term.is_sentinel() {
                            Vec::new()
                        } else {
                            vec![TheoryLit::new(eq_term, true)]
                        };
                        views.push(SelectView {
                            array,
                            index,
                            reason,
                        });
                    }
                }
            }

            views
        };

        let store_views_for = |array_term: TermId| -> Vec<StoreView> {
            let mut views = Vec::new();

            if let Some(&(base_array, store_index, _store_value)) =
                self.store_cache.get(&array_term)
            {
                views.push(StoreView {
                    base_array,
                    store_index,
                    reason: Vec::new(),
                });
            }

            if let Some(neighbors) = self.eq_adj.get(&array_term) {
                for &(other, eq_term) in neighbors {
                    if let Some(&(base_array, store_index, _store_value)) =
                        self.store_cache.get(&other)
                    {
                        let reason = if eq_term.is_sentinel() {
                            Vec::new()
                        } else {
                            vec![TheoryLit::new(eq_term, true)]
                        };
                        views.push(StoreView {
                            base_array,
                            store_index,
                            reason,
                        });
                    }
                }
            }

            views
        };

        let mut propagations = Vec::new();
        let mut select_views_cache: HashMap<TermId, Vec<SelectView>> = HashMap::new();
        let mut store_views_cache: HashMap<TermId, Vec<StoreView>> = HashMap::new();

        // ROW2 propagation (read-over-write different index):
        // i ≠ j → select(store(a, i, v), j) = select(a, j)
        // Sort for deterministic propagation order (#3060)
        let mut eq_entries: Vec<_> = self.equality_cache.iter().collect();
        eq_entries.sort_by_key(|(&term, _)| term.0);
        for (&eq_term, &(lhs, rhs)) in eq_entries {
            if self.assigns.get(&eq_term) == Some(&true) {
                continue;
            }

            if !select_views_cache.contains_key(&lhs) {
                select_views_cache.insert(lhs, select_views_for(lhs));
            }
            if !select_views_cache.contains_key(&rhs) {
                select_views_cache.insert(rhs, select_views_for(rhs));
            }
            let lhs_views = select_views_cache
                .get(&lhs)
                .expect("invariant: lhs select views inserted above");
            let rhs_views = select_views_cache
                .get(&rhs)
                .expect("invariant: rhs select views inserted above");

            let mut propagate_with_reasons = |mut reasons: Vec<TheoryLit>| {
                reasons.retain(|lit| lit.term != eq_term);
                // Skip propagations with no antecedents.
                if reasons.is_empty() {
                    return;
                }
                reasons.sort_by_key(|lit| (lit.term.0, lit.value));
                reasons.dedup_by_key(|lit| (lit.term, lit.value));
                propagations.push(TheoryPropagation {
                    literal: TheoryLit::new(eq_term, true),
                    reason: reasons,
                });
            };

            let mut did_propagate = false;

            for lv in lhs_views {
                if !store_views_cache.contains_key(&lv.array) {
                    store_views_cache.insert(lv.array, store_views_for(lv.array));
                }
                let store_views = store_views_cache
                    .get(&lv.array)
                    .expect("invariant: lhs store views inserted above");
                for store_view in store_views {
                    for rv in rhs_views {
                        let mut reasons: Vec<TheoryLit> = Vec::new();
                        reasons.extend(lv.reason.clone());
                        reasons.extend(rv.reason.clone());
                        reasons.extend(store_view.reason.clone());

                        if !require_equal(&mut reasons, lv.index, rv.index) {
                            continue;
                        }
                        if !require_equal(&mut reasons, rv.array, store_view.base_array) {
                            continue;
                        }
                        if !require_distinct(&mut reasons, lv.index, store_view.store_index) {
                            continue;
                        }

                        propagate_with_reasons(reasons);
                        did_propagate = true;
                        break;
                    }
                    if did_propagate {
                        break;
                    }
                }
                if did_propagate {
                    break;
                }
            }

            if did_propagate {
                continue;
            }

            for rv in rhs_views {
                if !store_views_cache.contains_key(&rv.array) {
                    store_views_cache.insert(rv.array, store_views_for(rv.array));
                }
                let store_views = store_views_cache
                    .get(&rv.array)
                    .expect("invariant: rhs store views inserted above");
                for store_view in store_views {
                    for lv in lhs_views {
                        let mut reasons: Vec<TheoryLit> = Vec::new();
                        reasons.extend(lv.reason.clone());
                        reasons.extend(rv.reason.clone());
                        reasons.extend(store_view.reason.clone());

                        if !require_equal(&mut reasons, lv.index, rv.index) {
                            continue;
                        }
                        if !require_equal(&mut reasons, lv.array, store_view.base_array) {
                            continue;
                        }
                        if !require_distinct(&mut reasons, rv.index, store_view.store_index) {
                            continue;
                        }

                        propagate_with_reasons(reasons);
                        did_propagate = true;
                        break;
                    }
                    if did_propagate {
                        break;
                    }
                }
                if did_propagate {
                    break;
                }
            }
        }

        let mut deduped = Vec::with_capacity(propagations.len());
        for propagation in propagations {
            let signature = (propagation.literal, propagation.reason.clone());
            if self.sent_propagations.insert(signature) {
                deduped.push(propagation);
            }
        }

        self.propagation_count += deduped.len() as u64;
        deduped
    }
}
