// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Equality propagation for the array theory solver.
//!
//! Implements Nelson-Oppen equality propagation derived from array axioms:
//! - ROW1/ROW2 select-store resolution
//! - Store-chain resolution
//! - Array congruence propagation
//! - Store value injectivity
//! - Effective store map decomposition
//! - Cross-chain resolution through asserted array equalities
//! - Store permutation equality detection

use super::*;

impl ArraySolver<'_> {
    /// Discover equalities implied by array axioms for Nelson-Oppen propagation (#4665).
    ///
    /// When `select(store(a, i, v), j)` and `i ≠ j` (including from external
    /// disequalities injected by the combined solver), ROW2 implies:
    ///   `select(store(a, i, v), j) = select(a, j)`
    ///
    /// When `select(store(a, i, v), j)` and `i = j`, ROW1 implies:
    ///   `select(store(a, i, v), j) = v`
    ///
    /// These discovered equalities are propagated to EUF so that transitive
    /// reasoning can detect conflicts (e.g., `sel1 = 42` and `sel2 ≠ 42`
    /// with ROW2-derived `sel1 = sel2`).
    pub(super) fn propagate_equalities_impl(&mut self) -> EqualityPropagationResult {
        self.populate_caches();
        // (#6820) Ensure equiv class cache is fresh for select_pair_index lookups.
        self.build_equiv_class_cache();

        // #6546: Short-circuit when the equality graph, term caches, and
        // external facts haven't changed since the last call. The sent_equalities
        // dedup set prevents returning duplicates, so if no new information was
        // added, the scan will find nothing new. This avoids O(n^2) re-scanning
        // on every N-O iteration when only the SAT assignment changed without
        // affecting the equality structure.
        let current_snapshot = (
            self.eq_adj_version,
            self.select_cache.len(),
            self.store_cache.len(),
            self.external_diseqs.len(),
            self.external_eqs.len(),
            self.diseq_set.len(),
        );
        if self.prop_eq_snapshot == Some(current_snapshot) {
            return EqualityPropagationResult::default();
        }
        let mut result = EqualityPropagationResult::default();
        // Seed seen set with previously-sent equalities to prevent re-discovery
        // across N-O fixpoint iterations (#5121).
        let mut seen_equalities = self.sent_equalities.clone();

        let mut push_equality = |lhs: TermId, rhs: TermId, mut reason: Vec<TheoryLit>| {
            if lhs == rhs {
                return;
            }
            let key = Self::ordered_pair(lhs, rhs);
            if seen_equalities.insert(key) {
                reason.sort_by_key(|lit| (lit.term.0, lit.value));
                reason.dedup_by_key(|lit| (lit.term, lit.value));
                result
                    .equalities
                    .push(DiscoveredEquality::new(lhs, rhs, reason));
            }
        };
        let proven_equal_reasons =
            |lhs: TermId, rhs: TermId| self.explain_equal_if_provable(lhs, rhs);

        for (&select_term, &(array, index)) in &self.select_cache {
            // Check if array is a store term (possibly through equalities)
            let store_info =
                if let Some(&(base, store_idx, store_val)) = self.store_cache.get(&array) {
                    Some((base, store_idx, store_val, Vec::new()))
                } else {
                    // Check through equality-linked store terms
                    self.eq_adj.get(&array).and_then(|neighbors| {
                        neighbors.iter().find_map(|&(other, _)| {
                            let &(base, store_idx, store_val) = self.store_cache.get(&other)?;
                            let reasons = proven_equal_reasons(array, other)?;
                            Some((base, store_idx, store_val, reasons))
                        })
                    })
                };

            let Some((base_array, store_idx, store_val, store_reasons)) = store_info else {
                continue;
            };

            if let Some(diseq_reasons) = self.explain_distinct_if_provable(index, store_idx) {
                // ROW2: select(store(a, i, v), j) = select(a, j) when i ≠ j

                // Case 1: direct select(base_array, index) lookup
                if let Some(&other_select) = self.select_pair_index.get(&(base_array, index)) {
                    if other_select != select_term {
                        let mut reasons = store_reasons.clone();
                        reasons.extend(diseq_reasons.clone());
                        push_equality(select_term, other_select, reasons);
                    }
                }

                // Case 2: select(equiv_member, index) where equiv_member = base_array
                if let Some(class_idx) = self.equiv_class_map.get(&base_array) {
                    if let Some(class) = self.equiv_classes.get(*class_idx) {
                        for &member in class {
                            if member == base_array {
                                continue;
                            }
                            if let Some(&other_select) =
                                self.select_pair_index.get(&(member, index))
                            {
                                if other_select != select_term {
                                    let Some(mut reasons) =
                                        proven_equal_reasons(member, base_array)
                                    else {
                                        continue;
                                    };
                                    reasons.extend(store_reasons.clone());
                                    reasons.extend(diseq_reasons.clone());
                                    push_equality(select_term, other_select, reasons);
                                }
                            }
                        }
                    }
                }
            } else if self.known_equal(index, store_idx) {
                // ROW1: select(store(a, i, v), i) = v
                let mut reasons = store_reasons.clone();
                reasons.extend(proven_equal_reasons(index, store_idx).unwrap_or_default());
                push_equality(select_term, store_val, reasons);
            }

            // Store-chain resolution
            if let Some((resolved_value, reasons)) =
                self.resolve_select_through_stores(array, index)
            {
                push_equality(select_term, resolved_value, reasons);
            }
        }

        // Store-chain resolution for N-O equality propagation (#5086, #6608).
        let select_entries: Vec<_> = self.select_cache.iter().map(|(&k, &v)| (k, v)).collect();
        type SelectReasonEntry = (TermId, Vec<TheoryLit>);
        type BaseSelectGroups = HashMap<(TermId, TermId), Vec<SelectReasonEntry>>;

        let mut base_groups: BaseSelectGroups = HashMap::new();
        let mut value_resolved: Vec<(TermId, TermId, Vec<TheoryLit>)> = Vec::new();
        for &(select_term, (array, index)) in &select_entries {
            let (resolution, reasons) =
                self.resolve_select_base_for_propagation_with_reasons(array, index);
            match resolution {
                SelectResolution::Value(val) => {
                    value_resolved.push((select_term, val, reasons));
                }
                SelectResolution::Base(base) => {
                    base_groups
                        .entry((base, index))
                        .or_default()
                        .push((select_term, reasons));
                }
                SelectResolution::Unresolved => {}
            }
        }
        for (select_term, val, reasons) in value_resolved {
            push_equality(select_term, val, reasons);
        }
        for (_key, group) in &base_groups {
            if group.len() < 2 {
                continue;
            }
            for i in 1..group.len() {
                let mut reasons = group[0].1.clone();
                reasons.extend(group[i].1.clone());
                push_equality(group[0].0, group[i].0, reasons);
            }
        }

        // Array congruence propagation (#5086).
        let mut array_to_selects: HashMap<TermId, Vec<(TermId, TermId)>> = HashMap::new();
        for &(select_term, (array, index)) in &select_entries {
            array_to_selects
                .entry(array)
                .or_default()
                .push((index, select_term));
        }
        for (&_eq_term, &(lhs, rhs)) in &self.equality_cache {
            if self.assigns.get(&_eq_term) != Some(&true) {
                continue;
            }
            if !matches!(self.terms.sort(lhs), Sort::Array(_)) {
                continue;
            }
            let lhs_selects = array_to_selects.get(&lhs).cloned().unwrap_or_default();
            let rhs_selects = array_to_selects.get(&rhs).cloned().unwrap_or_default();
            for &(idx_l, sel_l) in &lhs_selects {
                for &(idx_r, sel_r) in &rhs_selects {
                    let Some(mut reasons) = proven_equal_reasons(lhs, rhs) else {
                        continue;
                    };
                    let Some(idx_reasons) = proven_equal_reasons(idx_l, idx_r) else {
                        continue;
                    };
                    if sel_l != sel_r {
                        reasons.extend(idx_reasons);
                        push_equality(sel_l, sel_r, reasons);
                    }
                }
            }
        }
        // Transitive array equalities via eq_adj
        let array_terms: Vec<TermId> = array_to_selects.keys().copied().collect();
        for &arr in &array_terms {
            let equiv_class = self.get_equiv_class(arr);
            for &other_arr in &equiv_class {
                if other_arr == arr {
                    continue;
                }
                if let Some(other_selects) = array_to_selects.get(&other_arr) {
                    let arr_selects = array_to_selects.get(&arr).cloned().unwrap_or_default();
                    for &(idx_a, sel_a) in &arr_selects {
                        for &(idx_o, sel_o) in other_selects {
                            let Some(mut reasons) = proven_equal_reasons(arr, other_arr) else {
                                continue;
                            };
                            let Some(idx_reasons) = proven_equal_reasons(idx_a, idx_o) else {
                                continue;
                            };
                            if sel_a != sel_o {
                                reasons.extend(idx_reasons);
                                push_equality(sel_a, sel_o, reasons);
                            }
                        }
                    }
                }
            }
        }

        // Store value injectivity propagation (#6282).
        {
            let store_terms: Vec<TermId> = self.store_cache.keys().copied().collect();
            for &s1 in &store_terms {
                let &(_base1, idx1, val1) = match self.store_cache.get(&s1) {
                    Some(v) => v,
                    None => continue,
                };
                let equiv = self.get_equiv_class(s1);
                for s2 in equiv {
                    if s2 <= s1 {
                        continue;
                    }
                    let &(_base2, idx2, val2) = match self.store_cache.get(&s2) {
                        Some(v) => v,
                        None => continue,
                    };
                    if !self.known_equal(idx1, idx2) {
                        continue;
                    }
                    let Some(mut reasons) = proven_equal_reasons(s1, s2) else {
                        continue;
                    };
                    let Some(idx_reasons) = proven_equal_reasons(idx1, idx2) else {
                        continue;
                    };
                    reasons.extend(idx_reasons);
                    push_equality(val1, val2, reasons);
                }
            }
        }

        // Effective store map decomposition (#5086).
        for (&_eq_term, &(lhs, rhs)) in &self.equality_cache {
            if self.assigns.get(&_eq_term) != Some(&true) {
                continue;
            }
            if !matches!(self.terms.sort(lhs), Sort::Array(_)) {
                continue;
            }
            let lhs_map = self.collect_effective_stores(lhs);
            let rhs_map = self.collect_effective_stores(rhs);
            if let (Some((_base_a, map_a)), Some((_base_b, map_b))) = (lhs_map, rhs_map) {
                for &(idx_a, val_a) in &map_a {
                    for &(idx_b, val_b) in &map_b {
                        let Some(mut reasons) = proven_equal_reasons(lhs, rhs) else {
                            continue;
                        };
                        let Some(idx_reasons) = proven_equal_reasons(idx_a, idx_b) else {
                            continue;
                        };
                        reasons.extend(idx_reasons);
                        push_equality(val_a, val_b, reasons);
                    }
                }
            }
        }

        // Cross-chain resolution through asserted array equalities (#6282).
        {
            let mut select_indices: Vec<TermId> =
                select_entries.iter().map(|&(_, (_, idx))| idx).collect();
            select_indices.sort_by_key(|t| t.0);
            select_indices.dedup();

            let mut index_to_selects: HashMap<TermId, Vec<(TermId, TermId)>> = HashMap::new();
            for &(select_term, (array, index)) in &select_entries {
                index_to_selects
                    .entry(index)
                    .or_default()
                    .push((select_term, array));
            }

            let mut eq_pairs_seen: HashSet<(TermId, TermId)> = HashSet::new();
            let mut eq_pairs: Vec<(TermId, TermId)> = Vec::new();
            for (&_eq_term, &(lhs, rhs)) in &self.equality_cache {
                if self.assigns.get(&_eq_term) != Some(&true) {
                    continue;
                }
                if !matches!(self.terms.sort(lhs), Sort::Array(_)) {
                    continue;
                }
                let key = Self::ordered_pair(lhs, rhs);
                if eq_pairs_seen.insert(key) {
                    eq_pairs.push((lhs, rhs));
                }
            }

            for (lhs, rhs) in eq_pairs {
                let Some(array_eq_reasons) = proven_equal_reasons(lhs, rhs) else {
                    continue;
                };
                for &idx in &select_indices {
                    let (lhs_res, lhs_res_reasons) =
                        self.resolve_select_base_for_propagation_with_reasons(lhs, idx);
                    let (rhs_res, rhs_res_reasons) =
                        self.resolve_select_base_for_propagation_with_reasons(rhs, idx);

                    let selects_at_idx = index_to_selects.get(&idx).cloned().unwrap_or_default();

                    match (lhs_res, rhs_res) {
                        (SelectResolution::Base(base_l), SelectResolution::Base(base_r)) => {
                            if base_l == base_r {
                                continue;
                            }
                            let lhs_sels: Vec<(TermId, Vec<TheoryLit>)> = selects_at_idx
                                .iter()
                                .filter_map(|&(sel, arr)| {
                                    if arr == base_l {
                                        Some((sel, Vec::new()))
                                    } else {
                                        proven_equal_reasons(arr, base_l)
                                            .map(|reasons| (sel, reasons))
                                    }
                                })
                                .collect();
                            let rhs_sels: Vec<(TermId, Vec<TheoryLit>)> = selects_at_idx
                                .iter()
                                .filter_map(|&(sel, arr)| {
                                    if arr == base_r {
                                        Some((sel, Vec::new()))
                                    } else {
                                        proven_equal_reasons(arr, base_r)
                                            .map(|reasons| (sel, reasons))
                                    }
                                })
                                .collect();
                            for (sel_l, sel_l_reasons) in &lhs_sels {
                                for (sel_r, sel_r_reasons) in &rhs_sels {
                                    let mut reasons = array_eq_reasons.clone();
                                    reasons.extend(lhs_res_reasons.clone());
                                    reasons.extend(rhs_res_reasons.clone());
                                    reasons.extend(sel_l_reasons.clone());
                                    reasons.extend(sel_r_reasons.clone());
                                    push_equality(*sel_l, *sel_r, reasons);
                                }
                            }
                        }
                        (SelectResolution::Value(val_l), SelectResolution::Base(base_r)) => {
                            for &(sel, arr) in &selects_at_idx {
                                let Some(mut reasons) = (if arr == base_r {
                                    Some(Vec::new())
                                } else {
                                    proven_equal_reasons(arr, base_r)
                                }) else {
                                    continue;
                                };
                                reasons.extend(array_eq_reasons.clone());
                                reasons.extend(lhs_res_reasons.clone());
                                reasons.extend(rhs_res_reasons.clone());
                                push_equality(sel, val_l, reasons);
                            }
                        }
                        (SelectResolution::Base(base_l), SelectResolution::Value(val_r)) => {
                            for &(sel, arr) in &selects_at_idx {
                                let Some(mut reasons) = (if arr == base_l {
                                    Some(Vec::new())
                                } else {
                                    proven_equal_reasons(arr, base_l)
                                }) else {
                                    continue;
                                };
                                reasons.extend(array_eq_reasons.clone());
                                reasons.extend(lhs_res_reasons.clone());
                                reasons.extend(rhs_res_reasons.clone());
                                push_equality(sel, val_r, reasons);
                            }
                        }
                        (SelectResolution::Value(val_l), SelectResolution::Value(val_r)) => {
                            let mut reasons = array_eq_reasons.clone();
                            reasons.extend(lhs_res_reasons.clone());
                            reasons.extend(rhs_res_reasons.clone());
                            push_equality(val_l, val_r, reasons);
                        }
                        _ => {}
                    }
                }
            }
        }

        // Store permutation equality detection (#5086).
        {
            let mut chain_candidates: Vec<TermId> = Vec::new();
            for &(array, _index) in self.select_cache.values() {
                chain_candidates.push(array);
            }
            for (_eq_term, &(lhs, rhs)) in self.equality_cache.iter() {
                if matches!(self.terms.sort(lhs), Sort::Array(_)) {
                    chain_candidates.push(lhs);
                    chain_candidates.push(rhs);
                }
            }
            chain_candidates.sort();
            chain_candidates.dedup();

            let mut chain_maps: Vec<StoreChainEntry> = Vec::new();
            for array_term in &chain_candidates {
                if let Some((base, effective_map)) = self.collect_effective_stores(*array_term) {
                    if !effective_map.is_empty() {
                        chain_maps.push((*array_term, base, effective_map));
                    }
                }
            }

            // Group by base array and compare effective maps
            chain_maps.sort_by_key(|&(_, base, _)| base.0);
            let mut i = 0;
            while i < chain_maps.len() {
                let base = chain_maps[i].1;
                let mut j = i + 1;
                while j < chain_maps.len() && chain_maps[j].1 == base {
                    j += 1;
                }
                for a in i..j {
                    for b in (a + 1)..j {
                        let base_a = chain_maps[a].1;
                        let base_b = chain_maps[b].1;
                        let Some(mut reasons) = self.effective_stores_match_with_reasons(
                            &chain_maps[a].2,
                            &chain_maps[b].2,
                        ) else {
                            continue;
                        };
                        let Some(base_reasons) = proven_equal_reasons(base_a, base_b) else {
                            continue;
                        };
                        reasons.extend(base_reasons);
                        push_equality(chain_maps[a].0, chain_maps[b].0, reasons);
                    }
                }
                i = j;
            }

            // Cross-base equiv class store permutation
            for a in 0..chain_maps.len() {
                for b in (a + 1)..chain_maps.len() {
                    let base_a = chain_maps[a].1;
                    let base_b = chain_maps[b].1;
                    let Some(mut reasons) = self
                        .effective_stores_match_with_reasons(&chain_maps[a].2, &chain_maps[b].2)
                    else {
                        continue;
                    };
                    let Some(base_reasons) = proven_equal_reasons(base_a, base_b) else {
                        continue;
                    };
                    if base_a != base_b {
                        reasons.extend(base_reasons);
                        push_equality(chain_maps[a].0, chain_maps[b].0, reasons);
                    }
                }
            }
        }

        // Remember which equalities were sent so we don't resend them.
        self.sent_equalities = seen_equalities;
        // #6546: Save snapshot so the next call short-circuits if nothing changed.
        self.prop_eq_snapshot = Some(current_snapshot);
        result
    }
}
