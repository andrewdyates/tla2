// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Store-related and structural axiom conflict checkers.
//!
//! Implements detection of:
//! - Store chain resolution
//! - Conflicting store equalities (extensionality)
//! - Disjunctive store-target equalities
//! - Nested select conflicts
//! - Const-array read axiom
//! - Self-store detection
//! - Array equality conflicts

use super::*;

impl ArraySolver<'_> {
    /// Check for conflicts by resolving select terms through store chains (#4304).
    pub(crate) fn check_store_chain_resolution(&self) -> Option<TheoryResult> {
        let mut selects: Vec<_> = self.select_cache.iter().collect();
        selects.sort_by_key(|(&term, _)| term.0);

        for (&select_term, &(array, index)) in &selects {
            if let Some((resolved_value, mut reasons)) =
                self.resolve_select_through_stores(array, index)
            {
                if let Some(val_diseq_reasons) =
                    self.explain_distinct_if_provable(select_term, resolved_value)
                {
                    reasons.extend(val_diseq_reasons);
                    reasons.sort_by_key(|lit| (lit.term.0, lit.value));
                    reasons.dedup_by_key(|lit| (lit.term, lit.value));

                    if reasons.is_empty() {
                        continue;
                    }
                    return Self::conflict_reasons_to_lemma(reasons);
                }
            }
        }
        None
    }

    fn stores_in_equiv_class(&self, equiv: &[TermId]) -> Vec<(TermId, TermId, TermId, TermId)> {
        equiv
            .iter()
            .filter_map(|&member| {
                self.store_cache
                    .get(&member)
                    .map(|&(base, idx, val)| (member, base, idx, val))
            })
            .collect()
    }

    fn conflicting_store_pair_reasons(
        &self,
        first: (TermId, TermId, TermId, TermId),
        second: (TermId, TermId, TermId, TermId),
    ) -> Option<Vec<TheoryLit>> {
        let (s1, base1, idx1, val1) = first;
        let (s2, base2, idx2, val2) = second;
        if !self.known_equal(base1, base2) || !self.known_equal(idx1, idx2) {
            return None;
        }

        let val_diseq_reasons = self.explain_distinct_if_provable(val1, val2)?;

        let mut reasons = Vec::new();
        if let Some(eq) = self.get_eq_term(s1, s2) {
            reasons.push(TheoryLit::new(eq, true));
        }
        if base1 != base2 {
            if let Some(eq) = self.get_eq_term(base1, base2) {
                reasons.push(TheoryLit::new(eq, true));
            }
        }
        if idx1 != idx2 {
            if let Some(eq) = self.get_eq_term(idx1, idx2) {
                reasons.push(TheoryLit::new(eq, true));
            }
        }
        reasons.extend(val_diseq_reasons);
        if reasons.is_empty() {
            return None;
        }
        Some(reasons)
    }

    /// Check for conflicting store equalities (#4304).
    pub(crate) fn check_conflicting_store_equalities(&self) -> Option<TheoryResult> {
        let mut checked_classes: HashSet<TermId> = HashSet::new();
        for &store_term in self.store_cache.keys() {
            let equiv = self.get_equiv_class(store_term);
            let repr = equiv.iter().copied().min().unwrap_or(store_term);
            if !checked_classes.insert(repr) {
                continue;
            }
            let stores_in_class = self.stores_in_equiv_class(&equiv);
            for (i, first) in stores_in_class.iter().enumerate() {
                for second in stores_in_class.iter().skip(i + 1) {
                    if let Some(reasons) = self.conflicting_store_pair_reasons(*first, *second) {
                        return Self::conflict_reasons_to_lemma(reasons);
                    }
                }
            }
        }
        None
    }

    /// Check direct `store(base, idx, val) = target` equalities for the
    /// disjunctive consequence `idx1 = idx2 ∨ base = target` (#5086, #6885).
    pub(crate) fn check_disjunctive_store_target_equalities(&mut self) -> Option<TheoryResult> {
        let mut grouped: HashMap<(TermId, TermId), Vec<(TermId, TermId)>> = HashMap::new();
        let mut eq_entries: Vec<_> = self.equality_cache.iter().collect();
        eq_entries.sort_by_key(|(&eq_term, _)| eq_term.0);

        for (&eq_term, &(lhs, rhs)) in &eq_entries {
            if self.assigns.get(&eq_term) != Some(&true) {
                continue;
            }
            let direct_store_eq = if let Some(&(base, idx, _val)) = self.store_cache.get(&lhs) {
                Some((base, idx, rhs))
            } else if let Some(&(base, idx, _val)) = self.store_cache.get(&rhs) {
                Some((base, idx, lhs))
            } else {
                None
            };
            let Some((base, idx, target)) = direct_store_eq else {
                continue;
            };
            grouped
                .entry((base, target))
                .or_default()
                .push((eq_term, idx));
        }

        let mut groups: Vec<_> = grouped.into_iter().collect();
        groups.sort_by_key(|&((base, target), _)| (base.0, target.0));

        for ((base, target), mut store_eqs) in groups {
            if self.known_equal(base, target) {
                continue;
            }
            store_eqs.sort_by_key(|&(eq_term, idx)| (eq_term.0, idx.0));

            for (i, &(eq_i, idx_i)) in store_eqs.iter().enumerate() {
                for &(eq_j, idx_j) in store_eqs.iter().skip(i + 1) {
                    if idx_i == idx_j || self.known_equal(idx_i, idx_j) {
                        continue;
                    }

                    let idx_eq = self.get_eq_term(idx_i, idx_j);
                    let base_eq = self.get_eq_term(base, target);

                    if let (Some(idx_eq), Some(base_eq)) = (idx_eq, base_eq) {
                        let idx_sat = self.assigns.get(&idx_eq) == Some(&true);
                        let base_sat = self.assigns.get(&base_eq) == Some(&true);
                        if idx_sat || base_sat {
                            continue;
                        }

                        let mut clause = vec![
                            TheoryLit::new(eq_i, false),
                            TheoryLit::new(eq_j, false),
                            TheoryLit::new(idx_eq, true),
                            TheoryLit::new(base_eq, true),
                        ];
                        clause.sort_by_key(|lit| (lit.term.0, lit.value));
                        clause.dedup_by_key(|lit| (lit.term, lit.value));
                        return Some(TheoryResult::NeedLemmas(vec![TheoryLemma::new(clause)]));
                    }

                    let mut requests = Vec::new();
                    for (lhs, rhs) in [(idx_i, idx_j), (base, target)] {
                        if self.known_equal(lhs, rhs) || self.get_eq_term(lhs, rhs).is_some() {
                            continue;
                        }
                        let key = Self::ordered_pair(lhs, rhs);
                        if self.requested_model_eqs.insert(key) {
                            requests.push(ModelEqualityRequest {
                                lhs,
                                rhs,
                                reason: vec![
                                    TheoryLit::new(eq_i, true),
                                    TheoryLit::new(eq_j, true),
                                ],
                            });
                        }
                    }

                    match requests.len() {
                        0 => {}
                        1 => {
                            return Some(TheoryResult::NeedModelEquality(
                                requests.pop().expect("invariant: len checked above"),
                            ));
                        }
                        _ => return Some(TheoryResult::NeedModelEqualities(requests)),
                    }
                }
            }
        }

        None
    }

    /// Check conflicts via nested select simplification.
    pub(crate) fn check_nested_select_conflicts(&self) -> Option<TheoryResult> {
        struct NormalizedSelectState {
            select_term: TermId,
            normalized: Option<(TermId, TermId)>,
            eq_terms: Vec<TermId>,
            diseq_reasons: Vec<TheoryLit>,
        }

        let candidate_pairs = self.select_conflict_candidate_pairs();

        let mut needed: HashSet<TermId> = HashSet::with_capacity(candidate_pairs.len() * 2);
        for &(s1, s2) in &candidate_pairs {
            needed.insert(s1);
            needed.insert(s2);
        }
        let select_terms: HashMap<_, _> = needed
            .iter()
            .copied()
            .map(|select_term| {
                let (normalized, eq_terms, diseq_reasons) = self.normalize_select(select_term);
                (
                    select_term,
                    NormalizedSelectState {
                        select_term,
                        normalized,
                        eq_terms,
                        diseq_reasons,
                    },
                )
            })
            .collect();

        for (sel1_term, sel2_term) in candidate_pairs {
            let Some(sel1) = select_terms.get(&sel1_term) else {
                continue;
            };
            let Some(sel2) = select_terms.get(&sel2_term) else {
                continue;
            };

            if let (Some((base1, idx1)), Some((base2, idx2))) = (sel1.normalized, sel2.normalized) {
                let same_base = base1 == base2 || self.known_equal(base1, base2);
                let same_index = idx1 == idx2 || self.known_equal(idx1, idx2);

                if same_base && same_index {
                    let Some(sel_diseq_reasons) =
                        self.explain_distinct_if_provable(sel1.select_term, sel2.select_term)
                    else {
                        continue;
                    };

                    let mut reasons = sel_diseq_reasons;

                    reasons.extend(sel1.diseq_reasons.iter().copied());
                    reasons.extend(sel2.diseq_reasons.iter().copied());

                    for &eq_term in &sel1.eq_terms {
                        reasons.push(TheoryLit::new(eq_term, true));
                    }
                    for &eq_term in &sel2.eq_terms {
                        reasons.push(TheoryLit::new(eq_term, true));
                    }

                    if base1 != base2 {
                        if let Some(eq_term) = self.get_eq_term(base1, base2) {
                            reasons.push(TheoryLit::new(eq_term, true));
                        }
                    }

                    if idx1 != idx2 {
                        if let Some(eq_term) = self.get_eq_term(idx1, idx2) {
                            reasons.push(TheoryLit::new(eq_term, true));
                        }
                    }

                    return Self::conflict_reasons_to_lemma(reasons);
                }
            }
        }
        None
    }

    /// Check const-array read axiom:
    /// select(const-array(v), i) = v for any index i.
    ///
    /// Event-driven (#6546 Step 1): processes `pending_const_reads` queue.
    pub(crate) fn check_const_array_read(&mut self) -> Option<TheoryResult> {
        let pairs = std::mem::take(&mut self.pending_const_reads);
        let mut sorted = pairs;
        sorted.sort_by_key(|&(sel, _)| sel.0);
        sorted.dedup();

        let mut retained = Vec::new();
        for (select_term, const_array_term) in sorted {
            if let Some(&default_val) = self.const_array_cache.get(&const_array_term) {
                if let Some(val_diseq_reasons) =
                    self.explain_distinct_if_provable(select_term, default_val)
                {
                    if val_diseq_reasons.is_empty() {
                        retained.push((select_term, const_array_term));
                        continue;
                    }
                    self.pending_const_reads = retained;
                    return Self::conflict_reasons_to_lemma(val_diseq_reasons);
                }
            }
            retained.push((select_term, const_array_term));
        }
        self.pending_const_reads = retained;
        None
    }

    /// Check self-store conflicts:
    /// If store(a, i, v) = a is asserted, then select(a, i) must equal v.
    pub(crate) fn check_self_store(&mut self) -> Option<TheoryResult> {
        let mut pairs = std::mem::take(&mut self.pending_self_store);
        pairs.sort_unstable_by_key(|&(eq, st)| (eq.0, st.0));
        pairs.dedup();

        let mut retained = Vec::new();
        let mut iter = pairs.into_iter();
        while let Some((eq_term, store_term)) = iter.next() {
            if self.assigns.get(&eq_term) != Some(&true) {
                continue;
            }

            let Some(&(lhs, rhs)) = self.equality_cache.get(&eq_term) else {
                continue;
            };
            let base_term = if lhs == store_term {
                rhs
            } else if rhs == store_term {
                lhs
            } else {
                continue;
            };

            let Some(&(store_base, store_idx, store_val)) = self.store_cache.get(&store_term)
            else {
                continue;
            };

            if !self.known_equal(base_term, store_base) {
                retained.push((eq_term, store_term));
                continue;
            }

            let mut candidate_selects = Vec::with_capacity(2);
            if let Some(select_term) = self.get_exact_select_term(base_term, store_idx) {
                candidate_selects.push(select_term);
            }
            if store_base != base_term {
                if let Some(select_term) = self.get_exact_select_term(store_base, store_idx) {
                    if !candidate_selects.contains(&select_term) {
                        candidate_selects.push(select_term);
                    }
                }
            }
            candidate_selects.sort_unstable_by_key(|term| term.0);
            candidate_selects.dedup();

            let mut fallback_selects: Vec<_> = self.select_cache.keys().copied().collect();
            fallback_selects.sort_unstable_by_key(|term| term.0);
            fallback_selects.retain(|term| !candidate_selects.contains(term));

            for select_term in candidate_selects
                .iter()
                .copied()
                .chain(fallback_selects.into_iter())
            {
                let Some(&(sel_array, sel_index)) = self.select_cache.get(&select_term) else {
                    continue;
                };
                if !self.known_equal(sel_array, base_term)
                    && !self.known_equal(sel_array, store_base)
                {
                    continue;
                }
                if !self.known_equal(sel_index, store_idx) {
                    continue;
                }

                if let Some(val_diseq_reasons) =
                    self.explain_distinct_if_provable(select_term, store_val)
                {
                    let mut reasons = val_diseq_reasons;

                    reasons.push(TheoryLit::new(eq_term, true));

                    if sel_array != base_term && sel_array != store_base {
                        if let Some(arr_eq) = self.get_eq_term(sel_array, base_term) {
                            reasons.push(TheoryLit::new(arr_eq, true));
                        } else if let Some(arr_eq) = self.get_eq_term(sel_array, store_base) {
                            reasons.push(TheoryLit::new(arr_eq, true));
                        }
                    }

                    if base_term != store_base {
                        if let Some(base_eq) = self.get_eq_term(base_term, store_base) {
                            reasons.push(TheoryLit::new(base_eq, true));
                        }
                    }

                    if sel_index != store_idx {
                        if let Some(idx_eq) = self.get_eq_term(sel_index, store_idx) {
                            reasons.push(TheoryLit::new(idx_eq, true));
                        }
                    }

                    if reasons.is_empty() {
                        continue;
                    }

                    retained.extend(iter);
                    self.pending_self_store = retained;
                    return Self::conflict_reasons_to_lemma(reasons);
                }
            }

            retained.push((eq_term, store_term));
        }
        self.pending_self_store = retained;
        None
    }

    /// Check array equality conflicts:
    /// If a = b is asserted, then for any index i where we have both select(a, i) and select(b, i),
    /// they must be equal.
    pub(crate) fn check_array_equality(&self) -> Option<TheoryResult> {
        let mut array_selects: HashMap<TermId, Vec<(TermId, TermId)>> = HashMap::new();
        let mut sorted_selects: Vec<_> = self.select_cache.iter().collect();
        sorted_selects.sort_by_key(|(&term, _)| term.0);
        for (&select_term, &(array, index)) in sorted_selects {
            array_selects
                .entry(array)
                .or_default()
                .push((index, select_term));
        }

        let mut eq_entries: Vec<_> = self.equality_cache.iter().collect();
        eq_entries.sort_by_key(|(&term, _)| term.0);
        for (&eq_term, &(lhs, rhs)) in eq_entries {
            if self.assigns.get(&eq_term) == Some(&true) {
                if let (Some(lhs_selects), Some(rhs_selects)) =
                    (array_selects.get(&lhs), array_selects.get(&rhs))
                {
                    for &(idx1, sel1) in lhs_selects {
                        for &(idx2, sel2) in rhs_selects {
                            if let Some(sel_diseq_reasons) = {
                                if !self.known_equal(idx1, idx2) {
                                    None
                                } else {
                                    self.explain_distinct_if_provable(sel1, sel2)
                                }
                            } {
                                let mut reasons = sel_diseq_reasons;
                                reasons.push(TheoryLit::new(eq_term, true));

                                if idx1 != idx2 {
                                    if let Some(idx_eq) = self.get_eq_term(idx1, idx2) {
                                        reasons.push(TheoryLit::new(idx_eq, true));
                                    }
                                }

                                return Self::conflict_reasons_to_lemma(reasons);
                            }
                        }
                    }
                }
            }
        }
        None
    }
}
