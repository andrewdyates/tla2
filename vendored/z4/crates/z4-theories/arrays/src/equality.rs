// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Equality graph management for the array theory solver.
//!
//! Handles equality adjacency graph construction, incremental updates,
//! affine integer expression parsing, equivalence class caching, and
//! assignment recording.
//!
//! Query methods (known_equal, known_distinct, explanation generation)
//! are in `equality_query`.

use super::*;

impl ArraySolver<'_> {
    /// Return canonically ordered pair (min, max) for symmetric lookups
    pub(crate) fn ordered_pair(a: TermId, b: TermId) -> (TermId, TermId) {
        if a.0 <= b.0 {
            (a, b)
        } else {
            (b, a)
        }
    }

    pub(crate) fn is_equality_term(&self, term: TermId) -> bool {
        matches!(self.terms.get(term), TermData::App(sym, args) if sym.name() == "=" && args.len() == 2)
    }

    pub(crate) fn equality_assignment_affects_eq_graph(
        prev: Option<bool>,
        next: Option<bool>,
    ) -> bool {
        prev == Some(true) || next == Some(true)
    }

    fn warm_assignment_indices_ready(&self, term: TermId) -> bool {
        !self.dirty
            && !self.assign_dirty
            && self.populated_terms == self.terms.len()
            && self.equality_cache.contains_key(&term)
    }

    pub(crate) fn queue_pending_registered_equality(&mut self, term: TermId) {
        if !self.pending_registered_equalities.contains(&term) {
            self.pending_registered_equalities.push(term);
        }
    }

    pub(crate) fn apply_pending_registered_equalities(&mut self) {
        if self.assign_dirty || self.pending_registered_equalities.is_empty() {
            return;
        }

        let pending = std::mem::take(&mut self.pending_registered_equalities);
        for term in pending {
            debug_assert!(
                self.equality_cache.contains_key(&term),
                "arrays: pending late-registered equality missing from equality_cache"
            );
            if let Some(value) = self.assigns.get(&term).copied() {
                self.update_assignment_indices_incrementally(term, None, Some(value));
            }
        }
    }

    fn remove_eq_adj_edge(
        adj: &mut HashMap<TermId, Vec<(TermId, TermId)>>,
        from: TermId,
        to: TermId,
        eq_term: TermId,
    ) {
        let remove_entry = if let Some(neighbors) = adj.get_mut(&from) {
            neighbors.retain(|&(other, existing_term)| !(other == to && existing_term == eq_term));
            neighbors.is_empty()
        } else {
            false
        };
        if remove_entry {
            adj.remove(&from);
        }
    }

    fn replace_eq_adj_edge(
        adj: &mut HashMap<TermId, Vec<(TermId, TermId)>>,
        from: TermId,
        to: TermId,
        old_eq_term: TermId,
        new_eq_term: TermId,
    ) {
        let Some(neighbors) = adj.get_mut(&from) else {
            return;
        };
        for entry in neighbors.iter_mut() {
            if *entry == (to, old_eq_term) {
                *entry = (to, new_eq_term);
                return;
            }
        }
    }

    fn find_alternative_equality_term(
        &self,
        lhs: TermId,
        rhs: TermId,
        value: bool,
        exclude: TermId,
    ) -> Option<TermId> {
        self.equality_cache
            .iter()
            .find_map(|(&eq_term, &(eq_lhs, eq_rhs))| {
                let same_pair = Self::ordered_pair(eq_lhs, eq_rhs) == Self::ordered_pair(lhs, rhs);
                if eq_term != exclude && same_pair && self.assigns.get(&eq_term) == Some(&value) {
                    Some(eq_term)
                } else {
                    None
                }
            })
    }

    pub(crate) fn add_true_equality_edge(&mut self, lhs: TermId, rhs: TermId, eq_term: TermId) {
        self.eq_adj.entry(lhs).or_default().push((rhs, eq_term));
        self.eq_adj.entry(rhs).or_default().push((lhs, eq_term));
    }

    fn update_assignment_indices_incrementally(
        &mut self,
        term: TermId,
        prev: Option<bool>,
        next: Option<bool>,
    ) {
        let Some(&(lhs, rhs)) = self.equality_cache.get(&term) else {
            return;
        };
        let key = Self::ordered_pair(lhs, rhs);

        match prev {
            Some(true) if next != Some(true) => {
                if let Some(replacement) = self.find_alternative_equality_term(lhs, rhs, true, term)
                {
                    Self::replace_eq_adj_edge(&mut self.eq_adj, lhs, rhs, term, replacement);
                    Self::replace_eq_adj_edge(&mut self.eq_adj, rhs, lhs, term, replacement);
                } else {
                    Self::remove_eq_adj_edge(&mut self.eq_adj, lhs, rhs, term);
                    Self::remove_eq_adj_edge(&mut self.eq_adj, rhs, lhs, term);
                }
            }
            Some(false) if next != Some(false) => {
                let has_alternative_false = self
                    .find_alternative_equality_term(lhs, rhs, false, term)
                    .is_some();
                if !has_alternative_false && !self.external_diseqs.contains(&key) {
                    self.diseq_set.remove(&key);
                }
            }
            _ => {}
        }

        match next {
            Some(true) if prev != Some(true) => {
                if self
                    .find_alternative_equality_term(lhs, rhs, true, term)
                    .is_none()
                {
                    self.add_true_equality_edge(lhs, rhs, term);
                }
            }
            Some(false) if prev != Some(false) => {
                self.diseq_set.insert(key);
            }
            _ => {}
        }

        if Self::equality_assignment_affects_eq_graph(prev, next) {
            self.note_eq_graph_changed();
        }
    }

    pub(crate) fn note_eq_graph_changed(&mut self) {
        self.eq_adj_version = self.eq_adj_version.wrapping_add(1);
        self.equiv_class_cache_version = None;
    }

    fn merge_affine_terms(
        lhs: &mut HashMap<String, BigInt>,
        rhs: &HashMap<String, BigInt>,
        sign: i32,
    ) {
        for (symbol, coeff) in rhs {
            let signed = if sign >= 0 {
                coeff.clone()
            } else {
                -coeff.clone()
            };
            let entry = lhs.entry(symbol.clone()).or_insert_with(|| BigInt::from(0));
            *entry += signed;
            if *entry == BigInt::from(0) {
                lhs.remove(symbol);
            }
        }
    }

    fn scale_affine(expr: &mut AffineIntExpr, factor: &BigInt) {
        expr.1 *= factor;
        for coeff in expr.0.values_mut() {
            *coeff *= factor;
        }
        expr.0.retain(|_, coeff| *coeff != BigInt::from(0));
    }

    fn parse_affine_int_expr(&self, term: TermId) -> Option<Rc<AffineIntExpr>> {
        if let Some(cached) = self.affine_int_expr_cache.borrow().get(&term).cloned() {
            return cached;
        }

        let parsed = match self.terms.get(term) {
            TermData::Const(Constant::Int(n)) => Some((HashMap::new(), n.clone())),
            TermData::Var(name, _) => {
                let mut vars = HashMap::new();
                vars.insert(name.clone(), BigInt::from(1));
                Some((vars, BigInt::from(0)))
            }
            TermData::App(Symbol::Named(name), args) => match name.as_str() {
                "+" => {
                    let mut vars = HashMap::new();
                    let mut constant = BigInt::from(0);
                    for &arg in args {
                        let parsed_arg = self.parse_affine_int_expr(arg)?;
                        let (arg_vars, arg_const) = parsed_arg.as_ref();
                        Self::merge_affine_terms(&mut vars, arg_vars, 1);
                        constant += arg_const;
                    }
                    Some((vars, constant))
                }
                "-" if args.len() == 1 => {
                    let mut expr = self.parse_affine_int_expr(args[0])?.as_ref().clone();
                    Self::scale_affine(&mut expr, &BigInt::from(-1));
                    Some(expr)
                }
                "-" if args.len() >= 2 => {
                    let mut expr = self.parse_affine_int_expr(args[0])?.as_ref().clone();
                    for &arg in &args[1..] {
                        let parsed_arg = self.parse_affine_int_expr(arg)?;
                        let (arg_vars, arg_const) = parsed_arg.as_ref();
                        Self::merge_affine_terms(&mut expr.0, arg_vars, -1);
                        expr.1 -= arg_const;
                    }
                    Some(expr)
                }
                "*" => {
                    let mut const_factor = BigInt::from(1);
                    let mut non_constant: Option<AffineIntExpr> = None;
                    for &arg in args {
                        let parsed_arg = self.parse_affine_int_expr(arg)?;
                        let parsed = parsed_arg.as_ref();
                        if parsed.0.is_empty() {
                            const_factor *= &parsed.1;
                        } else if non_constant.is_none() {
                            non_constant = Some(parsed.clone());
                        } else {
                            return None;
                        }
                    }
                    let mut expr = non_constant.unwrap_or((HashMap::new(), BigInt::from(1)));
                    Self::scale_affine(&mut expr, &const_factor);
                    Some(expr)
                }
                _ => None,
            },
            _ => None,
        }
        .map(Rc::new);

        self.affine_int_expr_cache
            .borrow_mut()
            .insert(term, parsed.clone());
        parsed
    }

    /// Detect tautological disequalities from affine offset structure:
    /// two affine forms with identical variable coefficients but different
    /// constants (for example `i` vs `i + 1`, `(+ i 1)` vs `(+ i 2)`).
    ///
    /// This is O(1) per call (cached parse) and is needed in the propagation
    /// path where the arithmetic theory may not have propagated disequalities
    /// yet.  The expensive affine BFS (`affine_forms_with_reasons`,
    /// `distinct_by_equality_substituted_affine`) was removed in #6820.
    pub(crate) fn distinct_by_affine_offset(&self, t1: TermId, t2: TermId) -> bool {
        let Some(lhs) = self.parse_affine_int_expr(t1) else {
            return false;
        };
        let Some(rhs) = self.parse_affine_int_expr(t2) else {
            return false;
        };
        let lhs = lhs.as_ref();
        let rhs = rhs.as_ref();
        lhs.0 == rhs.0 && lhs.1 != rhs.1
    }

    /// Detect arithmetic equalities that hold by affine normalization.
    ///
    /// This lets array ROW reasoning treat duplicated arithmetic expressions
    /// (for example two independent `(+ i 1)` terms) as equal even when they
    /// were parsed into distinct TermIds.
    pub(crate) fn equal_by_affine_form(&self, t1: TermId, t2: TermId) -> bool {
        let Some(lhs) = self.parse_affine_int_expr(t1) else {
            return false;
        };
        let Some(rhs) = self.parse_affine_int_expr(t2) else {
            return false;
        };
        let lhs = lhs.as_ref();
        let rhs = rhs.as_ref();
        lhs.0 == rhs.0 && lhs.1 == rhs.1
    }

    /// Rebuild disequality set and adjacency list from current assignments.
    pub(crate) fn rebuild_assign_indices(&mut self) {
        if !self.assign_dirty {
            return;
        }

        #[cfg(test)]
        {
            self.assign_index_rebuilds += 1;
        }

        self.diseq_set.clear();
        self.eq_adj.clear();

        // Sort by eq_term for deterministic adjacency/disequality construction (#3060)
        let mut eq_entries: Vec<_> = self.equality_cache.iter().collect();
        eq_entries.sort_by_key(|(&term, _)| term.0);
        for (&eq_term, &(lhs, rhs)) in eq_entries {
            match self.assigns.get(&eq_term) {
                Some(&true) => {
                    self.eq_adj.entry(lhs).or_default().push((rhs, eq_term));
                    self.eq_adj.entry(rhs).or_default().push((lhs, eq_term));
                }
                Some(&false) => {
                    let key = Self::ordered_pair(lhs, rhs);
                    self.diseq_set.insert(key);
                }
                None => {}
            }
        }

        // Merge external disequalities from combined solver (#4665)
        for &key in &self.external_diseqs {
            self.diseq_set.insert(key);
        }

        // Merge external equalities from combined solver (#4665)
        let sentinel = TermId::SENTINEL;
        for &(t1, t2) in &self.external_eqs {
            self.eq_adj.entry(t1).or_default().push((t2, sentinel));
            self.eq_adj.entry(t2).or_default().push((t1, sentinel));
        }

        self.pending_registered_equalities.clear();
        self.assign_dirty = false;
    }

    /// Compute equivalence classes from eq_adj using connected components.
    /// Reuses the previous cache until the equality graph connectivity changes.
    pub(crate) fn build_equiv_class_cache(&mut self) {
        debug_assert!(
            !self.assign_dirty,
            "arrays: build_equiv_class_cache called before rebuild_assign_indices"
        );
        if self.equiv_class_cache_version == Some(self.eq_adj_version) {
            return;
        }

        self.equiv_class_map.clear();
        self.equiv_classes.clear();

        for &start in self.eq_adj.keys() {
            if self.equiv_class_map.contains_key(&start) {
                continue;
            }
            let class_idx = self.equiv_classes.len();
            let mut class = Vec::new();
            let mut queue = vec![start];

            while let Some(t) = queue.pop() {
                if self.equiv_class_map.contains_key(&t) {
                    continue;
                }
                self.equiv_class_map.insert(t, class_idx);
                class.push(t);
                if let Some(neighbors) = self.eq_adj.get(&t) {
                    for &(other, _) in neighbors {
                        if !self.equiv_class_map.contains_key(&other) {
                            queue.push(other);
                        }
                    }
                }
            }

            self.equiv_classes.push(class);
        }

        self.equiv_class_cache_version = Some(self.eq_adj_version);
        #[cfg(test)]
        {
            self.equiv_class_cache_builds += 1;
        }
    }

    /// Record an assignment with trail support
    pub(crate) fn record_assignment(&mut self, term: TermId, value: bool) {
        match self.assigns.get(&term).copied() {
            Some(prev) if prev == value => {}
            prev => {
                self.trail.push((term, prev));
                self.assigns.insert(term, value);
                if self.is_equality_term(term) {
                    if self.warm_assignment_indices_ready(term) {
                        self.update_assignment_indices_incrementally(term, prev, Some(value));
                    } else if !self.dirty
                        && !self.assign_dirty
                        && term.index() >= self.populated_terms
                    {
                        self.queue_pending_registered_equality(term);
                    } else {
                        self.assign_dirty = true;
                        if Self::equality_assignment_affects_eq_graph(prev, Some(value)) {
                            self.note_eq_graph_changed();
                        }
                    }
                    // Event-driven self-store (#6820): when an equality involving
                    // a store term is assigned true, queue for check_self_store.
                    if value {
                        if let Some(&(lhs, rhs)) = self.equality_cache.get(&term) {
                            if self.store_cache.contains_key(&lhs) {
                                self.pending_self_store.push((term, lhs));
                            }
                            if self.store_cache.contains_key(&rhs) {
                                self.pending_self_store.push((term, rhs));
                            }
                        }
                    }
                }
            }
        }
    }
}
