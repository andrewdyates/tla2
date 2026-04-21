// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model extraction for the array theory solver.
//!
//! Builds `ArrayInterpretation` from store chains, const-array terms, and
//! select-derived entries for use in satisfying model output.

use super::*;

impl ArraySolver<'_> {
    /// Extract an array model from the current solver state (#6047, #7022).
    ///
    /// Walks store chains, const-array terms, and select cache entries to build
    /// `ArrayInterpretation` for each tracked array. `term_values` maps term IDs
    /// to their string representations in the current model.
    ///
    /// Select-derived entries (#7022): For base arrays without stores, selects
    /// are the only source of index→value mappings. When EUF derives index
    /// equality (e.g., `x = y`), both `select(a, x)` and `select(a, y)` should
    /// resolve to the same value. By adding select-derived entries keyed by
    /// concrete index value, EUF-equal indices naturally deduplicate.
    pub fn extract_model(&mut self, term_values: &HashMap<TermId, String>) -> ArrayModel {
        let mut model = ArrayModel::default();

        // For each array term that has a store chain or const-array base,
        // reconstruct its interpretation.
        for (&arr_term, _) in &self.array_vars {
            let mut interp = ArrayInterpretation::default();
            let mut current = arr_term;

            // Walk the store chain backwards to collect stores
            while let Some(&(base, idx, val)) = self.store_cache.get(&current) {
                let idx_str = term_values.get(&idx).cloned().unwrap_or_default();
                let val_str = term_values.get(&val).cloned().unwrap_or_default();
                if !idx_str.is_empty() && !val_str.is_empty() {
                    interp.stores.push((idx_str, val_str));
                }
                current = base;
            }

            // Check for const-array default
            if let Some(&default_term) = self.const_array_cache.get(&current) {
                if let Some(val_str) = term_values.get(&default_term) {
                    interp.default = Some(val_str.clone());
                }
            }

            if !interp.stores.is_empty() || interp.default.is_some() {
                model.array_values.insert(arr_term, interp);
            }
        }

        // Add select-derived entries (#7022): for base arrays without explicit
        // stores, selects provide index→value mappings from the EUF model.
        for (&select_term, &(array_term, index_term)) in &self.select_cache {
            // Find the base array by peeling stores
            let mut base = array_term;
            while let Some(&(inner_base, _, _)) = self.store_cache.get(&base) {
                base = inner_base;
            }

            let idx_str = match term_values.get(&index_term) {
                Some(s) if !s.is_empty() => s.clone(),
                _ => continue,
            };
            let val_str = match term_values.get(&select_term) {
                Some(s) if !s.is_empty() => s.clone(),
                _ => continue,
            };

            let interp = model.array_values.entry(base).or_default();
            // Only add if this index isn't already covered by a store entry
            // (stores are authoritative — they define the array's content).
            if !interp.stores.iter().any(|(k, _)| k == &idx_str) {
                interp.stores.push((idx_str, val_str));
            }
        }

        // #7435: Propagate interpretations across EUF equivalence classes.
        // When UF establishes equality between array terms (e.g.,
        // seq_array(seq_empty) = const_array(0)), terms in the same class
        // should share the same interpretation. Without this, a UF application
        // like seq_array(seq_empty) gets no interpretation even though its
        // EUF-equal partner const_array(0) has one with a default value.
        if !self.eq_adj.is_empty() && !self.assign_dirty {
            self.build_equiv_class_cache();
            // For each equivalence class, find the richest interpretation
            // (prefer one with a default, then most stores) and propagate it
            // to all class members that lack one.
            for class in &self.equiv_classes {
                // Find the best interpretation in this class
                let best = class
                    .iter()
                    .filter_map(|t| model.array_values.get(t).map(|interp| (*t, interp)))
                    .max_by_key(|(_, interp)| {
                        (usize::from(interp.default.is_some()), interp.stores.len())
                    });
                if let Some((_, best_interp)) = best {
                    let best_interp = best_interp.clone();
                    for &member in class {
                        if !model.array_values.contains_key(&member) {
                            // Only propagate to array_vars members (tracked arrays)
                            if self.array_vars.contains_key(&member) {
                                model.array_values.insert(member, best_interp.clone());
                            }
                        }
                    }
                }
            }
        }

        model
    }
}
