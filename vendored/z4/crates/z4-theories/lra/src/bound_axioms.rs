// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl LraSolver {
    pub(crate) fn generate_bound_axiom_terms_inner(&self) -> Vec<(TermId, bool, TermId, bool)> {
        let mut axioms = Vec::new();
        let mut seen = std::collections::HashSet::new();
        let mut total_indexed = 0usize;
        let mut vars_with_bounds = 0usize;
        let mut max_bounds = 0usize;
        let compound_wakeup_vars = self
            .compound_use_index
            .values()
            .filter(|atoms| !atoms.is_empty())
            .count();
        let compound_wakeup_edges = self
            .compound_use_index
            .values()
            .map(Vec::len)
            .sum::<usize>();
        for atoms in self.atom_index.values() {
            total_indexed += atoms.len();
            if atoms.len() >= 2 {
                vars_with_bounds += 1;
                max_bounds = max_bounds.max(atoms.len());
            }
        }
        if total_indexed > 0 || compound_wakeup_edges > 0 {
            tracing::info!(
                atom_index_vars = self.atom_index.len(),
                vars_with_bounds,
                total_indexed,
                max_bounds,
                compound_wakeup_vars,
                compound_wakeup_edges,
                compound_queued = self.last_compound_propagations_queued,
                "Bound axiom generation stats (#4919)"
            );
        }
        for atoms in self.atom_index.values() {
            if atoms.len() < 2 {
                continue;
            }
            // Generate axioms for ALL pairs of bounds on the same variable (#4919).
            // Z3 uses nearest-neighbor (4 axioms per new bound), but this batch
            // path generates all-pairs at init time for the pre-search atom set.
            // Z4 also creates bound atoms incrementally during search (see
            // generate_incremental_bound_axioms); this batch path covers the
            // initial set registered before search begins.
            for (i, a1) in atoms.iter().enumerate() {
                for (j, a2) in atoms.iter().enumerate() {
                    if j <= i {
                        continue;
                    }
                    if a1.term == a2.term {
                        continue;
                    }
                    self.mk_bound_axiom_terms(a1, a2, &mut axioms, &mut seen);
                }
            }
        }
        // Generate axioms connecting equality atoms to bound atoms (#4919).
        // For each single-variable equality (= x k), generate:
        //   ~eq ∨ bound   when eq implies bound  (x=k → x>=k' when k'<=k)
        //   ~eq ∨ ~bound  when eq contradicts bound (x=k → ¬(x>=k') when k'>k)
        // This connects equality atoms to the bound ordering system without
        // decomposing the equality, preserving the original equality semantics
        // for the theory solver while enabling BCP propagation.
        for (&eq_term, cached) in &self.atom_cache {
            let Some(info) = cached else { continue };
            if !info.is_eq || info.expr.coeffs.len() != 1 {
                continue;
            }
            let (var, ref coeff) = info.expr.coeffs[0];
            if coeff.is_zero() {
                continue;
            }
            let k = (-info.expr.constant.clone() / coeff.clone()).to_big();
            let Some(bounds) = self.atom_index.get(&var) else {
                continue;
            };
            for bound in bounds {
                if bound.term == eq_term {
                    continue;
                }
                if !bound.is_upper {
                    let implies = if bound.strict {
                        bound.bound_value < k
                    } else {
                        bound.bound_value <= k
                    };
                    if implies {
                        let key = if eq_term <= bound.term {
                            (eq_term, bound.term)
                        } else {
                            (bound.term, eq_term)
                        };
                        if seen.insert(key) {
                            axioms.push((eq_term, false, bound.term, true));
                        }
                    }
                    let contradicts = if bound.strict {
                        bound.bound_value >= k
                    } else {
                        bound.bound_value > k
                    };
                    if contradicts {
                        axioms.push((eq_term, false, bound.term, false));
                    }
                } else {
                    let implies = if bound.strict {
                        bound.bound_value > k
                    } else {
                        bound.bound_value >= k
                    };
                    if implies {
                        let key = if eq_term <= bound.term {
                            (eq_term, bound.term)
                        } else {
                            (bound.term, eq_term)
                        };
                        if seen.insert(key) {
                            axioms.push((eq_term, false, bound.term, true));
                        }
                    }
                    let contradicts = if bound.strict {
                        bound.bound_value <= k
                    } else {
                        bound.bound_value < k
                    };
                    if contradicts {
                        axioms.push((eq_term, false, bound.term, false));
                    }
                }
            }
        }
        axioms
    }

    pub(crate) fn generate_incremental_bound_axioms_inner(
        &self,
        atom: TermId,
    ) -> Vec<(TermId, bool, TermId, bool)> {
        let Some(Some(info)) = self.atom_cache.get(&atom) else {
            return Vec::new();
        };
        if info.is_eq || info.is_distinct {
            return Vec::new();
        }
        if info.expr.coeffs.len() != 1 {
            return Vec::new();
        }
        let (var, coeff) = &info.expr.coeffs[0];
        let var = *var;
        if coeff.is_zero() {
            return Vec::new();
        }

        let Some(existing) = self.atom_index.get(&var) else {
            return Vec::new();
        };
        if existing.is_empty() {
            return Vec::new();
        }

        let bound_value = (-info.expr.constant.clone() / coeff.clone()).to_big();
        let coeff_positive = coeff.is_positive();
        let is_upper = matches!((info.is_le, coeff_positive), (true, true) | (false, false));
        let new_ref = AtomRef {
            term: atom,
            bound_value,
            is_upper,
            strict: info.strict,
        };

        let mut lo_inf: Option<&AtomRef> = None;
        let mut lo_sup: Option<&AtomRef> = None;
        let mut hi_inf: Option<&AtomRef> = None;
        let mut hi_sup: Option<&AtomRef> = None;

        for existing_atom in existing {
            if existing_atom.term == atom {
                continue;
            }
            if existing_atom.bound_value == new_ref.bound_value
                && existing_atom.is_upper == new_ref.is_upper
                && existing_atom.strict == new_ref.strict
            {
                continue;
            }
            let k2 = &existing_atom.bound_value;
            if !existing_atom.is_upper {
                if *k2 < new_ref.bound_value {
                    if lo_inf.is_none_or(|b| *k2 > b.bound_value) {
                        lo_inf = Some(existing_atom);
                    }
                } else if lo_sup.is_none_or(|b| *k2 < b.bound_value) {
                    lo_sup = Some(existing_atom);
                }
            } else if *k2 < new_ref.bound_value {
                if hi_inf.is_none_or(|b| *k2 > b.bound_value) {
                    hi_inf = Some(existing_atom);
                }
            } else if hi_sup.is_none_or(|b| *k2 < b.bound_value) {
                hi_sup = Some(existing_atom);
            }
        }

        let mut axioms = Vec::new();
        let mut seen = std::collections::HashSet::new();
        for neighbor in [lo_inf, lo_sup, hi_inf, hi_sup].into_iter().flatten() {
            self.mk_bound_axiom_terms(&new_ref, neighbor, &mut axioms, &mut seen);
        }
        axioms
    }
}
