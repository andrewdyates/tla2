// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Diophantine substitution bound feasibility checking.
//!
//! Composes cached Diophantine substitutions and checks whether the composed
//! expressions are feasible given variable bounds. Detects cross-substitution
//! infeasibility in carry-chain / modular patterns.
//! Extracted from `dioph_bridge.rs` to keep each file under 500 lines.

use super::*;

impl LiaSolver<'_> {
    /// Check if Dioph substitutions are infeasible given variable bounds.
    ///
    /// Composes substitutions to detect cross-substitution infeasibility.
    /// When one substitution's LHS appears as an RHS variable in another,
    /// we substitute it in to reveal tighter constraints. For example:
    ///   c1 = 2 - c2 - c3 - c4
    ///   m1 = 1 + 21845*(c1+c2+c3+c4) - (m2+m3+m4+m5)
    /// After substituting c1 → 2 - c2 - c3 - c4:
    ///   m1 = 43691 - (m2+m3+m4+m5)
    /// So M = m1+...+m5 = 43691, which may violate bounds.
    pub(crate) fn check_substitution_bound_feasibility(&self) -> Option<Vec<TheoryLit>> {
        // Build a map of LHS → (coeffs, constant) for substitution composition
        let sub_map: SubstitutionMap<'_> = self
            .dioph_cached_substitutions
            .iter()
            .map(|(tid, cs, c)| (*tid, (cs.as_slice(), c)))
            .collect();

        for (term_id, coeffs, constant) in &self.dioph_cached_substitutions {
            let (composed_coeffs, composed_constant) =
                match Self::compose_substitution(term_id, coeffs, constant, &sub_map) {
                    Some(r) => r,
                    None => continue,
                };

            if self.composed_sub_violates_bounds(term_id, &composed_coeffs, &composed_constant) {
                return Some(self.build_sub_bound_conflict_all());
            }
        }

        None
    }

    /// Compose a substitution by replacing RHS variables that are themselves
    /// LHS of other substitutions. Returns (composed_coeffs, composed_constant)
    /// or None if composition yields a degenerate or unhandled self-reference.
    pub(crate) fn compose_substitution(
        term_id: &TermId,
        coeffs: &[(TermId, BigInt)],
        constant: &BigInt,
        sub_map: &SubstitutionMap<'_>,
    ) -> Option<(HashMap<TermId, BigInt>, BigInt)> {
        let mut composed_coeffs: HashMap<TermId, BigInt> = HashMap::new();
        let mut composed_constant = constant.clone();

        for (dep_term, coeff) in coeffs {
            if let Some((sub_coeffs, sub_const)) = sub_map.get(dep_term) {
                composed_constant += coeff * *sub_const;
                for (sub_dep, sub_coeff) in *sub_coeffs {
                    *composed_coeffs.entry(*sub_dep).or_insert_with(BigInt::zero) +=
                        coeff * sub_coeff;
                }
            } else {
                *composed_coeffs
                    .entry(*dep_term)
                    .or_insert_with(BigInt::zero) += coeff;
            }
        }

        composed_coeffs.retain(|_, c| !c.is_zero());

        // Handle self-reference: term_id appears on both sides after composition
        if let Some(sc) = composed_coeffs.remove(term_id) {
            let divisor = BigInt::one() - &sc;
            if divisor.is_zero() {
                return None;
            } else if divisor == BigInt::one() {
                // No change needed
            } else if divisor == -BigInt::one() {
                composed_constant = -composed_constant;
                for v in composed_coeffs.values_mut() {
                    *v = -v.clone();
                }
            } else {
                return None; // Complex divisor: skip
            }
        }

        Some((composed_coeffs, composed_constant))
    }

    /// Check if a composed substitution's implied bounds violate the variable's actual bounds.
    pub(crate) fn composed_sub_violates_bounds(
        &self,
        term_id: &TermId,
        composed_coeffs: &HashMap<TermId, BigInt>,
        composed_constant: &BigInt,
    ) -> bool {
        let (term_lo, term_hi) = self.get_integer_bounds_for_term_extended(Some(*term_id));

        let mut implied_lo = Some(composed_constant.clone());
        let mut implied_hi = Some(composed_constant.clone());

        for (dep_term, coeff) in composed_coeffs {
            let (dep_lo, dep_hi) = self.get_integer_bounds_for_term_extended(Some(*dep_term));
            let (Some(dl), Some(dh)) = (dep_lo, dep_hi) else {
                return false; // Unbounded dep → can't conclude infeasible
            };

            if coeff.is_positive() {
                if let Some(lo) = implied_lo.as_mut() {
                    *lo += coeff * &dl;
                }
                if let Some(hi) = implied_hi.as_mut() {
                    *hi += coeff * &dh;
                }
            } else {
                if let Some(lo) = implied_lo.as_mut() {
                    *lo += coeff * &dh;
                }
                if let Some(hi) = implied_hi.as_mut() {
                    *hi += coeff * &dl;
                }
            }
        }

        let (Some(il), Some(ih)) = (implied_lo, implied_hi) else {
            return false;
        };

        // Empty implied range
        if il > ih {
            return true;
        }
        // Implied range entirely below lower bound
        if let Some(ref tl) = term_lo {
            if ih < *tl {
                return true;
            }
        }
        // Implied range entirely above upper bound
        if let Some(ref tu) = term_hi {
            if il > *tu {
                return true;
            }
        }
        false
    }

    /// Build a conflict clause from ALL substitution equalities and ALL variable bounds.
    ///
    /// Used when composed substitution analysis detects infeasibility that involves
    /// multiple substitutions and multiple variable bounds simultaneously.
    pub(crate) fn build_sub_bound_conflict_all(&self) -> Vec<TheoryLit> {
        let mut conflict: Vec<TheoryLit> = self
            .dioph_cached_reasons
            .iter()
            .map(|&(lit, val)| TheoryLit::new(lit, val))
            .collect();
        let mut seen: HashSet<TheoryLit> = conflict.iter().copied().collect();

        // Add bound reasons for ALL variables in ALL substitutions.
        // Use HashSet for O(1) dedup instead of Vec::contains().
        for (term_id, coeffs, _) in &self.dioph_cached_substitutions {
            for reason in self.get_bound_reasons_for_term(Some(*term_id)) {
                if seen.insert(reason) {
                    conflict.push(reason);
                }
            }
            for (dep_term, _) in coeffs {
                for reason in self.get_bound_reasons_for_term(Some(*dep_term)) {
                    if seen.insert(reason) {
                        conflict.push(reason);
                    }
                }
            }
        }
        conflict
    }
}
