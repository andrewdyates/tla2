// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Simplex tableau row representation.
//!
//! Extracted from `types.rs` for code health (#5970).

use num_rational::BigRational;
use num_traits::{One, Zero};

use crate::rational::Rational;
use crate::types::add_sparse_term_rat;
use crate::types::normalize_sparse_coeffs_rat;

/// A row in the simplex tableau
///
/// Represents: basic_var = Σ(coeff * var) + constant
#[derive(Debug, Clone)]
pub(crate) struct TableauRow {
    /// The basic variable for this row
    pub(crate) basic_var: u32,
    /// Sparse coefficients: (variable, coefficient) — fast Rational for i64 fast path
    pub(crate) coeffs: Vec<(u32, Rational)>,
    /// Constant term (RHS constant after normalization)
    pub(crate) constant: Rational,
}

impl TableauRow {
    /// Create a tableau row with canonicalized sparse coefficients.
    pub(crate) fn new_rat(
        basic_var: u32,
        coeffs: Vec<(u32, Rational)>,
        constant: Rational,
    ) -> Self {
        Self {
            basic_var,
            coeffs: normalize_sparse_coeffs_rat(coeffs),
            constant,
        }
    }

    /// Create from BigRational coefficients (convenience for callers not yet migrated).
    pub(crate) fn new(
        basic_var: u32,
        coeffs: Vec<(u32, BigRational)>,
        constant: BigRational,
    ) -> Self {
        let rat_coeffs: Vec<(u32, Rational)> = coeffs
            .into_iter()
            .map(|(v, c)| (v, Rational::from(c)))
            .collect();
        Self::new_rat(basic_var, rat_coeffs, Rational::from(constant))
    }

    /// Get the coefficient for a variable, or zero if not present
    pub(crate) fn coeff(&self, var: u32) -> Rational {
        self.coeffs
            .binary_search_by_key(&var, |(v, _)| *v)
            .ok()
            .map_or_else(Rational::zero, |idx| self.coeffs[idx].1.clone())
    }

    /// Get a reference to the coefficient for a variable, or `None` if zero/absent.
    /// Avoids cloning in hot paths where only a reference is needed.
    #[inline]
    pub(crate) fn coeff_ref(&self, var: u32) -> Option<&Rational> {
        self.coeffs
            .binary_search_by_key(&var, |(v, _)| *v)
            .ok()
            .map(|idx| &self.coeffs[idx].1)
    }

    /// Get coefficient as BigRational (for callers that still need it).
    pub(crate) fn coeff_big(&self, var: u32) -> BigRational {
        self.coeff(var).to_big()
    }

    #[cfg(any(test, kani))]
    pub(crate) fn add_coeff(&mut self, var: u32, coeff: Rational) {
        add_sparse_term_rat(&mut self.coeffs, var, coeff);
    }

    #[cfg(kani)] // Only used by #[cfg(kani)] verification module
    pub(crate) fn contains(&self, var: u32) -> bool {
        self.coeffs.binary_search_by_key(&var, |(v, _)| *v).is_ok()
    }

    #[cfg(any(test, kani))]
    pub(crate) fn remove_coeff(&mut self, var: u32) {
        if let Ok(idx) = self.coeffs.binary_search_by_key(&var, |(v, _)| *v) {
            self.coeffs.remove(idx);
        }
    }

    /// Substitute `entering_var` with a scaled copy of `subst_coeffs` in a single
    /// sorted-merge pass, avoiding O(w²) from repeated `add_coeff` calls (#6194).
    ///
    /// Equivalent to: `remove_coeff(entering_var)` then `add_coeff(v, c * scale)`
    /// for each `(v, c)` in `subst_coeffs`, but runs in O(w log w) instead of O(w²).
    /// `subst_coeffs` must be sorted by variable index (which TableauRow guarantees).
    /// The constant adjustment must be applied separately by the caller.
    pub(crate) fn substitute_var(
        &mut self,
        entering_var: u32,
        subst_coeffs: &[(u32, Rational)],
        scale: &Rational,
    ) {
        fn next_old_term(
            iter: &mut std::vec::IntoIter<(u32, Rational)>,
            entering_var: u32,
        ) -> Option<(u32, Rational)> {
            iter.find(|(var, _)| *var != entering_var)
        }

        // Determine scale category once to avoid repeated pattern matching.
        // Most pivot coefficients are ±1 for sparse LRA tableaux.
        let scale_is_one = scale.is_one();
        let scale_is_neg_one = scale.is_neg_one();

        fn next_scaled_addition(
            iter: &mut std::slice::Iter<'_, (u32, Rational)>,
            entering_var: u32,
            scale: &Rational,
            scale_is_one: bool,
            scale_is_neg_one: bool,
        ) -> Option<(u32, Rational)> {
            iter.find_map(|(var, coeff)| {
                if *var == entering_var {
                    return None;
                }
                // Fast paths: avoid full Rational multiply for ±1 scale.
                let scaled = if scale_is_one {
                    coeff.clone()
                } else if scale_is_neg_one {
                    -coeff
                } else {
                    coeff * scale
                };
                if scaled.is_zero() {
                    None
                } else {
                    Some((*var, scaled))
                }
            })
        }

        // Stream old coeffs and scaled substitution terms directly into the
        // merged result so the pivot loop avoids allocating an intermediate
        // additions vector on every affected row.
        let old = std::mem::take(&mut self.coeffs);
        let mut result = Vec::with_capacity(old.len() + subst_coeffs.len());
        let mut old_iter = old.into_iter();
        let mut subst_iter = subst_coeffs.iter();
        let mut old_term = next_old_term(&mut old_iter, entering_var);
        let mut addition = next_scaled_addition(
            &mut subst_iter,
            entering_var,
            scale,
            scale_is_one,
            scale_is_neg_one,
        );

        loop {
            match (old_term.as_ref(), addition.as_ref()) {
                (Some((old_var, _)), Some((new_var, _))) => match old_var.cmp(new_var) {
                    std::cmp::Ordering::Less => {
                        result.push(old_term.take().expect("old term present"));
                        old_term = next_old_term(&mut old_iter, entering_var);
                    }
                    std::cmp::Ordering::Greater => {
                        result.push(addition.take().expect("addition present"));
                        addition = next_scaled_addition(
                            &mut subst_iter,
                            entering_var,
                            scale,
                            scale_is_one,
                            scale_is_neg_one,
                        );
                    }
                    std::cmp::Ordering::Equal => {
                        let (var, old_coeff) = old_term.take().expect("old term present");
                        let (_, added_coeff) = addition.take().expect("addition present");
                        let merged = old_coeff + added_coeff;
                        if !merged.is_zero() {
                            result.push((var, merged));
                        }
                        old_term = next_old_term(&mut old_iter, entering_var);
                        addition = next_scaled_addition(
                            &mut subst_iter,
                            entering_var,
                            scale,
                            scale_is_one,
                            scale_is_neg_one,
                        );
                    }
                },
                (Some(_), None) => {
                    result.push(old_term.take().expect("old term present"));
                    result.extend(old_iter.filter(|(var, _)| *var != entering_var));
                    break;
                }
                (None, Some(_)) => {
                    result.push(addition.take().expect("addition present"));
                    result.extend(std::iter::from_fn(|| {
                        next_scaled_addition(
                            &mut subst_iter,
                            entering_var,
                            scale,
                            scale_is_one,
                            scale_is_neg_one,
                        )
                    }));
                    break;
                }
                (None, None) => break,
            }
        }

        self.coeffs = result;
    }

    /// Like `substitute_var`, but also tracks column-index deltas as a byproduct
    /// of the merge — no post-hoc binary searches needed (#8003).
    ///
    /// Returns `(added, removed)` where:
    /// - `added`: variables that were NOT in this row before but ARE now
    /// - `removed`: variables that WERE in this row before but are NOT now
    ///
    /// `entering_var` is always in `removed` (since it existed and is being
    /// substituted out). The caller's `col_added`/`col_removed` buffers are
    /// cleared and populated.
    pub(crate) fn substitute_var_with_col_deltas(
        &mut self,
        entering_var: u32,
        subst_coeffs: &[(u32, Rational)],
        scale: &Rational,
        col_added: &mut Vec<u32>,
        col_removed: &mut Vec<u32>,
    ) {
        col_added.clear();
        col_removed.clear();

        let scale_is_one = scale.is_one();
        let scale_is_neg_one = scale.is_neg_one();

        let old = std::mem::take(&mut self.coeffs);
        let mut result = Vec::with_capacity(old.len() + subst_coeffs.len());

        // Two-pointer merge over old row (sorted) and subst_coeffs (sorted).
        // entering_var is skipped in both streams.
        let mut oi = 0usize; // index into old
        let mut si = 0usize; // index into subst_coeffs

        // Skip dead entries (entering_var) efficiently via helper closures.
        // old is sorted, subst_coeffs is sorted.

        // Advance old past entering_var entries
        #[inline(always)]
        fn advance_old(old: &[(u32, Rational)], oi: &mut usize, entering_var: u32) -> bool {
            while *oi < old.len() {
                if old[*oi].0 != entering_var {
                    return true;
                }
                *oi += 1;
            }
            false
        }

        // Advance subst past entering_var entries and compute scaled value
        #[inline(always)]
        fn advance_subst<'a>(
            subst: &'a [(u32, Rational)],
            si: &mut usize,
            entering_var: u32,
            scale: &Rational,
            scale_is_one: bool,
            scale_is_neg_one: bool,
        ) -> Option<(u32, Rational)> {
            while *si < subst.len() {
                let (v, ref c) = subst[*si];
                *si += 1;
                if v == entering_var {
                    continue;
                }
                let scaled = if scale_is_one {
                    c.clone()
                } else if scale_is_neg_one {
                    -c
                } else {
                    c * scale
                };
                if !scaled.is_zero() {
                    return Some((v, scaled));
                }
            }
            None
        }

        // Track that entering_var is being removed (it was in old row)
        let had_entering = old.binary_search_by_key(&entering_var, |(v, _)| *v).is_ok();
        if had_entering {
            col_removed.push(entering_var);
        }

        let has_old = advance_old(&old, &mut oi, entering_var);
        let mut pending_subst =
            advance_subst(subst_coeffs, &mut si, entering_var, scale, scale_is_one, scale_is_neg_one);

        let mut have_old = has_old;

        loop {
            match (have_old, pending_subst.as_ref()) {
                (true, Some((sv, _))) => {
                    let (ov, _) = &old[oi];
                    match ov.cmp(sv) {
                        std::cmp::Ordering::Less => {
                            // Old var not in subst — survives unchanged
                            result.push(old[oi].clone());
                            oi += 1;
                            have_old = advance_old(&old, &mut oi, entering_var);
                        }
                        std::cmp::Ordering::Greater => {
                            // New var from subst — col addition
                            let (v, c) = pending_subst.take().expect("subst present");
                            col_added.push(v);
                            result.push((v, c));
                            pending_subst = advance_subst(
                                subst_coeffs, &mut si, entering_var, scale,
                                scale_is_one, scale_is_neg_one,
                            );
                        }
                        std::cmp::Ordering::Equal => {
                            // Both have this var — merge
                            let (var, ref old_c) = old[oi];
                            let (_, added_c) = pending_subst.take().expect("subst present");
                            let merged = old_c + &added_c;
                            if merged.is_zero() {
                                // Was present, now gone — col removal
                                col_removed.push(var);
                            } else {
                                result.push((var, merged));
                            }
                            oi += 1;
                            have_old = advance_old(&old, &mut oi, entering_var);
                            pending_subst = advance_subst(
                                subst_coeffs, &mut si, entering_var, scale,
                                scale_is_one, scale_is_neg_one,
                            );
                        }
                    }
                }
                (true, None) => {
                    // Drain remaining old entries (skip entering_var)
                    result.push(old[oi].clone());
                    oi += 1;
                    while oi < old.len() {
                        if old[oi].0 != entering_var {
                            result.push(old[oi].clone());
                        }
                        oi += 1;
                    }
                    break;
                }
                (false, Some(_)) => {
                    // Drain remaining subst entries — all are new additions
                    let (v, c) = pending_subst.take().expect("subst present");
                    col_added.push(v);
                    result.push((v, c));
                    while let Some((v, c)) = advance_subst(
                        subst_coeffs, &mut si, entering_var, scale,
                        scale_is_one, scale_is_neg_one,
                    ) {
                        col_added.push(v);
                        result.push((v, c));
                    }
                    break;
                }
                (false, None) => break,
            }
        }

        self.coeffs = result;
    }
}
