// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Row-level reason collection for implied bounds.
//!
//! Extracted from `implied_bounds.rs` to reduce file size.
//! Contains: `collect_reasons_from_explanation`, `collect_row_reasons_dedup`,
//! `collect_row_reasons_recursive`, `collect_reasons_from_row_for_basic`,
//! and `collect_single_row_reasons`.

use super::*;

impl LraSolver {
    /// Collect reasons using eagerly-stored explanation data (#6617).
    /// See `implied_bounds.rs::collect_reasons_from_explanation` for docs.
    pub(crate) fn collect_reasons_from_explanation(
        &self,
        explanation: &BoundExplanation,
        reasons: &mut Vec<TheoryLit>,
        seen: &mut HashSet<(TermId, bool)>,
        visited_vars: &mut HashSet<(u32, bool)>,
    ) -> bool {
        for &(var, used_upper) in &explanation.contributing_vars {
            if !visited_vars.insert((var, used_upper)) {
                continue;
            }
            let vi = var as usize;
            let info = match self.vars.get(vi) {
                Some(i) => i,
                None => return false,
            };
            let direct = if used_upper { &info.upper } else { &info.lower };
            if let Some(bound) = direct {
                for (term, val) in bound.reason_pairs() {
                    if !term.is_sentinel() && seen.insert((term, val)) {
                        reasons.push(TheoryLit::new(term, val));
                    }
                }
                continue;
            }
            let implied = if vi < self.implied_bounds.len() {
                if used_upper {
                    self.implied_bounds[vi].1.as_ref()
                } else {
                    self.implied_bounds[vi].0.as_ref()
                }
            } else {
                None
            };
            match implied {
                Some(ib) if ib.explanation.is_some() => {
                    if !self.collect_reasons_from_explanation(
                        ib.explanation.as_ref().unwrap(),
                        reasons,
                        seen,
                        visited_vars,
                    ) {
                        return false;
                    }
                }
                _ => return false,
            }
        }
        true
    }

    /// Collect reasons for a variable's implied bound from its tableau row.
    ///
    /// If `var` is a basic variable with row `x_b = c + sum(a_j * x_j)`,
    /// and all nonbasic variables have direct bounds contributing to the
    /// implied bound of `x_b`, collect those direct-bound reasons.
    ///
    /// Returns `true` if all reasons were collected successfully (complete).
    /// Deduplicates reason literals using a shared
    /// `seen` set. This prevents the same reason atom from appearing multiple times
    /// when multiple variables share the same bound reason (#4919).
    ///
    /// When a nonbasic variable lacks a direct bound, recursively searches for
    /// a tableau row defining it as a basic variable and collects transitive
    /// reasons (depth-limited to avoid pathological chains).
    pub(crate) fn collect_row_reasons_dedup(
        &self,
        var: u32,
        need_upper: bool,
        reasons: &mut Vec<TheoryLit>,
        seen: &mut HashSet<(TermId, bool)>,
    ) -> bool {
        // #6617: Try eager explanation first — flat loop, no depth limit.
        let vi = var as usize;
        if vi < self.implied_bounds.len() {
            let ib = if need_upper {
                &self.implied_bounds[vi].1
            } else {
                &self.implied_bounds[vi].0
            };
            if let Some(ib) = ib {
                if let Some(ref expl) = ib.explanation {
                    let mut visited_vars = HashSet::new();
                    if self.collect_reasons_from_explanation(expl, reasons, seen, &mut visited_vars)
                    {
                        return true;
                    }
                    // Eager path failed — clear partial results, fall through to recursive.
                    reasons.clear();
                    seen.clear();
                }
            }
        }
        // Fallback: depth-limited recursive walk.
        let mut visited_vars = HashSet::new();
        self.collect_row_reasons_recursive(var, need_upper, reasons, seen, &mut visited_vars, 0)
    }

    // collect_row_reasons_recursive, collect_reasons_from_row_for_basic
    // extracted to implied_row_recursive.rs

    // collect_row_derivation_reasons_lb/ub removed (#6564): these populated
    // eager implied-bound reason snapshots, which were the root cause of
    // stale-reason false-UNSAT. Reasons are collected lazily at propagation
    // time via collect_row_reasons_dedup.

    /// Single-level reason collection from a specific derivation row (#4919).
    /// For an implied bound on `var` derived from `row_idx`, collects direct-bound
    /// reasons from all other variables in the row. Returns `None` if any variable
    /// lacks a direct bound (reason chain would require expensive recursion).
    ///
    /// `need_upper`: the direction of the bound being derived for `var`.
    pub(crate) fn collect_single_row_reasons(
        &self,
        var: u32,
        need_upper: bool,
        row_idx: usize,
    ) -> Option<Vec<TheoryLit>> {
        if row_idx >= self.rows.len() {
            return None;
        }
        let row = &self.rows[row_idx];
        let bv = row.basic_var;
        let is_basic = bv == var;
        let mut reasons = Vec::new();
        let mut seen = HashSet::new();

        if !is_basic {
            // Target is nonbasic: determine sum direction from coefficient
            let var_coeff_pos = match row.coeffs.binary_search_by_key(&var, |(v, _)| *v) {
                Ok(idx) => row.coeffs[idx].1.is_positive(),
                Err(_) => return None,
            };
            let sum_need_upper = var_coeff_pos == need_upper;

            // Basic variable's bound
            let bvi = bv as usize;
            if bvi >= self.vars.len() {
                return None;
            }
            let bv_bound = if sum_need_upper {
                &self.vars[bvi].upper
            } else {
                &self.vars[bvi].lower
            };
            match bv_bound {
                Some(b) => {
                    for (term, val) in b.reason_pairs() {
                        if seen.insert((term, val)) {
                            reasons.push(TheoryLit::new(term, val));
                        }
                    }
                }
                None => {
                    // #6564: Collect implied-bound reasons lazily.
                    if !self.collect_row_reasons_dedup(bv, sum_need_upper, &mut reasons, &mut seen)
                    {
                        return None;
                    }
                }
            }

            // Other nonbasic variables
            for &(nv, ref coeff) in &row.coeffs {
                if nv == var {
                    continue;
                }
                let nvi = nv as usize;
                if nvi >= self.vars.len() {
                    return None;
                }
                let nv_need_upper = coeff.is_positive() != sum_need_upper;
                let nv_bound = if nv_need_upper {
                    &self.vars[nvi].upper
                } else {
                    &self.vars[nvi].lower
                };
                match nv_bound {
                    Some(b) => {
                        for (term, val) in b.reason_pairs() {
                            if seen.insert((term, val)) {
                                reasons.push(TheoryLit::new(term, val));
                            }
                        }
                    }
                    None => {
                        // #6564: Collect implied-bound reasons lazily.
                        if !self.collect_row_reasons_dedup(
                            nv,
                            nv_need_upper,
                            &mut reasons,
                            &mut seen,
                        ) {
                            return None;
                        }
                    }
                }
            }
        } else {
            // Target is basic: need all nonbasic vars' bounds
            let sum_need_upper = need_upper;
            for &(nv, ref coeff) in &row.coeffs {
                let nvi = nv as usize;
                if nvi >= self.vars.len() {
                    return None;
                }
                let eq_c_positive = (-coeff).is_positive();
                let nv_need_upper = eq_c_positive != sum_need_upper;
                let nv_bound = if nv_need_upper {
                    &self.vars[nvi].upper
                } else {
                    &self.vars[nvi].lower
                };
                match nv_bound {
                    Some(b) => {
                        for (term, val) in b.reason_pairs() {
                            if seen.insert((term, val)) {
                                reasons.push(TheoryLit::new(term, val));
                            }
                        }
                    }
                    None => {
                        // #6564: Collect implied-bound reasons lazily.
                        if !self.collect_row_reasons_dedup(
                            nv,
                            nv_need_upper,
                            &mut reasons,
                            &mut seen,
                        ) {
                            return None;
                        }
                    }
                }
            }
        }

        if reasons.is_empty() {
            None
        } else {
            Some(reasons)
        }
    }
}
