// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Depth-limited recursive row reason collection for implied bounds.
//!
//! Contains `collect_row_reasons_recursive` (the core recursive walk) and
//! `collect_reasons_from_row_for_basic` (its per-row helper). Called from
//! `collect_row_reasons_dedup` in `implied_row_reasons.rs`.
//!
//! Extracted from implied_row_reasons.rs as part of #5970 code-health splits.

use super::*;

impl LraSolver {
    /// Depth-limited recursive row reason collection.
    /// `depth` limits transitive reasoning to avoid worst-case blowup.
    ///
    /// When `var` is the basic variable of a row, collects reasons from the
    /// nonbasic variables' bounds (the standard case).
    ///
    /// When `var` is NOT basic, uses the derivation row stored in `implied_bounds`
    /// (if available) to go directly to the row that derived the bound. Falls back
    /// to searching `col_index` if no stored row exists (#4919).
    ///
    /// Reference: Z3 stores a lazy explanation closure capturing the derivation row
    /// (`reference/z3/src/math/lp/bound_analyzer_on_row.h:298-319`).
    pub(crate) fn collect_row_reasons_recursive(
        &self,
        var: u32,
        need_upper: bool,
        reasons: &mut Vec<TheoryLit>,
        seen: &mut HashSet<(TermId, bool)>,
        visited_vars: &mut HashSet<(u32, bool)>,
        depth: u32,
    ) -> bool {
        // #6590: Reduced from 12 to 8. Depth 12 causes exponential blowup on
        // sc-* benchmarks (32s → should be <1s). Z3 does not do recursive
        // reason collection at all — it stores lazy explanations. Depth 8
        // allows moderate transitive reasoning while capping the cost.
        // (Depth 6 caused clocksynchro_9clocks regression from unsat to unknown.)
        const MAX_DEPTH: u32 = 8;
        if depth > MAX_DEPTH {
            return false;
        }
        // Prevent exponential re-exploration of the same (var, direction) pair
        // via different paths (#6364). Once we've started exploring a variable's
        // derivation chain, don't re-enter it from another branch.
        if !visited_vars.insert((var, need_upper)) {
            // Already visited — the reasons from the first visit are already
            // in the `reasons` vector if it succeeded. Skip re-exploration.
            return true;
        }
        // Case 1: var is basic — collect from nonbasic vars in its row.
        if let Some(&row_idx) = self.basic_var_to_row.get(&var) {
            let ok = self.collect_reasons_from_row_for_basic(
                row_idx,
                need_upper,
                reasons,
                seen,
                visited_vars,
                depth,
            );
            // #7654: Only cache successful visits. If the basic row failed,
            // remove our entry so a future request (from a different row
            // context) can retry this variable instead of assuming its
            // reasons are already in the vector.
            if !ok {
                visited_vars.remove(&(var, need_upper));
            }
            return ok;
        }
        // Case 2: var is nonbasic — use the derivation row from implied_bounds
        // if available, then fall back to col_index search.
        let vi = var as usize;

        // Get stored derivation row index from implied_bounds (usize::MAX = direct bound).
        let stored_row = if vi < self.implied_bounds.len() {
            let ib = if need_upper {
                &self.implied_bounds[vi].1
            } else {
                &self.implied_bounds[vi].0
            };
            ib.as_ref()
                .filter(|b| b.row_idx != usize::MAX)
                .map(|b| b.row_idx)
        } else {
            None
        };

        if vi >= self.col_index.len() && stored_row.is_none() {
            visited_vars.remove(&(var, need_upper));
            return false;
        }

        // Try stored derivation row first (likely to succeed since it was the
        // row used to derive the bound), then fall back to col_index search.
        let col_rows: &[usize] = if vi < self.col_index.len() {
            &self.col_index[vi]
        } else {
            &[]
        };
        // #7654: Snapshot visited_vars before the row loop. When a row attempt
        // fails, recursive calls within that row may have added entries to
        // visited_vars (for variables whose reasons were successfully collected
        // during that row's processing). The row rollback removes those reasons
        // from `reasons` and `seen`, but the visited_vars entries persist —
        // causing a later row to skip re-collecting those reasons (returning
        // true from the visited_vars check at line 49 without adding reasons).
        // Restoring visited_vars to the pre-row snapshot on failure ensures
        // entries from rolled-back recursive calls don't poison later rows.
        let visited_snapshot = visited_vars.clone();
        for row_idx in stored_row.into_iter().chain(
            col_rows
                .iter()
                .copied()
                .filter(|ri| Some(*ri) != stored_row),
        ) {
            if row_idx >= self.rows.len() {
                continue;
            }
            let row = &self.rows[row_idx];
            // Row: basic_var = constant + Σ(coeff_j * nonbasic_j)
            // To derive a bound on `var` (a nonbasic variable with coefficient c_var):
            //   c_var * var = basic_var - constant - Σ(c_j * other_j)
            //
            // We need bounds on the basic variable AND all other nonbasic variables.
            // Try collecting reasons from them. If any is missing, skip this row.
            //
            // Rollback approach (#4919): instead of cloning `seen` for each candidate
            // row, record the insertion point and rollback on failure. This eliminates
            // O(seen × candidate_rows) allocation overhead.
            // Every new entry in `reasons` after `reasons_mark` corresponds to a
            // freshly-inserted `seen` key (including from recursive calls), so
            // truncating reasons + removing those keys from `seen` is correct.
            let reasons_mark = reasons.len();
            let mut all_found = true;

            // Find coefficient of var in this row (binary search on sorted vec)
            let var_coeff = match row.coeffs.binary_search_by_key(&var, |(v, _)| *v) {
                Ok(idx) => &row.coeffs[idx].1,
                Err(_) => continue,
            };
            // Determine what bound direction we need for the "sum" side.
            let sum_need_upper = var_coeff.is_positive() == need_upper;

            // Basic variable: need bound in `sum_need_upper` direction
            let bv = row.basic_var as usize;
            if bv >= self.vars.len() {
                continue;
            }

            // Check if implied bound is tighter than direct bound (#6202)
            let bv_implied_derived = if bv < self.implied_bounds.len() {
                let ib = if sum_need_upper {
                    &self.implied_bounds[bv].1
                } else {
                    &self.implied_bounds[bv].0
                };
                ib.as_ref().filter(|b| b.row_idx != usize::MAX).is_some()
            } else {
                false
            };

            if bv_implied_derived {
                if !self.collect_row_reasons_recursive(
                    row.basic_var,
                    sum_need_upper,
                    reasons,
                    seen,
                    visited_vars,
                    depth + 1,
                ) {
                    for lit in reasons.drain(reasons_mark..) {
                        seen.remove(&(lit.term, lit.value));
                    }
                    visited_vars.clone_from(&visited_snapshot);
                    continue;
                }
            } else {
                let bv_info = &self.vars[bv];
                let bv_bound = if sum_need_upper {
                    &bv_info.upper
                } else {
                    &bv_info.lower
                };
                if let Some(b) = bv_bound {
                    for (term, val) in b.reason_pairs() {
                        if seen.insert((term, val)) {
                            reasons.push(TheoryLit::new(term, val));
                        }
                    }
                } else if !self.collect_row_reasons_recursive(
                    row.basic_var,
                    sum_need_upper,
                    reasons,
                    seen,
                    visited_vars,
                    depth + 1,
                ) {
                    for lit in reasons.drain(reasons_mark..) {
                        seen.remove(&(lit.term, lit.value));
                    }
                    visited_vars.clone_from(&visited_snapshot);
                    continue; // Try next row
                }
            }

            // Other nonbasic variables (not `var` itself)
            for &(nv, ref coeff) in &row.coeffs {
                if nv == var {
                    continue;
                }
                let nvi = nv as usize;
                if nvi >= self.vars.len() {
                    all_found = false;
                    break;
                }
                let nv_need_upper = coeff.is_positive() != sum_need_upper;

                // Check if implied bound is tighter than direct bound (#6202)
                let nv_implied_derived = if nvi < self.implied_bounds.len() {
                    let ib = if nv_need_upper {
                        &self.implied_bounds[nvi].1
                    } else {
                        &self.implied_bounds[nvi].0
                    };
                    ib.as_ref().filter(|b| b.row_idx != usize::MAX).is_some()
                } else {
                    false
                };

                if nv_implied_derived {
                    if !self.collect_row_reasons_recursive(
                        nv,
                        nv_need_upper,
                        reasons,
                        seen,
                        visited_vars,
                        depth + 1,
                    ) {
                        all_found = false;
                        break;
                    }
                } else {
                    let nv_info = &self.vars[nvi];
                    let nv_bound = if nv_need_upper {
                        &nv_info.upper
                    } else {
                        &nv_info.lower
                    };
                    if let Some(b) = nv_bound {
                        for (term, val) in b.reason_pairs() {
                            if seen.insert((term, val)) {
                                reasons.push(TheoryLit::new(term, val));
                            }
                        }
                    } else if !self.collect_row_reasons_recursive(
                        nv,
                        nv_need_upper,
                        reasons,
                        seen,
                        visited_vars,
                        depth + 1,
                    ) {
                        all_found = false;
                        break;
                    }
                }
            }

            if all_found {
                // Successfully collected all reasons from this row.
                return true;
            }
            // Rollback: undo all insertions into `seen`, `reasons`, and
            // `visited_vars` for this row (#7654).
            for lit in reasons.drain(reasons_mark..) {
                seen.remove(&(lit.term, lit.value));
            }
            visited_vars.clone_from(&visited_snapshot);
        }
        // All rows failed — remove our own entry so a future request
        // (from a different row context) can retry this variable.
        visited_vars.remove(&(var, need_upper));
        false
    }

    /// Collect reasons from a row where `var` is the basic variable.
    /// Helper for `collect_row_reasons_recursive` — the original Case 1 logic.
    pub(crate) fn collect_reasons_from_row_for_basic(
        &self,
        row_idx: usize,
        need_upper: bool,
        reasons: &mut Vec<TheoryLit>,
        seen: &mut HashSet<(TermId, bool)>,
        visited_vars: &mut HashSet<(u32, bool)>,
        depth: u32,
    ) -> bool {
        let row = &self.rows[row_idx];
        let mark = reasons.len();
        for &(nv, ref coeff) in &row.coeffs {
            let nvi = nv as usize;
            if nvi >= self.vars.len() {
                // Rollback partial additions from earlier nonbasic vars
                for lit in reasons.drain(mark..) {
                    seen.remove(&(lit.term, lit.value));
                }
                return false;
            }
            let nv_need_upper = coeff.is_positive() == need_upper;

            // Check if implied bound is tighter than direct bound (#6202).
            // compute_implied_bounds() may derive a tighter bound from another
            // tableau row. If that happened (row_idx != usize::MAX), the direct
            // bound's reasons are insufficient — we must trace through the
            // derivation row that produced the tighter bound.
            let implied_derived = if nvi < self.implied_bounds.len() {
                let ib = if nv_need_upper {
                    &self.implied_bounds[nvi].1
                } else {
                    &self.implied_bounds[nvi].0
                };
                ib.as_ref().filter(|b| b.row_idx != usize::MAX).is_some()
            } else {
                false
            };

            if implied_derived {
                // Implied bound was derived from a tableau row and is tighter
                // than the direct bound. Recursively collect from the derivation
                // chain to get the true set of reason literals.
                if !self.collect_row_reasons_recursive(
                    nv,
                    nv_need_upper,
                    reasons,
                    seen,
                    visited_vars,
                    depth + 1,
                ) {
                    // Rollback partial additions from earlier nonbasic vars
                    for lit in reasons.drain(mark..) {
                        seen.remove(&(lit.term, lit.value));
                    }
                    return false;
                }
            } else {
                let info = &self.vars[nvi];
                let bound = if nv_need_upper {
                    &info.upper
                } else {
                    &info.lower
                };
                if let Some(b) = bound {
                    for (term, val) in b.reason_pairs() {
                        if seen.insert((term, val)) {
                            reasons.push(TheoryLit::new(term, val));
                        }
                    }
                } else if !self.collect_row_reasons_recursive(
                    nv,
                    nv_need_upper,
                    reasons,
                    seen,
                    visited_vars,
                    depth + 1,
                ) {
                    // Rollback partial additions from earlier nonbasic vars
                    for lit in reasons.drain(mark..) {
                        seen.remove(&(lit.term, lit.value));
                    }
                    return false;
                }
            }
        }
        true
    }
}
