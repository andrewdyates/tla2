// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl LraSolver {
    /// Compute implied bounds for all variables from tableau rows.
    ///
    /// Two-pass approach following Z3's `bound_analyzer_on_row`:
    ///
    /// Pass 1: For each row `x_b = c + sum(a_j * x_j)`, if all nonbasic
    /// variables have bounds, derive bounds for the basic variable.
    ///
    /// Pass 2: For each row, if exactly one variable (basic or nonbasic)
    /// lacks a bound, derive that bound from all the others. This is Z3's
    /// "single unbounded" optimization from `limit_monoid_u`/`limit_monoid_l`.
    ///
    /// Reference: Z3 `bound_analyzer_on_row.h`, `theory_arith_core.h:2600-3060`
    pub(crate) fn compute_implied_bounds(&mut self) -> HashSet<u32> {
        let num_vars = self.vars.len();
        // #4919: Persist implied bounds across check() calls. Previously,
        // implied_bounds was cleared every call, discarding bounds derived
        // in the previous fixpoint. This prevented cascading: bounds derived
        // in check #1 were lost, so check #2's fixpoint couldn't build on
        // them. Z3's LP solver persists bounds across propagation passes.
        //
        // Soundness: implied bounds are cleared on pop()/reset()/soft_reset()
        // (when direct bounds may revert). Between those events, previously-
        // derived bounds remain valid because the direct bounds they depend
        // on are still asserted.
        //
        // We resize to accommodate new variables (added since last call),
        // then overlay direct bounds (keeping the tighter of direct vs
        // previously-derived implied bound).
        // Force overlay when new variables have been added since last call.
        let need_resize = self.implied_bounds.len() < num_vars;
        if need_resize {
            self.direct_bounds_changed_since_implied = true;
        }
        self.implied_bounds.resize(num_vars, (None, None));
        self.var_bound_gen.resize(num_vars, 0);
        self.row_computed_gen.resize(self.rows.len(), 0);
        let mut newly_bounded: HashSet<u32> = HashSet::new();

        // Overlay direct bounds into implied_bounds. A direct bound always
        // replaces a missing implied bound. When both exist, keep the tighter
        // one (direct bounds are always valid; implied bounds may be tighter
        // from previous fixpoint passes).
        // Direct bounds use row_idx = usize::MAX as sentinel.
        //
        // Incremental skip: when no direct bound has changed since the last
        // call (direct_bounds_changed_since_implied == false), the overlay
        // would recompute the same comparisons. Skip the O(num_vars) loop
        // entirely. This eliminates the dominant per-BCP cost when the theory
        // callback fires on cascade rows without new bound assertions.
        if self.direct_bounds_changed_since_implied {
            self.direct_bounds_changed_since_implied = false;
            // Incremental overlay (#8782): when direct_bounds_changed_vars tracks
            // specific changed variables, only overlay those instead of scanning
            // all vars. On resize or after pop/reset (vec empty + flag true),
            // fall back to full scan. Reduces O(num_vars) to O(changed_vars)
            // in the common BCP-cascade case.
            let use_incremental = !need_resize && !self.direct_bounds_changed_vars.is_empty();
            if use_incremental {
                let changed = std::mem::take(&mut self.direct_bounds_changed_vars);
                // #8003: Bump generation once for the batch of direct bound changes.
                self.bound_generation += 1;
                let cur_gen = self.bound_generation;
                for &var in &changed {
                    let i = var as usize;
                    if i >= self.vars.len() {
                        continue;
                    }
                    Self::overlay_direct_bound_for_var(&self.vars[i], &mut self.implied_bounds[i]);
                    self.register_fixed_term_var(var);
                    // Stamp variable so rows containing it are re-analyzed.
                    if i < self.var_bound_gen.len() {
                        self.var_bound_gen[i] = cur_gen;
                    }
                }
                self.direct_bounds_changed_vars = changed;
                self.direct_bounds_changed_vars.clear();
            } else {
                self.direct_bounds_changed_vars.clear();
                // #8003: Full scan — bump generation and stamp all vars.
                self.bound_generation += 1;
                let cur_gen = self.bound_generation;
                let mut fixed_vars = Vec::with_capacity(num_vars);
                for (i, info) in self.vars.iter().enumerate() {
                    Self::overlay_direct_bound_for_var(info, &mut self.implied_bounds[i]);
                    fixed_vars.push(i as u32);
                    if i < self.var_bound_gen.len() {
                        self.var_bound_gen[i] = cur_gen;
                    }
                }
                for var_idx in fixed_vars {
                    self.register_fixed_term_var(var_idx);
                }
            }
        }

        // Z3's bound propagation is a single pass over touched rows. When that
        // pass tightens bounds, the DPLL(T) loop re-enters theory propagation
        // later with freshly-touched rows instead of doing an in-function
        // fixpoint. Keep that architecture here: analyze the current row set
        // once, then seed touched_rows for the next call below.
        //
        // When touched_rows is empty we fall back to a full sweep. This keeps
        // initialization and direct unit tests working without requiring the
        // caller to pre-seed a row set.
        // #7719 D1: Use std::mem::take instead of clone to avoid O(rows) HashSet
        // clone per call. The function clears and reseeds touched_rows at the end
        // anyway, so taking ownership is equivalent but allocation-free.
        let iter_rows = if self.touched_rows.is_empty() {
            None
        } else {
            Some(std::mem::take(&mut self.touched_rows))
        };
        // Pre-allocate contribution vectors outside both loops to avoid
        // repeated heap allocation. Cleared and reused per row (#4919, P1:129).
        let mut lb_contribs: Vec<(usize, Rational, Rational, bool)> = Vec::new();
        let mut ub_contribs: Vec<(usize, Rational, Rational, bool)> = Vec::new();

        // Approach G diagnostic (#4919): count per-row unbounded-variable
        // distribution to understand bound starvation.
        if self.debug_lra && (self.check_count == 1 || self.check_count.is_multiple_of(200)) {
            let mut unbounded_dist: [u32; 6] = [0; 6]; // 0,1,2,3,4,5+
            for row in &self.rows {
                let bv = row.basic_var as usize;
                let mut n_unbounded_lb = 0u32;
                // Count unbounded (no lower bound) for basic var
                if bv < num_vars && self.implied_bounds[bv].0.is_none() {
                    n_unbounded_lb += 1;
                }
                for &(v, ref coeff) in &row.coeffs {
                    let vi = v as usize;
                    if vi >= num_vars {
                        continue;
                    }
                    let eq_c_pos = coeff.is_negative(); // eq_coeff = -coeff
                    let need_lb = eq_c_pos;
                    if need_lb {
                        if self.implied_bounds[vi].0.is_none() {
                            n_unbounded_lb += 1;
                        }
                    } else if self.implied_bounds[vi].1.is_none() {
                        n_unbounded_lb += 1;
                    }
                }
                let idx = std::cmp::min(n_unbounded_lb as usize, 5);
                unbounded_dist[idx] += 1;
            }
            safe_eprintln!(
                "[LRA] Approach G: row unbounded-var distribution (lb direction): \
                0={}, 1={}, 2={}, 3={}, 4={}, 5+={}, total_rows={}",
                unbounded_dist[0],
                unbounded_dist[1],
                unbounded_dist[2],
                unbounded_dist[3],
                unbounded_dist[4],
                unbounded_dist[5],
                self.rows.len()
            );
        }

        let mut updates: Vec<(usize, Option<ImpliedBound>, Option<ImpliedBound>)> = Vec::new();

        // #7973: When touched-row filtering is active, iterate only the
        // touched rows instead of scanning all rows. This converts O(total_rows)
        // to O(touched_rows), significant on LP benchmarks with 100+ rows
        // but only 5-10 touched per BCP callback.
        let row_indices: Vec<usize> = match &iter_rows {
            Some(touched) => {
                let mut v: Vec<usize> = touched.iter().copied().collect();
                v.sort_unstable();
                v
            }
            None => (0..self.rows.len()).collect(),
        };
        for &row_idx in &row_indices {
            let row = &self.rows[row_idx];
            let bv = row.basic_var as usize;
            // #6617: unified row-width limit (was 100 here, 300 in the
            // old inline path). Z3's bound_analyzer_on_row has no width
            // cap. Shared constant ensures rows 101-300 are still covered
            // now that the inline bound-writing path is removed.
            if bv >= num_vars || row.coeffs.len() > Self::MAX_TOUCHED_ROW_BOUND_SCAN_WIDTH {
                continue;
            }
            // #8003: Generation-based skip. If no variable in this row has had
            // its bound tightened since we last analyzed this row, the result
            // would be identical — skip the expensive arithmetic. Only applies
            // when iterating touched rows (not full sweep on first call) and
            // row_computed_gen is populated.
            if iter_rows.is_some() && row_idx < self.row_computed_gen.len() {
                let row_gen = self.row_computed_gen[row_idx];
                if row_gen > 0 {
                    let mut any_newer = false;
                    if bv < self.var_bound_gen.len() && self.var_bound_gen[bv] > row_gen {
                        any_newer = true;
                    }
                    if !any_newer {
                        for &(var, _) in &row.coeffs {
                            let vi = var as usize;
                            if vi < self.var_bound_gen.len()
                                && self.var_bound_gen[vi] > row_gen
                            {
                                any_newer = true;
                                break;
                            }
                        }
                    }
                    if !any_newer {
                        continue;
                    }
                }
            }
            // #6615 Packet 3: Skip rows with pathologically large coefficients.
            // Z3's row_has_a_big_num() (lar_solver.cpp:373-378) skips rows with
            // coefficients exceeding ~1000 bits. Matching on Rational::Big is a
            // zero-cost proxy: most LRA coefficients are Small(i64, i64).
            if row
                .coeffs
                .iter()
                .any(|(_, c)| matches!(c, Rational::Big(_)))
            {
                continue;
            }
            // #4919: Previously skipped rows with no unassigned atoms and
            // no refinement candidates. This optimization prevented the
            // fixpoint from discovering transitive bound implications:
            // deriving a bound for variable X in row A enables row B to
            // derive a bound for variable Y, even when neither X nor Y
            // has atoms. Z3's bound_analyzer_on_row has no such skip.
            // Removing this skip allows the current pass to discover row-local
            // implications, while cross-row cascading is handled by the next
            // compute_implied_bounds() call via touched_rows seeding below.

            // Build the full equation: x_b + sum((-a_j) * x_j) = constant
            // We analyze ALL variables in the equation (basic + nonbasic).
            //
            // Z3-style bound_analyzer_on_row algorithm:
            // Track how many variables lack needed bounds in each direction.
            // - 0 unbounded: derive bounds for ALL variables (O(n) trick)
            // - 1 unbounded: derive bound for that single variable
            // - 2+ unbounded: no derivation possible
            //
            // All arithmetic uses Rational (inline i64/i64) to avoid
            // BigRational heap allocation in the common case (#4919).

            // #7973: Two-pass approach for LB direction.
            // Pass 1: Cheap pre-scan to count unbounded variables (no arithmetic).
            // Pass 2: Full arithmetic only for rows with <=1 unbounded.
            // This avoids expensive Rational operations on rows where 2+ variables
            // lack bounds, which is the common case on LP-heavy benchmarks.
            let mut lb_unbounded_count = 0u32;
            let mut lb_prescan_valid = true;
            if self.implied_bounds[bv].0.is_none() {
                lb_unbounded_count += 1;
            }
            if lb_unbounded_count < 2 {
                for &(var, ref coeff) in &row.coeffs {
                    let vi = var as usize;
                    if vi >= num_vars {
                        lb_prescan_valid = false;
                        break;
                    }
                    let eq_c_pos = coeff.is_negative();
                    let has_bound = if eq_c_pos {
                        self.implied_bounds[vi].0.is_some()
                    } else {
                        self.implied_bounds[vi].1.is_some()
                    };
                    if !has_bound {
                        lb_unbounded_count += 1;
                        if lb_unbounded_count >= 2 {
                            break;
                        }
                    }
                }
            }

            // Lower bound direction: compute sum of min contributions
            // For eq_coeff > 0: min = eq_coeff * lb(x)
            // For eq_coeff < 0: min = eq_coeff * ub(x)
            // Track strictness: derived bound is strict iff any contributing
            // bound is strict (Z3 infinitesimal model, #4919).
            let mut lb_total = Rational::zero();
            let mut lb_unbounded_idx: i32 = -1; // -1: none, >=0: exactly one, -2: multiple
            let mut lb_valid = true;
            let mut lb_any_strict = false;

            // Reuse pre-allocated contribution storage (cleared each row).
            // Each entry: (var_idx, eq_coeff, min_contribution, is_strict)
            lb_contribs.clear();

            // Skip the expensive arithmetic pass for rows with 2+ unbounded.
            if lb_prescan_valid && lb_unbounded_count < 2 {
                // Basic var: eq_coeff = +1
                let bv_eq_c = Rational::one();
                match &self.implied_bounds[bv].0 {
                    Some(ib) => {
                        let contrib = &bv_eq_c * &ib.value;
                        lb_total += &contrib;
                        lb_any_strict |= ib.strict;
                        lb_contribs.push((bv, bv_eq_c.clone(), contrib, ib.strict));
                    }
                    None => {
                        lb_contribs.push((bv, bv_eq_c.clone(), Rational::zero(), false));
                        lb_unbounded_idx = 0; // index into lb_contribs
                    }
                }

                for &(var, ref coeff) in &row.coeffs {
                    let vi = var as usize;
                    if vi >= num_vars {
                        lb_valid = false;
                        break;
                    }
                    // #7973: Avoid computing -coeff; check coeff sign directly.
                    // eq_c = -coeff, so eq_c.is_positive() iff coeff.is_negative().
                    let eq_c_pos = coeff.is_negative();
                    let bound_ref = if eq_c_pos {
                        &self.implied_bounds[vi].0
                    } else {
                        &self.implied_bounds[vi].1
                    };
                    match bound_ref {
                        Some(ib) => {
                            let eq_c = -coeff;
                            // #8003: Fused multiply-add keeps accumulation in i128
                            // with a single GCD reduction instead of separate mul+add.
                            // This delays BigRational fallback by ~64 bits of headroom.
                            let contrib = lb_total.add_product(&eq_c, &ib.value);
                            lb_any_strict |= ib.strict;
                            // #8782: If the accumulator overflowed to BigRational,
                            // bail out — remaining arithmetic on this row will be
                            // dominated by BigRational GCD, which is the primary
                            // bottleneck on clocksynchro-style benchmarks.
                            if !lb_total.is_small() {
                                lb_valid = false;
                                break;
                            }
                            lb_contribs.push((vi, eq_c, contrib, ib.strict));
                        }
                        None => {
                            // Exactly one unbounded (pre-scan guaranteed <=1).
                            let eq_c = -coeff;
                            lb_contribs.push((vi, eq_c, Rational::zero(), false));
                            lb_unbounded_idx = (lb_contribs.len() - 1) as i32;
                        }
                    }
                }
            } else {
                lb_valid = lb_prescan_valid;
                lb_unbounded_idx = -2; // 2+ unbounded
            }

            if lb_valid {
                if lb_unbounded_idx == -1 {
                    // ALL variables bounded: derive bound for each variable.
                    // Strictness fix (#6242): when deriving a bound for variable vi,
                    // the strictness should be the OR of all OTHER variables'
                    // contributing bound strictness (excluding vi's own bound).
                    // Using lb_any_strict for all variables is unsound when only one
                    // variable contributes a strict bound — the derivation for THAT
                    // variable should NOT be strict.
                    let lb_strict_count = lb_contribs.iter().filter(|c| c.3).count();
                    let rhs_base = &row.constant - &lb_total;
                    // #8800: Skip derivation when rhs_base overflowed to BigRational.
                    // Each bound_val division below would trigger expensive BigRational
                    // GCD, which dominates compute_implied_bounds on LP-heavy benchmarks.
                    if !rhs_base.is_small() {
                        // Fall through — skip all lb derivations for this row.
                    } else {
                    for &(vi, ref eq_c, ref contrib, var_strict) in &lb_contribs {
                        if eq_c.is_zero() {
                            continue;
                        }
                        let bound_val = &(&rhs_base + contrib) / eq_c;
                        // derived_strict = any OTHER variable's bound was strict
                        let derived_strict = if lb_strict_count >= 2 {
                            true // multiple strict bounds → all derivations are strict
                        } else if lb_strict_count == 1 {
                            !var_strict // strict only if THIS variable wasn't the strict one
                        } else {
                            false // no strict bounds at all
                        };
                        let is_upper = eq_c.is_positive();
                        // #6615: Skip bounds that cannot imply any unassigned atom.
                        if !self.bound_is_interesting(vi as u32, is_upper, &bound_val) {
                            continue;
                        }
                        // #6617: Build eager explanation — all OTHER variables that
                        // contributed bounds in this LB direction derivation.
                        // LB direction: eq_c > 0 → used lower bound, eq_c < 0 → used upper.
                        let mut contributing_vars = SmallVec::new();
                        for &(other_vi, ref other_eq_c, _, _) in &lb_contribs {
                            if other_vi == vi {
                                continue;
                            }
                            let used_upper = other_eq_c.is_negative();
                            contributing_vars.push((other_vi as u32, used_upper));
                        }
                        let ib = ImpliedBound {
                            value: bound_val,
                            strict: derived_strict,
                            row_idx,
                            explanation: Some(BoundExplanation { contributing_vars }),
                        };
                        if is_upper {
                            updates.push((vi, None, Some(ib)));
                        } else {
                            updates.push((vi, Some(ib), None));
                        }
                    }
                    } // close rhs_base.is_small() else block
                } else if lb_unbounded_idx >= 0 {
                    // Exactly one unbounded: derive bound for that variable.
                    let idx = lb_unbounded_idx as usize;
                    let (target_vi, ref eq_c, _, _) = lb_contribs[idx];
                    if !eq_c.is_zero() {
                        let rhs = &row.constant - &lb_total;
                        let bound_val = &rhs / eq_c;
                        let is_upper = eq_c.is_positive();
                        // #8782: Always store single-unbounded implied bounds.
                        // This variable had NO bound on this side before; the new
                        // bound is genuine new information for cascade derivations.
                        // Z3 applies bound_is_interesting at the propagation layer,
                        // not at LP-level derivation. Filtering here blocks
                        // transitive cascades through intermediate variables.
                        {
                            let derived_strict = lb_any_strict;
                            // #6617: Build eager explanation — all other variables.
                            let mut contributing_vars = SmallVec::new();
                            for &(other_vi, ref other_eq_c, _, _) in &lb_contribs {
                                if other_vi == target_vi {
                                    continue;
                                }
                                let used_upper = other_eq_c.is_negative();
                                contributing_vars.push((other_vi as u32, used_upper));
                            }
                            let ib = ImpliedBound {
                                value: bound_val,
                                strict: derived_strict,
                                row_idx,
                                explanation: Some(BoundExplanation { contributing_vars }),
                            };
                            if is_upper {
                                updates.push((target_vi, None, Some(ib)));
                            } else {
                                updates.push((target_vi, Some(ib), None));
                            }
                        }
                    }
                }
                // lb_unbounded_idx == -2: 2+ unbounded, skip
            }

            // #7973: Two-pass approach for UB direction (symmetric with LB).
            let mut ub_unbounded_count = 0u32;
            let mut ub_prescan_valid = true;
            if self.implied_bounds[bv].1.is_none() {
                ub_unbounded_count += 1;
            }
            if ub_unbounded_count < 2 {
                for &(var, ref coeff) in &row.coeffs {
                    let vi = var as usize;
                    if vi >= num_vars {
                        ub_prescan_valid = false;
                        break;
                    }
                    let eq_c_pos = coeff.is_negative();
                    let has_bound = if eq_c_pos {
                        self.implied_bounds[vi].1.is_some()
                    } else {
                        self.implied_bounds[vi].0.is_some()
                    };
                    if !has_bound {
                        ub_unbounded_count += 1;
                        if ub_unbounded_count >= 2 {
                            break;
                        }
                    }
                }
            }

            // Upper bound direction (symmetric): sum of max contributions
            let mut ub_total = Rational::zero();
            let mut ub_unbounded_idx: i32 = -1;
            let mut ub_valid = true;
            let mut ub_any_strict = false;
            ub_contribs.clear();

            if ub_prescan_valid && ub_unbounded_count < 2 {
                // Basic var: eq_coeff = +1, max contribution = ub(x_b)
                let bv_eq_c_ub = Rational::one();
                match &self.implied_bounds[bv].1 {
                    Some(ib) => {
                        let contrib = &bv_eq_c_ub * &ib.value;
                        ub_total += &contrib;
                        ub_any_strict |= ib.strict;
                        ub_contribs.push((bv, bv_eq_c_ub, contrib, ib.strict));
                    }
                    None => {
                        ub_contribs.push((bv, bv_eq_c_ub, Rational::zero(), false));
                        ub_unbounded_idx = 0;
                    }
                }

                for &(var, ref coeff) in &row.coeffs {
                    let vi = var as usize;
                    if vi >= num_vars {
                        ub_valid = false;
                        break;
                    }
                    // #7973: Same sign-check optimization as LB direction.
                    let eq_c_pos = coeff.is_negative();
                    let bound_ref = if eq_c_pos {
                        &self.implied_bounds[vi].1
                    } else {
                        &self.implied_bounds[vi].0
                    };
                    match bound_ref {
                        Some(ib) => {
                            let eq_c = -coeff;
                            // #8003: Fused multiply-add (see LB direction comment).
                            let contrib = ub_total.add_product(&eq_c, &ib.value);
                            ub_any_strict |= ib.strict;
                            // #8782: Bail on BigRational overflow (see LB comment).
                            if !ub_total.is_small() {
                                ub_valid = false;
                                break;
                            }
                            ub_contribs.push((vi, eq_c, contrib, ib.strict));
                        }
                        None => {
                            // Exactly one unbounded (pre-scan guaranteed <=1).
                            let eq_c = -coeff;
                            ub_contribs.push((vi, eq_c, Rational::zero(), false));
                            ub_unbounded_idx = (ub_contribs.len() - 1) as i32;
                        }
                    }
                }
            } else {
                ub_valid = ub_prescan_valid;
                ub_unbounded_idx = -2; // 2+ unbounded
            }

            if ub_valid {
                if ub_unbounded_idx == -1 {
                    // ALL bounded: derive upper bound for each variable.
                    // Strictness fix (#6242): same as lower bound direction —
                    // exclude vi's own contribution from strictness aggregation.
                    let ub_strict_count = ub_contribs.iter().filter(|c| c.3).count();
                    let rhs_base = &row.constant - &ub_total;
                    // #8800: Skip derivation when rhs_base overflowed to BigRational.
                    if !rhs_base.is_small() {
                        // Skip all ub derivations for this row.
                    } else {
                    for &(vi, ref eq_c, ref contrib, var_strict) in &ub_contribs {
                        if eq_c.is_zero() {
                            continue;
                        }
                        let bound_val = &(&rhs_base + contrib) / eq_c;
                        let derived_strict = if ub_strict_count >= 2 {
                            true
                        } else if ub_strict_count == 1 {
                            !var_strict
                        } else {
                            false
                        };
                        // In UB direction: positive coeff → lower bound, negative → upper.
                        let is_upper = !eq_c.is_positive();
                        // #6615: Skip bounds that cannot imply any unassigned atom.
                        if !self.bound_is_interesting(vi as u32, is_upper, &bound_val) {
                            continue;
                        }
                        // #6617: Build eager explanation for UB direction.
                        // UB direction: eq_c > 0 → used upper bound, eq_c < 0 → used lower.
                        let mut contributing_vars = SmallVec::new();
                        for &(other_vi, ref other_eq_c, _, _) in &ub_contribs {
                            if other_vi == vi {
                                continue;
                            }
                            let used_upper = other_eq_c.is_positive();
                            contributing_vars.push((other_vi as u32, used_upper));
                        }
                        let ib = ImpliedBound {
                            value: bound_val,
                            strict: derived_strict,
                            row_idx,
                            explanation: Some(BoundExplanation { contributing_vars }),
                        };
                        if eq_c.is_positive() {
                            updates.push((vi, Some(ib), None));
                        } else {
                            updates.push((vi, None, Some(ib)));
                        }
                    }
                    } // close rhs_base.is_small() else block
                } else if ub_unbounded_idx >= 0 {
                    let idx = ub_unbounded_idx as usize;
                    let (target_vi, ref eq_c, _, _) = ub_contribs[idx];
                    if !eq_c.is_zero() {
                        let rhs = &row.constant - &ub_total;
                        let bound_val = &rhs / eq_c;
                        // #8782: Always store single-unbounded implied bounds
                        // (see LB single-unbounded path comment above).
                        {
                            let derived_strict = ub_any_strict;
                            // #6617: Build eager explanation for UB single-unbounded.
                            let mut contributing_vars = SmallVec::new();
                            for &(other_vi, ref other_eq_c, _, _) in &ub_contribs {
                                if other_vi == target_vi {
                                    continue;
                                }
                                let used_upper = other_eq_c.is_positive();
                                contributing_vars.push((other_vi as u32, used_upper));
                            }
                            let ib = ImpliedBound {
                                value: bound_val,
                                strict: derived_strict,
                                row_idx,
                                explanation: Some(BoundExplanation { contributing_vars }),
                            };
                            if eq_c.is_positive() {
                                updates.push((target_vi, Some(ib), None));
                            } else {
                                updates.push((target_vi, None, Some(ib)));
                            }
                        }
                    }
                }
            }
            // #8003: Stamp row generation after processing so it can be skipped
            // on the next iteration if no input bound changes.
            if row_idx < self.row_computed_gen.len() {
                self.row_computed_gen[row_idx] = self.bound_generation;
            }
        }

        // Apply deferred updates (only tighten, with strict-aware comparison)
        for (vi, new_lb, new_ub) in updates {
            if let Some(new_ib) = new_lb {
                let cur = &self.implied_bounds[vi].0;
                let tighter = match cur {
                    None => true,
                    Some(cur_ib) => {
                        new_ib.value > cur_ib.value
                            || (new_ib.value == cur_ib.value && new_ib.strict && !cur_ib.strict)
                    }
                };
                if tighter {
                    // Mark variable as dirty for interval propagation (#4919).
                    // Previously only variables with NO direct bound were marked,
                    // but tightened implied bounds can also enable new multi-variable
                    // interval propagations via compute_expr_interval().
                    newly_bounded.insert(vi as u32);
                    self.implied_bounds[vi].0 = Some(new_ib);
                    // #8003: Stamp variable generation so rows containing it
                    // will be re-analyzed on the next iteration.
                    self.bound_generation += 1;
                    if vi < self.var_bound_gen.len() {
                        self.var_bound_gen[vi] = self.bound_generation;
                    }
                }
            }
            if let Some(new_ib) = new_ub {
                let cur = &self.implied_bounds[vi].1;
                let tighter = match cur {
                    None => true,
                    Some(cur_ib) => {
                        new_ib.value < cur_ib.value
                            || (new_ib.value == cur_ib.value && new_ib.strict && !cur_ib.strict)
                    }
                };
                if tighter {
                    // Mark variable as dirty for interval propagation (#4919).
                    newly_bounded.insert(vi as u32);
                    self.implied_bounds[vi].1 = Some(new_ib);
                    // #8003: Stamp variable generation.
                    self.bound_generation += 1;
                    if vi < self.var_bound_gen.len() {
                        self.var_bound_gen[vi] = self.bound_generation;
                    }
                }
            }
            self.register_fixed_term_var(vi as u32);
        }
        // #4919: Seed touched_rows with rows containing newly-bounded
        // variables. This enables cascading across check() calls: bounds
        // derived in this fixpoint enable further derivations in the NEXT
        // compute_implied_bounds() call. Without this, the next call only
        // analyzes rows touched by new assert_var_bound calls (from BCP-fed
        // atom assertions), missing rows that could now derive bounds thanks
        // to the implied bounds we just computed.
        //
        // Clear first, then seed with cascade rows. New assert_var_bound
        // calls will add their own rows on top.
        self.touched_rows.clear();
        for &vi in &newly_bounded {
            let vi_usize = vi as usize;
            if vi_usize < self.col_index.len() {
                for &ri in &self.col_index[vi_usize] {
                    self.touched_rows.insert(ri);
                }
            }
            if let Some(&ri) = self.basic_var_to_row.get(&vi) {
                self.touched_rows.insert(ri);
            }
        }
        newly_bounded
    }

    /// Overlay a single variable's direct bounds into the implied_bounds slot.
    /// Extracted to avoid duplication between incremental and full-scan paths.
    fn overlay_direct_bound_for_var(
        info: &VarInfo,
        slot: &mut (Option<ImpliedBound>, Option<ImpliedBound>),
    ) {
        if let Some(b) = &info.lower {
            let direct_lb = ImpliedBound {
                value: b.value.clone(),
                strict: b.strict,
                row_idx: usize::MAX,
                explanation: None,
            };
            let replace = match &slot.0 {
                None => true,
                Some(existing) => {
                    direct_lb.value > existing.value
                        || (direct_lb.value == existing.value
                            && !existing.strict
                            && direct_lb.strict)
                }
            };
            if replace {
                slot.0 = Some(direct_lb);
            }
        }
        if let Some(b) = &info.upper {
            let direct_ub = ImpliedBound {
                value: b.value.clone(),
                strict: b.strict,
                row_idx: usize::MAX,
                explanation: None,
            };
            let replace = match &slot.1 {
                None => true,
                Some(existing) => {
                    direct_ub.value < existing.value
                        || (direct_ub.value == existing.value
                            && !existing.strict
                            && direct_ub.strict)
                }
            };
            if replace {
                slot.1 = Some(direct_ub);
            }
        }
    }
}
