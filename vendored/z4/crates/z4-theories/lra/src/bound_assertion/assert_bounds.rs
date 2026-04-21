// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl LraSolver {
    pub(crate) fn assert_bound_with_reasons(
        &mut self,
        expr: LinearExpr,
        mut bound: BigRational,
        bound_type: BoundType,
        mut strict: bool,
        reasons: &[(TermId, bool)],
        atom_key: Option<(TermId, bool)>,
    ) {
        // Integer canonicalization: for integer expressions, strict bounds
        // can be converted to non-strict with ±1 adjustment since all
        // values are integers. `expr < 0` → `expr <= -1`, `expr > 0` → `expr >= 1`.
        if self.integer_mode && strict {
            match bound_type {
                BoundType::Upper => {
                    // expr < bound → expr <= bound - 1
                    bound -= BigRational::one();
                    strict = false;
                }
                BoundType::Lower => {
                    // expr > bound → expr >= bound + 1
                    bound += BigRational::one();
                    strict = false;
                }
            }
        }

        if expr.is_constant() {
            // Pure constant comparison - check immediately.
            // For example, `(- n (+ i 1)) < (- n i)` simplifies to `-1 < 0`.
            // After cancellation: constant_expr <=/>=/</>= bound.
            let const_val = &expr.constant;
            let cmp = const_val.cmp_big(&bound);
            let satisfied = match (bound_type, strict) {
                (BoundType::Upper, false) => cmp != std::cmp::Ordering::Greater, // expr <= bound
                (BoundType::Upper, true) => cmp == std::cmp::Ordering::Less,     // expr < bound
                (BoundType::Lower, false) => cmp != std::cmp::Ordering::Less,    // expr >= bound
                (BoundType::Lower, true) => cmp == std::cmp::Ordering::Greater,  // expr > bound
            };
            if !satisfied && self.trivial_conflict.is_none() {
                // Constant constraint violated - record trivial conflict.
                // Only record the first conflict (don't overwrite with subsequent ones).
                //
                // #8012: Store ALL reason literals so the blocking clause is complete.
                // Previously only the first reason was kept, producing overly-strong
                // single-literal blocking clauses.
                //
                // Axioms (empty reasons) cannot produce a meaningful conflict literal.
                // If an axiom's constant check fails, the problem is theory-level UNSAT
                // and the conflict clause needs no blame literals (#6187).
                debug_assert!(
                    !reasons.is_empty(),
                    "BUG: axiom constant-expression violated (const={const_val}, bound={bound}, type={bound_type:?}, strict={strict})"
                );
                if !reasons.is_empty() {
                    let conflict_lits: Vec<TheoryLit> = reasons
                        .iter()
                        .map(|&(term, value)| TheoryLit::new(term, value))
                        .collect();
                    self.trivial_conflict = Some(conflict_lits);
                }
            }
            return;
        }

        // Fast path: a single affine variable constraint can be asserted as a direct bound.
        //
        // The atom parser normalizes comparisons into the form `expr <= bound` or `expr >= bound`,
        // where `expr` may include a constant offset (e.g. `x - 5 <= 0`).
        //
        // Avoid creating slack variables/tableau rows for the common case:
        //   coeff*x + const <= bound
        //   coeff*x + const >= bound
        if expr.coeffs.len() == 1 {
            let (var, coeff) = &expr.coeffs[0];
            if !coeff.is_zero() {
                let rhs = (bound - expr.constant.to_big()) / coeff.to_big();
                let coeff_positive = coeff.is_positive();
                let var_bound_type = match (bound_type, coeff_positive) {
                    (BoundType::Upper, true) | (BoundType::Lower, false) => BoundType::Upper, // x <= rhs
                    (BoundType::Upper, false) | (BoundType::Lower, true) => BoundType::Lower, // x >= rhs
                };
                // Farkas scale: when the original atom is `coeff*x + const <= bound`,
                // we normalize to `x <= (bound-const)/coeff`. The Farkas coefficient
                // for this reason must be scaled by 1/|coeff| so that the original
                // atom's variable terms cancel correctly in the certificate.
                let farkas_scale = BigRational::one() / coeff.abs_bigrational();
                if reasons.len() == 1 {
                    let (reason, reason_value) = reasons[0];
                    self.assert_var_bound(
                        *var,
                        rhs,
                        var_bound_type,
                        strict,
                        reason,
                        reason_value,
                        farkas_scale,
                    );
                } else {
                    // Multi-reason or axiom (empty reasons): use the
                    // multi-reason path which handles empty correctly (#6187).
                    let scales: Vec<BigRational> =
                        reasons.iter().map(|_| farkas_scale.clone()).collect();
                    self.assert_var_bound_with_reasons(
                        *var,
                        rhs,
                        var_bound_type,
                        strict,
                        reasons,
                        &scales,
                    );
                }
                return;
            }
        }

        // Reuse existing slack variable if this atom was previously asserted (#4919)
        // or pre-registered via register_atom (#4919 RC2).
        // After push/pop, bound_atoms is cleared but the slack variable and its
        // tableau row persist. Reusing the existing slack prevents unbounded tableau
        // growth across DPLL(T) backtracking cycles.
        let slack = if let Some((existing, ref cached_orig)) =
            atom_key.and_then(|k| self.atom_slack.get(&k).cloned())
        {
            // Reuse cached slack. Apply constant compensation (#6205):
            // The slack may have been created by a different atom's expression
            // via expr_to_slack, with a different constant offset. Without this
            // adjustment, re-assertions after push/pop assert the wrong bound,
            // causing false UNSAT on formulas with disjunctions.
            bound = bound - expr.constant.to_big() + cached_orig.to_big();
            existing
        } else {
            let (new_slack, orig_constant) = self.get_or_create_slack(&expr);
            // When the slack was created for an expression with a different constant
            // offset, adjust the bound to compensate (#6193).
            //
            // The slack `s` satisfies: s = sum(coeff_i * x_i) + orig_constant
            // We want to assert: sum(coeff_i * x_i) + expr.constant <=/>=  bound
            // Substituting: s - orig_constant + expr.constant <=/>=  bound
            // Therefore:    s <=/>=  bound - expr.constant + orig_constant
            bound = bound - expr.constant.to_big() + orig_constant.to_big();
            // Cache (slack, orig_constant) for reuse after push/pop (#6205)
            if let Some(key) = atom_key {
                self.atom_slack.insert(key, (new_slack, orig_constant.clone()));
            }
            new_slack
        };

        // Assert bound on slack variable. Scale is 1 because the slack variable
        // represents the original expression directly (no coefficient normalization).
        if self.debug_lra {
            safe_eprintln!(
                "[LRA]   -> slack var={}, adjusted_bound={}, {:?}, strict={}",
                slack,
                bound,
                bound_type,
                strict,
            );
        }
        if reasons.len() == 1 {
            let (reason, reason_value) = reasons[0];
            self.assert_var_bound(
                slack,
                bound,
                bound_type,
                strict,
                reason,
                reason_value,
                BigRational::one(),
            );
        } else {
            // Multi-reason or axiom (empty reasons): use the
            // multi-reason path which handles empty correctly (#6187).
            let scales: Vec<BigRational> = reasons.iter().map(|_| BigRational::one()).collect();
            self.assert_var_bound_with_reasons(slack, bound, bound_type, strict, reasons, &scales);
        }
    }

    /// Assert a bound on a single variable. Returns `true` if the bound was
    /// actually tightened (new bound is stricter than existing), `false` if
    /// the new bound was redundant.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn assert_var_bound(
        &mut self,
        var: u32,
        bound: BigRational,
        bound_type: BoundType,
        strict: bool,
        reason: TermId,
        reason_value: bool,
        reason_scale: BigRational,
    ) -> bool {
        let debug = self.debug_lra_bounds;
        if debug {
            safe_eprintln!("[LRA_BOUNDS] assert_var_bound: var={}, bound={}, type={:?}, strict={}, reason={:?}, scale={}",
                var, bound, bound_type, strict, reason, reason_scale);
        }

        while self.vars.len() <= var as usize {
            self.vars.push(VarInfo::default());
        }
        let info = &mut self.vars[var as usize];

        if debug {
            safe_eprintln!(
                "[LRA_BOUNDS]   BEFORE: lb={:?}, ub={:?}",
                info.lower.as_ref().map(|b| &b.value),
                info.upper.as_ref().map(|b| &b.value)
            );
        }

        // Save old bound for backtracking (only clone the bound being modified).
        let old_bound = match bound_type {
            BoundType::Lower => info.lower.clone(),
            BoundType::Upper => info.upper.clone(),
        };
        self.trail.push((var, bound_type, old_bound));

        let new_bound = Bound::new(
            bound.into(),
            vec![reason],
            vec![reason_value],
            vec![reason_scale],
            strict,
        );

        let tightened = match bound_type {
            BoundType::Lower => {
                // Only update if tighter
                let should_update = match &info.lower {
                    None => true,
                    Some(existing) => {
                        new_bound.value > existing.value
                            || (new_bound.value == existing.value
                                && new_bound.strict
                                && !existing.strict)
                    }
                };
                if should_update {
                    info.lower = Some(new_bound);
                }
                should_update
            }
            BoundType::Upper => {
                // Only update if tighter
                let should_update = match &info.upper {
                    None => true,
                    Some(existing) => {
                        new_bound.value < existing.value
                            || (new_bound.value == existing.value
                                && new_bound.strict
                                && !existing.strict)
                    }
                };
                if should_update {
                    info.upper = Some(new_bound);
                }
                should_update
            }
        };

        if debug {
            let info = &self.vars[var as usize];
            safe_eprintln!(
                "[LRA_BOUNDS]   AFTER: lb={:?}, ub={:?}, tightened={}",
                info.lower.as_ref().map(|b| &b.value),
                info.upper.as_ref().map(|b| &b.value),
                tightened,
            );
        }

        if tightened {
            self.bounds_tightened_since_simplex = true;
            self.direct_bounds_changed_since_implied = true;
            self.direct_bounds_changed_vars.push(var);
            self.propagation_dirty_vars.insert(var);
            // Mark rows containing this variable as touched (#4919).
            // Z3 equivalent: activate() → insert_to_columns_with_changed_bounds(j)
            // → detect_rows_with_changed_bounds() → add_column_rows_to_touched_rows(j).
            // Without this, compute_implied_bounds sees an empty touched_rows set
            // and derives 0 bounds on benchmarks with many free variables.
            let vi = var as usize;
            if vi < self.col_index.len() {
                for &ri in &self.col_index[vi] {
                    self.touched_rows.insert(ri);
                }
            }
            if let Some(&ri) = self.basic_var_to_row.get(&var) {
                self.touched_rows.insert(ri);
            }
            self.propagate_direct_touched_rows_pending = true;
            // Eager per-variable propagation (#4919 RC2): when a bound on this
            // variable tightens, immediately propagate implications to atoms
            // involving this variable. This avoids waiting for the full simplex
            // round and gives the SAT solver immediate pruning.
            self.propagate_var_atoms(var);
            // Eager fixed-variable equality detection (#6617 Packet 2):
            // When lower == upper for a variable, register it immediately so
            // the value-table lookup can fire equalities without waiting for
            // compute_implied_bounds(). Z3 equivalent: fixed_var_eh().
            let is_fixed = {
                let vi = var as usize;
                self.vars.get(vi).is_some_and(|info| {
                    matches!(
                        (&info.lower, &info.upper),
                        (Some(lb), Some(ub)) if !lb.strict && !ub.strict && lb.value == ub.value
                    )
                })
            };
            if is_fixed {
                self.register_fixed_term_var(var);
            }
            // Pre-simplex inline refinement removed (#6617): the post-simplex
            // compute_implied_bounds() + queue_post_simplex_refinements() path
            // already handles all materializable vars (including slack) in a
            // single O(touched_rows) batch pass. The inline per-variable scan
            // was O(N × rows_per_var) where N = bound tightenings per check,
            // causing 20-350x slowdowns on sc-* benchmarks vs Z3.

            // Incrementally update the infeasible heap for this variable and
            // all basic variables in rows containing it (#8782). This avoids
            // a full O(rows) rebuild_infeasible_heap() at the start of simplex
            // when only a few variables' bounds changed.
            if !self.heap_stale {
                self.track_var_feasibility(var);
                let vi = var as usize;
                if vi < self.col_index.len() {
                    let n = self.col_index[vi].len();
                    for idx in 0..n {
                        let ri = self.col_index[vi][idx];
                        let bv = self.rows[ri].basic_var;
                        self.track_var_feasibility(bv);
                    }
                }
            }
        }
        self.dirty = true;
        tightened
    }

    /// Assert a bound on a single variable with multiple reasons.
    /// Used when bounds are derived from multiple constraints (e.g., Diophantine solving).
    /// Returns `true` if the bound was actually tightened.
    pub(crate) fn assert_var_bound_with_reasons(
        &mut self,
        var: u32,
        bound: BigRational,
        bound_type: BoundType,
        strict: bool,
        reasons: &[(TermId, bool)],
        reason_scales: &[BigRational],
    ) -> bool {
        while self.vars.len() <= var as usize {
            self.vars.push(VarInfo::default());
        }
        let info = &mut self.vars[var as usize];

        // Save old bound for backtracking (only clone the bound being modified).
        let old_bound = match bound_type {
            BoundType::Lower => info.lower.clone(),
            BoundType::Upper => info.upper.clone(),
        };
        self.trail.push((var, bound_type, old_bound));

        let (reason_ids, reason_vals): (Vec<_>, Vec<_>) = reasons.iter().copied().unzip();
        let new_bound = Bound::new(
            bound.into(),
            reason_ids,
            reason_vals,
            reason_scales.to_vec(),
            strict,
        );

        let tightened = match bound_type {
            BoundType::Lower => {
                // Only update if tighter
                let should_update = match &info.lower {
                    None => true,
                    Some(existing) => {
                        new_bound.value > existing.value
                            || (new_bound.value == existing.value
                                && new_bound.strict
                                && !existing.strict)
                    }
                };
                if should_update {
                    info.lower = Some(new_bound);
                }
                should_update
            }
            BoundType::Upper => {
                // Only update if tighter
                let should_update = match &info.upper {
                    None => true,
                    Some(existing) => {
                        new_bound.value < existing.value
                            || (new_bound.value == existing.value
                                && new_bound.strict
                                && !existing.strict)
                    }
                };
                if should_update {
                    info.upper = Some(new_bound);
                }
                should_update
            }
        };

        if tightened {
            self.bounds_tightened_since_simplex = true;
            self.direct_bounds_changed_since_implied = true;
            self.direct_bounds_changed_vars.push(var);
            self.propagation_dirty_vars.insert(var);
            // Mark rows containing this variable as touched (#4919 Phase A)
            let vi = var as usize;
            if vi < self.col_index.len() {
                for &ri in &self.col_index[vi] {
                    self.touched_rows.insert(ri);
                }
            }
            if let Some(&ri) = self.basic_var_to_row.get(&var) {
                self.touched_rows.insert(ri);
            }
            self.propagate_direct_touched_rows_pending = true;
            self.propagate_var_atoms(var);
            // Incremental heap maintenance (#8782) — same as assert_var_bound.
            if !self.heap_stale {
                self.track_var_feasibility(var);
                let vi = var as usize;
                if vi < self.col_index.len() {
                    let n = self.col_index[vi].len();
                    for idx in 0..n {
                        let ri = self.col_index[vi][idx];
                        let bv = self.rows[ri].basic_var;
                        self.track_var_feasibility(bv);
                    }
                }
            }
        }
        self.dirty = true;
        tightened
    }
}
