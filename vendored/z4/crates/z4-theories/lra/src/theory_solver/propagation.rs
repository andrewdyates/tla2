// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Propagation pipeline for the LRA theory solver.

use super::*;

impl LraSolver {
    pub(super) fn propagate_impl(&mut self) -> Vec<TheoryPropagation> {
        let mut propagations = Vec::new();
        // Drain same-variable chain propagations computed in check().
        // Slack variables are filtered at the source (propagate_var_atoms,
        // compute_bound_propagations, implied bounds) via slack_var_set (#6242).
        let pending: Vec<PendingPropagation> = std::mem::take(&mut self.pending_propagations);
        let pending_count = pending.len();
        let mut seen = std::mem::take(&mut self.reason_seen_buf);
        seen.clear();
        let retained_dirty: Vec<u32> = self
            .propagation_dirty_vars
            .iter()
            .copied()
            .filter(|var| self.compound_use_index.contains_key(var))
            .collect();
        for p in pending {
            let mut prop = p.propagation;
            if p.deferred.is_some() {
                // #7935 / #6242: Deferred row-reason materialization is DISABLED.
                //
                // Row-walking at propagation time is unsound because the simplex
                // basis may have changed between check() and propagate(). Instead,
                // try to reconstruct the reason from the current variable-interval
                // bounds via compute_expr_interval + collect_interval_reasons.
                //
                // The interval path uses direct variable bounds (which have stable
                // reason_pairs) and implied bounds. For variables with only implied
                // bounds, collect_interval_reasons falls back to row-walking, which
                // carries the same unsoundness risk. However, the interval
                // confirmation step (checking that the atom IS still implied by
                // current bounds) acts as a semantic filter: if the basis change
                // invalidated the implication, the interval check will fail and the
                // propagation is silently dropped.
                //
                // If the interval path confirms the propagation, emit it eagerly.
                // Otherwise, silently drop the propagation.
                let emitted = 'interval: {
                    let atom_term = prop.literal.term;
                    let Some(Some(info)) = self.atom_cache.get(&atom_term) else {
                        break 'interval false;
                    };
                    let expr = info.expr.clone();
                    let is_le = info.is_le;
                    let strict = info.strict;
                    let (lb, ub) = self.compute_expr_interval(&expr);
                    let implied_true = if prop.literal.value {
                        if is_le {
                            ub.as_ref()
                                .is_some_and(|ep| Self::endpoint_implies_le_zero(ep, strict))
                        } else {
                            lb.as_ref()
                                .is_some_and(|ep| Self::endpoint_implies_ge_zero(ep, strict))
                        }
                    } else if is_le {
                        lb.as_ref()
                            .is_some_and(|ep| Self::endpoint_implies_not_le_zero(ep, strict))
                    } else {
                        ub.as_ref()
                            .is_some_and(|ep| Self::endpoint_implies_not_ge_zero(ep, strict))
                    };
                    if !implied_true {
                        break 'interval false;
                    }
                    let for_upper = if prop.literal.value { is_le } else { !is_le };
                    let reason = self.collect_interval_reasons(&expr, for_upper);
                    if reason.is_empty() {
                        break 'interval false;
                    }
                    prop.reason = reason;
                    self.deferred_reason_count += 1;
                    self.propagated_atoms
                        .insert((prop.literal.term, prop.literal.value));
                    propagations.push(prop);
                    true
                };
                if !emitted {
                    continue;
                }
            } else if !prop.reason.is_empty() {
                self.eager_reason_count += 1;
                propagations.push(prop);
            }
        }
        self.reason_seen_buf = seen;

        // #7982: Conflict-based propagation throttle. After many conflicts,
        // skip the expensive implied-bound computation and interval propagation.
        // Pending propagations from check() are still drained above (they were
        // computed before the threshold was hit). New interval-based propagations
        // are only derived when the conflict count is below the threshold.
        // Reference: Z3 theory_lra.cpp:3315 propagation_mode().
        const PROPAGATION_CONFLICT_THRESHOLD: u64 = 1000;
        if self.conflict_count >= PROPAGATION_CONFLICT_THRESHOLD {
            self.propagation_dirty_vars.clear();
            self.propagation_count += propagations.len() as u64;
            return propagations;
        }

        // #6987: Refresh simplex feasibility before propagate-time row analysis.
        // Z3's propagate_core() calls make_feasible() before deriving LP-backed
        // implications. Without this, compute_implied_bounds() runs against a
        // stale basis when BCP tightens bounds between check() calls.
        //
        // #6256: If the refresh fails (infeasible), skip interval propagation —
        // variable values are stale and would compute incorrect implied bounds.
        // check() will report the actual conflict on the next round.
        if !self.refresh_simplex_for_propagate() {
            self.propagation_dirty_vars.clear();
            return propagations;
        }

        // #6617 Packet 1: Run compute_implied_bounds during propagation when
        // rows are touched by BCP atom assertions. This restores the tighter
        // BCP -> theory -> BCP feedback loop that regressed out of current
        // HEAD during the lib.rs / module extraction churn.
        //
        // Reference: Z3 theory_lra.cpp:2206-2271, lar_solver.h:281-301
        //
        // Z3 runs touched-row analysis whenever rows are activated; skipping
        // small row sets strands single-row cascades until the next check()
        // round and leaves the main sc-* path on the slower check-time lane.
        if self.propagate_direct_touched_rows_pending && !self.touched_rows.is_empty() {
            // Snapshot touched rows before compute_implied_bounds clears them.
            // Used for offset equality discovery below.
            let touched_snapshot = self.touched_rows.clone();
            let newly_bounded = self.compute_implied_bounds();
            self.propagate_direct_touched_rows_pending = false;
            if !newly_bounded.is_empty() {
                self.propagation_dirty_vars.extend(&newly_bounded);
                self.queue_post_simplex_refinements(&newly_bounded, self.debug_lra);
            }
            // #6617 Packet 1: Discover offset equalities (nf==2 rows) from
            // the same touched rows. Z3's cheap_eq_on_nbase detects x1 = x2
            // when two rows share a non-fixed column y with coefficient +/-1
            // and equal offsets. Equalities feed the E-graph for BCP cascades.
            // Reference: z3/src/math/lp/lp_bound_propagator.h:357-418
            self.discover_offset_equalities(&touched_snapshot);
        }

        // #4919 Phase C: removed atom_cache.len() < 4 threshold.
        // Interval propagation now runs whenever dirty variables exist, regardless
        // of cache size. The dirty_vars filter already limits work to O(dirty × atoms_per_var).

        // Collect candidate atoms whose variables had bounds change (#4919 propagation opt).
        // Instead of scanning ALL atoms in atom_cache, only check atoms referencing
        // variables in propagation_dirty_vars. This reduces work from O(all_atoms) to
        // O(dirty_vars * atoms_per_var) per propagate() call.
        let dirty = std::mem::take(&mut self.propagation_dirty_vars);

        let candidates: Vec<(TermId, bool)> = if dirty.is_empty() {
            // No bound changes — skip interval propagation entirely.
            Vec::new()
        } else {
            // For each dirty variable, look up atoms that reference it via var_to_atoms.
            let mut seen = HashSet::new();
            let mut result = Vec::new();
            for &var in &dirty {
                // #7851 D2: Skip variables where all bound atoms are already assigned.
                let vi = var as usize;
                if vi < self.unassigned_atom_count.len() && self.unassigned_atom_count[vi] == 0 {
                    continue;
                }
                if let Some(atoms) = self.var_to_atoms.get(&var) {
                    for &atom_term in atoms {
                        if !seen.insert(atom_term) {
                            continue;
                        }
                        // Filter: not eq/distinct, not already asserted.
                        // Note: multi-variable atoms (coeffs.len() > 1) are now
                        // included (#4919). compute_expr_interval uses implied
                        // bounds to derive finite intervals for compound atoms.
                        if let Some(Some(info)) = self.atom_cache.get(&atom_term) {
                            if info.is_eq || info.is_distinct {
                                continue;
                            }
                            if self.asserted.contains_key(&atom_term) {
                                continue;
                            }
                            result.push((atom_term, info.strict));
                        }
                    }
                }
            }
            result
        };

        let candidate_count = candidates.len();
        for (atom_term, strict) in &candidates {
            // Borrow the expression from atom_cache without cloning.
            // We need the LinearExpr for compute_expr_interval and collect_interval_reasons.
            // Since we don't mutate atom_cache during this loop, this is safe via
            // index-based access: get the expr reference, compute, then collect reasons.
            let (expr, is_le) = match self.atom_cache.get(atom_term) {
                Some(Some(info)) => (&info.expr, info.is_le),
                _ => continue,
            };

            // Compound atoms are queued during check(); the remaining candidates are
            // single-variable atoms handled with plain interval propagation.
            let (lb, ub) = self.compute_expr_interval(expr);

            // is_le=true: atom asserts "expr <= 0" (or "expr < 0" if strict)
            //   true when UB(expr) <= 0, false when LB(expr) > 0
            // is_le=false: atom asserts "expr >= 0" (or "expr > 0" if strict)
            //   true when LB(expr) >= 0, false when UB(expr) < 0
            let implied_true = if is_le {
                ub.as_ref()
                    .is_some_and(|ep| Self::endpoint_implies_le_zero(ep, *strict))
            } else {
                lb.as_ref()
                    .is_some_and(|ep| Self::endpoint_implies_ge_zero(ep, *strict))
            };

            let implied_false = if is_le {
                lb.as_ref()
                    .is_some_and(|ep| Self::endpoint_implies_not_le_zero(ep, *strict))
            } else {
                ub.as_ref()
                    .is_some_and(|ep| Self::endpoint_implies_not_ge_zero(ep, *strict))
            };

            // Mutual exclusion: an atom cannot be both implied-true and implied-false.
            // If both hold, the expression interval brackets zero from both sides,
            // which means the bounds are contradictory — simplex should have returned UNSAT.
            debug_assert!(
                !(implied_true && implied_false),
                "LRA propagate() contradiction: atom {atom_term:?} is both implied-true and implied-false",
            );

            if implied_true && !self.propagated_atoms.contains(&(*atom_term, true)) {
                // is_le=true: implied-true uses UB → for_upper=true
                // is_le=false: implied-true uses LB → for_upper=false
                let for_upper = is_le;
                let reason = self.collect_interval_reasons(expr, for_upper);
                if !reason.is_empty() {
                    self.eager_reason_count += 1;
                    self.propagated_atoms.insert((*atom_term, true));
                    propagations.push(TheoryPropagation {
                        literal: TheoryLit::new(*atom_term, true),
                        reason,
                    });
                }
            } else if implied_false && !self.propagated_atoms.contains(&(*atom_term, false)) {
                // is_le=true: implied-false uses LB → for_upper=false
                // is_le=false: implied-false uses UB → for_upper=true
                let for_upper = !is_le;
                let reason = self.collect_interval_reasons(expr, for_upper);
                if !reason.is_empty() {
                    self.eager_reason_count += 1;
                    self.propagated_atoms.insert((*atom_term, false));
                    propagations.push(TheoryPropagation {
                        literal: TheoryLit::new(*atom_term, false),
                        reason,
                    });
                }
            }
        }

        if self.debug_lra && (!propagations.is_empty() || candidate_count > 0) {
            safe_eprintln!(
                "[LRA] propagate(): pending={}, candidates={}, interval_found={}, total={}",
                pending_count,
                candidate_count,
                propagations.len().saturating_sub(pending_count),
                propagations.len(),
            );
        }
        // Preserve compound wake keys across propagation so the next post-simplex
        // check can still observe them. `propagate()` consumes the current dirty
        // round, but compound wakeups are a cross-round structural signal rather
        // than a one-shot queue item.
        self.propagation_dirty_vars.extend(retained_dirty);
        // Soundness check: every propagation must have non-empty reasons, and
        // every reason literal must be currently asserted. Empty reasons cause
        // invalid conflict clauses in the DPLL layer; stale reasons cause unsound learning.
        // In combined_theory_mode (LIRA/AUFLIRA), cross-sort reason atoms from
        // the partner theory (e.g., LIA Int atoms) are injected via
        // assert_tight_bound/assert_cross_sort_bounds/assert_shared_equality and
        // are NOT tracked in this LRA's local `asserted` map. The reason chain
        // is still valid because the DPLL layer tracks all assertions globally.
        #[cfg(debug_assertions)]
        if !self.combined_theory_mode {
            for prop in &propagations {
                debug_assert!(
                    !prop.reason.is_empty(),
                    "LRA propagate() empty reason for {:?}",
                    prop.literal
                );
                for r in &prop.reason {
                    debug_assert!(
                        self.asserted.get(&r.term) == Some(&r.value),
                        "LRA propagate() reason {:?} not currently asserted (asserted={:?})",
                        r,
                        self.asserted.get(&r.term)
                    );
                }
            }
        } else {
            // In combined mode, still check non-empty reasons — that invariant
            // is universal regardless of which theory owns the reason atom.
            #[cfg(debug_assertions)]
            for prop in &propagations {
                debug_assert!(
                    !prop.reason.is_empty(),
                    "LRA propagate() empty reason for {:?} (combined mode)",
                    prop.literal
                );
            }
        }

        self.propagation_count += propagations.len() as u64;
        propagations
    }
}
