// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl LraSolver {
    #[inline]
    pub(super) fn dual_simplex_iteration_budget(max_iters: usize, bland_mode: bool) -> usize {
        if bland_mode {
            max_iters.saturating_mul(10).min(10_000_000)
        } else {
            max_iters
        }
    }

    /// Run dual simplex to check feasibility
    /// Run dual simplex to check feasibility of the current LP state.
    ///
    /// Public for LIA's tentative big-cut testing (Z3 gomory.cpp:496-503).
    pub fn dual_simplex(&mut self) -> TheoryResult {
        // Limit iterations to prevent infinite loops.
        // With Bland's rule, simplex terminates in O(2^n) worst case but typically polynomial.
        // Z3's `tableau_rows` strategy has effectively NO iteration limit — it relies on
        // Bland's rule mathematical termination guarantee. Z4's Rational type uses an
        // inline i64/i64 fast path that avoids BigRational allocation in >95% of
        // operations, making per-iteration cost close to Z3's double arithmetic.
        // Scale 200 + cap 10M (#7852: was scale 20 + cap 1M, causing premature Unknown
        // on LP-family benchmarks like rand_70_300, vpm2-30, tsp_rand where Z3 solves
        // in 1-8s). For 300 rows + 370 vars: min(10000 + 670*200, 10M) = 144K iters.
        // UNSAT detection exits early regardless of cap; cap only matters for feasibility
        // search on large SAT instances.
        let base_iters = 10_000usize;
        let scale_iters = (self.rows.len() + self.vars.len()) * 200;
        let max_iters = std::cmp::min(base_iters + scale_iters, 10_000_000);
        self.dual_simplex_with_max_iters(max_iters)
    }

    /// Run dual simplex with a tighter per-invocation budget for propagation-time
    /// checks (#8003 Gap 4). During BCP, a single theory check should not consume
    /// the entire timeout on degenerate problems. If the budget is exhausted, return
    /// `Sat` ("no conflict found") so the SAT solver can continue — the full check()
    /// call will run the unrestricted simplex later.
    ///
    /// Budget: `max(200, 5 * num_vars)` — enough for typical propagation but caps
    /// degenerate cases. Reduced from `max(1000, 10 * num_vars)` because profile
    /// data from sc-6 and simple_startup benchmarks shows BCP simplex calls
    /// dominate runtime: 7125 calls x 2000 iter budget = 14M iterations, while
    /// Z3 runs 0 simplex during propagation. A smaller budget catches shallow
    /// conflicts (which are most theory conflicts) while deferring deeper ones
    /// to the full check() call.
    pub fn dual_simplex_propagate(&mut self) -> TheoryResult {
        let propagation_budget = std::cmp::max(200, 5 * self.vars.len());
        let result = self.dual_simplex_with_max_iters(propagation_budget);
        // Budget exhaustion during propagation is not a real Unknown — it just means
        // we didn't find a conflict within the budget. Return Sat so the SAT solver
        // continues; the final check() will run the full simplex.
        if matches!(result, TheoryResult::Unknown) {
            self.propagation_budget_exhaustions += 1;
            debug!(
                target: "z4::lra",
                budget = propagation_budget,
                exhaustions = self.propagation_budget_exhaustions,
                "LRA propagation simplex budget exhausted, deferring to full check"
            );
            TheoryResult::Sat
        } else {
            result
        }
    }

    pub(crate) fn dual_simplex_with_max_iters(&mut self, max_iters: usize) -> TheoryResult {
        let mut iterations_run = 0usize;
        let mut pivot_count = 0usize;
        let mut nonbasic_repair_rounds = 0usize;
        let mut leaving_fixups = 0usize;
        let summarize = |outcome: &'static str,
                         reason: &'static str,
                         iterations: usize,
                         pivots: usize,
                         repairs: usize,
                         fixups: usize,
                         rows: usize,
                         vars: usize| {
            info!(
                target: "z4::lra",
                outcome,
                reason,
                iterations,
                pivots,
                nonbasic_repair_rounds = repairs,
                leaving_fixups = fixups,
                rows,
                vars,
                max_iters,
                "LRA dual simplex summary"
            );
        };

        #[cfg(debug_assertions)]
        self.debug_assert_tableau_consistency("dual_simplex:start");

        // Check for trivial conflicts from constant constraints (e.g., `0 < 0` or `-1 >= 0`)
        if let Some(lits) = self.trivial_conflict.take() {
            summarize(
                "unsat",
                "trivial_conflict",
                iterations_run,
                pivot_count,
                nonbasic_repair_rounds,
                leaving_fixups,
                self.rows.len(),
                self.vars.len(),
            );
            return TheoryResult::Unsat(lits);
        }

        // Quick UNSAT check: contradictory bounds on a variable are immediately infeasible.
        //
        // This is important for problems that are purely a conjunction of bounds (no tableau
        // rows). The main dual-simplex loop focuses on pivoting basic variables, so we need an
        // explicit contradiction check for non-basic-only constraints.
        for var in 0..self.vars.len() {
            let info = &self.vars[var];
            let (Some(lower), Some(upper)) = (&info.lower, &info.upper) else {
                continue;
            };

            let contradicts = lower.value > upper.value
                || (lower.value == upper.value && (lower.strict || upper.strict));
            if contradicts {
                if debug_lra() {
                    self.debug_log_contradictory_bounds(var as u32, lower, upper);
                }
                use num_rational::Rational64;
                let mut literals = Vec::new();
                let mut coefficients = Vec::new();
                let mut all_fit = true;
                // Track whether each bound contributed real (non-sentinel) reasons.
                // Reasonless bounds must still degrade to Unknown, but sentinel-only
                // axioms can be omitted from a partial conflict just like the row-
                // based conflict builders do (#6679, #4919).
                let mut lower_has_real = false;
                let mut upper_has_real = false;
                for ((reason, reason_value), scale) in
                    lower.reasons.iter().zip(&lower.reason_values).zip(
                        lower
                            .reason_scales
                            .iter()
                            .chain(std::iter::repeat(crate::types::big_rational_one())),
                    )
                {
                    if !reason.is_sentinel() {
                        lower_has_real = true;
                        literals.push(TheoryLit::new(*reason, *reason_value));
                        match Self::bigrational_to_rational64(scale) {
                            Some(c) => coefficients.push(c),
                            None => {
                                all_fit = false;
                                coefficients.push(Rational64::from(1));
                            }
                        }
                    }
                }
                for ((reason, reason_value), scale) in
                    upper.reasons.iter().zip(&upper.reason_values).zip(
                        upper
                            .reason_scales
                            .iter()
                            .chain(std::iter::repeat(crate::types::big_rational_one())),
                    )
                {
                    if !reason.is_sentinel() {
                        upper_has_real = true;
                        literals.push(TheoryLit::new(*reason, *reason_value));
                        match Self::bigrational_to_rational64(scale) {
                            Some(c) => coefficients.push(c),
                            None => {
                                all_fit = false;
                                coefficients.push(Rational64::from(1));
                            }
                        }
                    }
                }
                let lower_is_reasonless = lower.reasons.is_empty();
                let upper_is_reasonless = upper.reasons.is_empty();
                if lower_is_reasonless || upper_is_reasonless {
                    summarize(
                        "unknown",
                        "bound_conflict_without_literals",
                        iterations_run,
                        pivot_count,
                        nonbasic_repair_rounds,
                        leaving_fixups,
                        self.rows.len(),
                        self.vars.len(),
                    );
                    return TheoryResult::Unknown;
                }
                let has_sentinel_only_bound = !lower_has_real || !upper_has_real;
                if has_sentinel_only_bound {
                    if literals.is_empty() {
                        summarize(
                            "unknown",
                            "bound_conflict_without_literals",
                            iterations_run,
                            pivot_count,
                            nonbasic_repair_rounds,
                            leaving_fixups,
                            self.rows.len(),
                            self.vars.len(),
                        );
                        return TheoryResult::Unknown;
                    }
                    let (dedup_lits, _) = Self::deduplicate_conflict(literals, None);
                    debug_assert!(
                        !dedup_lits.is_empty(),
                        "BUG: sentinel-only contradictory-bounds conflict lost all real literals"
                    );
                    summarize(
                        "unsat",
                        "contradictory_variable_bounds_partial",
                        iterations_run,
                        pivot_count,
                        nonbasic_repair_rounds,
                        leaving_fixups,
                        self.rows.len(),
                        self.vars.len(),
                    );
                    return TheoryResult::UnsatWithFarkas(TheoryConflict::new(dedup_lits));
                }
                let farkas_opt = if all_fit {
                    Some(FarkasAnnotation::new(coefficients))
                } else {
                    None
                };
                let (dedup_lits, dedup_coeffs) =
                    Self::deduplicate_conflict(literals, farkas_opt.as_ref());
                let farkas = if !dedup_coeffs.is_empty() {
                    Some(FarkasAnnotation::new(dedup_coeffs))
                } else if all_fit {
                    Some(FarkasAnnotation::new(
                        (0..dedup_lits.len()).map(|_| Rational64::from(1)).collect(),
                    ))
                } else {
                    None
                };
                debug_assert!(
                    !dedup_lits.is_empty(),
                    "BUG: both bounds have real reasons but dedup produced empty literals"
                );
                summarize(
                    "unsat",
                    "contradictory_variable_bounds",
                    iterations_run,
                    pivot_count,
                    nonbasic_repair_rounds,
                    leaving_fixups,
                    self.rows.len(),
                    self.vars.len(),
                );
                return TheoryResult::UnsatWithFarkas(match farkas {
                    Some(f) => TheoryConflict::with_farkas(dedup_lits, f),
                    None => TheoryConflict::new(dedup_lits),
                });
            }
        }

        // Row-level infeasibility precheck for strict bounds (#2021).
        //
        // For each row basic_var = Σ(coeff_i * nb_var_i) + constant, compute the implied
        // bounds on basic_var from the non-basic variables' bounds. If the implied lower
        // bound (considering strictness) exceeds the upper bound, or vice versa, it's UNSAT.
        //
        // This catches infeasibility without running simplex iterations (e.g., x > 0,
        // y > 0, x + y <= 0). Even with InfRational eliminating cycling, this precheck
        // provides faster UNSAT detection by examining row structure directly.
        if let Some(conflict) = self.check_row_strict_infeasibility() {
            summarize(
                "unsat",
                "row_strict_infeasibility_precheck",
                iterations_run,
                pivot_count,
                nonbasic_repair_rounds,
                leaving_fixups,
                self.rows.len(),
                self.vars.len(),
            );
            return conflict;
        }

        let debug = debug_lra();
        if debug {
            safe_eprintln!(
                "[LRA] dual_simplex: {} rows, {} vars, max_iters={}",
                self.rows.len(),
                self.vars.len(),
                max_iters
            );
        }

        let mut last_print = 0usize;
        // Cycling detection: track basis signatures (hash of basic variable set).
        // With InfRational (#4919 RC0), degenerate cycling from strict bounds
        // is eliminated. The basis hash check serves as a safety net for any
        // remaining degenerate cases (e.g., equal non-strict bounds creating
        // zero-step pivots). When repeated bases are detected, Bland mode
        // activates to guarantee termination (#2718, #4919 Phase 2).

        // Reset Bland mode at the start of each simplex invocation (#4919 Phase 2).
        // Bland mode is activated during the run if basis repeats are detected.
        self.bland_mode = false;
        self.basis_repeat_count = 0;

        // Compute initial basis hash from all basic variables (#6221 Finding 1).
        // Use incremental XOR hashing: O(1) per pivot instead of O(rows).
        // mix_u32 provides avalanche mixing to avoid trivial XOR collisions.
        let mut basis_hash: u64 = 0;
        for row in &self.rows {
            basis_hash ^= Self::mix_u32(row.basic_var);
        }
        let mut prev_basis_hash: u64 = basis_hash;

        // Build infeasible heap before the main loop (#4919 Phase B, #8782).
        // When heap_stale is false, incremental track_var_feasibility() calls
        // during bound assertion have kept the heap current — skip the O(rows)
        // full rebuild.
        if self.heap_stale {
            self.rebuild_infeasible_heap();
        }

        let bland_gated_cap = Self::dual_simplex_iteration_budget(max_iters, true);
        for iter in 0..bland_gated_cap {
            // #7852: keep the smaller budget while searching normally, but
            // once repeated bases trigger Bland mode allow up to 10x more
            // pivots (capped at 10M) so LP-family cases can finish.
            let cap = Self::dual_simplex_iteration_budget(max_iters, self.bland_mode);
            if iter >= cap {
                break;
            }
            iterations_run = iter + 1;
            trace!(
                target: "z4::lra",
                iter,
                rows = self.rows.len(),
                vars = self.vars.len(),
                "LRA dual simplex iteration start"
            );
            if debug && (iter < 20 || iter - last_print >= 10000) {
                last_print = iter;
                safe_eprintln!(
                    "[LRA] iter {} - {} rows, {} vars",
                    iter,
                    self.rows.len(),
                    self.vars.len()
                );
            }
            // Extract infeasible basic variable with greatest bound violation (#4919).
            // Greatest-error pivot reduces total pivots by attacking largest violations first.
            let violated_row = self.pop_greatest_error();

            let Some((row_idx, violated_bound)) = violated_row else {
                if debug && iter < 20 {
                    safe_eprintln!("[LRA] iter {} - no violated row, checking non-basic", iter);
                }
                // All basic variables satisfy bounds - check non-basic too.
                // Iterate in-place to avoid Vec<u32> allocation per SAT check.
                let mut saw_violation = false;
                let mut did_fix = false;
                for i in 0..self.vars.len() {
                    if !matches!(self.vars[i].status, Some(VarStatus::NonBasic)) {
                        continue;
                    }
                    let var = i as u32;
                    if let Some(violated_type) = self.violates_bounds(var) {
                        saw_violation = true;
                        let info = &self.vars[var as usize];
                        if let Some(nv) = Self::choose_nonbasic_fix_value(info, violated_type) {
                            self.update_nonbasic(var, nv);
                            did_fix = true;
                        }
                    }
                }

                // If we changed any non-basic assignments (or observed a strict-at-bound
                // violation we didn't resolve here), re-enter the main loop so we can
                // pivot on any newly violated basic variables.
                if did_fix || saw_violation {
                    nonbasic_repair_rounds += 1;
                    debug!(
                        target: "z4::lra",
                        iter,
                        saw_violation,
                        did_fix,
                        "LRA non-basic repair round before continuing"
                    );
                    if debug && iter < 20 {
                        safe_eprintln!("[LRA] iter {} - fixed non-basic, continuing", iter);
                    }
                    continue;
                }

                if debug {
                    safe_eprintln!("[LRA] Returning Sat at iter {}", iter);
                    for (i, info) in self.vars.iter().enumerate() {
                        let status = match &info.status {
                            Some(VarStatus::Basic(r)) => format!("B(row{r})"),
                            Some(VarStatus::NonBasic) => "NB".to_string(),
                            None => "?".to_string(),
                        };
                        safe_eprintln!("[LRA]   var {} = {} ({})", i, info.value, status);
                    }
                }
                summarize(
                    "sat",
                    "all_bounds_satisfied",
                    iterations_run,
                    pivot_count,
                    nonbasic_repair_rounds,
                    leaving_fixups,
                    self.rows.len(),
                    self.vars.len(),
                );
                return TheoryResult::Sat;
            };

            if debug && iter < 20 {
                let row = &self.rows[row_idx];
                let basic_var = row.basic_var;
                let basic_info = &self.vars[basic_var as usize];
                let lb = basic_info
                    .lower
                    .as_ref()
                    .map(|b| format!("{}({})", b.value, if b.strict { "<" } else { "<=" }))
                    .unwrap_or_default();
                let ub = basic_info
                    .upper
                    .as_ref()
                    .map(|b| format!("{}({})", b.value, if b.strict { ">" } else { ">=" }))
                    .unwrap_or_default();
                safe_eprintln!("[LRA] iter {} - violated row {}, basic_var={}, val={}, lb={}, ub={}, bound {:?}",
                    iter, row_idx, basic_var, basic_info.value, lb, ub, violated_bound);
            }

            // Find a suitable pivot candidate using cost-benefit heuristic (#4919 Phase 2).
            // Prefers entering variables with smaller column size (cheaper pivot).
            // Falls back to Bland's rule after BLAND_THRESHOLD repeated bases to
            // guarantee termination on degenerate LPs (#2718).
            let chosen: Option<(u32, InfRational)> = if let Some((entering_var, _direction)) =
                self.find_beneficial_entering(row_idx, violated_bound)
            {
                let new_val = self.compute_update_amount(row_idx, entering_var, violated_bound);
                Some((entering_var, new_val))
            } else {
                None
            };

            let Some((entering_var, new_val)) = chosen else {
                let conflict = self.build_conflict_with_farkas(row_idx);
                if conflict.literals.is_empty() {
                    summarize(
                        "unknown",
                        "conflict_without_literals",
                        iterations_run,
                        pivot_count,
                        nonbasic_repair_rounds,
                        leaving_fixups,
                        self.rows.len(),
                        self.vars.len(),
                    );
                    return TheoryResult::Unknown;
                }
                summarize(
                    "unsat",
                    "no_pivot_candidate_conflict",
                    iterations_run,
                    pivot_count,
                    nonbasic_repair_rounds,
                    leaving_fixups,
                    self.rows.len(),
                    self.vars.len(),
                );
                // Soundness check: conflict clause must be non-empty when
                // returning UNSAT (empty conflicts degrade to Unknown above).
                debug_assert!(
                    !conflict.literals.is_empty(),
                    "BUG: simplex returning UnsatWithFarkas with empty conflict clause"
                );
                return TheoryResult::UnsatWithFarkas(conflict);
            };

            debug!(
                target: "z4::lra",
                iter,
                row_idx,
                entering_var,
                new_value = %new_val,
                "LRA pivot candidate selected"
            );

            if debug && iter < 20 {
                let nb_info = &self.vars[entering_var as usize];
                let nb_lb = nb_info
                    .lower
                    .as_ref()
                    .map(|b| format!("{}({})", b.value, if b.strict { "<" } else { "<=" }))
                    .unwrap_or_default();
                let nb_ub = nb_info
                    .upper
                    .as_ref()
                    .map(|b| format!("{}({})", b.value, if b.strict { ">" } else { ">=" }))
                    .unwrap_or_default();
                safe_eprintln!(
                    "[LRA] iter {} - pivot: entering_var={}, old_val={}, new_val={}, lb={}, ub={}",
                    iter,
                    entering_var,
                    nb_info.value,
                    new_val,
                    nb_lb,
                    nb_ub
                );
            }

            // Capture leaving variable before pivot
            let leaving_var = self.rows[row_idx].basic_var;

            // Update the non-basic variable
            self.update_nonbasic(entering_var, new_val);

            if debug && iter < 20 {
                let row = &self.rows[row_idx];
                let basic_info = &self.vars[row.basic_var as usize];
                safe_eprintln!(
                    "[LRA] iter {} - after update: basic_var={} val={}",
                    iter,
                    row.basic_var,
                    basic_info.value
                );
            }

            // Pivot to swap basic/non-basic
            self.pivot(row_idx, entering_var);
            pivot_count += 1;

            // After pivot: entering_var is now basic, leaving_var is now non-basic.
            // Update heap membership for both (#4919 Phase B).
            self.track_var_feasibility(entering_var);
            self.track_var_feasibility(leaving_var);

            // Track basis hash for cycling detection → Bland mode activation (#4919 Phase 2).
            // Incremental O(1) update (#6221 Finding 1): XOR out leaving, XOR in entering.
            if !self.bland_mode {
                basis_hash ^= Self::mix_u32(leaving_var) ^ Self::mix_u32(entering_var);
                if basis_hash == prev_basis_hash {
                    self.basis_repeat_count += 1;
                    if self.basis_repeat_count >= BLAND_THRESHOLD {
                        self.bland_mode = true;
                        // Rebuild heap with smallest-index keys for anti-cycling
                        self.rebuild_infeasible_heap();
                        debug!(
                            target: "z4::lra",
                            iter,
                            repeat_count = self.basis_repeat_count,
                            "LRA activating Bland's rule after repeated bases"
                        );
                    }
                } else {
                    self.basis_repeat_count = 0;
                    prev_basis_hash = basis_hash;
                }
            }

            // After pivot, the leaving variable is now non-basic. Ensure it
            // sits at its nearest feasible bound. The update_nonbasic + pivot
            // sequence can leave it at an intermediate value when the entering
            // variable was clamped to its own bounds. Non-basic variables must
            // be at bounds for the simplex invariant (and Bland's rule
            // termination guarantee) to hold (#2718).
            {
                let violated = self.violates_bounds(leaving_var);
                if let Some(violated_type) = violated {
                    let info = &self.vars[leaving_var as usize];
                    if let Some(fix_val) = Self::choose_nonbasic_fix_value(info, violated_type) {
                        self.update_nonbasic(leaving_var, fix_val);
                        leaving_fixups += 1;
                    }
                }
            }

            #[cfg(debug_assertions)]
            self.debug_assert_tableau_consistency("dual_simplex:post_pivot");

            // Periodically re-check strict bound infeasibility (#2665).
            // After pivots transform the tableau, strict bound contradictions
            // may become detectable that weren't visible before the loop.
            // This is a fast UNSAT shortcut — detects row-level contradictions
            // involving strict bounds without waiting for the simplex to exhaust
            // all pivot candidates.
            if (iter + 1) % 64 == 0 {
                if let Some(conflict) = self.check_row_strict_infeasibility() {
                    summarize(
                        "unsat",
                        "row_strict_infeasibility_iterative",
                        iterations_run,
                        pivot_count,
                        nonbasic_repair_rounds,
                        leaving_fixups,
                        self.rows.len(),
                        self.vars.len(),
                    );
                    return conflict;
                }
            }
        }

        // Too many iterations - return unknown
        summarize(
            "unknown",
            "max_iterations_reached",
            iterations_run,
            pivot_count,
            nonbasic_repair_rounds,
            leaving_fixups,
            self.rows.len(),
            self.vars.len(),
        );
        TheoryResult::Unknown
    }
}
