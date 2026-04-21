// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Core LIA check logic.
//!
//! Implements the main `check_inner()` method which coordinates:
//! - Constant Bool atom contradiction detection
//! - GCD feasibility tests
//! - Diophantine equation solving (2-variable and general)
//! - Iterative Diophantine tightening
//! - Gomory cut generation
//! - HNF cut generation
//! - Direct enumeration for small variable domains
//! - Integer bounds gap detection
//! - Modular constraint checking
//! - Branch-and-bound splitting

use super::*;

impl LiaSolver<'_> {
    /// #8012: Augment Farkas conflict with ALL shared equality reasons.
    ///
    /// When N-O shared equalities create tight bounds on simplex variables,
    /// the Farkas conflict may omit the EUF equality reason. This adds all
    /// shared equality reasons to ensure the conflict clause is sound.
    pub(super) fn augment_farkas_with_shared_eq_reasons(
        &self, conflict: &mut TheoryConflict,
    ) {
        if self.shared_equalities.is_empty() {
            return;
        }
        let mut seen: HashSet<TheoryLit> = conflict.literals.iter().copied().collect();
        let mut added = 0usize;
        for (_, _, reasons) in &self.shared_equalities {
            for reason in reasons {
                if seen.insert(*reason) {
                    conflict.literals.push(*reason);
                    added += 1;
                }
            }
        }
        if added > 0 {
            conflict.farkas = None;
        }
    }

    /// Core LIA check logic. Called by `TheorySolver::check()` which wraps the
    /// result to count conflicts.
    pub(super) fn check_inner(&mut self) -> TheoryResult {
        let debug = self.debug_lia_check;

        // Cached models are only valid for the current asserted set.
        self.direct_enum_witness = None;

        // Handle constant Bool atoms (e.g., term layer folds `X = X` to `true`).
        // Asserting `true` as false (or `false` as true) is an immediate contradiction.
        for &(term, value) in &self.asserted {
            match self.terms.get(term) {
                TermData::Const(Constant::Bool(b)) if value != *b => {
                    return TheoryResult::Unsat(vec![TheoryLit { term, value }]);
                }
                _ => {}
            }
        }

        // GCD test: quick check for integer infeasibility
        // For equations like 4x + 4y + 4z - 2w = 49, GCD(4,4,4,2)=2 doesn't divide 49
        if let Some(mut conflict) = self.gcd_test() {
            if debug {
                safe_eprintln!("[LIA] GCD test detected UNSAT");
            }
            debug_assert!(
                !conflict.literals.is_empty(),
                "BUG: LIA GCD test: returned UnsatWithFarkas with empty conflict literals"
            );
            self.augment_farkas_with_shared_eq_reasons(&mut conflict);
            return TheoryResult::UnsatWithFarkas(conflict);
        }

        // Diophantine solver: for equality-dense problems, try variable elimination.
        let equality_key = self.equality_key();
        if debug {
            safe_eprintln!(
                "[LIA] eq_key.len={} dioph_key.len={} eq={}",
                equality_key.len(),
                self.dioph_equality_key.len(),
                equality_key == self.dioph_equality_key
            );
        }
        let has_equalities = !equality_key.is_empty();
        // #8012 soundness: Skip Dioph when shared equalities are active.
        let should_run_dioph =
            has_equalities && self.dioph_equality_key != equality_key && self.shared_equalities.is_empty();
        self.dioph_equality_key = equality_key;
        if !has_equalities {
            self.dioph_safe_dependent_vars.clear();
            self.dioph_cached_substitutions.clear();
            self.dioph_cached_modular_gcds.clear();
            self.dioph_cached_reasons.clear();
        }

        if should_run_dioph {
            if let Some(reasons) = self.try_two_variable_solve() {
                if debug {
                    safe_eprintln!("[LIA] 2-variable solver detected UNSAT");
                }
                debug_assert!(
                    !reasons.is_empty(),
                    "BUG: LIA 2-var Diophantine: returned empty conflict reasons"
                );
                if let TheoryResult::UnsatWithFarkas(mut conflict) = self.lra.check() {
                    self.augment_farkas_with_shared_eq_reasons(&mut conflict);
                    return TheoryResult::UnsatWithFarkas(conflict);
                }
                return TheoryResult::Unsat(reasons);
            }

            if let Some(reasons) = self.try_diophantine_solve() {
                if debug {
                    safe_eprintln!("[LIA] Diophantine solver detected UNSAT");
                }
                debug_assert!(
                    !reasons.is_empty(),
                    "BUG: LIA Diophantine: returned empty conflict reasons"
                );
                if let TheoryResult::UnsatWithFarkas(mut conflict) = self.lra.check() {
                    self.augment_farkas_with_shared_eq_reasons(&mut conflict);
                    return TheoryResult::UnsatWithFarkas(conflict);
                }
                return TheoryResult::Unsat(reasons);
            }
        }

        // Iterative Dioph tightening loop (Z3's continue_with_check pattern).
        // Reference: Z3 dioph_eq.cpp check() at line 2162.
        // #8012: Skip when shared equalities are active.
        if self.shared_equalities.is_empty() {
            let max_tighten_rounds = 4;
            let mut prev_fixed_count = self.count_fixed_integer_vars();

            for tighten_round in 0..max_tighten_rounds {
                if self.dioph_cached_substitutions.is_empty() {
                    break;
                }

                let bounds_tightened = self.propagate_bounds_through_substitutions();
                if bounds_tightened {
                    if let TheoryResult::UnsatWithFarkas(mut conflict) = self.lra.check() {
                        self.augment_farkas_with_shared_eq_reasons(&mut conflict);
                        return TheoryResult::UnsatWithFarkas(conflict);
                    }
                }

                let rows_tightened = self.tighten_tableau_rows_via_dioph();
                if rows_tightened {
                    if let TheoryResult::UnsatWithFarkas(mut conflict) = self.lra.check() {
                        self.augment_farkas_with_shared_eq_reasons(&mut conflict);
                        return TheoryResult::UnsatWithFarkas(conflict);
                    }
                }

                if !bounds_tightened && !rows_tightened {
                    break;
                }

                let new_fixed_count = self.count_fixed_integer_vars();
                if new_fixed_count <= prev_fixed_count {
                    break;
                }

                if debug {
                    safe_eprintln!(
                        "[LIA] Dioph tighten round {}: {} newly fixed vars (was {}, now {})",
                        tighten_round,
                        new_fixed_count - prev_fixed_count,
                        prev_fixed_count,
                        new_fixed_count
                    );
                }
                prev_fixed_count = new_fixed_count;

                if self.should_timeout() {
                    if debug {
                        safe_eprintln!("[LIA] Timeout during iterative Dioph tightening");
                    }
                    return TheoryResult::Unknown;
                }

                if let Some(reasons) = self.try_diophantine_solve() {
                    if debug {
                        safe_eprintln!(
                            "[LIA] Dioph re-solve (round {}) detected UNSAT",
                            tighten_round
                        );
                    }
                    if let TheoryResult::UnsatWithFarkas(mut conflict) = self.lra.check() {
                        self.augment_farkas_with_shared_eq_reasons(&mut conflict);
                        return TheoryResult::UnsatWithFarkas(conflict);
                    }
                    return TheoryResult::Unsat(reasons);
                }
            }
        }

        self.gomory_iterations = 0;
        self.hnf_iterations = 0;
        let mut cube_tried = false;

        loop {
            if self.should_timeout() {
                if debug {
                    safe_eprintln!("[LIA] Timeout, returning Unknown");
                }
                return TheoryResult::Unknown;
            }

            let lra_result = self.lra.check();

            if debug {
                safe_eprintln!(
                    "[LIA] LRA check result: {:?}, gomory_iter={}, hnf_iter={}",
                    lra_result,
                    self.gomory_iterations,
                    self.hnf_iterations
                );
            }

            match lra_result {
                TheoryResult::Unsat(reasons) => {
                    return TheoryResult::Unsat(reasons);
                }
                TheoryResult::UnsatWithFarkas(mut conflict) => {
                    self.augment_farkas_with_shared_eq_reasons(&mut conflict);
                    return TheoryResult::UnsatWithFarkas(conflict);
                }
                TheoryResult::Unknown => {
                    if let Some(mut conflict) = self.gcd_test_tableau() {
                        if debug {
                            safe_eprintln!(
                                "[LIA] Unknown recovery: tableau GCD test detected UNSAT"
                            );
                        }
                        self.augment_farkas_with_shared_eq_reasons(&mut conflict);
                        return TheoryResult::UnsatWithFarkas(conflict);
                    }

                    if let Some(mut conflict) = self.gcd_accumulative_test() {
                        if debug {
                            safe_eprintln!(
                                "[LIA] Unknown recovery: accumulative GCD test detected UNSAT"
                            );
                        }
                        self.augment_farkas_with_shared_eq_reasons(&mut conflict);
                        return TheoryResult::UnsatWithFarkas(conflict);
                    }

                    let hnf_var = self.integer_vars.iter().copied().find(|&v| {
                        self.lra
                            .get_bounds(v)
                            .is_some_and(|(lb, ub)| lb.is_some() || ub.is_some())
                    });
                    if let Some(var) = hnf_var {
                        if self.hnf_iterations
                            < Self::hnf_iteration_budget(
                                self.count_equalities(),
                                self.integer_vars.len(),
                            )
                            && self.try_hnf_cuts(var)
                        {
                            if debug {
                                safe_eprintln!(
                                    "[LIA] Unknown recovery: HNF cuts generated, re-checking"
                                );
                            }
                            continue;
                        }
                    }

                    if self.gomory_iterations < self.max_gomory_iterations {
                        let cuts = self.lra.generate_gomory_cuts(&self.integer_vars);
                        let small_cuts: Vec<_> = cuts
                            .into_iter()
                            .filter(z4_lra::GomoryCut::is_small)
                            .collect();
                        if !small_cuts.is_empty() {
                            if debug {
                                safe_eprintln!(
                                    "[LIA] Unknown recovery: adding {} small Gomory cuts",
                                    small_cuts.len()
                                );
                            }
                            for cut in &small_cuts {
                                self.lra.add_gomory_cut(cut, TermId::SENTINEL);
                            }
                            self.gomory_iterations += 1;
                            continue;
                        }
                    }

                    // #6220: Apply the same UNSAT-detection checks used in the Sat path.
                    // When LRA returns Unknown (e.g., ITE/nonlinear terms), the bounds
                    // it established are still valid, so integer gap detection, modular
                    // constraints, and direct enumeration can still detect UNSAT.
                    if let Some(conflict) = self.check_integer_bounds_conflict() {
                        if debug {
                            safe_eprintln!(
                                "[LIA] Unknown recovery: integer bounds gap detected UNSAT"
                            );
                        }
                        return TheoryResult::Unsat(conflict.literals);
                    }

                    if let Some(reasons) = self.check_single_equality_modular_constraints() {
                        if debug {
                            safe_eprintln!(
                                "[LIA] Unknown recovery: modular constraint detected UNSAT"
                            );
                        }
                        return TheoryResult::Unsat(reasons);
                    }

                    if let Some(reasons) = self.check_modular_constraint_conflict() {
                        if debug {
                            safe_eprintln!(
                                "[LIA] Unknown recovery: Dioph modular constraint detected UNSAT"
                            );
                        }
                        return TheoryResult::Unsat(reasons);
                    }

                    if self.gomory_iterations == 0 && self.hnf_iterations == 0 {
                        match self.try_direct_enumeration() {
                            DirectEnumResult::Unsat(reasons) => {
                                if debug {
                                    safe_eprintln!(
                                        "[LIA] Unknown recovery: direct enumeration detected UNSAT"
                                    );
                                }
                                return TheoryResult::Unsat(reasons);
                            }
                            DirectEnumResult::SatWitness => {
                                // LRA said Unknown but enumeration found a SAT witness.
                                // This is safe: the witness satisfies all integer constraints.
                                if debug {
                                    safe_eprintln!(
                                        "[LIA] Unknown recovery: direct enumeration found SAT witness"
                                    );
                                }
                                return TheoryResult::Sat;
                            }
                            DirectEnumResult::NoConclusion => {}
                        }
                    }

                    if let Some(split) = self.find_unsplit_integer_var() {
                        if debug {
                            safe_eprintln!(
                                "[LIA] LRA returned Unknown, splitting unsplit var {:?} at midpoint {}",
                                split.variable, split.value
                            );
                        }
                        return TheoryResult::NeedSplit(split);
                    }
                    if debug {
                        safe_eprintln!(
                            "[LIA] LRA returned Unknown, no splittable var, propagating"
                        );
                    }
                    return TheoryResult::Unknown;
                }
                TheoryResult::NeedSplit(split) => {
                    return TheoryResult::NeedSplit(split);
                }
                TheoryResult::NeedDisequalitySplit(split) => {
                    if let Some(reasons) = self.check_disequality_vs_modular(&split) {
                        if debug {
                            safe_eprintln!("[LIA] Disequality conflicts with modular constraint");
                        }
                        return TheoryResult::Unsat(reasons);
                    }
                    return TheoryResult::NeedDisequalitySplit(split);
                }
                TheoryResult::NeedExpressionSplit(split) => {
                    return TheoryResult::NeedExpressionSplit(split);
                }
                TheoryResult::NeedStringLemma(lemma) => {
                    return TheoryResult::NeedStringLemma(lemma);
                }
                TheoryResult::Sat => {
                    if let Some(conflict) = self.check_integer_bounds_conflict() {
                        // Integer-gap conflicts (e.g., x > 0 AND x < 1) use
                        // integer rounding, NOT a linear Farkas argument. Return
                        // plain Unsat to avoid semantic Farkas verification failure
                        // in the incremental DPLL(T) path (#4785).
                        return TheoryResult::Unsat(conflict.literals);
                    }

                    if let Some(reasons) = self.check_single_equality_modular_constraints() {
                        if debug {
                            safe_eprintln!("[LIA] Modular constraint detected UNSAT");
                        }
                        return TheoryResult::Unsat(reasons);
                    }

                    if let Some(reasons) = self.check_modular_constraint_conflict() {
                        if debug {
                            safe_eprintln!("[LIA] Dioph modular constraint detected UNSAT");
                        }
                        return TheoryResult::Unsat(reasons);
                    }

                    if self.gomory_iterations == 0 && self.hnf_iterations == 0 {
                        match self.try_direct_enumeration() {
                            DirectEnumResult::Unsat(reasons) => {
                                if debug {
                                    safe_eprintln!("[LIA] Direct enumeration detected UNSAT");
                                }
                                return TheoryResult::Unsat(reasons);
                            }
                            DirectEnumResult::SatWitness => {
                                if debug {
                                    safe_eprintln!("[LIA] Direct enumeration found SAT witness");
                                }
                                return TheoryResult::Sat;
                            }
                            DirectEnumResult::NoConclusion => {
                                if self.should_timeout() {
                                    if debug {
                                        safe_eprintln!("[LIA] Timeout during direct enumeration");
                                    }
                                    return TheoryResult::Unknown;
                                }
                            }
                        }
                    }

                    if let Some((var, value)) = self.check_integer_constraints() {
                        if let Some(mut conflict) = self.gcd_test_tableau() {
                            if debug {
                                safe_eprintln!("[LIA] Tableau GCD test detected UNSAT");
                            }
                            self.augment_farkas_with_shared_eq_reasons(&mut conflict);
                            return TheoryResult::UnsatWithFarkas(conflict);
                        }

                        if self.try_patching() {
                            if debug {
                                safe_eprintln!("[LIA] Patching succeeded, re-checking");
                            }
                            continue;
                        }

                        if !cube_tried {
                            cube_tried = true;
                            if self.lra.try_cube_test(&self.integer_vars) {
                                if debug {
                                    safe_eprintln!("[LIA] Cube test succeeded, re-checking");
                                }
                                continue;
                            }
                        }

                        if self.should_try_gomory(cube_tried) {
                            let cuts = self.lra.generate_gomory_cuts(&self.integer_vars);

                            if debug {
                                safe_eprintln!(
                                    "[LIA] Generated {} Gomory cuts (iter {})",
                                    cuts.len(),
                                    self.gomory_iterations,
                                );
                            }

                            if !cuts.is_empty() {
                                let mut small_cuts = Vec::new();
                                let mut big_cuts = Vec::new();
                                for cut in cuts {
                                    if cut.is_small() {
                                        small_cuts.push(cut);
                                    } else {
                                        big_cuts.push(cut);
                                    }
                                }

                                for cut in &small_cuts {
                                    let from_substituted = cut.source_term.is_some_and(|t| {
                                        self.dioph_safe_dependent_vars.contains(&t)
                                    });
                                    if from_substituted {
                                        self.lra.push();
                                        self.lra.add_gomory_cut(cut, TermId::SENTINEL);
                                        let tentative = self.lra.check();
                                        self.lra.pop();
                                        let made_infeasible = matches!(
                                            tentative,
                                            TheoryResult::Unsat(_)
                                                | TheoryResult::UnsatWithFarkas(_)
                                        );
                                        if made_infeasible {
                                            let base_ok = !matches!(
                                                self.lra.check(),
                                                TheoryResult::Unsat(_)
                                                    | TheoryResult::UnsatWithFarkas(_)
                                            );
                                            if base_ok {
                                                if debug {
                                                    safe_eprintln!(
                                                        "[LIA] Gomory: discarding substituted-row cut"
                                                    );
                                                }
                                                continue;
                                            }
                                        }
                                    }
                                    self.lra.add_gomory_cut(cut, TermId::SENTINEL);
                                }

                                if !big_cuts.is_empty() {
                                    if debug {
                                        safe_eprintln!(
                                            "[LIA] Testing {} big Gomory cuts tentatively",
                                            big_cuts.len()
                                        );
                                    }
                                    self.lra.push();
                                    for cut in &big_cuts {
                                        self.lra.add_gomory_cut(cut, TermId::SENTINEL);
                                    }
                                    let feasible = !matches!(
                                        self.lra.dual_simplex(),
                                        TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
                                    );
                                    self.lra.pop();

                                    if !feasible {
                                        if debug {
                                            safe_eprintln!(
                                                "[LIA] Big cuts render LP infeasible, keeping them"
                                            );
                                        }
                                        for cut in &big_cuts {
                                            self.lra.add_gomory_cut(cut, TermId::SENTINEL);
                                        }
                                    } else if debug {
                                        safe_eprintln!("[LIA] Big cuts did not help, discarding");
                                    }
                                }

                                self.gomory_iterations += 1;
                                continue;
                            }
                        }

                        let num_equalities = self.count_equalities();
                        let num_vars = self.integer_vars.len();
                        let is_equality_dense = Self::is_equality_dense(num_equalities, num_vars);
                        let max_hnf_per_check =
                            Self::hnf_iteration_budget(num_equalities, num_vars);

                        let pre_hnf_iter = self.hnf_iterations;

                        while self.hnf_iterations < max_hnf_per_check {
                            if self.should_timeout() {
                                if debug {
                                    safe_eprintln!(
                                        "[LIA] Timeout during HNF cuts, returning Unknown"
                                    );
                                }
                                return TheoryResult::Unknown;
                            }
                            if debug {
                                safe_eprintln!(
                                    "[LIA] Trying HNF cuts (iter {}/{}, {} equalities, {} vars, dense={})",
                                    self.hnf_iterations, max_hnf_per_check,
                                    num_equalities, num_vars, is_equality_dense
                                );
                            }
                            if self.try_hnf_cuts(var) {
                                if debug {
                                    safe_eprintln!(
                                        "[LIA] HNF cuts generated, continuing inner HNF loop"
                                    );
                                }
                                continue;
                            }
                            break;
                        }

                        if self.hnf_iterations > pre_hnf_iter {
                            if debug {
                                safe_eprintln!(
                                    "[LIA] Generated {} HNF cuts total, re-checking LRA",
                                    self.hnf_iterations - pre_hnf_iter
                                );
                            }
                            continue;
                        }

                        if debug {
                            safe_eprintln!(
                                "[LIA] Falling back to branch-and-bound (gomory={}, hnf={})",
                                self.gomory_iterations,
                                self.hnf_iterations
                            );
                        }
                        debug_assert!(
                            self.integer_vars.contains(&var),
                            "BUG: LIA branch-and-bound: split variable {} is not a tracked integer variable",
                            var.0
                        );
                        let split = Self::create_split_request(var, value);
                        debug_assert!(
                            split.floor < split.ceil,
                            "BUG: LIA branch-and-bound: floor {} >= ceil {} for non-integer value",
                            split.floor,
                            split.ceil
                        );
                        return TheoryResult::NeedSplit(split);
                    } else {
                        return TheoryResult::Sat;
                    }
                }
                TheoryResult::NeedLemmas(lemmas) => {
                    return TheoryResult::NeedLemmas(lemmas);
                }
                TheoryResult::NeedModelEquality(req) => {
                    return TheoryResult::NeedModelEquality(req);
                }
                TheoryResult::NeedModelEqualities(reqs) => {
                    return TheoryResult::NeedModelEqualities(reqs);
                }
                _ => {
                    // Forward any future TheoryResult variants from LRA unchanged.
                    return lra_result;
                }
            }
        }
    }

    /// Lightweight BCP-time check: keep local arithmetic conflicts and LRA
    /// propagation, but defer expensive Dioph/cut/branch-and-bound work to the
    /// final full `check()`.
    pub(super) fn check_during_propagate_inner(&mut self) -> TheoryResult {
        let debug = self.debug_lia_check;

        // Cached enumeration models are only valid for the current asserted set.
        self.direct_enum_witness = None;

        // Handle constant Bool atoms eagerly.
        for &(term, value) in &self.asserted {
            match self.terms.get(term) {
                TermData::Const(Constant::Bool(b)) if value != *b => {
                    return TheoryResult::Unsat(vec![TheoryLit { term, value }]);
                }
                _ => {}
            }
        }

        // Keep the fast, assignment-independent UNSAT checks at BCP time.
        if let Some(mut conflict) = self.gcd_test() {
            if debug {
                safe_eprintln!("[LIA] BCP-time GCD test detected UNSAT");
            }
            self.augment_farkas_with_shared_eq_reasons(&mut conflict);
            return TheoryResult::UnsatWithFarkas(conflict);
        }

        // Dioph substitutions are only sound if their equality key is current.
        // When new equalities arrive during BCP, drop stale caches but leave the
        // equality key pending so the final full check() still reruns the
        // expensive Dioph solve.
        let equality_key = self.equality_key();
        if equality_key.is_empty() || self.dioph_equality_key != equality_key {
            self.dioph_equality_key.clear();
            self.dioph_safe_dependent_vars.clear();
            self.dioph_cached_substitutions.clear();
            self.dioph_cached_modular_gcds.clear();
            self.dioph_cached_reasons.clear();
        }

        let lra_result = self.lra.check_during_propagate();

        // Preserve cheap integer-specific conflicts when the relaxation is
        // feasible or merely Unknown due to unsupported terms.
        if matches!(lra_result, TheoryResult::Sat | TheoryResult::Unknown) {
            if let Some(conflict) = self.check_integer_bounds_conflict() {
                if debug {
                    safe_eprintln!("[LIA] BCP-time integer bounds gap detected UNSAT");
                }
                return TheoryResult::Unsat(conflict.literals);
            }

            if let Some(reasons) = self.check_single_equality_modular_constraints() {
                if debug {
                    safe_eprintln!("[LIA] BCP-time modular constraint detected UNSAT");
                }
                return TheoryResult::Unsat(reasons);
            }

            if let Some(reasons) = self.check_modular_constraint_conflict() {
                if debug {
                    safe_eprintln!("[LIA] BCP-time Dioph modular constraint detected UNSAT");
                }
                return TheoryResult::Unsat(reasons);
            }
        }

        match lra_result {
            TheoryResult::NeedSplit(_)
            | TheoryResult::NeedDisequalitySplit(_)
            | TheoryResult::NeedExpressionSplit(_)
            | TheoryResult::NeedStringLemma(_)
            | TheoryResult::NeedModelEquality(_)
            | TheoryResult::NeedModelEqualities(_) => TheoryResult::Sat,
            TheoryResult::UnsatWithFarkas(mut conflict) => {
                self.augment_farkas_with_shared_eq_reasons(&mut conflict);
                TheoryResult::UnsatWithFarkas(conflict)
            }
            other => other,
        }
    }
}
