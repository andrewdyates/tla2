// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Preprocessing: lucky phases, local search, warmup, model verification.

use super::*;

/// Result of a complete lucky strategy attempt.
///
/// Mirrors CaDiCaL's lucky phase return codes: 10 (SAT), 20 (UNSAT), 0 (not lucky).
enum LuckyResult {
    Sat,
    Unsat,
    NotLucky,
}

/// Result of a lucky propagation discrepancy attempt.
///
/// Mirrors CaDiCaL's `lucky_propagate_discrepency` control flow:
/// - `Continue`: no conflict, variable was handled (may be assigned by propagation,
///   so caller should re-check the same variable via goto-START pattern)
/// - `Failed`: conflict could not be recovered — abort this lucky strategy
/// - `Unsat`: level-1 conflict analysis derived empty clause — formula is UNSAT
enum LuckyDiscrepancy {
    Continue,
    Failed,
    Unsat,
}

/// First SAT-model contract violation found during verification.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum ModelViolation {
    /// A non-deleted clause in the live clause database is unsatisfied.
    ClauseDb {
        clause_index: usize,
        clause_dimacs: Vec<i32>,
    },
}

impl Solver {
    // ==========================================================================
    // Lucky Phase (CaDiCaL-style pre-solving)
    // ==========================================================================

    /// Try lucky assignment strategies before full CDCL search
    ///
    /// Attempts several simple assignment patterns that can quickly solve
    /// "easy" formulas without full CDCL search. Returns Some(true) for SAT,
    /// Some(false) for UNSAT proven at level 0, None to continue to CDCL.
    ///
    /// CaDiCaL reference: lucky.cpp:439-504
    pub(super) fn try_lucky_phases(&mut self) -> Option<bool> {
        if self.is_interrupted() {
            return None;
        }
        // CaDiCaL lucky.cpp:440: must be at root level
        debug_assert_eq!(
            self.decision_level, 0,
            "BUG: try_lucky_phases called at decision level {} (expected 0)",
            self.decision_level,
        );

        // CaDiCaL: lucky phase decisions are artificial — suppress phase saving
        // in enqueue() to avoid corrupting the phase heuristic.
        self.suppress_phase_saving = true;

        // Monotone strategies: if every clause has at least one positive literal,
        // set all variables true. Symmetric for negative.
        // Reference: Kissat lucky.c:11-80 (no_all_negative_clauses / no_all_positive_clauses)
        //            Kissat lucky.c:323-362 (invocation in kissat_lucky)
        if !self.is_interrupted() {
            match self.lucky_positive_monotone() {
                LuckyResult::Sat => {
                    self.suppress_phase_saving = false;
                    return Some(true);
                }
                LuckyResult::Unsat => {
                    self.suppress_phase_saving = false;
                    return Some(false);
                }
                LuckyResult::NotLucky => self.lucky_reset(),
            }
        }

        if !self.is_interrupted() {
            match self.lucky_negative_monotone() {
                LuckyResult::Sat => {
                    self.suppress_phase_saving = false;
                    return Some(true);
                }
                LuckyResult::Unsat => {
                    self.suppress_phase_saving = false;
                    return Some(false);
                }
                LuckyResult::NotLucky => self.lucky_reset(),
            }
        }

        // Directional strategies: forward/backward x positive/negative.
        // Uses level-1 conflict analysis and goto-START re-check.
        // Reference: CaDiCaL lucky.cpp:129-265
        for &(positive, forward) in &[(false, true), (true, true), (false, false), (true, false)] {
            if self.is_interrupted() {
                self.suppress_phase_saving = false;
                return None;
            }
            match self.lucky_directional(positive, forward) {
                LuckyResult::Sat => {
                    self.suppress_phase_saving = false;
                    return Some(true);
                }
                LuckyResult::Unsat => {
                    self.suppress_phase_saving = false;
                    return Some(false);
                }
                LuckyResult::NotLucky => self.lucky_reset(),
            }
        }

        // Horn strategies: satisfy clauses via first positive/negative literal.
        // Reference: CaDiCaL lucky.cpp:275-435
        for &prefer_positive in &[true, false] {
            if self.is_interrupted() {
                self.suppress_phase_saving = false;
                return None;
            }
            match self.lucky_horn(prefer_positive) {
                LuckyResult::Sat => {
                    self.suppress_phase_saving = false;
                    return Some(true);
                }
                LuckyResult::Unsat => {
                    self.suppress_phase_saving = false;
                    return Some(false);
                }
                LuckyResult::NotLucky => self.lucky_reset(),
            }
        }

        self.suppress_phase_saving = false;

        // Propagate any units learned during lucky phases.
        // Capture conflict_ref for LRAT resolution chain (#4397).
        if self.decision_level == 0 {
            if self.is_interrupted() {
                return None;
            }
            if let Some(conflict_ref) = self.search_propagate() {
                self.record_level0_conflict_chain(conflict_ref);
                return Some(false);
            }
        }

        None // No lucky assignment found
    }

    /// Reset solver state after a failed lucky attempt
    pub(super) fn lucky_reset(&mut self) {
        if self.decision_level > 0 {
            self.backtrack(0);
        }
    }

    /// CaDiCaL-style discrepancy propagation for lucky phases.
    ///
    /// Decides `dec`, propagates. On conflict:
    /// - At level > 1: backtrack one level, try opposite polarity.
    ///   If that also conflicts, give up.
    /// - At level == 1: run full 1UIP conflict analysis to learn a unit clause,
    ///   backtrack to level 0, enqueue the unit, and re-propagate. If that
    ///   also conflicts, the formula is UNSAT.
    ///
    /// Returns `Continue` if no conflict (caller should re-check variable),
    /// `Failed` if unrecoverable, `Unsat` if empty clause derived.
    ///
    /// Reference: CaDiCaL lucky.cpp:129-153 (lucky_propagate_discrepency)
    fn lucky_propagate_discrepancy(&mut self, dec: Literal) -> LuckyDiscrepancy {
        if self.is_interrupted() {
            return LuckyDiscrepancy::Failed;
        }
        self.decide(dec);
        let conflict = self.search_propagate();
        if self.is_interrupted() {
            return LuckyDiscrepancy::Failed;
        }

        if let Some(conflict_ref) = conflict {
            if self.decision_level > 1 {
                // Level > 1: backtrack and try opposite polarity
                self.backtrack(self.decision_level - 1);
                self.decide(dec.negated());
                if self.search_propagate().is_some() {
                    return LuckyDiscrepancy::Failed;
                }
                if self.is_interrupted() {
                    return LuckyDiscrepancy::Failed;
                }
                return LuckyDiscrepancy::Continue;
            }

            // Level == 1: full 1UIP conflict analysis -> learns unit, backtracks to 0
            let result = self.analyze_conflict(conflict_ref);
            let uip = result.learned_clause[0];
            debug_assert_eq!(
                result.backtrack_level, 0,
                "Level-1 conflict must backtrack to 0"
            );
            self.backtrack(0);
            // CaDiCaL lucky.cpp:144
            debug_assert_eq!(
                self.decision_level, 0,
                "BUG: not at level 0 after lucky analysis"
            );

            // OTFS Branch B: use existing strengthened clause as driving clause.
            if let Some(driving_ref) = result.otfs_driving_clause {
                self.enqueue(uip, Some(driving_ref));
                self.conflict.return_learned_buf(result.learned_clause);
                self.conflict.return_chain_buf(result.resolution_chain);
            } else {
                // Add the learned unit clause.
                // Use add_learned_clause for ALL sizes so the clause is in the DB
                // with a valid ClauseRef. This ensures record_level0_conflict_chain
                // can find its ID via the reason when building LRAT hints (#4397).
                // Set DiagnosticPass::Learning so diagnostic trace classifies this
                // as a learned clause, not a theory lemma (#4172).
                self.set_diagnostic_pass(DiagnosticPass::Learning);
                let learned_ref = self.add_conflict_learned_clause(
                    result.learned_clause,
                    result.lbd,
                    result.resolution_chain,
                );
                self.clear_diagnostic_pass();
                self.enqueue(uip, Some(learned_ref));
            }

            // Re-propagate the learned unit.
            // Capture conflict_ref for LRAT resolution chain (#4397).
            if let Some(conflict_ref) = self.search_propagate() {
                // Second conflict at level 0 -> UNSAT
                self.record_level0_conflict_chain(conflict_ref);
                return LuckyDiscrepancy::Unsat;
            }
            if self.is_interrupted() {
                return LuckyDiscrepancy::Failed;
            }

            // Learned unit simplified the formula; continue lucky phase
            return LuckyDiscrepancy::Continue;
        }

        // No conflict
        LuckyDiscrepancy::Continue
    }

    /// Positive monotone: if every clause contains at least one positive literal,
    /// the formula is trivially SAT -- set all variables to true.
    ///
    /// A clause with all negative literals cannot be satisfied by setting all
    /// variables true, so we check that no such clause exists. If the check
    /// passes, we assign all unassigned variables to true with no conflicts.
    ///
    /// Reference: Kissat lucky.c:11-45 (no_all_negative_clauses)
    ///            Kissat lucky.c:323-341 (set all variables true)
    fn lucky_positive_monotone(&mut self) -> LuckyResult {
        debug_assert_eq!(self.decision_level, 0);

        // Check: every clause has at least one positive literal that is not
        // assigned false. Kissat lucky.c:20-22: !NEGATED(lit) && VALUE(lit) >= 0
        for idx in self.arena.indices().collect::<Vec<_>>() {
            if !self.arena.is_active(idx) {
                continue;
            }
            let lits = self.arena.literals(idx);
            if lits.is_empty() {
                continue;
            }
            let has_non_false_positive = lits
                .iter()
                .any(|lit| lit.is_positive() && self.lit_value(*lit) != Some(false));
            if !has_non_false_positive {
                return LuckyResult::NotLucky;
            }
        }

        // All clauses have at least one positive literal -- set all vars true.
        for var_idx in 0..self.num_vars {
            if self.var_is_assigned(var_idx) || self.var_lifecycle.is_removed(var_idx) {
                continue;
            }
            let lit = Literal::positive(Variable(var_idx as u32));
            self.decide(lit);
            debug_assert!(
                self.search_propagate().is_none(),
                "BUG: conflict in positive monotone lucky phase"
            );
        }
        LuckyResult::Sat
    }

    /// Negative monotone: if every clause contains at least one negative literal,
    /// the formula is trivially SAT -- set all variables to false.
    ///
    /// Symmetric to positive monotone. A clause with all positive literals cannot
    /// be satisfied by setting all variables false, so we check that no such
    /// clause exists.
    ///
    /// Reference: Kissat lucky.c:47-80 (no_all_positive_clauses)
    ///            Kissat lucky.c:343-362 (set all variables false)
    fn lucky_negative_monotone(&mut self) -> LuckyResult {
        debug_assert_eq!(self.decision_level, 0);

        // Check: every clause has at least one negative literal that is not
        // assigned false. Kissat lucky.c:56-58: NEGATED(lit) && VALUE(lit) >= 0
        for idx in self.arena.indices().collect::<Vec<_>>() {
            if !self.arena.is_active(idx) {
                continue;
            }
            let lits = self.arena.literals(idx);
            if lits.is_empty() {
                continue;
            }
            let has_non_false_negative = lits
                .iter()
                .any(|lit| !lit.is_positive() && self.lit_value(*lit) != Some(false));
            if !has_non_false_negative {
                return LuckyResult::NotLucky;
            }
        }

        // All clauses have at least one negative literal -- set all vars false.
        for var_idx in 0..self.num_vars {
            if self.var_is_assigned(var_idx) || self.var_lifecycle.is_removed(var_idx) {
                continue;
            }
            let lit = Literal::negative(Variable(var_idx as u32));
            self.decide(lit);
            debug_assert!(
                self.search_propagate().is_none(),
                "BUG: conflict in negative monotone lucky phase"
            );
        }
        LuckyResult::Sat
    }

    /// Try assigning all variables with given polarity and direction.
    ///
    /// Uses CaDiCaL goto-START re-check pattern: after discrepancy handling,
    /// the variable may have been assigned by propagation, so re-check it.
    ///
    /// Reference: CaDiCaL lucky.cpp:155-265
    fn lucky_directional(&mut self, positive: bool, forward: bool) -> LuckyResult {
        // CaDiCaL lucky.cpp:157-158: must not be UNSAT, must be at root level
        debug_assert!(
            !self.has_empty_clause,
            "BUG: lucky_directional called with has_empty_clause=true",
        );
        debug_assert_eq!(
            self.decision_level, 0,
            "BUG: lucky_directional not at root level (level={})",
            self.decision_level,
        );
        let make_lit = if positive {
            Literal::positive
        } else {
            Literal::negative
        };

        if forward {
            let mut var_idx = 0;
            while var_idx < self.num_vars {
                if self.is_interrupted() {
                    return LuckyResult::NotLucky;
                }
                if self.var_is_assigned(var_idx) || self.var_lifecycle.is_removed(var_idx) {
                    var_idx += 1;
                    continue;
                }
                match self.lucky_propagate_discrepancy(make_lit(Variable(var_idx as u32))) {
                    LuckyDiscrepancy::Continue => continue, // re-check same variable
                    LuckyDiscrepancy::Failed => return LuckyResult::NotLucky,
                    LuckyDiscrepancy::Unsat => return LuckyResult::Unsat,
                }
            }
        } else {
            let mut var_idx = self.num_vars;
            while var_idx > 0 {
                if self.is_interrupted() {
                    return LuckyResult::NotLucky;
                }
                var_idx -= 1;
                if self.var_is_assigned(var_idx) || self.var_lifecycle.is_removed(var_idx) {
                    continue;
                }
                match self.lucky_propagate_discrepancy(make_lit(Variable(var_idx as u32))) {
                    LuckyDiscrepancy::Continue => {
                        var_idx += 1; // counteract decrement to re-check same variable
                        continue;
                    }
                    LuckyDiscrepancy::Failed => return LuckyResult::NotLucky,
                    LuckyDiscrepancy::Unsat => return LuckyResult::Unsat,
                }
            }
        }
        LuckyResult::Sat
    }

    /// Try horn strategy: satisfy each clause via first literal of preferred polarity.
    ///
    /// Horn strategies don't use discrepancy -- they abort on conflict.
    /// Remaining unassigned variables get the opposite polarity as default.
    ///
    /// Reference: CaDiCaL lucky.cpp:275-435
    fn lucky_horn(&mut self, prefer_positive: bool) -> LuckyResult {
        // CaDiCaL lucky.cpp:277/375: must be at root level
        debug_assert_eq!(
            self.decision_level, 0,
            "BUG: lucky_horn not at root level (level={})",
            self.decision_level,
        );
        for clause_idx in self.arena.indices().collect::<Vec<_>>() {
            if self.is_interrupted() {
                return LuckyResult::NotLucky;
            }
            let off = clause_idx;
            if self.arena.is_empty_clause(off) {
                continue;
            }
            let len = self.arena.len_of(off);

            let mut satisfied = false;
            let mut first_match: Option<Literal> = None;

            for i in 0..len {
                let lit = self.arena.literal(off, i);
                match self.lit_value(lit) {
                    Some(true) => {
                        satisfied = true;
                        break;
                    }
                    Some(false) => continue,
                    None => {
                        if (lit.is_positive() == prefer_positive) && first_match.is_none() {
                            first_match = Some(lit);
                        }
                    }
                }
            }

            if satisfied {
                continue;
            }

            match first_match {
                Some(lit) if !self.var_lifecycle.is_removed(lit.variable().index()) => {
                    self.decide(lit);
                    if self.search_propagate().is_some() {
                        return LuckyResult::NotLucky;
                    }
                }
                Some(_) => continue,
                None => return LuckyResult::NotLucky,
            }
        }

        // Assign remaining variables with opposite polarity
        let default_lit = if prefer_positive {
            Literal::negative
        } else {
            Literal::positive
        };
        for var_idx in 0..self.num_vars {
            if !self.var_is_assigned(var_idx) && !self.var_lifecycle.is_removed(var_idx) {
                self.decide(default_lit(Variable(var_idx as u32)));
                if self.search_propagate().is_some() {
                    return LuckyResult::NotLucky;
                }
            }
        }
        LuckyResult::Sat
    }

    /// Run walk-based phase initialization.
    ///
    /// This uses ProbSAT random walk to find good initial phases for CDCL.
    /// The walk tries to minimize unsatisfied clauses and saves the best
    /// phases found for use in decision making.
    ///
    /// Walk phases are written to `phase[]` only, NOT to `target_phase[]`.
    /// CaDiCaL only calls walk during periodic rephasing (not at startup),
    /// so walk phases are always overridable. Writing to `target_phase`
    /// made walk phases sticky and caused CDCL to hang on instances where
    /// walk found adversarial phases (see #3361).
    ///
    /// Returns true if walk found a satisfying assignment (SAT), false otherwise.
    pub(super) fn try_walk(&mut self) -> bool {
        if !self.phase_init.walk_enabled {
            return false;
        }

        // Skip walk for small/medium formulas. CDCL alone solves these
        // quickly, and walk phases can steer CDCL into adversarial search
        // spaces on structured instances (e.g., simon-r16-1 with 2688 vars
        // hangs >30s with walk but solves in 3.6ms without). CaDiCaL only
        // uses walk during periodic rephasing, not at startup.
        if self.num_vars < 5_000 {
            return false;
        }

        // Skip startup walk on very large formulas (>5M active clauses). Walk
        // initialization builds occurrence lists by iterating all clauses
        // twice (count + build), costing O(clauses) before any walk steps.
        // CaDiCaL does NOT run walk at startup -- only during periodic
        // rephasing where tick-proportional budgets limit overhead.
        //
        // Raised from 1M to 5M: large industrial formulas (shuffling-2 at
        // 4.7M clauses) benefit significantly from walk-based phase init
        // over JW alone. Walk phases give CDCL a better starting trajectory,
        // reducing conflict count. The O(clauses) setup cost (~1.5s for 4.5M
        // clauses) is worthwhile when the alternative is 40K+ conflicts.
        if self.arena.active_clause_count() > 5_000_000 {
            return false;
        }

        // Use a seed based on problem characteristics for reproducibility
        let seed = (self.num_vars as u64)
            .wrapping_mul(31)
            .wrapping_add(self.num_original_clauses as u64);

        // Run walk to find good phases (written to self.phase only).
        // During preprocessing, no learned clauses exist yet, so
        // irredundant_only is the correct filter.
        crate::walk::walk(
            &self.arena,
            self.num_vars,
            &mut self.phase,
            &mut self.phase_init.walk_prev_phase,
            &mut self.phase_init.walk_stats,
            seed,
            self.phase_init.walk_limit,
            crate::walk::WalkFilter::irredundant_only(),
        )
    }

    /// Run warmup-based phase initialization.
    ///
    /// Uses CDCL propagation (ignoring conflicts) to find good initial phases.
    /// This is more efficient than walk for small/medium instances because
    /// it uses O(1) amortized 2-watched literal propagation instead of O(n^2)
    /// break-value computation.
    pub(super) fn try_warmup(&mut self) {
        if !self.phase_init.warmup_enabled {
            return;
        }

        // Skip warmup for very small formulas
        if self.num_vars < 20 || self.num_original_clauses < 50 {
            return;
        }

        // Skip warmup on very large formulas (>5M active clauses). Warmup
        // builds its own 2WL watch structure by iterating all clauses,
        // then runs propagation over all variables. Raised from 1M to 5M
        // to match the walk threshold -- large industrial formulas benefit
        // from warmup-derived target phases for stable mode search.
        if self.arena.active_clause_count() > 5_000_000 {
            return;
        }

        crate::warmup::warmup(
            &self.arena,
            self.num_vars,
            &self.phase,
            &mut self.target_phase,
            &mut self.phase_init.warmup_stats,
        );
    }

    /// Jeroslow-Wang initial phase selection.
    ///
    /// For each variable without a saved phase, computes JW scores for both
    /// polarities and sets the initial phase to the polarity with higher score.
    /// JW(l) = sum_{clause c containing l} 2^{-|c|}. This weights short clauses
    /// more heavily, since satisfying a short clause is more constrained.
    ///
    /// Cost: O(total_literals) -- single pass over all active clauses.
    /// On shuffling-2 (4.5M clauses), this takes ~10-20ms.
    ///
    /// Reference: Jeroslow & Wang (1990), "Solving Propositional Satisfiability
    /// Problems". CaDiCaL phases.cpp initial_phase=2 (JW-based).
    pub(super) fn init_jw_phases(&mut self) {
        // Only fill in phases that are still unset (don't override walk/warmup).
        let mut has_unset = false;
        for i in 0..self.num_vars {
            if self.phase[i] == 0 {
                has_unset = true;
                break;
            }
        }
        if !has_unset {
            return;
        }

        // Compute JW scores: pos_score[v] and neg_score[v].
        let mut pos_score = vec![0.0f64; self.num_vars];
        let mut neg_score = vec![0.0f64; self.num_vars];

        for idx in self.arena.indices() {
            if !self.arena.is_active(idx) {
                continue;
            }
            let lits = self.arena.literals(idx);
            let len = lits.len();
            if len == 0 {
                continue;
            }
            // 2^{-len}: for len=2 -> 0.25, len=3 -> 0.125, len=10 -> ~0.001
            let weight = (0.5f64).powi(len as i32);
            for &lit in lits {
                let var = lit.variable().index();
                if var < self.num_vars {
                    if lit.is_positive() {
                        pos_score[var] += weight;
                    } else {
                        neg_score[var] += weight;
                    }
                }
            }
        }

        // Set phase for variables that don't have one yet.
        for i in 0..self.num_vars {
            if self.phase[i] == 0 {
                // Choose polarity with higher JW score.
                self.phase[i] = if pos_score[i] >= neg_score[i] { 1 } else { -1 };
            }
        }
    }
}
