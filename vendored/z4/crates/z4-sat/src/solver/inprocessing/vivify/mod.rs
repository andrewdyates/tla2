// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Vivification: learned and irredundant clause strengthening.
//!
//! Split into submodules:
//! - `tier`: per-tier clause processing loop
//! - `analysis`: backward trail analysis for conflicts and implied literals

mod analysis;
mod tier;

use super::super::*;
use super::VivifyTierRun;

impl Solver {
    /// Run vivification (wrapper: always reschedules learned vivification).
    ///
    /// REQUIRES: decision_level == 0
    /// ENSURES: decision_level == 0
    pub(in crate::solver) fn vivify(&mut self) -> bool {
        let result = self.vivify_body();
        self.inproc_ctrl
            .vivify
            .reschedule(self.num_conflicts, VIVIFY_INTERVAL);
        result
    }

    /// Vivify body — early returns are safe; wrapper handles rescheduling.
    ///
    /// Vivification tries to remove literals from clauses by temporarily assuming
    /// their negation and propagating. If this leads to a conflict or implies
    /// another literal in the clause, the literal can be removed.
    ///
    /// CaDiCaL vivifies both irredundant and redundant clauses (vivify.cpp).
    /// Irredundant vivification is critical for structured instances (6-47x gap).
    ///
    /// This must be called at decision level 0 (after a restart) for correctness.
    fn vivify_body(&mut self) -> bool {
        if !self.enter_inprocessing() {
            return false;
        }

        // Scheduling handled by vivify_skip_reason() in the inprocessing
        // scheduler. No inner threshold — per-tier budgets limit effort. (#8134)

        let run_learned = self.should_vivify_learned();
        let run_irred = self.should_vivify_irred();

        let noccs = self.vivify_literal_scores();
        let mut enqueued_units = false;

        if run_learned {
            // CaDiCaL-style tick-proportional budgeting (vivify.cpp:1744).
            // Budget = VIVIFY_EFFORT_PERMILLE/1000 * (search_ticks - last_vivify_ticks).
            // Floor at VIVIFY_MIN_EFFORT to ensure progress even early in the search.
            let ticks_now = self.search_ticks[0] + self.search_ticks[1];
            let ticks_delta = ticks_now.saturating_sub(self.cold.last_vivify_ticks);
            let raw_budget = ticks_delta * VIVIFY_EFFORT_PERMILLE / 1000;
            let total_budget = raw_budget.max(VIVIFY_MIN_EFFORT);

            // Split budget across tiers by weight (CaDiCaL vivify.cpp:1753-1764).
            let total_weight =
                VIVIFY_TIER_WEIGHT_CORE + VIVIFY_TIER_WEIGHT_TIER2 + VIVIFY_TIER_WEIGHT_OTHER;
            let budget_core = total_budget * VIVIFY_TIER_WEIGHT_CORE / total_weight;
            let budget_tier2 = total_budget * VIVIFY_TIER_WEIGHT_TIER2 / total_weight;
            let budget_other = total_budget * VIVIFY_TIER_WEIGHT_OTHER / total_weight;

            for (tier, tier_budget) in [
                (VivifyTier::LearnedCore, budget_core),
                (VivifyTier::LearnedTier2, budget_tier2),
                (VivifyTier::LearnedOther, budget_other),
            ] {
                let run = self.vivify_tier(tier, &noccs, tier_budget);
                if run.conflict {
                    return true;
                }
                enqueued_units |= run.enqueued_units;
            }
            self.cold.last_vivify_ticks = self.search_ticks[0] + self.search_ticks[1];
        }

        if run_irred {
            // Irredundant vivification uses its own tick delta and weight.
            let ticks_delta = (self.search_ticks[0] + self.search_ticks[1])
                .saturating_sub(self.cold.last_vivify_irred_ticks);
            let irred_budget = ticks_delta * VIVIFY_EFFORT_PERMILLE / 1000
                * VIVIFY_TIER_WEIGHT_IRRED
                / (VIVIFY_TIER_WEIGHT_CORE
                    + VIVIFY_TIER_WEIGHT_TIER2
                    + VIVIFY_TIER_WEIGHT_OTHER
                    + VIVIFY_TIER_WEIGHT_IRRED);
            // Use at least a minimum budget based on the old fixed count to
            // prevent starvation on problems with very few search ticks.
            let irred_budget = irred_budget.max(VIVIFY_IRRED_CLAUSES_PER_CALL as u64);

            let run = self.vivify_tier(VivifyTier::Irredundant, &noccs, irred_budget);
            if run.conflict {
                return true;
            }
            enqueued_units |= run.enqueued_units;
            self.cold.last_vivify_irred_ticks = self.search_ticks[0] + self.search_ticks[1];
            self.schedule_next_irredundant_vivify(run);
        }

        if enqueued_units && self.vivify_propagate().is_some() {
            return true;
        }

        debug_assert_eq!(
            self.decision_level, 0,
            "BUG: vivify() did not restore decision level to 0"
        );
        false
    }

    /// Compute Jeroslow-Wang literal occurrence scores used to rank candidates.
    fn vivify_literal_scores(&self) -> Vec<i64> {
        // nocc(L) = sum over clauses C containing L of 2^(12 - min(|C|, 12))
        // Reference: CaDiCaL vivify.cpp:1370-1384
        let num_lits = self.num_vars * 2;
        let mut noccs: Vec<i64> = vec![0; num_lits];
        for idx in self.arena.active_indices() {
            let shift = 12i32 - self.arena.len_of(idx) as i32;
            let score: i64 = if shift < 1 { 1 } else { 1i64 << shift };
            for &lit in self.arena.literals(idx) {
                let li = lit.index();
                if li < num_lits {
                    noccs[li] += score;
                }
            }
        }
        noccs
    }

    #[inline]
    fn schedule_next_irredundant_vivify(&mut self, run: VivifyTierRun) {
        if run.is_low_yield() {
            self.cold.vivify_irred_delay_multiplier = self
                .cold
                .vivify_irred_delay_multiplier
                .saturating_mul(2)
                .min(VIVIFY_IRRED_MAX_DELAY_MULTIPLIER);
        } else {
            self.cold.vivify_irred_delay_multiplier = 1;
        }

        let delay = VIVIFY_IRRED_INTERVAL.saturating_mul(self.cold.vivify_irred_delay_multiplier);
        self.inproc_ctrl
            .vivify_irred
            .reschedule(self.num_conflicts, delay);
    }

    #[inline]
    fn vivify_clause_score(lits: &[Literal], noccs: &[i64]) -> i64 {
        let mut best = 0i64;
        let mut second = 0i64;
        for &lit in lits {
            let s = noccs.get(lit.index()).copied().unwrap_or(0);
            if s > best {
                second = best;
                best = s;
            } else if s > second {
                second = s;
            }
        }
        best + second
    }

    /// Run only irredundant (original-clause) vivification.
    ///
    /// This entry point is kept for focused tests and diagnostics. The normal
    /// solve loop should call `vivify()`, which schedules learned + irredundant
    /// tiers together.
    #[cfg(test)]
    pub(in crate::solver) fn vivify_irredundant(&mut self) -> bool {
        if !self.enter_inprocessing() || !self.inproc_ctrl.vivify.enabled {
            return false;
        }

        let noccs = self.vivify_literal_scores();
        self.ensure_reason_clause_marks_current();
        let run = self.vivify_tier(
            VivifyTier::Irredundant,
            &noccs,
            VIVIFY_IRRED_CLAUSES_PER_CALL as u64,
        );
        if run.conflict {
            return true;
        }

        self.schedule_next_irredundant_vivify(run);

        run.enqueued_units && self.vivify_propagate().is_some()
    }
}
