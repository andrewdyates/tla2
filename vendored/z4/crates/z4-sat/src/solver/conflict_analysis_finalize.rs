// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::kani_compat::det_hash_set_with_capacity;

impl Solver {
    pub(super) fn finalize_conflict_analysis(
        &mut self,
        uip: Literal,
        mut lrat_level0_vars: Vec<usize>,
    ) -> ConflictResult {
        self.conflict.set_asserting_literal(uip);
        self.update_bumpreason_decision_rate();

        // Snapshot learned clause before minimization for LRAT chain
        // computation. Minimization may remove literals whose transitive
        // reasons need to be included in the resolution chain.
        let original_learned: Vec<Literal> = if self.cold.lrat_enabled {
            (0..self.conflict.learned_count())
                .map(|i| self.conflict.learned_at(i))
                .collect()
        } else {
            Vec::new()
        };

        let lbd = self.conflict.compute_lbd(&self.var_data);
        let pre_min_clause_size = self.conflict.learned_count() + 1;
        debug_assert!(
            (lbd as usize) < pre_min_clause_size || pre_min_clause_size <= 1,
            "BUG: LBD ({lbd}) >= pre-minimization clause size ({pre_min_clause_size}) — CaDiCaL invariant: glue < size",
        );

        if self.shrink_enabled {
            self.shrink_and_minimize_learned_clause();
        } else {
            self.minimize_learned_clause();
        }

        self.clear_level_seen();
        self.bump_reason_literals();
        self.bump_analyzed_variables();

        // Forward LRAT chain computation: add reason chains for literals
        // removed during minimization and level-0 unit proof IDs.
        // CaDiCaL: calculate_minimize_chain() in minimize.cpp:155-199,
        // then unit_chain in analyze.cpp:1240-1246.
        if self.cold.lrat_enabled {
            let minimize_level0 = self.compute_lrat_chain_for_removed_literals(&original_learned);
            lrat_level0_vars.extend(minimize_level0);
        }

        if self.cold.lrat_enabled && !lrat_level0_vars.is_empty() {
            self.materialize_level0_unit_proofs();
            let mut rup_satisfied = det_hash_set_with_capacity(1 + self.conflict.learned_count());
            rup_satisfied.insert(uip.negated());
            for i in 0..self.conflict.learned_count() {
                rup_satisfied.insert(self.conflict.learned_at(i).negated());
            }
            self.append_lrat_unit_chain(&lrat_level0_vars, &rup_satisfied);
        }

        let backtrack_level = self.conflict.compute_backtrack_level(&self.var_data);
        let mut result = self.conflict.get_result(backtrack_level, lbd);

        crate::conflict::reorder_for_watches(
            &mut result.learned_clause,
            &self.var_data,
            backtrack_level,
        );

        self.debug_assert_learned_clause_invariants(uip, backtrack_level, &result.learned_clause);
        result
    }
}
