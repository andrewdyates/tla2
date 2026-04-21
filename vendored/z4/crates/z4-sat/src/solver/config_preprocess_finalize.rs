// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::mutate::ReasonPolicy;
use super::*;

impl Solver {
    #[allow(clippy::too_many_arguments, unused_variables)]
    pub(super) fn emit_preprocess_summary(
        &self,
        preprocess_start: std::time::Instant,
        t1_cong: u128,
        t2_bb: u128,
        t3_decomp: u128,
        t4_factor: u128,
        t5_bve: u128,
        t6_probe: u128,
    ) {
        #[cfg(z4_logging)]
        {
            let fixed = self.count_fixed_vars();
            let eliminated = self.inproc.bve.stats().vars_eliminated;
            let substituted = self.decompose_stats().substituted;
            let factored = self.cold.factor_factored_total;
            let active = self.num_vars - fixed - self.var_lifecycle.count_removed();
            let clauses = self.arena.active_clause_count();
            let preprocess_ms = preprocess_start.elapsed().as_millis();
            eprintln!(
                "c preprocess: fixed={fixed} eliminated={eliminated} \
                 substituted={substituted} factored={factored} \
                 active={active} clauses={clauses} time={preprocess_ms}ms \
                 [cong={t1_cong} bb={t2_bb} decomp={t3_decomp} factor={t4_factor} bve={t5_bve} probe={t6_probe}]"
            );
        }
    }

    pub(super) fn finalize_preprocess_clause_cleanup(&mut self) {
        self.defer_stale_reason_cleanup = true;
        let all_indices: Vec<usize> = self.arena.indices().collect();
        for idx in all_indices {
            if self.arena.is_empty_clause(idx) {
                continue;
            }
            let has_removed = self
                .arena
                .literals(idx)
                .iter()
                .any(|lit| self.var_lifecycle.is_removed(lit.variable().index()));
            if has_removed {
                self.delete_clause_checked(idx, ReasonPolicy::ClearLevel0);
            }
        }
        self.defer_stale_reason_cleanup = false;
        self.clear_stale_reasons();
    }
}
