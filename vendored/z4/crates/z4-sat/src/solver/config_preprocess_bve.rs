// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

pub(super) struct PreprocessBveOutcome {
    pub(super) found_unsat: bool,
    pub(super) rebuilt_watches: bool,
}

impl Solver {
    pub(super) fn run_preprocess_bve(
        &mut self,
        skip_gate_dependent_passes: bool,
        _skip_expensive_preprocessing_passes: bool,
    ) -> PreprocessBveOutcome {
        if !self.inproc_ctrl.bve.enabled {
            return PreprocessBveOutcome {
                found_unsat: false,
                rebuilt_watches: false,
            };
        }

        // Skip preprocessing BVE on very large dense formulas (#8136).
        let active_cls = self.arena.active_clause_count();
        let active_vars = self.num_vars.saturating_sub(self.count_fixed_vars());
        let density = if active_vars > 0 { active_cls as f64 / active_vars as f64 } else { 0.0 };
        if active_cls > PREPROCESS_BVE_SKIP_CLAUSE_THRESHOLD && density > PREPROCESS_BVE_SKIP_DENSITY {
            return PreprocessBveOutcome { found_unsat: false, rebuilt_watches: false };
        }

        self.watches.clear();
        self.watches_disconnected = true;

        // Pass 1: fastelim (bound=8). Runs on all formulas, including uniform
        // random k-SAT, because it relies on occurrence counting rather than
        // gate structure.
        self.inproc.bve.set_growth_bound(8);
        self.set_diagnostic_pass(DiagnosticPass::BVE);
        let mut bve_unsat = (self.cold.last_bve_fixed != self.fixed_count
            || self.cold.last_bve_marked != self.cold.bve_marked)
            && self.bve();
        self.clear_diagnostic_pass();

        // Passes 2-3: gate-based BVE (bounds 1, 2). Skip on uniform
        // non-binary formulas, which do not usually contain profitable gates.
        // Also skip gate-BVE on large formulas: gate extraction + extra rounds
        // add O(clauses * gate_checks) overhead while fastelim handles the bulk.
        if self.inproc_ctrl.gate.enabled
            && !skip_gate_dependent_passes
            && !_skip_expensive_preprocessing_passes
        {
            for pass_bound in [1, 2] {
                if bve_unsat || self.is_interrupted() {
                    break;
                }
                self.inproc.bve.reset_growth_bound_for_inprocessing();
                let mut current = 0u32;
                while current < pass_bound {
                    self.inproc.bve.increment_growth_bound();
                    current = if current == 0 { 1 } else { current * 2 };
                }
                self.cold.last_bve_marked = self.cold.bve_marked.wrapping_sub(1);
                self.set_diagnostic_pass(DiagnosticPass::BVE);
                bve_unsat = self.bve();
                self.clear_diagnostic_pass();
            }
        }

        self.clear_stale_reasons();
        // Preprocessing BVE: full re-propagation needed (#8095).
        self.mark_trail_affected(0);
        self.watches_disconnected = false;
        self.rebuild_watches();

        if bve_unsat || self.propagate_check_unsat() {
            return PreprocessBveOutcome {
                found_unsat: true,
                rebuilt_watches: true,
            };
        }

        PreprocessBveOutcome {
            found_unsat: false,
            rebuilt_watches: true,
        }
    }
}
