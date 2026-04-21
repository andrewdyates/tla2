// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Branch-heuristic selection helpers and MAB epoch management.

use super::*;

impl Solver {
    #[inline]
    pub(super) fn legacy_branch_heuristic(&self) -> BranchHeuristic {
        if self.stable_mode {
            BranchHeuristic::Evsids
        } else {
            BranchHeuristic::Vmtf
        }
    }

    /// Switch the active branch heuristic, handling CHB score swapping.
    ///
    /// When transitioning to or from CHB, the EVSIDS activities array and
    /// chb_scores array are swapped so the binary heap always orders by
    /// the active heuristic's scores.
    pub(super) fn switch_branch_heuristic(&mut self, new_heuristic: BranchHeuristic) {
        let old = self.active_branch_heuristic;
        if old == new_heuristic {
            return;
        }
        let leaving_chb = old == BranchHeuristic::Chb;
        let entering_chb = new_heuristic == BranchHeuristic::Chb;
        if leaving_chb || entering_chb {
            self.vsids.swap_chb_scores();
        }
        self.active_branch_heuristic = new_heuristic;
    }

    pub(super) fn sync_active_branch_heuristic(&mut self) {
        let target = match self.cold.branch_selector_mode {
            BranchSelectorMode::LegacyCoupled => self.legacy_branch_heuristic(),
            BranchSelectorMode::Fixed(heuristic) => heuristic,
            BranchSelectorMode::MabUcb1 => self.active_branch_heuristic,
        };
        self.switch_branch_heuristic(target);
    }

    pub(super) fn reset_branch_heuristic_selector(&mut self) {
        self.cold.branch_mab.reset();
        let target = match self.cold.branch_selector_mode {
            BranchSelectorMode::LegacyCoupled => self.legacy_branch_heuristic(),
            BranchSelectorMode::Fixed(heuristic) => heuristic,
            BranchSelectorMode::MabUcb1 => self.cold.branch_mab.default_arm(),
        };
        self.switch_branch_heuristic(target);
        self.start_branch_heuristic_epoch();
    }

    #[inline]
    pub(super) fn start_branch_heuristic_epoch(&mut self) {
        self.cold.branch_mab.start_epoch(
            self.num_conflicts,
            self.num_decisions,
            self.num_propagations,
            self.stats.lbd_sum,
            self.stats.lbd_count,
        );
    }

    pub(super) fn complete_branch_heuristic_epoch_if_needed(&mut self) {
        match self.cold.branch_selector_mode {
            BranchSelectorMode::LegacyCoupled | BranchSelectorMode::Fixed(_) => {
                self.sync_active_branch_heuristic();
            }
            BranchSelectorMode::MabUcb1 => {
                let completed = self.cold.branch_mab.finalize_epoch(
                    self.active_branch_heuristic,
                    self.num_conflicts,
                    self.num_decisions,
                    self.num_propagations,
                    self.stats.lbd_sum,
                    self.stats.lbd_count,
                );
                if completed {
                    let prev = self.active_branch_heuristic;
                    let next = self.cold.branch_mab.select_next_arm();
                    self.switch_branch_heuristic(next);
                    if next != prev {
                        self.stats.mab_arm_switches += 1;
                    }
                }
                self.start_branch_heuristic_epoch();
            }
        }
    }

    #[inline]
    pub(super) fn pick_branch_variable_by_active_heuristic(&mut self) -> Option<Variable> {
        self.pick_branch_variable_by_heuristic(self.active_branch_heuristic)
    }

    #[inline]
    fn pick_branch_variable_by_heuristic(
        &mut self,
        heuristic: BranchHeuristic,
    ) -> Option<Variable> {
        match heuristic {
            BranchHeuristic::Evsids | BranchHeuristic::Chb => loop {
                match self.vsids.pick_branching_variable(&self.vals) {
                    Some(var) if self.var_lifecycle.is_removed(var.index()) => {
                        self.vsids.remove_from_heap(var);
                    }
                    result => break result,
                }
            },
            BranchHeuristic::Vmtf => self.vsids.pick_branching_variable_vmtf_with_lifecycle(
                &self.vals,
                self.var_lifecycle.as_slice(),
            ),
        }
    }

    #[inline]
    pub(super) fn branch_priority_is_lower(
        &self,
        lhs: Variable,
        rhs: Variable,
        heuristic: BranchHeuristic,
    ) -> bool {
        match heuristic {
            BranchHeuristic::Evsids | BranchHeuristic::Chb => {
                self.vsids.activity(lhs) < self.vsids.activity(rhs)
            }
            BranchHeuristic::Vmtf => self.vsids.bump_order(lhs) < self.vsids.bump_order(rhs),
        }
    }
}
