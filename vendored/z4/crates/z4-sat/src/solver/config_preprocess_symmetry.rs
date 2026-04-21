// Copyright 2026 Andrew Yates.
// Author: AI Model
// Licensed under the Apache License, Version 2.0

//! Root-only symmetry preprocessing.

use super::mutate::AddResult;
use super::*;

const SYMMETRY_MAX_VARS: usize = 4_096;
const SYMMETRY_MAX_CLAUSES: usize = 20_000;
const SYMMETRY_MAX_PAIRS: usize = 128;
const SYMMETRY_MAX_GROUP_SIZE: usize = 64;

impl Solver {
    /// Detect variable symmetries via BreakID-style iterative refinement and
    /// emit lex-leader SBP clauses for each orbit.
    ///
    /// Returns `(unsat, changed)`.
    pub(super) fn preprocess_symmetry(&mut self) -> (bool, bool) {
        self.cold.symmetry_stats.begin_run();

        if !self.cold.symmetry_enabled {
            self.cold
                .symmetry_stats
                .skip(crate::symmetry::SymmetrySkipReason::Disabled);
            return (false, false);
        }
        if self.cold.has_been_incremental {
            self.cold
                .symmetry_stats
                .skip(crate::symmetry::SymmetrySkipReason::Incremental);
            return (false, false);
        }
        if self.proof_manager.is_some()
            || self.cold.clause_trace.is_some()
            || self.cold.lrat_enabled
        {
            self.cold
                .symmetry_stats
                .skip(crate::symmetry::SymmetrySkipReason::ProofMode);
            return (false, false);
        }
        if self.num_vars > SYMMETRY_MAX_VARS
            || self.arena.active_clause_count() > SYMMETRY_MAX_CLAUSES
        {
            self.cold
                .symmetry_stats
                .skip(crate::symmetry::SymmetrySkipReason::TooLarge);
            return (false, false);
        }

        let clauses = self.snapshot_root_irredundant_clauses_for_symmetry();
        if clauses.len() < 2 {
            self.cold
                .symmetry_stats
                .skip(crate::symmetry::SymmetrySkipReason::NoActiveClauses);
            return (false, false);
        }

        // BreakID pipeline: refinement → swap verification → orbit extraction → SBP
        let detector = crate::symmetry::detector::SymmetryDetector::new(
            SYMMETRY_MAX_PAIRS,
            SYMMETRY_MAX_GROUP_SIZE,
        );
        let (sbp_clauses, det_stats) = detector.detect_and_encode(&clauses);

        // Propagate detector stats into symmetry stats.
        self.cold.symmetry_stats.candidate_pairs = self
            .cold
            .symmetry_stats
            .candidate_pairs
            .saturating_add(det_stats.candidate_pairs);
        self.cold.symmetry_stats.pairs_detected = self
            .cold
            .symmetry_stats
            .pairs_detected
            .saturating_add(det_stats.pairs_detected);

        if sbp_clauses.is_empty() {
            self.cold
                .symmetry_stats
                .skip(crate::symmetry::SymmetrySkipReason::NoPairs);
            return (false, false);
        }

        // Deduplicate SBP clauses against existing formula.
        let existing_clause_counts = crate::symmetry::build_formula_counts(&clauses);
        let unique_sbps = crate::symmetry::detector::deduplicate_sbp_clauses(
            sbp_clauses,
            &existing_clause_counts,
        );

        let mut changed = false;
        for sbp in unique_sbps {
            let mut clause = sbp;
            match self.add_clause_watched(&mut clause) {
                AddResult::Added(_) | AddResult::Unit(_) => {
                    changed = true;
                    self.cold.symmetry_stats.sb_clauses_added =
                        self.cold.symmetry_stats.sb_clauses_added.saturating_add(1);
                }
                AddResult::Empty => return (true, true),
            }
        }

        (false, changed)
    }

    fn snapshot_root_irredundant_clauses_for_symmetry(&self) -> Vec<Vec<Literal>> {
        let mut clauses = Vec::new();

        for clause_idx in self.arena.active_indices() {
            if self.arena.is_dead(clause_idx) || self.arena.is_learned(clause_idx) {
                continue;
            }

            let mut reduced = Vec::with_capacity(self.arena.len_of(clause_idx));
            let mut satisfied = false;

            for &lit in self.arena.literals(clause_idx) {
                match self.lit_value(lit) {
                    Some(true) => {
                        satisfied = true;
                        break;
                    }
                    Some(false) => {}
                    None => reduced.push(lit),
                }
            }

            if satisfied || reduced.is_empty() {
                continue;
            }

            reduced.sort_unstable_by_key(|lit| lit.raw());
            clauses.push(reduced);
        }

        clauses
    }
}
