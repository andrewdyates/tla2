// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Generic sequence theory (Seq T) solving.
//!
//! Handles QF_SEQ and QF_SEQLIA logics. QF_SEQ uses the combined EUF+Seq
//! solver for Nelson-Oppen equality exchange (see #5951). QF_SEQLIA adds
//! LIA for `seq.len` reasoning with injected length axioms (see #5958).

mod axioms_core;
mod axioms_indexof;
mod axioms_replace;
mod axioms_search;
mod bv_transitivity;
mod ground;
mod scan;
#[cfg(test)]
mod tests;

use scan::SUPPORTED_SEQ_OPS;

use super::super::Executor;
use super::solve_harness::TheoryModels;
use super::MAX_SPLITS_LIA;
use crate::combined_solvers::{UfSeqLiaSolver, UfSeqSolver};
use crate::executor_types::{Result, SolveResult, UnknownReason};
use z4_core::term::{Symbol, TermData, TermId};

impl Executor {
    /// Solve using the combined EUF+Seq theory (QF_SEQ).
    ///
    /// If `seq.len` terms or axiom-generating operations (contains, extract, etc.)
    /// are detected, automatically routes to `solve_seq_lia()` for LIA reasoning.
    pub(in crate::executor) fn solve_seq(&mut self) -> Result<SolveResult> {
        // Guard: return Unknown for unsupported Seq operations (#5985).
        // Without axioms, these become uninterpreted functions → false SAT.
        if self.assertions_contain_unsupported_seq_ops() {
            self.last_unknown_reason = Some(UnknownReason::Incomplete);
            return Ok(SolveResult::Unknown);
        }

        // Route to SeqLIA if length terms or axiom-generating ops are present.
        // Operations like seq.contains, seq.extract, seq.prefixof, etc.
        // generate length constraints that require LIA reasoning (#5841).
        if self.assertions_contain_seq_len() || self.assertions_contain_axiom_ops() {
            return self.solve_seq_lia();
        }

        // Inject structural axioms (e.g., seq.nth) even without seq.len (#5841).
        let nth_axioms = self.collect_seq_nth_axioms();
        if !nth_axioms.is_empty() {
            let mut seen: hashbrown::HashSet<_> = self.ctx.assertions.iter().copied().collect();
            self.ctx
                .assertions
                .extend(nth_axioms.into_iter().filter(|axiom| seen.insert(*axiom)));
        }

        // Inject BV comparison transitivity axioms for Seq<BitVec> formulas (#7587, #7579).
        // When BV predicates (bvsle, bvule, etc.) appear in Seq formulas, EUF treats
        // them as uninterpreted — losing ordering transitivity. Explicit axioms restore it.
        let bv_trans_axioms = self.collect_bv_transitivity_axioms();
        if !bv_trans_axioms.is_empty() {
            let mut seen: hashbrown::HashSet<_> = self.ctx.assertions.iter().copied().collect();
            self.ctx.assertions.extend(
                bv_trans_axioms
                    .into_iter()
                    .filter(|axiom| seen.insert(*axiom)),
            );
        }

        // Skip model validation for Seq: extract_model() only populates values
        // for concretizable terms (seq.unit/empty/concat). Unconstrained Seq
        // variables get no model value, causing finalize_sat_model_validation()
        // to degrade SAT to Unknown. Same pattern as FP (fp.rs:992) and
        // String (strings.rs:491,780) solvers. (#6486)
        self.skip_model_eval = true;

        solve_incremental_theory_pipeline!(self,
            tag: "Seq",
            create_theory: UfSeqSolver::new(&self.ctx.terms),
            extract_models: |theory| {
                let (euf_model, seq_model) = theory.extract_models();
                TheoryModels {
                    euf: Some(euf_model),
                    seq: Some(seq_model),
                    ..TheoryModels::default()
                }
            },
            track_theory_stats: true,
            set_unknown_on_error: false
        )
    }

    /// Solve using the combined EUF+Seq+LIA theory (QF_SEQLIA).
    ///
    /// Injects `seq.len` axioms then solves with `UfSeqLiaSolver` (#5958).
    pub(in crate::executor) fn solve_seq_lia(&mut self) -> Result<SolveResult> {
        // Guard: return Unknown for unsupported Seq operations (#5985).
        if self.assertions_contain_unsupported_seq_ops() {
            self.last_unknown_reason = Some(UnknownReason::Incomplete);
            return Ok(SolveResult::Unknown);
        }

        let seq_len_axioms = self.collect_seq_len_axioms();
        if !seq_len_axioms.is_empty() {
            let mut seen: hashbrown::HashSet<_> = self.ctx.assertions.iter().copied().collect();
            self.ctx.assertions.extend(
                seq_len_axioms
                    .into_iter()
                    .filter(|axiom| seen.insert(*axiom)),
            );
        }

        // Inject BV comparison transitivity axioms for Seq<BitVec> formulas (#7587, #7579).
        let bv_trans_axioms = self.collect_bv_transitivity_axioms();
        if !bv_trans_axioms.is_empty() {
            let mut seen: hashbrown::HashSet<_> = self.ctx.assertions.iter().copied().collect();
            self.ctx.assertions.extend(
                bv_trans_axioms
                    .into_iter()
                    .filter(|axiom| seen.insert(*axiom)),
            );
        }

        // Skip model validation for SeqLIA: same rationale as solve_seq() (#6486).
        self.skip_model_eval = true;

        let solve_interrupt = self.solve_interrupt.clone();
        let solve_deadline = self.solve_deadline;
        solve_incremental_split_loop_pipeline!(self,
            tag: "SeqLIA",
            persistent_sat_field: lia_persistent_sat,
            create_theory: UfSeqLiaSolver::new(&self.ctx.terms),
            extract_models: |theory| {
                let (euf_model, seq_model, lia_model) = theory.extract_models();
                TheoryModels {
                    euf: Some(euf_model),
                    seq: Some(seq_model),
                    lia: lia_model,
                    ..TheoryModels::default()
                }
            },
            max_splits: MAX_SPLITS_LIA,
            pre_theory_import: |theory, lc, hc, ds| {
                theory.import_learned_state(std::mem::take(lc), std::mem::take(hc));
                theory.import_dioph_state(std::mem::take(ds));
            },
            post_theory_export: |_theory| {
                let (lc, hc) = _theory.take_learned_state();
                let ds = _theory.take_dioph_state();
                (lc, hc, ds)
            },
            pre_iter_check: |_s| {
                solve_interrupt
                    .as_ref()
                    .is_some_and(|flag| flag.load(std::sync::atomic::Ordering::Relaxed))
                    || solve_deadline.is_some_and(|dl| std::time::Instant::now() >= dl)
            }
        )
    }

    /// Solve QF_SEQ with check-sat-assuming (#5994, #7656).
    ///
    /// Mirrors `solve_seq()` but temporarily adds assumptions to assertions,
    /// using UfSeqSolver (not bare SeqSolver) for correct Nelson-Oppen reasoning.
    ///
    /// Uses `with_isolated_incremental_state` to prevent assumption-scoped
    /// clauses from leaking into the persistent SAT solver. Without isolation,
    /// contradictory assumptions encoded as permanent unit clauses poison the
    /// incremental state, causing subsequent calls to return false UNSAT (#7656).
    pub(in crate::executor) fn solve_seq_with_assumptions(
        &mut self,
        assertions: &[TermId],
        assumptions: &[TermId],
    ) -> Result<SolveResult> {
        let mut scoped_assertions = Vec::with_capacity(assertions.len() + assumptions.len());
        scoped_assertions.extend(assertions.iter().copied());
        scoped_assertions.extend(assumptions.iter().copied());

        let result = self.with_isolated_incremental_state(Some(scoped_assertions), Self::solve_seq);

        match result {
            Ok(SolveResult::Unsat) => {
                self.last_assumption_core = Some(assumptions.to_vec());
                Ok(SolveResult::Unsat)
            }
            Ok(SolveResult::Sat) => {
                self.last_assumption_core = None;
                Ok(SolveResult::Sat)
            }
            Ok(SolveResult::Unknown) => {
                self.last_assumption_core = None;
                Ok(SolveResult::Unknown)
            }
            Err(err) => {
                self.last_assumption_core = None;
                Err(err)
            }
        }
    }

    /// Solve QF_SEQLIA with check-sat-assuming (#5994, #7656).
    ///
    /// Mirrors `solve_seq_lia()` but temporarily adds assumptions to assertions,
    /// using UfSeqLiaSolver with axiom injection for correct Seq+LIA reasoning.
    ///
    /// Uses `with_isolated_incremental_state` to prevent assumption-scoped
    /// clauses from leaking into the persistent SAT solver (#7656).
    pub(in crate::executor) fn solve_seq_lia_with_assumptions(
        &mut self,
        assertions: &[TermId],
        assumptions: &[TermId],
    ) -> Result<SolveResult> {
        let mut scoped_assertions = Vec::with_capacity(assertions.len() + assumptions.len());
        scoped_assertions.extend(assertions.iter().copied());
        scoped_assertions.extend(assumptions.iter().copied());

        let result =
            self.with_isolated_incremental_state(Some(scoped_assertions), Self::solve_seq_lia);

        match result {
            Ok(SolveResult::Unsat) => {
                self.last_assumption_core = Some(assumptions.to_vec());
                Ok(SolveResult::Unsat)
            }
            Ok(SolveResult::Sat) => {
                self.last_assumption_core = None;
                Ok(SolveResult::Sat)
            }
            Ok(SolveResult::Unknown) => {
                self.last_assumption_core = None;
                Ok(SolveResult::Unknown)
            }
            Err(err) => {
                self.last_assumption_core = None;
                Err(err)
            }
        }
    }

    /// Check whether any assertion contains a `seq.len` application.
    fn assertions_contain_seq_len(&self) -> bool {
        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        let mut visited = hashbrown::HashSet::new();
        while let Some(term) = stack.pop() {
            if !visited.insert(term) {
                continue;
            }
            match self.ctx.terms.get(term) {
                TermData::App(Symbol::Named(name), args) => {
                    if name == "seq.len" {
                        return true;
                    }
                    for &arg in args {
                        stack.push(arg);
                    }
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, t, e) => {
                    stack.push(*c);
                    stack.push(*t);
                    stack.push(*e);
                }
                _ => {}
            }
        }
        false
    }

    /// Check whether assertions contain any unsupported Seq operations (#5985, #6026).
    ///
    /// Uses a positive allowlist (`SUPPORTED_SEQ_OPS`) instead of a negative blocklist.
    /// Any `seq.*` application not in the allowlist triggers Unknown, preventing
    /// unrecognized operations from silently becoming uninterpreted functions (false SAT).
    pub(in crate::executor) fn assertions_contain_unsupported_seq_ops(&self) -> bool {
        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        let mut visited = hashbrown::HashSet::new();
        while let Some(term) = stack.pop() {
            if !visited.insert(term) {
                continue;
            }
            match self.ctx.terms.get(term) {
                TermData::App(Symbol::Named(name), args) => {
                    if name.starts_with("seq.") && !SUPPORTED_SEQ_OPS.contains(&name.as_str()) {
                        return true;
                    }
                    for &arg in args {
                        stack.push(arg);
                    }
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, t, e) => {
                    stack.push(*c);
                    stack.push(*t);
                    stack.push(*e);
                }
                _ => {}
            }
        }
        false
    }
}
