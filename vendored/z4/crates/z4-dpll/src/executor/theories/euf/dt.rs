// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Datatype (DT) theory solving and DT+X combined routes.

use super::super::super::Executor;
use crate::executor_types::{Result, SolveResult};
use crate::preprocess::PreprocessingPass;
#[cfg(not(kani))]
use hashbrown::HashSet;
#[cfg(kani)]
use z4_core::kani_compat::DetHashSet as HashSet;
use z4_core::{Sort, TermId};
use z4_dt::DtSolver;

impl Executor {
    /// Solve using DT (datatypes) theory for QF_DT logic.
    ///
    /// Implements DPLL(T) with datatype theory solver. The solver handles:
    /// - Constructor clash detection: C1(a) = C2(b) where C1 != C2 → CONFLICT
    /// - Injectivity: C(a1,...,an) = C(b1,...,bn) → a1=b1 ∧ ... ∧ an=bn
    /// - Selector semantics: sel_i(C(a_1,...,a_n)) = a_i
    ///
    /// Proof tracking is handled natively by `solve_incremental_theory_pipeline!`
    /// (#6705).
    pub(in crate::executor) fn solve_dt(&mut self) -> Result<SolveResult> {
        // Lift non-Bool ITEs out of predicates/applications (#5082).
        let lifted: Vec<TermId> = self.ctx.terms.lift_arithmetic_ite_all(&self.ctx.assertions);
        self.ctx.assertions = lifted;

        // Register DT selector axioms as theory lemmas for proof tracking
        let base_assertions: HashSet<TermId> = self.ctx.assertions.iter().copied().collect();
        let extra_axioms = self.dt_selector_axioms(&base_assertions);
        if self.produce_proofs_enabled() {
            for &axiom in &extra_axioms {
                let _ = self.proof_tracker.add_theory_lemma(vec![axiom]);
            }
        }

        // Pre-collect datatype registration data to avoid borrowing self.ctx
        // inside the macro (which already holds a mutable borrow on self).
        let dt_info: Vec<(String, Vec<String>)> = self
            .ctx
            .datatype_iter()
            .map(|(name, ctors)| (name.to_owned(), ctors.to_vec()))
            .collect();

        // Add selector axioms to self.ctx.assertions temporarily;
        // the incremental pipeline reads assertions from there.
        let base_len = self.ctx.assertions.len();
        self.ctx.assertions.extend(extra_axioms);

        let result = solve_incremental_theory_pipeline!(self,
            tag: "DT",
            create_theory: {
                let mut t = DtSolver::new(&self.ctx.terms);
                for (dt_name, constructors) in &dt_info {
                    t.register_datatype(dt_name, constructors);
                }
                t
            },
            extract_models: |_theory| TheoryModels::default(),
            track_theory_stats: false,
            set_unknown_on_error: false
        );

        // Restore assertions to original length (remove temporary axioms).
        self.ctx.assertions.truncate(base_len);
        result
    }

    /// Shared DT delegation: occurs-check, selector/acyclicity axioms, delegate, truncate.
    ///
    /// All `solve_dt_*` methods follow the same pattern (#3536):
    /// 1. DT occurs-check fast path → early UNSAT (#1776)
    /// 2. Generate DT selector axioms from base assertions
    /// 3. Optionally generate acyclicity depth axioms (#1764)
    /// 4. Temporarily extend assertions with DT axioms
    /// 5. Delegate to underlying theory solver
    /// 6. Truncate assertions to restore original state (#1770)
    fn solve_with_dt_axioms(
        &mut self,
        acyclicity_sort: Option<Sort>,
        solve_fn: fn(&mut Self) -> Result<SolveResult>,
    ) -> Result<SolveResult> {
        // Flatten top-level conjunctions so DT axiom scan sees individual
        // equalities, not (and ...) wrappers. Without this, the reachability
        // filter in dt_selector_axioms misses DT constructors inside
        // conjunctions, causing false-SAT on DT+BV formulas (#7016).
        let mut flatten = crate::preprocess::FlattenAnd::new();
        flatten.apply(&mut self.ctx.terms, &mut self.ctx.assertions);

        if self.dt_occurs_check_unsat_from_equalities(&self.ctx.assertions, &[]) {
            self.last_unknown_reason = None;
            return Ok(SolveResult::Unsat);
        }

        let base_assertions: HashSet<TermId> = self.ctx.assertions.iter().copied().collect();
        let mut extra_axioms = self.dt_selector_axioms(&base_assertions);

        if let Some(sort) = acyclicity_sort {
            extra_axioms.extend(self.dt_acyclicity_depth_axioms(sort));
        }

        let base_len = self.ctx.assertions.len();
        self.ctx.assertions.extend(extra_axioms);
        let result = solve_fn(self);
        self.ctx.assertions.truncate(base_len);
        result
    }

    /// Solve combined DT + LIA (#1760). DT axioms + acyclicity(Int) → AUFLIA.
    pub(in crate::executor) fn solve_dt_auflia(&mut self) -> Result<SolveResult> {
        self.solve_with_dt_axioms(Some(Sort::Int), Self::solve_auf_lia)
    }

    /// Solve combined DT + LRA (#1760). DT axioms + acyclicity(Real) → AUFLRA.
    pub(in crate::executor) fn solve_dt_auflra(&mut self) -> Result<SolveResult> {
        self.solve_with_dt_axioms(Some(Sort::Real), Self::solve_auf_lra)
    }

    /// Solve combined DT + LIRA (#5402). DT axioms + acyclicity(Int) → AUFLIRA.
    pub(in crate::executor) fn solve_dt_auflira(&mut self) -> Result<SolveResult> {
        self.solve_with_dt_axioms(Some(Sort::Int), Self::solve_auflira)
    }

    /// Solve combined DT + BV (#1766). DT axioms only (no acyclicity) → UFBV.
    pub(in crate::executor) fn solve_dt_ufbv(&mut self) -> Result<SolveResult> {
        self.solve_with_dt_axioms(None, Self::solve_ufbv)
    }

    /// Solve combined DT + Arrays + BV (#1766). DT axioms only → AUFBV.
    pub(in crate::executor) fn solve_dt_aufbv(&mut self) -> Result<SolveResult> {
        self.solve_with_dt_axioms(None, Self::solve_aufbv)
    }

    /// Solve combined DT + Arrays (#1766). DT axioms only → Array+EUF.
    pub(in crate::executor) fn solve_dt_ax(&mut self) -> Result<SolveResult> {
        self.solve_with_dt_axioms(None, Self::solve_array_euf)
    }
}
