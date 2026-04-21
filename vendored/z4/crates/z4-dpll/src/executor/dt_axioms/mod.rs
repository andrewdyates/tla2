// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Datatype (DT) axiom generation for combined DT+theory solver paths.
//!
//! Three DT axiom generators used by the executor's combined solver dispatch:
//!
//! - [`Executor::dt_selector_axioms`]: Selector projection, tester evaluation,
//!   exhaustiveness, constructor, and equality-to-tester axioms (A-E).
//! - [`Executor::dt_acyclicity_depth_axioms`]: Depth-function acyclicity encoding
//!   via rank functions (Barrett, Shikanian, Tinelli 2007).
//! - [`Executor::dt_occurs_check_unsat_from_equalities`]: Fast-path cycle detection
//!   using the pure DT solver's occurs-check.
//!
//! Originally a single file (`dt_axioms.rs`), split into submodules for code health.

mod acyclicity;
mod selector;

#[cfg(not(kani))]
use hashbrown::HashSet;
#[cfg(kani)]
use z4_core::kani_compat::DetHashSet as HashSet;
use z4_core::term::Symbol;
use z4_core::{Sort, TermData, TermId, TheorySolver};
use z4_dt::DtSolver;

use super::Executor;
use crate::executor_types::{Result, SolveResult};
use crate::logic_detection::TheoryKind;

/// Selector metadata: list of (selector_name, selector_sort) pairs
pub(in crate::executor) type SelectorList = Vec<(String, Sort)>;

impl Executor {
    /// Fast path: detect datatype cycles using the pure DT solver's occurs-check.
    ///
    /// This is used for combined DT+arithmetic paths (DT_AUFLIA/DT_AUFLRA). The depth-axiom
    /// encoding is incomplete for multi-hop equality cycles (#1776), but acyclicity is a
    /// datatype-only property and can be decided without arithmetic reasoning.
    ///
    /// Safety: Only considers top-level asserted/assumed *equalities* (no Boolean structure).
    pub(in crate::executor) fn dt_occurs_check_unsat_from_equalities(
        &self,
        assertions: &[TermId],
        assumptions: &[TermId],
    ) -> bool {
        // If no datatypes are declared, the DT solver has nothing to contribute.
        if self.ctx.datatype_iter().next().is_none() {
            return false;
        }

        let mut dt = DtSolver::new(&self.ctx.terms);
        for (dt_name, constructors) in self.ctx.datatype_iter() {
            dt.register_datatype(dt_name, constructors);
        }

        let mut saw_equality = false;
        for &t in assertions.iter().chain(assumptions.iter()) {
            // Only consider top-level equalities (asserted/assumed facts).
            let is_eq = matches!(
                self.ctx.terms.get(t),
                TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2
            );
            if !is_eq {
                continue;
            }
            saw_equality = true;
            dt.assert_literal(t, true);
        }

        if !saw_equality {
            return false;
        }

        matches!(dt.check(), z4_core::TheoryResult::Unsat(_))
    }

    /// Unified check-sat-assuming path for all DT-combined logics.
    ///
    /// Handles the common DT pattern:
    /// 1. Occurs-check fast path (returns UNSAT if cyclic)
    /// 2. DT selector axiom generation from assertions + assumptions
    /// 3. Optional acyclicity depth axiom generation
    /// 4. Dispatch to the appropriate theory solver
    ///
    /// # Arguments
    ///
    /// * `base_assertions` - The permanent assertions plus any scope-level additions
    /// * `assumptions` - Temporary assumptions for this check-sat call
    /// * `acyclicity_sort` - If `Some(sort)`, generate acyclicity depth axioms using
    ///   that sort for the depth function. `None` for BV/Array arms where the theory
    ///   solver cannot handle integer arithmetic (#1766).
    /// * `dispatch` - Which theory solver to route to after axiom generation.
    ///
    /// Extracted from 6 near-identical match arms in `check_sat_assuming` (#5564).
    pub(in crate::executor) fn dt_combined_check_sat_assuming(
        &mut self,
        base_assertions: &[TermId],
        assumptions: &[TermId],
        acyclicity_sort: Option<Sort>,
        dispatch: DtSolverDispatch,
    ) -> Result<SolveResult> {
        // Fast path: pure DT occurs-check can decide acyclicity even when the
        // depth-axiom encoding is incomplete for multi-hop cycles (#1776).
        if self.dt_occurs_check_unsat_from_equalities(base_assertions, assumptions) {
            self.last_unknown_reason = None;
            self.last_result = Some(SolveResult::Unsat);
            self.last_assumption_core = Some(vec![]);
            return Ok(SolveResult::Unsat);
        }

        // Include assumptions in base_set for DT axiom generation (#1768).
        // Equalities like `(= x (cons n x))` in assumptions must be processed.
        let mut base_set: HashSet<TermId> = base_assertions.iter().copied().collect();
        base_set.extend(assumptions.iter().copied());
        let dt_axioms = self.dt_selector_axioms(&base_set);

        let mut extended_assertions = base_assertions.to_vec();
        extended_assertions.extend(dt_axioms);

        // Generate and add acyclicity depth axioms if the theory solver can handle
        // the arithmetic encoding (Sort::Int or Sort::Real).
        let acyclicity_axioms = if let Some(sort) = acyclicity_sort {
            // Temporarily add assumptions to ctx.assertions for depth axiom
            // generation (#1768). This ensures depth congruence axioms are
            // generated for assumption equalities.
            let original_assertions_len = self.ctx.assertions.len();
            self.ctx.assertions.extend(assumptions.iter().copied());
            let axioms = self.dt_acyclicity_depth_axioms(sort);
            self.ctx.assertions.truncate(original_assertions_len);

            extended_assertions.extend(axioms.iter().copied());
            axioms
        } else {
            vec![]
        };

        // Temporarily add acyclicity depth axioms to ctx.assertions so
        // validate_model checks them during check_sat_assuming, matching
        // the scope of the non-assuming DT solve methods (#3240). Selector
        // axioms are not added here because the model evaluator lacks full
        // DT selector-constructor reduction semantics.
        let pre_solve_len = self.ctx.assertions.len();
        self.ctx.assertions.extend(acyclicity_axioms);

        let result = match dispatch {
            DtSolverDispatch::AufLia => {
                self.solve_auf_lia_with_assumptions(&extended_assertions, assumptions)
            }
            DtSolverDispatch::AufLira => {
                self.solve_auflira_with_assumptions(&extended_assertions, assumptions)
            }
            DtSolverDispatch::Theory(kind) => {
                self.solve_with_assumptions_for_theory(&extended_assertions, assumptions, kind)
            }
        };

        // Restore assertions after solving.
        self.ctx.assertions.truncate(pre_solve_len);
        result
    }
}

/// Dispatch variant for DT-combined solver routing.
///
/// Parameterizes which underlying theory solver the DT-combined path should
/// route to after generating DT axioms.
#[derive(Debug, Clone, Copy)]
pub(in crate::executor) enum DtSolverDispatch {
    /// Route to `solve_auf_lia_with_assumptions` (split-aware DT+LIA, #1771).
    AufLia,
    /// Route to `solve_auflira_with_assumptions` (DT+LIRA, #5402).
    AufLira,
    /// Route to `solve_with_assumptions_for_theory` with the given theory kind.
    Theory(TheoryKind),
}
