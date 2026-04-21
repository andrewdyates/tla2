// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! CNF/Tseitin encoding for check_sat queries.
//!
//! Converts the preprocessed query into a SAT solver instance with
//! Tseitin-encoded clauses, optionally with per-conjunct assumptions
//! for unsat-core extraction.

use std::time::{Duration, Instant};

use rustc_hash::FxHashMap;
use z4_core::{TermId, Tseitin};

use super::super::context::SmtContext;
use super::super::types::SmtResult;
use super::CnfState;
use super::PreparedQuery;
use crate::ChcExpr;

#[cfg(not(kani))]
use hashbrown::HashMap as HbHashMap;
#[cfg(kani)]
use z4_core::kani_compat::DetHashMap as HbHashMap;

impl SmtContext {
    /// Build the CNF encoding for a check_sat query.
    ///
    /// Converts the preprocessed expressions into Tseitin clauses and
    /// populates a fresh SAT solver. When the query has multiple
    /// top-level conjuncts, each gets its own assumption literal for
    /// unsat-core extraction.
    ///
    /// Returns `Err(SmtResult::Unknown)` on budget or timeout exhaustion.
    pub(super) fn build_check_sat_cnf(
        &mut self,
        prepared: &PreparedQuery,
        start: Instant,
        timeout: Option<Duration>,
    ) -> Result<CnfState, SmtResult> {
        let use_assumptions = prepared.top_conjuncts.len() >= 2;

        let (term_to_var, var_to_term, num_vars, sat, assumptions, assumption_map) =
            if use_assumptions {
                let conjunct_terms: Vec<(ChcExpr, TermId)> = prepared
                    .top_conjuncts
                    .iter()
                    .map(|c| (c.clone(), self.convert_expr(c)))
                    .collect();

                // Bail out if conversion budget was exceeded (#2771).
                if self.conversion_budget_exceeded {
                    return Err(SmtResult::Unknown);
                }
                // #5877: Check timeout after expression conversion. For BV-to-Int
                // problems with unrolled transitions (k>=2), convert_expr can exceed
                // the per-query timeout, starving the portfolio of time for PDR.
                if let Some(t) = timeout {
                    if start.elapsed() >= t {
                        return Err(SmtResult::Unknown);
                    }
                }

                let mut tseitin = Tseitin::new(&self.terms);

                let mut assumptions: Vec<z4_sat::Literal> =
                    Vec::with_capacity(conjunct_terms.len());
                let mut assumption_map: FxHashMap<z4_sat::Literal, ChcExpr> = FxHashMap::default();

                for (c, c_term) in &conjunct_terms {
                    let cnf_lit = tseitin.encode(*c_term, true);
                    let sat_lit = z4_sat::Literal::from_dimacs(cnf_lit);
                    assumptions.push(sat_lit);
                    assumption_map.insert(sat_lit, c.clone());
                }

                let mut sat = z4_sat::Solver::new(tseitin.num_vars() as usize);
                // #5384: enable clause tracing for UNSAT verification defense.
                sat.enable_clause_trace();
                // #7410: CHC creates fresh SAT solvers per query (one-shot).
                // Vivification is pure overhead for one-shot solvers since
                // benefits only amortize over many solves.
                sat.set_vivify_enabled(false);
                // #5877 / #6248: CHC SMT creates a fresh SAT solver per query.
                // For BV-heavy queries, inprocessing is pure overhead and
                // conditioning dominates runtime with repeated one-shot passes.
                if prepared.features.has_bv {
                    sat.disable_all_inprocessing();
                }
                for clause in tseitin.all_clauses() {
                    let lits: Vec<z4_sat::Literal> = clause
                        .0
                        .iter()
                        .map(|&lit| z4_sat::Literal::from_dimacs(lit))
                        .collect();
                    sat.add_clause(lits);
                }

                // #5877: Check timeout after Tseitin encoding. Large formulas
                // (BV-to-Int at k>=2) can produce huge CNFs that exceed the budget.
                if let Some(t) = timeout {
                    if start.elapsed() >= t {
                        return Err(SmtResult::Unknown);
                    }
                }

                (
                    tseitin.term_to_var().clone(),
                    tseitin.var_to_term().clone(),
                    tseitin.num_vars(),
                    sat,
                    Some(assumptions),
                    Some(assumption_map),
                )
            } else {
                // Fall back to the legacy "assert root" encoding for non-conjunction queries.
                let term = self.convert_expr(&prepared.normalized);
                if self.conversion_budget_exceeded {
                    return Err(SmtResult::Unknown);
                }
                // #5877: Check timeout after expression conversion.
                if let Some(t) = timeout {
                    if start.elapsed() >= t {
                        return Err(SmtResult::Unknown);
                    }
                }
                let tseitin = Tseitin::new(&self.terms);
                let result = tseitin.transform(term);

                // #5877: Check timeout after Tseitin encoding.
                if let Some(t) = timeout {
                    if start.elapsed() >= t {
                        return Err(SmtResult::Unknown);
                    }
                }

                let mut sat = z4_sat::Solver::new(result.num_vars as usize);
                // #5384: enable clause tracing for UNSAT verification defense.
                sat.enable_clause_trace();
                // #7410: Vivify is pure overhead for one-shot CHC SAT queries.
                sat.set_vivify_enabled(false);
                // #5877 / #6248: CHC SMT builds a fresh SAT solver for each query.
                // For BV-heavy one-shot queries, inprocessing does not amortize
                // across solves and conditioning becomes dominant overhead.
                if prepared.features.has_bv {
                    sat.disable_all_inprocessing();
                }
                for clause in &result.clauses {
                    let lits: Vec<z4_sat::Literal> = clause
                        .0
                        .iter()
                        .map(|&lit| z4_sat::Literal::from_dimacs(lit))
                        .collect();
                    sat.add_clause(lits);
                }

                (
                    result.term_to_var.clone(),
                    result.var_to_term.clone(),
                    result.num_vars,
                    sat,
                    None,
                    None,
                )
            };

        Ok(CnfState {
            term_to_var,
            var_to_term,
            num_vars,
            sat,
            assumptions,
            assumption_map,
            bv_var_offset: 0,
            bv_term_to_bits: HbHashMap::default(),
        })
    }
}
