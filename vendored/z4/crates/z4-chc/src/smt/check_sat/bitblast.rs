// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Eager BV bit-blasting adapter for check_sat queries.
//!
//! Bit-blasts BV predicates into SAT clauses and connects them to the
//! Tseitin encoding produced by the CNF stage. Uses persistent BV
//! caching to avoid redundant work across queries with identical
//! BV structure.

use rustc_hash::FxHashMap;
use z4_core::TermId;

use super::super::context::SmtContext;
use super::support::add_offset_bv_clause;
use super::CnfState;
use crate::expr::ExprFeatures;

#[cfg(test)]
use super::{record_bv_bitblast_for_tests, record_bv_new_clauses_for_tests};

impl SmtContext {
    /// Attach BV bit-blasting to the CNF state if the query has BV operations.
    ///
    /// Modifies `state` in place: grows the SAT solver, adds BV clauses,
    /// and wires Tseitin variables to their BV predicate equivalents.
    pub(super) fn attach_bv_bitblasting(&mut self, features: &ExprFeatures, state: &mut CnfState) {
        if !features.has_bv {
            return;
        }

        use z4_bv::BvSolver;
        #[cfg(test)]
        record_bv_bitblast_for_tests();

        let mut persistent_bv_cache = std::mem::take(&mut self.persistent_bv_cache);
        let mut bv_solver = BvSolver::new(&self.terms);
        let current_terms: Vec<TermId> = state.var_to_term.values().copied().collect();
        let mut bv_key_memo = FxHashMap::default();
        let current_signature =
            self.bv_cache_signature(current_terms.iter().copied(), &mut bv_key_memo);
        let reuse_cached_bv = persistent_bv_cache.signature == current_signature;
        if reuse_cached_bv {
            bv_key_memo =
                self.restore_cached_bv_state(&persistent_bv_cache, &mut bv_solver, current_terms);
        }
        let mut bv_connections: Vec<(u32, i32)> = Vec::new();

        // Check each Tseitin variable's term for BV predicates.
        for (&tseitin_var, &term) in &state.var_to_term {
            if let Some(bv_lit) = bv_solver.bitblast_predicate(term) {
                bv_connections.push((tseitin_var, bv_lit));
            }
        }

        let new_pre_connection_clauses = bv_solver.take_clauses();
        #[cfg(test)]
        record_bv_new_clauses_for_tests(new_pre_connection_clauses.len());

        // #6090: checked conversion — num_vars exceeding i32::MAX cannot
        // be represented in DIMACS literal encoding. Skip BV if overflow.
        if !bv_connections.is_empty() && i32::try_from(state.num_vars).is_ok() {
            let offset = state.num_vars as i32; // safe: checked above
            let bv_total_vars = bv_solver.num_vars();

            // Grow SAT solver to accommodate BV variables.
            state
                .sat
                .ensure_num_vars((state.num_vars + bv_total_vars) as usize);

            // Replay the persistent BV circuit before wiring query-local
            // Tseitin roots. This keeps the fresh SAT solver aligned with
            // any cached BV literals restored into `bv_solver`.
            if reuse_cached_bv {
                for clause in &persistent_bv_cache.clauses {
                    add_offset_bv_clause(&mut state.sat, clause, offset);
                }
            }
            for clause in &new_pre_connection_clauses {
                add_offset_bv_clause(&mut state.sat, clause, offset);
            }

            // Connect Tseitin variables to BV predicate variables.
            // For each BV predicate, tseitin_var ↔ bv_lit (offset).
            for (tseitin_var, bv_lit) in &bv_connections {
                let bv_lit_offset = if *bv_lit > 0 {
                    *bv_lit + offset
                } else {
                    *bv_lit - offset
                };
                let tseitin_lit = *tseitin_var as i32;
                // tseitin_var → bv_lit
                state.sat.add_clause(vec![
                    z4_sat::Literal::from_dimacs(-tseitin_lit),
                    z4_sat::Literal::from_dimacs(bv_lit_offset),
                ]);
                // bv_lit → tseitin_var
                state.sat.add_clause(vec![
                    z4_sat::Literal::from_dimacs(tseitin_lit),
                    z4_sat::Literal::from_dimacs(-bv_lit_offset),
                ]);
            }

            // Clauses may have been generated during connection phase.
            let new_post_connection_clauses = bv_solver.take_clauses();
            #[cfg(test)]
            record_bv_new_clauses_for_tests(new_post_connection_clauses.len());
            for clause in &new_post_connection_clauses {
                add_offset_bv_clause(&mut state.sat, clause, offset);
            }

            self.capture_cached_bv_state(
                &mut persistent_bv_cache,
                &bv_solver,
                current_signature,
                &mut bv_key_memo,
                new_pre_connection_clauses
                    .into_iter()
                    .chain(new_post_connection_clauses)
                    .collect(),
            );

            state.bv_var_offset = offset;
            state.bv_term_to_bits = bv_solver
                .term_to_bits()
                .iter()
                .map(|(&k, v)| (k, v.clone()))
                .collect();
            state.num_vars += bv_total_vars;

            if crate::debug_chc_smt_enabled() {
                safe_eprintln!(
                    "[CHC-SMT] BV bit-blasting: {} connections, {} BV vars, {} total vars, {} cached clauses",
                    bv_connections.len(),
                    bv_total_vars,
                    state.num_vars,
                    persistent_bv_cache.clauses.len(),
                );
            }
        } else {
            self.capture_cached_bv_state(
                &mut persistent_bv_cache,
                &bv_solver,
                current_signature,
                &mut bv_key_memo,
                new_pre_connection_clauses,
            );
        }
        self.persistent_bv_cache = persistent_bv_cache;
    }
}
