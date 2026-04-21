// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! BV bitblasting for incremental SAT contexts.
//!
//! Handles creation and management of BV circuit clauses within the
//! persistent SAT solver, including gate/division cache persistence
//! across incremental calls.

use super::IncrementalSatContext;
use z4_core::TermStore;

impl IncrementalSatContext {
    /// Bit-blast new BV predicates in var_to_term and add clauses to SAT solver.
    ///
    /// Creates a temporary BvSolver with restored state from previous calls, processes
    /// any new BV predicates, and saves the updated state. Uses a fixed BV variable
    /// offset (set on first BV encounter) for consistent variable assignments. (#5122)
    pub(super) fn bitblast_new_bv_predicates(&mut self, terms: &TermStore, global: bool) {
        use z4_bv::BvSolver;

        // Create BvSolver and restore cached state.
        let mut bv = BvSolver::new(terms);
        bv.set_next_var(self.bv_next_var);
        for (&term, bits) in &self.bv_term_to_bits {
            bv.set_term_bits(term, bits.clone());
        }
        bv.set_predicate_to_var(self.bv_predicate_to_var.clone());
        bv.set_bool_to_var(self.bv_bool_to_var.clone());
        // Restore gate and division caches (#5877 Phase 2): prevents redundant gate
        // variables when re-bitblasting shared sub-expressions across incremental calls.
        bv.set_gate_caches(
            self.bv_and_cache.clone(),
            self.bv_or_cache.clone(),
            self.bv_xor_cache.clone(),
        );
        bv.set_div_caches(
            self.bv_unsigned_div_cache.clone(),
            self.bv_signed_div_cache.clone(),
        );

        // Check each var_to_term entry for new BV predicates.
        let mut new_connections: Vec<(u32, i32)> = Vec::new();
        for (&tseitin_var, &term) in &self.var_to_term {
            if self.bv_connected_tseitin_vars.contains(&tseitin_var) {
                continue;
            }
            if let Some(bv_lit) = bv.bitblast_predicate(term) {
                new_connections.push((tseitin_var, bv_lit));
            }
        }

        if new_connections.is_empty() && bv.num_vars() == self.bv_next_var.saturating_sub(1) {
            // No new BV work; skip clause/connection phase.
            return;
        }

        // Set BV offset on first encounter.
        // #6090: checked conversion — skip BV if num_vars exceeds i32 range.
        let offset = match self.bv_var_offset {
            Some(o) => o,
            None => {
                let o = match i32::try_from(self.num_vars) {
                    Ok(o) => o,
                    Err(_) => return, // too many vars for DIMACS encoding
                };
                self.bv_var_offset = Some(o);
                o
            }
        };
        let bv_total_vars = bv.num_vars();

        // Grow SAT solver.
        self.sat
            .ensure_num_vars((offset as u32 + bv_total_vars) as usize);

        // Add BV circuit clauses (with offset).
        let add_clause = |sat: &mut z4_sat::Solver, clause: &z4_core::CnfClause, global: bool| {
            let lits: Vec<z4_sat::Literal> = clause
                .literals()
                .iter()
                .map(|&lit| {
                    let offset_lit = if lit > 0 { lit + offset } else { lit - offset };
                    z4_sat::Literal::from_dimacs(offset_lit)
                })
                .collect();
            if global {
                sat.add_clause_global(lits);
            } else {
                sat.add_clause(lits);
            }
        };

        for clause in bv.take_clauses() {
            add_clause(&mut self.sat, &clause, global);
        }

        // Add connection clauses for new BV predicates.
        // These mix Tseitin literals (no offset) with BV literals (offset),
        // so they CANNOT go through the add_clause closure which offsets all lits.
        for &(tseitin_var, bv_lit) in &new_connections {
            let bv_lit_offset = if bv_lit > 0 {
                bv_lit + offset
            } else {
                bv_lit - offset
            };
            let tseitin_lit = tseitin_var as i32;
            // Equivalence: tseitin_var ↔ bv_lit
            let c1_lits = vec![
                z4_sat::Literal::from_dimacs(-tseitin_lit),
                z4_sat::Literal::from_dimacs(bv_lit_offset),
            ];
            let c2_lits = vec![
                z4_sat::Literal::from_dimacs(tseitin_lit),
                z4_sat::Literal::from_dimacs(-bv_lit_offset),
            ];
            if global {
                self.sat.add_clause_global(c1_lits);
                self.sat.add_clause_global(c2_lits);
            } else {
                self.sat.add_clause(c1_lits);
                self.sat.add_clause(c2_lits);
            }
            self.bv_connected_tseitin_vars.insert(tseitin_var);
        }

        // Clauses generated during connection phase.
        for clause in bv.take_clauses() {
            add_clause(&mut self.sat, &clause, global);
        }

        // Save BV state for future calls.
        self.bv_next_var = bv.num_vars() + 1;
        for (term, bits) in bv.term_to_bits() {
            self.bv_term_to_bits
                .entry(*term)
                .or_insert_with(|| bits.clone());
        }
        for (&term, &lit) in bv.predicate_to_var() {
            self.bv_predicate_to_var.entry(term).or_insert(lit);
        }
        for (&term, &lit) in bv.bool_to_var() {
            self.bv_bool_to_var.entry(term).or_insert(lit);
        }
        // Save gate and division caches (#5877 Phase 2).
        let (and_c, or_c, xor_c) = bv.gate_caches();
        self.bv_and_cache = and_c.clone();
        self.bv_or_cache = or_c.clone();
        self.bv_xor_cache = xor_c.clone();
        let (udiv_c, sdiv_c) = bv.div_caches();
        self.bv_unsigned_div_cache = udiv_c.clone();
        self.bv_signed_div_cache = sdiv_c.clone();
    }
}
