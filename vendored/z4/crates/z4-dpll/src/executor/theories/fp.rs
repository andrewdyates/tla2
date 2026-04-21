// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! FP (IEEE 754 floating-point) solve pipeline via eager bit-blasting.
//!
//! Routes QF_FP formulas through Tseitin encoding + FP bit-blasting + SAT.
//! The FP solver generates CNF clauses at decomposition time; `check()` is
//! trivially SAT. The real work is linking FP predicate results back to
//! Tseitin variables so the SAT solver sees the FP semantics.

mod bitblast;
mod blocking;
mod support;
#[cfg(test)]
mod tests;
mod to_real;
mod to_real_rewrite;
mod to_real_solve;

use z4_core::{CnfClause, Tseitin};
use z4_fp::FpSolver;
use z4_sat::{SatResult, Solver as SatSolver};

use crate::executor_types::{Result, SolveResult};

use super::super::Executor;

use support::{check_fp_support, FpPredicateResult, FpSupportStatus};
use to_real::offset_cnf_lit;

impl Executor {
    /// Solve QF_FP (quantifier-free IEEE 754 floating-point) using eager bit-blasting.
    ///
    /// Pipeline:
    /// 1. Tseitin encode assertions into CNF
    /// 2. Walk Tseitin terms for FP predicates, bitblast each via `FpSolver`
    /// 3. Link FP predicate results to Tseitin variables
    /// 4. Feed combined CNF to SAT solver
    pub(in crate::executor) fn solve_fp(&mut self) -> Result<SolveResult> {
        // --- Guard: check for unsupported FP operations ---
        // Supported with full bit-blasting (#3586):
        //   fp.add, fp.sub, fp.mul, fp.div, fp.sqrt, fp.fma, fp.roundToIntegral,
        //   fp.rem (Float16/Float32 only), to_fp (constant or variable BV/FP args),
        //   to_fp_unsigned (constant or variable BV args), fp.to_ubv, fp.to_sbv
        // fp.to_real: handled via two-phase solve (FP bit-blast + model eval)
        // Other unsupported ops: returns Unknown
        match check_fp_support(&self.ctx.terms, &self.ctx.assertions) {
            FpSupportStatus::Unsupported => return Ok(SolveResult::Unknown),
            FpSupportStatus::OnlyToReal => return self.solve_fp_to_real(),
            FpSupportStatus::FullySupported => {}
        }

        // --- Phase 1: Tseitin transformation ---
        let mut tseitin = Tseitin::new(&self.ctx.terms);
        for &assertion in &self.ctx.assertions {
            tseitin.assert_term(assertion);
        }
        let tseitin_result = z4_core::TseitinResult::new(
            tseitin.all_clauses().to_vec(),
            tseitin.term_to_var().clone(),
            tseitin.var_to_term().clone(),
            0,
            tseitin.num_vars(),
        );

        // --- Phase 2: FP bit-blasting ---
        let mut fp_solver = FpSolver::new_with_tseitin(&self.ctx.terms, tseitin.term_to_var());

        // Walk Tseitin-encoded terms for FP predicates. Each FP predicate
        // (fp.eq, fp.lt, fp.isNaN, etc.) gets a Tseitin variable that must
        // be linked to the FP bit-blast result.
        let mut linking_pairs: Vec<(i32, i32)> = Vec::new();
        for (&tseitin_var, &term) in &tseitin_result.var_to_term {
            match self.bitblast_fp_predicate(&mut fp_solver, term) {
                FpPredicateResult::Bitblasted(fp_lit) => {
                    linking_pairs.push((tseitin_var as i32, fp_lit));
                }
                FpPredicateResult::NotFpPredicate => {}
                FpPredicateResult::Unsupported => {
                    // Unrecognized FP predicate — return Unknown rather than
                    // leaving the Tseitin variable free (false-SAT risk, #6189).
                    return Ok(SolveResult::Unknown);
                }
            }
        }

        // Check for encoding gaps: ITE conditions that couldn't be resolved
        // as FP predicates or linked via Tseitin map. An unconstrained condition
        // variable would make the SAT result unsound (false-SAT risk).
        if fp_solver.has_encoding_gap() {
            tracing::warn!("FP encoding has unresolvable ITE condition — returning Unknown");
            return Ok(SolveResult::Unknown);
        }

        let fp_clauses = fp_solver.take_clauses();
        let condition_links = fp_solver.take_pending_condition_links();
        let fp_num_vars = fp_solver.num_vars();
        let var_offset = tseitin_result.num_vars as i32;

        // --- Phase 3: Combine Tseitin + FP clauses ---
        let mut all_clauses = tseitin_result.clauses.clone();

        // Add FP clauses with variable offset
        for clause in fp_clauses {
            let offset_lits: Vec<i32> = clause
                .literals()
                .iter()
                .map(|&lit| offset_cnf_lit(lit, var_offset))
                .collect();
            all_clauses.push(CnfClause::new(offset_lits));
        }

        // Add linking clauses (bidirectional equivalence)
        for (tseitin_lit, fp_lit) in linking_pairs {
            let fp_lit_offset = offset_cnf_lit(fp_lit, var_offset);
            all_clauses.push(CnfClause::binary(-tseitin_lit, fp_lit_offset));
            all_clauses.push(CnfClause::binary(tseitin_lit, -fp_lit_offset));
        }

        // Add ITE condition linking clauses (#3586): connect FP proxy variables
        // allocated by encode_bool_condition to their Tseitin counterparts.
        for (fp_var, tseitin_var) in condition_links {
            let fp_lit_offset = offset_cnf_lit(fp_var as i32, var_offset);
            let tseitin_lit = tseitin_var as i32;
            all_clauses.push(CnfClause::binary(-tseitin_lit, fp_lit_offset));
            all_clauses.push(CnfClause::binary(tseitin_lit, -fp_lit_offset));
        }

        let total_vars = tseitin_result.num_vars + fp_num_vars;

        // --- Phase 4: SAT solving ---
        let mut solver = SatSolver::new(total_vars as usize);
        self.apply_random_seed_to_sat(&mut solver);
        self.apply_progress_to_sat(&mut solver);
        solver.set_congruence_enabled(false);
        // Adaptive reorder gate for large FP instances (#8118).
        if total_vars as usize > 50_000 {
            solver.set_reorder_enabled(false);
        }
        if let Some(seed) = self.random_seed {
            solver.set_random_seed(seed);
        }

        for clause in &all_clauses {
            let lits: Vec<z4_sat::Literal> = clause
                .literals()
                .iter()
                .map(|&lit| crate::cnf_lit_to_sat(lit))
                .collect();
            solver.add_clause(lits);
        }

        let should_stop = self.make_should_stop();
        let result = solver.solve_interruptible(should_stop).into_inner();

        collect_sat_stats!(self, &solver);

        // Extract FP and BV models from SAT assignment before storing
        let (fp_model, bv_model) = if let SatResult::Sat(ref sat_model) = result {
            let term_to_fp = fp_solver.term_to_fp().clone();
            let fp = Self::extract_fp_model_from_bits(
                sat_model,
                &term_to_fp,
                var_offset,
                &self.ctx.terms,
            );
            // Extract BV model from FP solver's cached BV term bits (#3586).
            // This enables model validation for QF_BVFP formulas where BV
            // variables participate in to_fp/to_fp_unsigned conversions.
            let bv_term_bits = fp_solver.bv_term_bits();
            let bv = if bv_term_bits.is_empty() {
                None
            } else {
                Some(Self::extract_bv_model_from_fp_bits(
                    sat_model,
                    bv_term_bits,
                    var_offset,
                    &self.ctx.terms,
                ))
            };
            (Some(fp), bv)
        } else {
            (None, None)
        };

        self.solve_and_store_model_full(
            result,
            &tseitin_result,
            None,
            None,
            None,
            None,
            bv_model,
            fp_model,
            None,
            None,
        )
    }

    /// Solve QF_BVFP (bitvectors + floating-point).
    ///
    /// For the initial wiring, routes through the FP solver. Pure BV terms
    /// are handled as uninterpreted by the Tseitin encoding. A full BV+FP
    /// integration (shared variable namespace) is a follow-up.
    pub(in crate::executor) fn solve_bvfp(&mut self) -> Result<SolveResult> {
        self.solve_fp()
    }
}
