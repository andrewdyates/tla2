// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Theory-specific solving routines.
//!
//! This module contains the `solve_*` implementations that power `check-sat` for
//! each supported logic/theory combination.
//!
//! Split into sub-modules by theory family:
//! - `propositional`: Pure SAT
//! - `euf`: EUF, DT, ArrayEUF
//! - `lra`: LRA (pure real arithmetic)
//! - `lia`: LIA, NIA (pure integer arithmetic)
//! - `combined`: UF+LRA, AUFLIA, AUFLRA, LIRA, AUFLIRA (combined theories)
//! - `bv`: BV, ABV, UFBV, AUFBV solve pipelines
//! - `bv_config`: BvSolveConfig parameterization for BV logic variants
//! - `bv_model`: BV model extraction from SAT assignments
//! - `bv_eval`: BV expression evaluation for model recovery
//! - `bv_axioms_array`: Array read-over-write axiom generation for QF_ABV/QF_AUFBV
//! - `bv_axioms_euf`: EUF congruence axiom generation for QF_UFBV/QF_AUFBV
//! - `lia_eval`: LIA model evaluation and recovery helpers
//! - `solve_harness_helpers`: Free helpers for assertion flattening and source tracking
//! - `model_helpers`: Model storage and proof building

pub(in crate::executor) mod bv;
mod bv_axioms_array;
mod bv_axioms_euf;
mod bv_axioms_non_bv;
mod bv_config;
mod bv_encoding;
mod bv_eval;
mod bv_eval_bool;
mod bv_incremental;
mod bv_model;
mod combined;
mod euf;
mod incremental_scope;
pub(crate) use euf::reachable_term_set;
mod fp;
mod fp_model;
mod lia;
mod lia_eval;
mod lra;
mod model_helpers;
mod nra;
mod propositional;
mod seq;
mod skolem_cache;
pub(in crate::executor) mod solve_harness;
mod solve_harness_helpers;
pub(in crate::executor) mod split_incremental;
mod strings;
mod strings_analysis;
mod strings_eval;
mod strings_lemma;
mod strings_lia;
mod strings_preregister;

pub(crate) use split_incremental::BoundRefinementReplayKey;

use z4_core::term::{Symbol, TermData};
use z4_core::{Sort, TermId, TermStore};
use z4_sat::{Solver as SatSolver, Variable as SatVariable};

/// Result of array axiom generation for QF_ABV
pub(in crate::executor) struct ArrayAxiomResult {
    /// Generated CNF clauses
    pub(in crate::executor) clauses: Vec<z4_core::CnfClause>,
    /// Number of additional variables used
    pub(in crate::executor) num_vars: u32,
}

/// Result of EUF congruence axiom generation for QF_UFBV/QF_AUFBV
pub(in crate::executor) struct EufAxiomResult {
    /// Generated CNF clauses
    pub(in crate::executor) clauses: Vec<z4_core::CnfClause>,
    /// Number of additional variables used
    pub(in crate::executor) num_vars: u32,
}

/// Maximum branch-and-bound split iterations for pure integer arithmetic solvers.
///
/// QF_LIA is decidable, so we keep this high to reduce spurious `Unknown`
/// results on hard-but-finite problems (#2472/#2475).
pub(in crate::executor) const MAX_SPLITS_LIA: usize = 1_000_000;

/// Maximum branch-and-bound split iterations for mixed Int/Real solvers.
///
/// Mixed arithmetic can still require conservative guards to avoid runaway
/// split growth in combined-theory paths.
pub(in crate::executor) const MAX_SPLITS_MIXED: usize = 100_000;

/// Maximum disequality split iterations for pure real arithmetic (QF_LRA).
///
/// LRA only needs splits for disequalities (`x != c` → `x < c OR x > c`).
/// This is typically much smaller than LIA branch-and-bound.
pub(in crate::executor) const MAX_SPLITS_LRA: usize = 100_000;

/// Threshold for detecting unbounded variables in integer arithmetic.
/// Variables with absolute value exceeding this are considered potentially unbounded.
pub(in crate::executor) const UNBOUNDED_THRESHOLD: i32 = 20;

/// Maximum string lemma iterations for QF_S/QF_SLIA solving.
///
/// Each iteration adds one split lemma clause from the string theory solver.
/// CVC5 typically converges in <100 iterations even on complex benchmarks.
pub(in crate::executor) const MAX_STRING_LEMMA_ITERATIONS: usize = 10_000;

cached_env_flag!(pub(in crate::executor::theories) debug_auflia_enabled, "Z4_DEBUG_AUFLIA");
cached_env_flag!(pub(in crate::executor::theories) debug_ite_conditions_enabled, "Z4_DEBUG_ITE_CONDITIONS");
cached_env_flag!(pub(in crate::executor::theories) debug_linking_enabled, "Z4_DEBUG_LINKING");
cached_env_flag!(pub(in crate::executor::theories) debug_preprocessed_enabled, "Z4_DEBUG_PREPROCESSED");

/// Freeze a SAT variable exactly once.
///
/// Incremental DPLL(T) reuses SAT instances across many check-sat calls. Theory-facing
/// variables (assertion roots, active atoms, split atoms) must remain available for
/// future clauses and model synchronization, so they must not be eliminated by BVE.
#[inline]
pub(in crate::executor::theories) fn freeze_var_if_needed(
    solver: &mut SatSolver,
    var: SatVariable,
) {
    if !solver.is_frozen(var) {
        solver.freeze(var);
    }
}

pub(in crate::executor) fn parse_expression_split_disequality(
    terms: &TermStore,
    disequality_term: TermId,
) -> Option<(TermId, TermId, bool)> {
    match terms.get(disequality_term) {
        TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2 => {
            Some((args[0], args[1], false))
        }
        TermData::App(Symbol::Named(name), args) if name == "distinct" && args.len() == 2 => {
            Some((args[0], args[1], true))
        }
        TermData::Not(inner) => match terms.get(*inner) {
            TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2 => {
                // `distinct` is often normalized to `not (= ...)`, so treat `not` like `distinct`
                // for conditional split encoding: `~term OR ...`.
                Some((args[0], args[1], true))
            }
            _ => None,
        },
        _ => None,
    }
}

pub(in crate::executor) fn create_expression_split_atoms(
    terms: &mut TermStore,
    disequality_term: TermId,
) -> Option<(TermId, TermId, bool)> {
    let (lhs, rhs, is_distinct) = parse_expression_split_disequality(terms, disequality_term)?;
    if terms.sort(lhs) != terms.sort(rhs) {
        return None;
    }

    match terms.sort(lhs) {
        Sort::Real => {
            let lt_atom = terms.mk_lt(lhs, rhs);
            let gt_atom = terms.mk_gt(lhs, rhs);
            Some((lt_atom, gt_atom, is_distinct))
        }
        Sort::Int => {
            // For integers, use non-strict inequalities with adjusted bounds
            // to avoid fractional solutions in the LRA relaxation.
            // E != F becomes: E <= F-1 OR E >= F+1.
            let neg_one = terms.mk_int(num_bigint::BigInt::from(-1));
            let pos_one = terms.mk_int(num_bigint::BigInt::from(1));
            let rhs_minus_one = terms.mk_add(vec![rhs, neg_one]);
            let rhs_plus_one = terms.mk_add(vec![rhs, pos_one]);
            let le_atom = terms.mk_le(lhs, rhs_minus_one);
            let ge_atom = terms.mk_ge(lhs, rhs_plus_one);
            Some((le_atom, ge_atom, is_distinct))
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests;
