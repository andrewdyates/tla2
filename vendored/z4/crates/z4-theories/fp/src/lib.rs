// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![forbid(unsafe_code)]

//! Z4 FP - IEEE 754 Floating-point theory solver
//!
//! Implements the SMT-LIB FloatingPoint theory via bit-blasting to bitvectors.
//! The solver handles all IEEE 754-2008 operations including:
//!
//! - Standard precisions: Float16, Float32, Float64, Float128
//! - Special values: +0, -0, +infinity, -infinity, NaN
//! - Rounding modes: RNE, RNA, RTP, RTN, RTZ
//! - Classification: isNaN, isInfinite, isZero, isNormal, isSubnormal
//! - Comparisons: fp.eq, fp.lt, fp.leq, fp.gt, fp.geq
//! - Arithmetic: fp.add, fp.sub, fp.mul, fp.div, fp.sqrt, fp.fma
//!
//! ## IEEE 754 Bit Layout
//!
//! ```text
//! | sign (1 bit) | exponent (eb bits) | significand (sb-1 bits) |
//! ```
//!
//! Where `eb` = exponent bits, `sb` = significand bits (including hidden bit).
//!
//! ## Example
//!
//! ```text
//! use z4_fp::{FpSolver, RoundingMode, FpPrecision};
//!
//! let solver = FpSolver::new(&terms);
//! // Float32: 8 exponent bits, 24 significand bits (23 stored + 1 hidden)
//! let fp32 = FpPrecision::Float32;
//! ```

#![warn(missing_docs)]
#![warn(clippy::all)]

mod arithmetic_advanced;
mod arithmetic_core;
mod bitblast;
mod bv_circuits;
mod constructors;
mod conversion;
mod decompose;
mod fma;
mod gates;
mod integral;
mod model_value;
mod model_value_convert;
mod rounding;
mod special_ops;
mod standalone;
mod theory_impl;

#[cfg(test)]
mod tests_basic;
#[cfg(test)]
mod tests_fp16_ops;
#[cfg(test)]
mod tests_model_value;
#[cfg(test)]
mod tests_rounding_decision;
#[cfg(test)]
mod tests_support;
#[cfg(kani)]
mod verification;

pub use model_value::FpModelValue;
pub use standalone::FpSolverStandalone;

#[cfg(not(kani))]
use hashbrown::HashMap;
use std::collections::BTreeMap;
#[cfg(kani)]
use z4_core::kani_compat::DetHashMap as HashMap;
use z4_core::term::{TermId, TermStore};
use z4_core::{CnfClause, CnfLit};

/// IEEE 754 rounding modes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum RoundingMode {
    /// Round to nearest, ties to even (default).
    #[default]
    RNE,
    /// Round to nearest, ties away from zero.
    RNA,
    /// Round toward positive infinity.
    RTP,
    /// Round toward negative infinity.
    RTN,
    /// Round toward zero.
    RTZ,
}

impl RoundingMode {
    /// Get rounding mode from SMT-LIB name.
    pub fn from_name(name: &str) -> Option<Self> {
        match name {
            "RNE" | "roundNearestTiesToEven" => Some(Self::RNE),
            "RNA" | "roundNearestTiesToAway" => Some(Self::RNA),
            "RTP" | "roundTowardPositive" => Some(Self::RTP),
            "RTN" | "roundTowardNegative" => Some(Self::RTN),
            "RTZ" | "roundTowardZero" => Some(Self::RTZ),
            _ => None,
        }
    }

    /// Get SMT-LIB name.
    pub fn name(&self) -> &'static str {
        match self {
            Self::RNE => "RNE",
            Self::RNA => "RNA",
            Self::RTP => "RTP",
            Self::RTN => "RTN",
            Self::RTZ => "RTZ",
        }
    }
}

/// Standard IEEE 754 precisions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FpPrecision {
    /// IEEE 754 binary16: 5 exponent bits, 11 significand bits.
    Float16,
    /// IEEE 754 binary32: 8 exponent bits, 24 significand bits.
    Float32,
    /// IEEE 754 binary64: 11 exponent bits, 53 significand bits.
    Float64,
    /// IEEE 754 binary128: 15 exponent bits, 113 significand bits.
    Float128,
    /// Custom precision.
    Custom {
        /// Number of exponent bits.
        eb: u32,
        /// Number of significand bits (including hidden bit).
        sb: u32,
    },
}

impl FpPrecision {
    /// Get exponent bits.
    pub fn exponent_bits(&self) -> u32 {
        match self {
            Self::Float16 => 5,
            Self::Float32 => 8,
            Self::Float64 => 11,
            Self::Float128 => 15,
            Self::Custom { eb, .. } => *eb,
        }
    }

    /// Get significand bits (including hidden bit).
    pub fn significand_bits(&self) -> u32 {
        match self {
            Self::Float16 => 11,
            Self::Float32 => 24,
            Self::Float64 => 53,
            Self::Float128 => 113,
            Self::Custom { sb, .. } => *sb,
        }
    }

    /// Get total bit width (1 sign + eb exponent + sb-1 stored significand).
    pub fn total_bits(&self) -> u32 {
        1 + self.exponent_bits() + self.significand_bits() - 1
    }

    /// Get bias for exponent (`2^(eb-1) - 1`).
    pub fn bias(&self) -> u32 {
        (1 << (self.exponent_bits() - 1)) - 1
    }

    /// Get max exponent value (`all 1s = 2^eb - 1`).
    pub fn max_exponent(&self) -> u32 {
        (1 << self.exponent_bits()) - 1
    }

    /// Create from exponent and significand bit counts.
    pub fn from_eb_sb(eb: u32, sb: u32) -> Self {
        match (eb, sb) {
            (5, 11) => Self::Float16,
            (8, 24) => Self::Float32,
            (11, 53) => Self::Float64,
            (15, 113) => Self::Float128,
            _ => Self::Custom { eb, sb },
        }
    }
}

/// A floating-point value decomposed into sign, exponent, and significand.
#[derive(Debug, Clone)]
pub struct FpDecomposed {
    /// Sign bit (0 = positive, 1 = negative).
    pub sign: CnfLit,
    /// Exponent bits (biased representation).
    pub exponent: Vec<CnfLit>,
    /// Significand bits (stored part, without hidden bit).
    pub significand: Vec<CnfLit>,
    /// Precision of this FP value.
    pub precision: FpPrecision,
}

impl FpDecomposed {
    /// Total bits for this decomposed value.
    pub fn total_bits(&self) -> usize {
        1 + self.exponent.len() + self.significand.len()
    }
}

/// Model extracted from FP solver with variable assignments.
#[derive(Debug, Clone)]
pub struct FpModel {
    /// Variable assignments: `term_id -> concrete FP value`.
    pub values: HashMap<TermId, FpModelValue>,
}

/// Floating-point theory solver using bit-blasting.
pub struct FpSolver<'a> {
    /// Reference to the term store.
    terms: &'a TermStore,
    /// Mapping from FP term IDs to their decomposed representations.
    term_to_fp: HashMap<TermId, FpDecomposed>,
    /// Cache of BV term -> CNF bit vectors.
    bv_term_bits: HashMap<TermId, Vec<CnfLit>>,
    /// Generated CNF clauses.
    clauses: Vec<CnfClause>,
    /// Next fresh variable (1-indexed for DIMACS compatibility).
    next_var: u32,
    /// Per-theory runtime statistics (#4706).
    check_count: u64,
    /// Per-theory runtime statistics (#4706).
    conflict_count: u64,
    /// Per-theory runtime statistics (#4706).
    propagation_count: u64,
    /// Cached `Z4_DEBUG_FP` / `Z4_DEBUG_THEORY` env-var flag (#4706).
    debug: bool,
    /// Cached canonical false literal.
    cached_false: Option<CnfLit>,
    /// Cached canonical true literal.
    cached_true: Option<CnfLit>,
    /// Tseitin term-to-variable mapping (optional).
    term_to_cnf: Option<BTreeMap<TermId, u32>>,
    /// Pending condition links for ITE conditions that need Tseitin linking.
    pending_condition_links: Vec<(u32, u32)>,
    /// True when an FP-sorted ITE condition could not be resolved.
    has_encoding_gap: bool,
}

impl<'a> FpSolver<'a> {
    /// Create a new FP solver.
    #[must_use]
    pub fn new(terms: &'a TermStore) -> Self {
        Self {
            terms,
            term_to_fp: HashMap::new(),
            bv_term_bits: HashMap::new(),
            clauses: Vec::new(),
            next_var: 1,
            check_count: 0,
            conflict_count: 0,
            propagation_count: 0,
            debug: std::env::var("Z4_DEBUG_FP").is_ok() || std::env::var("Z4_DEBUG_THEORY").is_ok(),
            cached_false: None,
            cached_true: None,
            term_to_cnf: None,
            pending_condition_links: Vec::new(),
            has_encoding_gap: false,
        }
    }

    /// Create a new FP solver with Tseitin term-to-variable mapping.
    #[must_use]
    pub fn new_with_tseitin(terms: &'a TermStore, tseitin: &BTreeMap<TermId, u32>) -> Self {
        Self {
            terms,
            term_to_fp: HashMap::new(),
            bv_term_bits: HashMap::new(),
            clauses: Vec::new(),
            next_var: 1,
            check_count: 0,
            conflict_count: 0,
            propagation_count: 0,
            debug: std::env::var("Z4_DEBUG_FP").is_ok() || std::env::var("Z4_DEBUG_THEORY").is_ok(),
            cached_false: None,
            cached_true: None,
            term_to_cnf: Some(tseitin.clone()),
            pending_condition_links: Vec::new(),
            has_encoding_gap: false,
        }
    }

    /// Returns true if the encoding encountered an unresolvable ITE condition.
    pub fn has_encoding_gap(&self) -> bool {
        self.has_encoding_gap
    }

    /// Get the generated CNF clauses.
    pub fn clauses(&self) -> &[CnfClause] {
        &self.clauses
    }

    /// Take ownership of the generated CNF clauses.
    pub fn take_clauses(&mut self) -> Vec<CnfClause> {
        std::mem::take(&mut self.clauses)
    }

    /// Take pending condition links for ITE conditions that need Tseitin linking.
    pub fn take_pending_condition_links(&mut self) -> Vec<(u32, u32)> {
        std::mem::take(&mut self.pending_condition_links)
    }

    /// Get the number of variables used.
    pub fn num_vars(&self) -> u32 {
        self.next_var - 1
    }

    /// Get the mapping from term IDs to decomposed FP representations.
    pub fn term_to_fp(&self) -> &HashMap<TermId, FpDecomposed> {
        &self.term_to_fp
    }

    /// Allocate a fresh CNF variable.
    pub(crate) fn fresh_var(&mut self) -> CnfLit {
        let var = self.next_var as CnfLit;
        self.next_var += 1;
        var
    }

    /// Add a clause.
    pub(crate) fn add_clause(&mut self, clause: CnfClause) {
        self.clauses.push(clause);
    }

    /// Allocate a fresh decomposed FP value with unconstrained bits.
    pub(crate) fn fresh_decomposed(&mut self, precision: FpPrecision) -> FpDecomposed {
        let eb = precision.exponent_bits();
        let sb = precision.significand_bits();
        FpDecomposed {
            sign: self.fresh_var(),
            exponent: (0..eb).map(|_| self.fresh_var()).collect(),
            significand: (0..(sb - 1)).map(|_| self.fresh_var()).collect(),
            precision,
        }
    }

    /// Constrain a decomposed FP to a constant bit pattern.
    pub(crate) fn constrain_constant(
        &mut self,
        fp: &FpDecomposed,
        sign_val: bool,
        exp_bit: impl Fn(u32) -> bool,
        sig_bit: impl Fn(u32) -> bool,
    ) {
        let sign_lit = if sign_val { fp.sign } else { -fp.sign };
        self.add_clause(CnfClause::unit(sign_lit));

        for (i, &bit) in fp.exponent.iter().enumerate() {
            let lit = if exp_bit(i as u32) { bit } else { -bit };
            self.add_clause(CnfClause::unit(lit));
        }

        for (i, &bit) in fp.significand.iter().enumerate() {
            let lit = if sig_bit(i as u32) { bit } else { -bit };
            self.add_clause(CnfClause::unit(lit));
        }
    }

    /// Constrain result exponent/significand for NaN/Inf special cases.
    pub(crate) fn constrain_nan_inf(
        &mut self,
        result: &FpDecomposed,
        result_nan: CnfLit,
        result_inf: CnfLit,
    ) -> CnfLit {
        let special = self.make_or(result_nan, result_inf);
        for &exp in &result.exponent {
            self.add_clause(CnfClause::new(vec![-special, exp]));
        }
        let sig_len = result.significand.len();
        for (i, &sig_bit) in result.significand.iter().enumerate() {
            self.add_clause(CnfClause::new(vec![-result_inf, -sig_bit]));
            if i == sig_len - 1 {
                self.add_clause(CnfClause::new(vec![-result_nan, sig_bit]));
            }
        }
        special
    }
}
