// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Floating-point conversion and arithmetic operations.
//!
//! FP-to-BV, BV-to-FP, FP-to-Real, FP precision conversion, and rounded
//! arithmetic (add, sub, mul, div, sqrt, fma, rem, roundToIntegral).
//! Predicate and comparison operations are in `floating_point.rs`.

use super::types::{SolverError, Term};
use super::Solver;
use z4_core::{BitVecSort, Sort, Symbol};

impl Solver {
    // --- FP conversions ---

    /// Convert FP to signed bitvector: ((_ fp.to_sbv w) rm x).
    /// Panics if `x` is not a FloatingPoint sort.
    #[deprecated(note = "use try_fp_to_sbv() which returns Result instead of panicking")]
    pub fn fp_to_sbv(&mut self, rm: Term, x: Term, width: u32) -> Term {
        self.try_fp_to_sbv(rm, x, width)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to convert FP to signed bitvector (fallible).
    ///
    /// Returns [`SolverError::SortMismatch`] if `x` is not a FloatingPoint sort.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_to_sbv(&mut self, rm: Term, x: Term, width: u32) -> Result<Term, SolverError> {
        self.expect_fp("fp.to_sbv", x)?;
        let sort = Sort::BitVec(BitVecSort { width });
        Ok(Term(self.terms_mut().mk_app(
            Symbol::indexed("fp.to_sbv", vec![width]),
            vec![rm.0, x.0],
            sort,
        )))
    }

    /// Convert FP to unsigned bitvector: ((_ fp.to_ubv w) rm x).
    /// Panics if `x` is not a FloatingPoint sort.
    #[deprecated(note = "use try_fp_to_ubv() which returns Result instead of panicking")]
    pub fn fp_to_ubv(&mut self, rm: Term, x: Term, width: u32) -> Term {
        self.try_fp_to_ubv(rm, x, width)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to convert FP to unsigned bitvector (fallible).
    ///
    /// Returns [`SolverError::SortMismatch`] if `x` is not a FloatingPoint sort.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_to_ubv(&mut self, rm: Term, x: Term, width: u32) -> Result<Term, SolverError> {
        self.expect_fp("fp.to_ubv", x)?;
        let sort = Sort::BitVec(BitVecSort { width });
        Ok(Term(self.terms_mut().mk_app(
            Symbol::indexed("fp.to_ubv", vec![width]),
            vec![rm.0, x.0],
            sort,
        )))
    }

    /// Convert FP to real: (fp.to_real x).
    /// Panics if `x` is not a FloatingPoint sort.
    #[deprecated(note = "use try_fp_to_real() which returns Result instead of panicking")]
    pub fn fp_to_real(&mut self, x: Term) -> Term {
        self.try_fp_to_real(x).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to convert FP to real (fallible).
    ///
    /// Returns [`SolverError::SortMismatch`] if `x` is not a FloatingPoint sort.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_to_real(&mut self, x: Term) -> Result<Term, SolverError> {
        self.expect_fp("fp.to_real", x)?;
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("fp.to_real"),
            vec![x.0],
            Sort::Real,
        )))
    }

    /// Convert FP to IEEE 754 bitvector (bit-pattern reinterpretation): (fp.to_ieee_bv x).
    ///
    /// Returns [`SolverError::SortMismatch`] if `x` is not a FloatingPoint sort.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_to_ieee_bv(&mut self, x: Term) -> Result<Term, SolverError> {
        let (eb, sb) = self.expect_fp("fp.to_ieee_bv", x)?;
        let sort = Sort::BitVec(BitVecSort { width: eb + sb });
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("fp.to_ieee_bv"),
            vec![x.0],
            sort,
        )))
    }

    /// Construct FP from sign, exponent, significand bitvectors: (fp sign exp sig).
    /// Panics if `sign`, `exp`, or `sig` are not bitvector sorts.
    #[deprecated(note = "use try_fp_from_bvs() which returns Result instead of panicking")]
    pub fn fp_from_bvs(&mut self, sign: Term, exp: Term, sig: Term, eb: u32, sb: u32) -> Term {
        self.try_fp_from_bvs(sign, exp, sig, eb, sb)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to construct FP from sign, exponent, significand bitvectors (fallible).
    ///
    /// Returns [`SolverError::SortMismatch`] if any argument is not a bitvector sort.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_from_bvs(
        &mut self,
        sign: Term,
        exp: Term,
        sig: Term,
        eb: u32,
        sb: u32,
    ) -> Result<Term, SolverError> {
        self.expect_bitvec("fp (sign)", sign)?;
        self.expect_bitvec("fp (exponent)", exp)?;
        self.expect_bitvec("fp (significand)", sig)?;
        let sort = Sort::FloatingPoint(eb, sb);
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("fp"),
            vec![sign.0, exp.0, sig.0],
            sort,
        )))
    }

    /// Convert bitvector to FP (interpret as IEEE 754): ((_ to_fp eb sb) rm bv).
    /// Panics if `bv` is not a bitvector sort.
    #[deprecated(note = "use try_bv_to_fp() which returns Result instead of panicking")]
    pub fn bv_to_fp(&mut self, rm: Term, bv: Term, eb: u32, sb: u32) -> Term {
        self.try_bv_to_fp(rm, bv, eb, sb)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to convert bitvector to FP (fallible).
    ///
    /// Returns [`SolverError::SortMismatch`] if `bv` is not a bitvector sort.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_bv_to_fp(
        &mut self,
        rm: Term,
        bv: Term,
        eb: u32,
        sb: u32,
    ) -> Result<Term, SolverError> {
        self.expect_bitvec("to_fp", bv)?;
        let sort = Sort::FloatingPoint(eb, sb);
        Ok(Term(self.terms_mut().mk_app(
            Symbol::indexed("to_fp", vec![eb, sb]),
            vec![rm.0, bv.0],
            sort,
        )))
    }

    /// Convert unsigned bitvector to FP: ((_ to_fp_unsigned eb sb) rm bv).
    /// Panics if `bv` is not a bitvector sort.
    #[deprecated(note = "use try_bv_to_fp_unsigned() which returns Result instead of panicking")]
    pub fn bv_to_fp_unsigned(&mut self, rm: Term, bv: Term, eb: u32, sb: u32) -> Term {
        self.try_bv_to_fp_unsigned(rm, bv, eb, sb)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to convert unsigned bitvector to FP (fallible).
    ///
    /// Returns [`SolverError::SortMismatch`] if `bv` is not a bitvector sort.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_bv_to_fp_unsigned(
        &mut self,
        rm: Term,
        bv: Term,
        eb: u32,
        sb: u32,
    ) -> Result<Term, SolverError> {
        self.expect_bitvec("to_fp_unsigned", bv)?;
        let sort = Sort::FloatingPoint(eb, sb);
        Ok(Term(self.terms_mut().mk_app(
            Symbol::indexed("to_fp_unsigned", vec![eb, sb]),
            vec![rm.0, bv.0],
            sort,
        )))
    }

    /// Convert FP to different precision: ((_ to_fp eb sb) rm fp).
    /// Panics if `fp` is not a FloatingPoint sort.
    #[deprecated(note = "use try_fp_to_fp() which returns Result instead of panicking")]
    pub fn fp_to_fp(&mut self, rm: Term, fp: Term, eb: u32, sb: u32) -> Term {
        self.try_fp_to_fp(rm, fp, eb, sb)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to convert FP to different precision (fallible).
    ///
    /// Returns [`SolverError::SortMismatch`] if `fp` is not a FloatingPoint sort.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_to_fp(
        &mut self,
        rm: Term,
        fp: Term,
        eb: u32,
        sb: u32,
    ) -> Result<Term, SolverError> {
        self.expect_fp("to_fp (fp)", fp)?;
        let sort = Sort::FloatingPoint(eb, sb);
        Ok(Term(self.terms_mut().mk_app(
            Symbol::indexed("to_fp", vec![eb, sb]),
            vec![rm.0, fp.0],
            sort,
        )))
    }

    // --- FP rounded arithmetic operations ---

    /// Create FP addition with rounding mode: `(fp.add rm a b)`.
    #[deprecated(note = "use try_fp_add() which returns Result instead of panicking")]
    pub fn fp_add(&mut self, rm: Term, a: Term, b: Term) -> Term {
        self.try_fp_add(rm, a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create FP addition with rounding mode (fallible).
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_add(&mut self, rm: Term, a: Term, b: Term) -> Result<Term, SolverError> {
        let (eb, sb) = self.expect_same_fp("fp.add", a, b)?;
        let sort = Sort::FloatingPoint(eb, sb);
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("fp.add"),
            vec![rm.0, a.0, b.0],
            sort,
        )))
    }

    /// Create FP subtraction with rounding mode: `(fp.sub rm a b)`.
    #[deprecated(note = "use try_fp_sub() which returns Result instead of panicking")]
    pub fn fp_sub(&mut self, rm: Term, a: Term, b: Term) -> Term {
        self.try_fp_sub(rm, a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create FP subtraction with rounding mode (fallible).
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_sub(&mut self, rm: Term, a: Term, b: Term) -> Result<Term, SolverError> {
        let (eb, sb) = self.expect_same_fp("fp.sub", a, b)?;
        let sort = Sort::FloatingPoint(eb, sb);
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("fp.sub"),
            vec![rm.0, a.0, b.0],
            sort,
        )))
    }

    /// Create FP multiplication with rounding mode: `(fp.mul rm a b)`.
    #[deprecated(note = "use try_fp_mul() which returns Result instead of panicking")]
    pub fn fp_mul(&mut self, rm: Term, a: Term, b: Term) -> Term {
        self.try_fp_mul(rm, a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create FP multiplication with rounding mode (fallible).
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_mul(&mut self, rm: Term, a: Term, b: Term) -> Result<Term, SolverError> {
        let (eb, sb) = self.expect_same_fp("fp.mul", a, b)?;
        let sort = Sort::FloatingPoint(eb, sb);
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("fp.mul"),
            vec![rm.0, a.0, b.0],
            sort,
        )))
    }

    /// Create FP division with rounding mode: `(fp.div rm a b)`.
    #[deprecated(note = "use try_fp_div() which returns Result instead of panicking")]
    pub fn fp_div(&mut self, rm: Term, a: Term, b: Term) -> Term {
        self.try_fp_div(rm, a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create FP division with rounding mode (fallible).
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_div(&mut self, rm: Term, a: Term, b: Term) -> Result<Term, SolverError> {
        let (eb, sb) = self.expect_same_fp("fp.div", a, b)?;
        let sort = Sort::FloatingPoint(eb, sb);
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("fp.div"),
            vec![rm.0, a.0, b.0],
            sort,
        )))
    }

    /// Create FP square root with rounding mode: `(fp.sqrt rm a)`.
    #[deprecated(note = "use try_fp_sqrt() which returns Result instead of panicking")]
    pub fn fp_sqrt(&mut self, rm: Term, a: Term) -> Term {
        self.try_fp_sqrt(rm, a).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create FP square root with rounding mode (fallible).
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_sqrt(&mut self, rm: Term, a: Term) -> Result<Term, SolverError> {
        let (eb, sb) = self.expect_fp("fp.sqrt", a)?;
        let sort = Sort::FloatingPoint(eb, sb);
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("fp.sqrt"),
            vec![rm.0, a.0],
            sort,
        )))
    }

    /// Create FP fused multiply-add with rounding mode: `(fp.fma rm a b c)`.
    ///
    /// Computes `a * b + c` with a single rounding.
    #[deprecated(note = "use try_fp_fma() which returns Result instead of panicking")]
    pub fn fp_fma(&mut self, rm: Term, a: Term, b: Term, c: Term) -> Term {
        self.try_fp_fma(rm, a, b, c)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create FP fused multiply-add with rounding mode (fallible).
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_fma(&mut self, rm: Term, a: Term, b: Term, c: Term) -> Result<Term, SolverError> {
        let (eb, sb) = self.expect_same_fp("fp.fma", a, b)?;
        let (eb_c, sb_c) = self.expect_fp("fp.fma", c)?;
        if eb != eb_c || sb != sb_c {
            return Err(SolverError::SortMismatch {
                operation: "fp.fma",
                expected: "FloatingPoint (same precision for all operands)",
                got: vec![Sort::FloatingPoint(eb, sb), Sort::FloatingPoint(eb_c, sb_c)],
            });
        }
        let sort = Sort::FloatingPoint(eb, sb);
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("fp.fma"),
            vec![rm.0, a.0, b.0, c.0],
            sort,
        )))
    }

    /// Create FP remainder: `(fp.rem a b)`.
    ///
    /// IEEE 754 remainder (no rounding mode needed).
    #[deprecated(note = "use try_fp_rem() which returns Result instead of panicking")]
    pub fn fp_rem(&mut self, a: Term, b: Term) -> Term {
        self.try_fp_rem(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create FP remainder (fallible).
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_rem(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        let (eb, sb) = self.expect_same_fp("fp.rem", a, b)?;
        let sort = Sort::FloatingPoint(eb, sb);
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("fp.rem"),
            vec![a.0, b.0],
            sort,
        )))
    }

    /// Create FP round-to-integral: `(fp.roundToIntegral rm a)`.
    #[deprecated(note = "use try_fp_round_to_integral() which returns Result instead of panicking")]
    pub fn fp_round_to_integral(&mut self, rm: Term, a: Term) -> Term {
        self.try_fp_round_to_integral(rm, a)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create FP round-to-integral (fallible).
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_round_to_integral(&mut self, rm: Term, a: Term) -> Result<Term, SolverError> {
        let (eb, sb) = self.expect_fp("fp.roundToIntegral", a)?;
        let sort = Sort::FloatingPoint(eb, sb);
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("fp.roundToIntegral"),
            vec![rm.0, a.0],
            sort,
        )))
    }
}
