// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Floating-point operations for Z4 Solver API (#5774).
//!
//! FP operations are constructed via `mk_app` with SMT-LIB standard symbol
//! names. The FP theory solver recognizes these symbols and handles them via
//! eager bit-blasting.

use super::types::{SolverError, Term};
use super::Solver;
use z4_core::{Sort, Symbol};

impl Solver {
    // --- Sort helpers ---

    pub(super) fn expect_fp(
        &self,
        operation: &'static str,
        t: Term,
    ) -> Result<(u32, u32), SolverError> {
        let sort = self.terms().sort(t.0).clone();
        match sort {
            Sort::FloatingPoint(eb, sb) => Ok((eb, sb)),
            other => Err(SolverError::SortMismatch {
                operation,
                expected: "FloatingPoint",
                got: vec![other],
            }),
        }
    }

    pub(super) fn expect_same_fp(
        &self,
        operation: &'static str,
        a: Term,
        b: Term,
    ) -> Result<(u32, u32), SolverError> {
        let (eb_a, sb_a) = self.expect_fp(operation, a)?;
        let (eb_b, sb_b) = self.expect_fp(operation, b)?;
        if eb_a != eb_b || sb_a != sb_b {
            return Err(SolverError::SortMismatch {
                operation,
                expected: "FloatingPoint (same precision)",
                got: vec![
                    Sort::FloatingPoint(eb_a, sb_a),
                    Sort::FloatingPoint(eb_b, sb_b),
                ],
            });
        }
        Ok((eb_a, sb_a))
    }

    // --- FP constants ---

    /// Create FP +infinity constant for the given precision.
    #[must_use = "this creates a term that is usually needed for assertions"]
    pub fn fp_plus_infinity(&mut self, eb: u32, sb: u32) -> Term {
        let sort = Sort::FloatingPoint(eb, sb);
        Term(
            self.terms_mut()
                .mk_app(Symbol::indexed("+oo", vec![eb, sb]), vec![], sort),
        )
    }

    /// Create FP -infinity constant for the given precision.
    #[must_use = "this creates a term that is usually needed for assertions"]
    pub fn fp_minus_infinity(&mut self, eb: u32, sb: u32) -> Term {
        let sort = Sort::FloatingPoint(eb, sb);
        Term(
            self.terms_mut()
                .mk_app(Symbol::indexed("-oo", vec![eb, sb]), vec![], sort),
        )
    }

    /// Create FP NaN constant for the given precision.
    #[must_use = "this creates a term that is usually needed for assertions"]
    pub fn fp_nan(&mut self, eb: u32, sb: u32) -> Term {
        let sort = Sort::FloatingPoint(eb, sb);
        Term(
            self.terms_mut()
                .mk_app(Symbol::indexed("NaN", vec![eb, sb]), vec![], sort),
        )
    }

    /// Create FP +zero constant for the given precision.
    #[must_use = "this creates a term that is usually needed for assertions"]
    pub fn fp_plus_zero(&mut self, eb: u32, sb: u32) -> Term {
        let sort = Sort::FloatingPoint(eb, sb);
        Term(
            self.terms_mut()
                .mk_app(Symbol::indexed("+zero", vec![eb, sb]), vec![], sort),
        )
    }

    /// Create FP -zero constant for the given precision.
    #[must_use = "this creates a term that is usually needed for assertions"]
    pub fn fp_minus_zero(&mut self, eb: u32, sb: u32) -> Term {
        let sort = Sort::FloatingPoint(eb, sb);
        Term(
            self.terms_mut()
                .mk_app(Symbol::indexed("-zero", vec![eb, sb]), vec![], sort),
        )
    }

    // --- FP unary operations ---

    /// Create FP absolute value.
    #[deprecated(note = "use try_fp_abs() which returns Result instead of panicking")]
    pub fn fp_abs(&mut self, a: Term) -> Term {
        self.try_fp_abs(a).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create FP absolute value (fallible).
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_abs(&mut self, a: Term) -> Result<Term, SolverError> {
        let (eb, sb) = self.expect_fp("fp.abs", a)?;
        let sort = Sort::FloatingPoint(eb, sb);
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("fp.abs"),
            vec![a.0],
            sort,
        )))
    }

    /// Create FP negation.
    #[deprecated(note = "use try_fp_neg() which returns Result instead of panicking")]
    pub fn fp_neg(&mut self, a: Term) -> Term {
        self.try_fp_neg(a).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create FP negation (fallible).
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_neg(&mut self, a: Term) -> Result<Term, SolverError> {
        let (eb, sb) = self.expect_fp("fp.neg", a)?;
        let sort = Sort::FloatingPoint(eb, sb);
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("fp.neg"),
            vec![a.0],
            sort,
        )))
    }

    // --- FP comparison predicates (return Bool) ---

    /// Create FP IEEE equality.
    #[deprecated(note = "use try_fp_eq() which returns Result instead of panicking")]
    pub fn fp_eq(&mut self, a: Term, b: Term) -> Term {
        self.try_fp_eq(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create FP IEEE equality (fallible).
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_eq(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        self.expect_same_fp("fp.eq", a, b)?;
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("fp.eq"),
            vec![a.0, b.0],
            Sort::Bool,
        )))
    }

    /// Create FP less-than.
    #[deprecated(note = "use try_fp_lt() which returns Result instead of panicking")]
    pub fn fp_lt(&mut self, a: Term, b: Term) -> Term {
        self.try_fp_lt(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create FP less-than (fallible).
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_lt(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        self.expect_same_fp("fp.lt", a, b)?;
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("fp.lt"),
            vec![a.0, b.0],
            Sort::Bool,
        )))
    }

    /// Create FP less-than-or-equal.
    #[deprecated(note = "use try_fp_le() which returns Result instead of panicking")]
    pub fn fp_le(&mut self, a: Term, b: Term) -> Term {
        self.try_fp_le(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create FP less-than-or-equal (fallible).
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_le(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        self.expect_same_fp("fp.leq", a, b)?;
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("fp.leq"),
            vec![a.0, b.0],
            Sort::Bool,
        )))
    }

    /// Create FP greater-than.
    #[deprecated(note = "use try_fp_gt() which returns Result instead of panicking")]
    pub fn fp_gt(&mut self, a: Term, b: Term) -> Term {
        self.try_fp_gt(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create FP greater-than (fallible).
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_gt(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        self.expect_same_fp("fp.gt", a, b)?;
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("fp.gt"),
            vec![a.0, b.0],
            Sort::Bool,
        )))
    }

    /// Create FP greater-than-or-equal.
    #[deprecated(note = "use try_fp_ge() which returns Result instead of panicking")]
    pub fn fp_ge(&mut self, a: Term, b: Term) -> Term {
        self.try_fp_ge(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create FP greater-than-or-equal (fallible).
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_ge(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        self.expect_same_fp("fp.geq", a, b)?;
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("fp.geq"),
            vec![a.0, b.0],
            Sort::Bool,
        )))
    }

    // --- FP classification predicates (return Bool) ---

    /// Create FP isNaN predicate.
    #[deprecated(note = "use try_fp_is_nan() which returns Result instead of panicking")]
    pub fn fp_is_nan(&mut self, a: Term) -> Term {
        self.try_fp_is_nan(a).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create FP isNaN predicate (fallible).
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_is_nan(&mut self, a: Term) -> Result<Term, SolverError> {
        self.expect_fp("fp.isNaN", a)?;
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("fp.isNaN"),
            vec![a.0],
            Sort::Bool,
        )))
    }

    /// Create FP isInfinite predicate.
    #[deprecated(note = "use try_fp_is_infinite() which returns Result instead of panicking")]
    pub fn fp_is_infinite(&mut self, a: Term) -> Term {
        self.try_fp_is_infinite(a).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create FP isInfinite predicate (fallible).
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_is_infinite(&mut self, a: Term) -> Result<Term, SolverError> {
        self.expect_fp("fp.isInfinite", a)?;
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("fp.isInfinite"),
            vec![a.0],
            Sort::Bool,
        )))
    }

    /// Create FP isZero predicate.
    #[deprecated(note = "use try_fp_is_zero() which returns Result instead of panicking")]
    pub fn fp_is_zero(&mut self, a: Term) -> Term {
        self.try_fp_is_zero(a).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create FP isZero predicate (fallible).
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_is_zero(&mut self, a: Term) -> Result<Term, SolverError> {
        self.expect_fp("fp.isZero", a)?;
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("fp.isZero"),
            vec![a.0],
            Sort::Bool,
        )))
    }

    /// Create FP isNormal predicate.
    #[deprecated(note = "use try_fp_is_normal() which returns Result instead of panicking")]
    pub fn fp_is_normal(&mut self, a: Term) -> Term {
        self.try_fp_is_normal(a).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create FP isNormal predicate (fallible).
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_is_normal(&mut self, a: Term) -> Result<Term, SolverError> {
        self.expect_fp("fp.isNormal", a)?;
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("fp.isNormal"),
            vec![a.0],
            Sort::Bool,
        )))
    }

    /// Create FP isSubnormal predicate.
    #[deprecated(note = "use try_fp_is_subnormal() which returns Result instead of panicking")]
    pub fn fp_is_subnormal(&mut self, a: Term) -> Term {
        self.try_fp_is_subnormal(a)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create FP isSubnormal predicate (fallible).
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_is_subnormal(&mut self, a: Term) -> Result<Term, SolverError> {
        self.expect_fp("fp.isSubnormal", a)?;
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("fp.isSubnormal"),
            vec![a.0],
            Sort::Bool,
        )))
    }

    /// Create FP isPositive predicate.
    #[deprecated(note = "use try_fp_is_positive() which returns Result instead of panicking")]
    pub fn fp_is_positive(&mut self, a: Term) -> Term {
        self.try_fp_is_positive(a).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create FP isPositive predicate (fallible).
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_is_positive(&mut self, a: Term) -> Result<Term, SolverError> {
        self.expect_fp("fp.isPositive", a)?;
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("fp.isPositive"),
            vec![a.0],
            Sort::Bool,
        )))
    }

    /// Create FP isNegative predicate.
    #[deprecated(note = "use try_fp_is_negative() which returns Result instead of panicking")]
    pub fn fp_is_negative(&mut self, a: Term) -> Term {
        self.try_fp_is_negative(a).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create FP isNegative predicate (fallible).
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_is_negative(&mut self, a: Term) -> Result<Term, SolverError> {
        self.expect_fp("fp.isNegative", a)?;
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("fp.isNegative"),
            vec![a.0],
            Sort::Bool,
        )))
    }

    // --- FP min/max ---

    /// Create FP minimum.
    #[deprecated(note = "use try_fp_min() which returns Result instead of panicking")]
    pub fn fp_min(&mut self, a: Term, b: Term) -> Term {
        self.try_fp_min(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create FP minimum (fallible).
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_min(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        let (eb, sb) = self.expect_same_fp("fp.min", a, b)?;
        let sort = Sort::FloatingPoint(eb, sb);
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("fp.min"),
            vec![a.0, b.0],
            sort,
        )))
    }

    /// Create FP maximum.
    #[deprecated(note = "use try_fp_max() which returns Result instead of panicking")]
    pub fn fp_max(&mut self, a: Term, b: Term) -> Term {
        self.try_fp_max(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create FP maximum (fallible).
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_max(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        let (eb, sb) = self.expect_same_fp("fp.max", a, b)?;
        let sort = Sort::FloatingPoint(eb, sb);
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("fp.max"),
            vec![a.0, b.0],
            sort,
        )))
    }

    // --- Rounding mode ---

    /// Create a rounding mode term from its SMT-LIB short name.
    ///
    /// Valid names: "RNE", "RNA", "RTP", "RTN", "RTZ".
    /// The FP solver matches on the symbol name, not the sort.
    ///
    /// # Panics
    ///
    /// Panics if `name` is not a valid rounding mode.
    /// Use [`try_fp_rounding_mode`](Self::try_fp_rounding_mode) for a fallible version.
    #[deprecated(note = "use try_fp_rounding_mode() which returns Result instead of panicking")]
    pub fn fp_rounding_mode(&mut self, name: &str) -> Term {
        self.try_fp_rounding_mode(name)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a rounding mode term from its SMT-LIB short name.
    ///
    /// Returns [`SolverError::InvalidArgument`] if `name` is not one of
    /// "RNE", "RNA", "RTP", "RTN", "RTZ".
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_rounding_mode(&mut self, name: &str) -> Result<Term, SolverError> {
        if !matches!(name, "RNE" | "RNA" | "RTP" | "RTN" | "RTZ") {
            return Err(SolverError::InvalidArgument {
                operation: "fp_rounding_mode",
                message: format!(
                    "invalid rounding mode '{name}': expected RNE, RNA, RTP, RTN, or RTZ"
                ),
            });
        }
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named(name),
            vec![],
            Sort::Bool,
        )))
    }

    // Conversion and arithmetic operations are in floating_point_conv.rs.
}
