// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Division, modulo, absolute value, min/max, type conversions, and comparison
//! term constructors for TermStore.
//!
//! Extracted from `arithmetic.rs` as part of code-health module split.
//! The primary arithmetic operations (add, sub, mul, neg) remain in `arithmetic.rs`.

use super::*;
use num_traits::One;

impl TermStore {
    /// Create real division with constant folding
    pub fn mk_div(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        debug_assert!(self.sort(lhs) == &Sort::Real && self.sort(rhs) == &Sort::Real);
        // Constant folding for rationals
        if let (Some(r1), Some(r2)) = (self.get_rational(lhs), self.get_rational(rhs)) {
            if !r2.is_zero() {
                return self.mk_rational(r1.clone() / r2.clone());
            }
        }

        // x / 1 = x
        if let Some(r) = self.get_rational(rhs) {
            if *r == BigRational::one() {
                return lhs;
            }
        }

        // 0 / x = 0 (when x != 0)
        if let Some(r) = self.get_rational(lhs) {
            if r.is_zero() {
                return self.mk_rational(BigRational::zero());
            }
        }

        // x / x = 1 (when x is the same term)
        if lhs == rhs {
            return self.mk_rational(BigRational::one());
        }

        self.intern(
            TermData::App(Symbol::named("/"), vec![lhs, rhs]),
            Sort::Real,
        )
    }

    /// Create integer division with constant folding
    pub fn mk_intdiv(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        debug_assert!(self.sort(lhs) == &Sort::Int && self.sort(rhs) == &Sort::Int);
        // Constant folding for integers
        if let (Some(n1), Some(n2)) = (self.get_int(lhs), self.get_int(rhs)) {
            if !n2.is_zero() {
                // SMT-LIB div: Euclidean division where remainder is always non-negative.
                // a = b * q + r, 0 <= r < |b|.
                // Compute non-negative remainder first, then derive quotient.
                let rem = smt_euclid_rem(n1, n2);
                return self.mk_int((n1 - &rem) / n2);
            }
        }

        // x div 1 = x
        if let Some(n) = self.get_int(rhs) {
            if n.is_one() {
                return lhs;
            }
        }

        // 0 div x = 0 (when x != 0)
        if let Some(n) = self.get_int(lhs) {
            if n.is_zero() {
                return self.mk_int(BigInt::zero());
            }
        }

        // x div x = 1 (when x is the same term)
        if lhs == rhs {
            return self.mk_int(BigInt::one());
        }

        self.intern(
            TermData::App(Symbol::named("div"), vec![lhs, rhs]),
            Sort::Int,
        )
    }

    /// Create modulo with constant folding
    pub fn mk_mod(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        debug_assert!(self.sort(lhs) == &Sort::Int && self.sort(rhs) == &Sort::Int);
        // Constant folding for integers
        if let (Some(n1), Some(n2)) = (self.get_int(lhs), self.get_int(rhs)) {
            if !n2.is_zero() {
                // SMT-LIB mod: Euclidean remainder, always non-negative.
                // a = b * (div a b) + (mod a b), 0 <= (mod a b) < |b|.
                return self.mk_int(smt_euclid_rem(n1, n2));
            }
        }

        // x mod 1 = 0
        if let Some(n) = self.get_int(rhs) {
            if n.is_one() {
                return self.mk_int(BigInt::zero());
            }
        }

        // 0 mod x = 0 (when x != 0)
        if let Some(n) = self.get_int(lhs) {
            if n.is_zero() {
                return self.mk_int(BigInt::zero());
            }
        }

        // x mod x = 0 (when x != 0)
        if lhs == rhs {
            return self.mk_int(BigInt::zero());
        }

        self.intern(
            TermData::App(Symbol::named("mod"), vec![lhs, rhs]),
            Sort::Int,
        )
    }

    /// Create absolute value with constant folding and ITE expansion
    ///
    /// For non-constant arguments, expands `(abs x)` to `(ite (>= x 0) x (- x))`.
    /// This ensures the LIA theory can properly reason about absolute value.
    pub fn mk_abs(&mut self, arg: TermId) -> TermId {
        debug_assert!(
            matches!(self.sort(arg), Sort::Int | Sort::Real),
            "BUG: mk_abs expects Int or Real, got {:?}",
            self.sort(arg)
        );
        // Constant folding for integers
        if let Some(n) = self.get_int(arg) {
            if n.is_negative() {
                return self.mk_int(-n.clone());
            }
            return arg;
        }

        // Constant folding for rationals
        if let Some(r) = self.get_rational(arg) {
            if *r < BigRational::zero() {
                return self.mk_rational(-r.clone());
            }
            return arg;
        }

        // Expand to ITE: (abs x) -> (ite (>= x 0) x (- x))
        // This allows the LIA/LRA theories to properly handle abs
        let zero = match self.sort(arg) {
            Sort::Real => self.mk_rational(BigRational::zero()),
            _ => self.mk_int(BigInt::zero()),
        };
        let cond = self.mk_ge(arg, zero);
        let neg_arg = self.mk_neg(arg);
        self.mk_ite(cond, arg, neg_arg)
    }

    /// Create minimum of two values with constant folding and ITE expansion
    ///
    /// For non-constant arguments, expands `(min x y)` to `(ite (<= x y) x y)`.
    pub fn mk_min(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        debug_assert!(
            matches!(self.sort(lhs), Sort::Int | Sort::Real),
            "BUG: mk_min expects Int or Real, got {:?}",
            self.sort(lhs)
        );
        debug_assert!(
            self.sort(lhs) == self.sort(rhs),
            "BUG: mk_min expects same sort, got {:?} vs {:?}",
            self.sort(lhs),
            self.sort(rhs)
        );
        // Same value: min(x, x) = x
        if lhs == rhs {
            return lhs;
        }

        // Integer constant folding
        if let (Some(n1), Some(n2)) = (self.get_int(lhs), self.get_int(rhs)) {
            return if n1 < n2 {
                self.mk_int(n1.clone())
            } else {
                self.mk_int(n2.clone())
            };
        }

        // Rational constant folding
        if let (Some(r1), Some(r2)) = (self.get_rational(lhs), self.get_rational(rhs)) {
            return if r1 < r2 {
                self.mk_rational(r1.clone())
            } else {
                self.mk_rational(r2.clone())
            };
        }

        // Expand to ITE: (min x y) -> (ite (<= x y) x y)
        let cond = self.mk_le(lhs, rhs);
        self.mk_ite(cond, lhs, rhs)
    }

    /// Create maximum of two values with constant folding and ITE expansion
    ///
    /// For non-constant arguments, expands `(max x y)` to `(ite (>= x y) x y)`.
    pub fn mk_max(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        debug_assert!(
            matches!(self.sort(lhs), Sort::Int | Sort::Real),
            "BUG: mk_max expects Int or Real, got {:?}",
            self.sort(lhs)
        );
        debug_assert!(
            self.sort(lhs) == self.sort(rhs),
            "BUG: mk_max expects same sort, got {:?} vs {:?}",
            self.sort(lhs),
            self.sort(rhs)
        );
        // Same value: max(x, x) = x
        if lhs == rhs {
            return lhs;
        }

        // Integer constant folding
        if let (Some(n1), Some(n2)) = (self.get_int(lhs), self.get_int(rhs)) {
            return if n1 > n2 {
                self.mk_int(n1.clone())
            } else {
                self.mk_int(n2.clone())
            };
        }

        // Rational constant folding
        if let (Some(r1), Some(r2)) = (self.get_rational(lhs), self.get_rational(rhs)) {
            return if r1 > r2 {
                self.mk_rational(r1.clone())
            } else {
                self.mk_rational(r2.clone())
            };
        }

        // Expand to ITE: (max x y) -> (ite (>= x y) x y)
        let cond = self.mk_ge(lhs, rhs);
        self.mk_ite(cond, lhs, rhs)
    }

    // =======================================================================
    // Type conversion operations
    // =======================================================================

    /// Convert an integer to a real (SMT-LIB: `to_real`).
    ///
    /// For constants, this creates a rational with denominator 1.
    /// For symbolic integers, creates a `to_real` application.
    pub fn mk_to_real(&mut self, arg: TermId) -> TermId {
        debug_assert!(
            self.sort(arg) == &Sort::Int,
            "BUG: mk_to_real expects Int arg, got {:?}",
            self.sort(arg)
        );

        // Constant folding: convert integer constant to rational
        if let Some(n) = self.get_int(arg) {
            return self.mk_rational(BigRational::from(n.clone()));
        }

        self.intern(
            TermData::App(Symbol::named("to_real"), vec![arg]),
            Sort::Real,
        )
    }

    /// Convert a real to an integer via floor (SMT-LIB: `to_int`).
    ///
    /// For constants, computes floor(r). For symbolic reals, creates a `to_int` application.
    pub fn mk_to_int(&mut self, arg: TermId) -> TermId {
        debug_assert!(
            self.sort(arg) == &Sort::Real,
            "BUG: mk_to_int expects Real arg, got {:?}",
            self.sort(arg)
        );

        // Constant folding: floor of rational
        if let Some(r) = self.get_rational(arg) {
            return self.mk_int(r.floor().to_integer());
        }

        self.intern(TermData::App(Symbol::named("to_int"), vec![arg]), Sort::Int)
    }

    /// Test if a real value is an integer (SMT-LIB: `is_int`).
    ///
    /// For constants, returns true/false. For symbolic reals, creates an `is_int` application.
    pub fn mk_is_int(&mut self, arg: TermId) -> TermId {
        debug_assert!(
            self.sort(arg) == &Sort::Real,
            "BUG: mk_is_int expects Real arg, got {:?}",
            self.sort(arg)
        );

        // Constant folding: check if rational is an integer
        if let Some(r) = self.get_rational(arg) {
            return self.mk_bool(r.is_integer());
        }

        self.intern(
            TermData::App(Symbol::named("is_int"), vec![arg]),
            Sort::Bool,
        )
    }

    // =======================================================================
    // Comparison operations with constant folding
    // =======================================================================

    /// Create less-than comparison with constant folding
    pub fn mk_lt(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        debug_assert!(
            matches!(self.sort(lhs), Sort::Int | Sort::Real),
            "BUG: mk_lt expects Int or Real, got {:?}",
            self.sort(lhs)
        );
        debug_assert!(
            self.sort(lhs) == self.sort(rhs),
            "BUG: mk_lt expects same sort, got {:?} < {:?}",
            self.sort(lhs),
            self.sort(rhs)
        );
        // x < x = false
        if lhs == rhs {
            return self.false_term();
        }

        // Integer constant folding
        if let (Some(n1), Some(n2)) = (self.get_int(lhs), self.get_int(rhs)) {
            return self.mk_bool(n1 < n2);
        }

        // Rational constant folding
        if let (Some(r1), Some(r2)) = (self.get_rational(lhs), self.get_rational(rhs)) {
            return self.mk_bool(r1 < r2);
        }

        self.intern(
            TermData::App(Symbol::named("<"), vec![lhs, rhs]),
            Sort::Bool,
        )
    }

    /// Create less-than-or-equal comparison with constant folding
    pub fn mk_le(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        debug_assert!(
            matches!(self.sort(lhs), Sort::Int | Sort::Real),
            "BUG: mk_le expects Int or Real, got {:?}",
            self.sort(lhs)
        );
        debug_assert!(
            self.sort(lhs) == self.sort(rhs),
            "BUG: mk_le expects same sort, got {:?} <= {:?}",
            self.sort(lhs),
            self.sort(rhs)
        );
        // x <= x = true
        if lhs == rhs {
            return self.true_term();
        }

        // Integer constant folding
        if let (Some(n1), Some(n2)) = (self.get_int(lhs), self.get_int(rhs)) {
            return self.mk_bool(n1 <= n2);
        }

        // Rational constant folding
        if let (Some(r1), Some(r2)) = (self.get_rational(lhs), self.get_rational(rhs)) {
            return self.mk_bool(r1 <= r2);
        }

        self.intern(
            TermData::App(Symbol::named("<="), vec![lhs, rhs]),
            Sort::Bool,
        )
    }

    /// Create greater-than comparison with constant folding
    ///
    /// Normalized to less-than: (> a b) -> (< b a)
    pub fn mk_gt(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        // Normalize: (> a b) -> (< b a) for canonical form
        self.mk_lt(rhs, lhs)
    }

    /// Create greater-than-or-equal comparison with constant folding
    ///
    /// Normalized to less-than-or-equal: (>= a b) -> (<= b a)
    pub fn mk_ge(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        // Normalize: (>= a b) -> (<= b a) for canonical form
        self.mk_le(rhs, lhs)
    }
}
