// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Arithmetic evaluation helpers for model evaluation.
//!
//! Handles SMT-LIB arithmetic operations: `+`, `-`, `*`, `/`, `div`, `mod`,
//! `abs`, `to_real`, `to_int`, `is_int`, `<`, `<=`, `>`, `>=`.
//!
//! Extracted from `mod.rs` to reduce file size (#5970 code-health splits).
//! All methods are `impl Executor` — they share the same method namespace.

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};
use z4_core::TermId;

use super::{EvalValue, Executor, Model};

impl Executor {
    /// Evaluate an arithmetic operator application.
    ///
    /// Caller must only pass recognized arithmetic operator names.
    pub(super) fn evaluate_arith_app(
        &self,
        model: &Model,
        name: &str,
        args: &[TermId],
    ) -> EvalValue {
        match name {
            // Arithmetic addition
            "+" => {
                let mut sum = BigRational::zero();
                for &arg in args {
                    match self.evaluate_term(model, arg) {
                        EvalValue::Rational(r) => sum += r,
                        _ => return EvalValue::Unknown,
                    }
                }
                EvalValue::Rational(sum)
            }
            // Arithmetic subtraction (unary or binary)
            "-" => {
                if args.is_empty() {
                    return EvalValue::Unknown;
                }
                let first = self.evaluate_term(model, args[0]);
                match first {
                    EvalValue::Rational(mut result) => {
                        if args.len() == 1 {
                            // Unary negation
                            EvalValue::Rational(-result)
                        } else {
                            // Binary/n-ary subtraction
                            for &arg in &args[1..] {
                                match self.evaluate_term(model, arg) {
                                    EvalValue::Rational(r) => result -= r,
                                    _ => return EvalValue::Unknown,
                                }
                            }
                            EvalValue::Rational(result)
                        }
                    }
                    _ => EvalValue::Unknown,
                }
            }
            // Arithmetic multiplication
            "*" => {
                let mut product = BigRational::one();
                for &arg in args {
                    match self.evaluate_term(model, arg) {
                        EvalValue::Rational(r) => product *= r,
                        _ => return EvalValue::Unknown,
                    }
                }
                EvalValue::Rational(product)
            }
            // Arithmetic division
            "/" => {
                if args.len() != 2 {
                    return EvalValue::Unknown;
                }
                let num = self.evaluate_term(model, args[0]);
                let denom = self.evaluate_term(model, args[1]);
                match (num, denom) {
                    (EvalValue::Rational(n), EvalValue::Rational(d)) => {
                        if d.is_zero() {
                            EvalValue::Unknown // Division by zero
                        } else {
                            EvalValue::Rational(n / d)
                        }
                    }
                    _ => EvalValue::Unknown,
                }
            }
            // SMT-LIB integer division (Euclidean, rounds toward -∞)
            // div t1 t2 = floor(t1/t2) when t2 > 0
            //           = ceil(t1/t2) when t2 < 0
            // Defined such that (mod t1 t2) is always non-negative.
            "div" => {
                if args.len() != 2 {
                    return EvalValue::Unknown;
                }
                let lhs = self.evaluate_term(model, args[0]);
                let rhs = self.evaluate_term(model, args[1]);
                match (lhs, rhs) {
                    (EvalValue::Rational(n), EvalValue::Rational(d)) => {
                        if d.is_zero() || !n.is_integer() || !d.is_integer() {
                            EvalValue::Unknown
                        } else {
                            let ni = n.numer().clone();
                            let di = d.numer().clone();
                            let q = Self::euclidean_div(&ni, &di);
                            EvalValue::Rational(BigRational::from_integer(q))
                        }
                    }
                    _ => EvalValue::Unknown,
                }
            }
            // SMT-LIB integer modulo (Euclidean, always non-negative)
            // mod t1 t2 = t1 - (div t1 t2) * t2
            // Result satisfies: 0 <= (mod t1 t2) < |t2|
            "mod" => {
                if args.len() != 2 {
                    return EvalValue::Unknown;
                }
                let lhs = self.evaluate_term(model, args[0]);
                let rhs = self.evaluate_term(model, args[1]);
                match (lhs, rhs) {
                    (EvalValue::Rational(n), EvalValue::Rational(d)) => {
                        if d.is_zero() || !n.is_integer() || !d.is_integer() {
                            EvalValue::Unknown
                        } else {
                            let ni = n.numer().clone();
                            let di = d.numer().clone();
                            let q = Self::euclidean_div(&ni, &di);
                            let r = ni - q * &di;
                            EvalValue::Rational(BigRational::from_integer(r))
                        }
                    }
                    _ => EvalValue::Unknown,
                }
            }
            // Absolute value
            "abs" => {
                if args.len() != 1 {
                    return EvalValue::Unknown;
                }
                match self.evaluate_term(model, args[0]) {
                    EvalValue::Rational(v) => EvalValue::Rational(v.abs()),
                    _ => EvalValue::Unknown,
                }
            }
            // Int-to-Real conversion (#5947): to_real(x) evaluates
            // x and returns its value. LRA treats to_real as identity,
            // but the model evaluator needs this to look up Int-sorted
            // variables in the LIA model for model validation.
            "to_real" => {
                if args.len() != 1 {
                    return EvalValue::Unknown;
                }
                self.evaluate_term(model, args[0])
            }
            // Real-to-Int conversion: to_int(x) = floor(x)
            "to_int" => {
                if args.len() != 1 {
                    return EvalValue::Unknown;
                }
                match self.evaluate_term(model, args[0]) {
                    EvalValue::Rational(r) => {
                        let floored = r.floor().to_integer();
                        EvalValue::Rational(BigRational::from(floored))
                    }
                    other => other,
                }
            }
            // is_int(x) = true iff x is an integer
            "is_int" => {
                if args.len() != 1 {
                    return EvalValue::Unknown;
                }
                match self.evaluate_term(model, args[0]) {
                    EvalValue::Rational(r) => EvalValue::Bool(r.is_integer()),
                    _ => EvalValue::Unknown,
                }
            }
            // Less than
            "<" => self.eval_arith_cmp(model, args, |l, r| l < r),
            // Less than or equal
            "<=" => self.eval_arith_cmp(model, args, |l, r| l <= r),
            // Greater than
            ">" => self.eval_arith_cmp(model, args, |l, r| l > r),
            // Greater than or equal
            ">=" => self.eval_arith_cmp(model, args, |l, r| l >= r),
            _ => unreachable!("evaluate_arith_app called with non-arithmetic operator: {name}"),
        }
    }

    /// Helper for binary arithmetic comparison operators.
    fn eval_arith_cmp(
        &self,
        model: &Model,
        args: &[TermId],
        cmp: impl FnOnce(&BigRational, &BigRational) -> bool,
    ) -> EvalValue {
        if args.len() != 2 {
            return EvalValue::Unknown;
        }
        let lhs = self.evaluate_term(model, args[0]);
        let rhs = self.evaluate_term(model, args[1]);
        match (lhs, rhs) {
            (EvalValue::Rational(l), EvalValue::Rational(r)) => EvalValue::Bool(cmp(&l, &r)),
            _ => EvalValue::Unknown,
        }
    }

    /// SMT-LIB Euclidean integer division: floor(n/d).
    ///
    /// Returns the unique integer q such that n = q*d + r and 0 <= r < |d|.
    /// Rust's truncating division differs from SMT-LIB when n and d have
    /// opposite signs.
    pub(super) fn euclidean_div(n: &BigInt, d: &BigInt) -> BigInt {
        use num_integer::Integer;
        let (q, r) = n.div_rem(d);
        // Rust truncates toward zero; adjust when remainder is negative.
        if r < BigInt::zero() {
            if *d > BigInt::zero() {
                q - 1
            } else {
                q + 1
            }
        } else {
            q
        }
    }
}
