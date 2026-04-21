// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Subtraction and multiplication term constructors.
//!
//! Negation and addition are in `arithmetic`.
//! Division, modulo, abs, min/max, conversions, and comparisons are in `arith_div_cmp`.

use super::*;
use num_traits::One;

impl TermStore {
    /// Create subtraction with constant folding and normalization to addition form
    ///
    /// Converts binary subtraction to addition: (a - b) -> (+ a (- b))
    /// Converts n-ary subtraction to addition: (- a b c) -> (+ a (- b) (- c))
    /// This normalization enables coefficient collection across subtraction operations.
    #[allow(clippy::needless_pass_by_value)]
    pub fn mk_sub(&mut self, args: Vec<TermId>) -> TermId {
        if args.is_empty() {
            return self.mk_int(BigInt::zero());
        }
        if args.len() == 1 {
            // Unary minus
            return self.mk_neg(args[0]);
        }

        debug_assert!(
            args.iter()
                .all(|&a| matches!(self.sort(a), Sort::Int | Sort::Real)),
            "BUG: mk_sub expects Int or Real args"
        );
        debug_assert!(
            args.windows(2).all(|w| self.sort(w[0]) == self.sort(w[1])),
            "BUG: mk_sub expects same sort args"
        );

        let sort = self.sort(args[0]).clone();

        // For binary subtraction: constant folding
        if args.len() == 2 {
            let (a, b) = (args[0], args[1]);

            // Integer constant folding
            if let (Some(n1), Some(n2)) = (self.get_int(a), self.get_int(b)) {
                return self.mk_int(n1.clone() - n2.clone());
            }

            // Rational constant folding
            if let (Some(r1), Some(r2)) = (self.get_rational(a), self.get_rational(b)) {
                return self.mk_rational(r1.clone() - r2.clone());
            }

            // x - 0 = x
            if let Some(n) = self.get_int(b) {
                if n.is_zero() {
                    return a;
                }
            }
            if let Some(r) = self.get_rational(b) {
                if r.is_zero() {
                    return a;
                }
            }

            // 0 - x = -x
            if let Some(n) = self.get_int(a) {
                if n.is_zero() {
                    return self.mk_neg(b);
                }
            }
            if let Some(r) = self.get_rational(a) {
                if r.is_zero() {
                    return self.mk_neg(b);
                }
            }

            // x - x = 0
            if a == b {
                return if sort == Sort::Int {
                    self.mk_int(BigInt::zero())
                } else {
                    self.mk_rational(BigRational::zero())
                };
            }

            // Convert binary subtraction to addition form: (a - b) -> (+ a (- b))
            // This enables coefficient collection across subtraction operations
            // Example: (2x - x) -> (+ 2x (- x)) -> x (via coefficient collection in mk_add)
            let neg_b = self.mk_neg(b);
            return self.mk_add(vec![a, neg_b]);
        }

        // N-ary subtraction: (- a b c) -> (+ a (- b) (- c))
        // Negate all arguments except the first
        let first = args[0];
        let mut add_args = vec![first];
        for &arg in &args[1..] {
            add_args.push(self.mk_neg(arg));
        }
        self.mk_add(add_args)
    }

    /// Create multiplication with constant folding
    ///
    /// Flattens nested multiplications: (* (* a b) c) -> (* a b c)
    /// Simplifies multiply by -1: (* -1 x) -> (- x)
    #[allow(clippy::needless_pass_by_value)]
    pub fn mk_mul(&mut self, args: Vec<TermId>) -> TermId {
        if args.is_empty() {
            return self.mk_int(BigInt::one());
        }
        if args.len() == 1 {
            return args[0];
        }

        debug_assert!(
            args.iter()
                .all(|&a| matches!(self.sort(a), Sort::Int | Sort::Real)),
            "BUG: mk_mul expects Int or Real args"
        );
        debug_assert!(
            args.windows(2).all(|w| self.sort(w[0]) == self.sort(w[1])),
            "BUG: mk_mul expects same sort args"
        );

        let sort = self.sort(args[0]).clone();

        // Phase 1: Flatten nested multiplications
        // (* (* a b) c) -> (* a b c)
        let mut flattened = Vec::new();
        for &arg in &args {
            match self.get(arg) {
                TermData::App(Symbol::Named(name), nested_args) if name == "*" => {
                    // Flatten: extract nested multiplication arguments
                    let nested = nested_args.clone();
                    flattened.extend(nested);
                }
                _ => flattened.push(arg),
            }
        }

        // Phase 2: Check for zero (annihilation) - must check early
        for &id in &flattened {
            if let Some(n) = self.get_int(id) {
                if n.is_zero() {
                    return self.mk_int(BigInt::zero());
                }
            }
            if let Some(r) = self.get_rational(id) {
                if r.is_zero() {
                    return self.mk_rational(BigRational::zero());
                }
            }
        }

        // Phase 3: Constant folding (all constants)
        if sort == Sort::Int && self.all_int_consts(&flattened) {
            let mut product = BigInt::one();
            for &id in &flattened {
                if let Some(n) = self.get_int(id) {
                    product *= n;
                }
            }
            return self.mk_int(product);
        }

        if sort == Sort::Real && self.all_rational_consts(&flattened) {
            let mut product = BigRational::one();
            for &id in &flattened {
                if let Some(r) = self.get_rational(id) {
                    product *= r;
                }
            }
            return self.mk_rational(product);
        }

        // Phase 4: Partial constant folding and identity elimination
        // Collect constants and non-constants
        let (consts, non_consts): (Vec<_>, Vec<_>) = if sort == Sort::Int {
            flattened
                .iter()
                .partition(|&&id| self.get_int(id).is_some())
        } else if sort == Sort::Real {
            flattened
                .iter()
                .partition(|&&id| self.get_rational(id).is_some())
        } else {
            (vec![], flattened.iter().collect())
        };

        // Fold all constants into one
        let mut result_args: Vec<TermId> = non_consts.into_iter().copied().collect();
        let mut const_product_int = BigInt::one();
        let mut const_product_rat = BigRational::one();
        let mut has_const = false;

        if !consts.is_empty() {
            has_const = true;
            if sort == Sort::Int {
                for &id in &consts {
                    if let Some(n) = self.get_int(*id) {
                        const_product_int *= n;
                    }
                }
            } else if sort == Sort::Real {
                for &id in &consts {
                    if let Some(r) = self.get_rational(*id) {
                        const_product_rat *= r;
                    }
                }
            }
        }

        // Phase 5: Handle special constant values
        if has_const {
            if sort == Sort::Int {
                // Zero annihilates
                if const_product_int.is_zero() {
                    return self.mk_int(BigInt::zero());
                }
                // Multiply by -1: (* -1 x) -> (- x)
                if const_product_int == BigInt::from(-1) {
                    if result_args.is_empty() {
                        return self.mk_int(BigInt::from(-1));
                    }
                    if result_args.len() == 1 {
                        return self.mk_neg(result_args[0]);
                    }
                    // (* -1 a b) -> (- (* a b))
                    let inner_mul = self.mk_mul(result_args);
                    return self.mk_neg(inner_mul);
                }
                // Identity: don't add 1 to the product
                if !const_product_int.is_one() {
                    result_args.push(self.mk_int(const_product_int));
                }
            } else if sort == Sort::Real {
                // Zero annihilates
                if const_product_rat.is_zero() {
                    return self.mk_rational(BigRational::zero());
                }
                // Multiply by -1: (* -1 x) -> (- x)
                if const_product_rat == BigRational::from(BigInt::from(-1)) {
                    if result_args.is_empty() {
                        return self.mk_rational(BigRational::from(BigInt::from(-1)));
                    }
                    if result_args.len() == 1 {
                        return self.mk_neg(result_args[0]);
                    }
                    // (* -1 a b) -> (- (* a b))
                    let inner_mul = self.mk_mul(result_args);
                    return self.mk_neg(inner_mul);
                }
                // Identity: don't add 1 to the product
                if const_product_rat != BigRational::one() {
                    result_args.push(self.mk_rational(const_product_rat));
                }
            }
        }

        // Phase 6: Distribute constants over addition for linear normalization
        //
        // (* c (+ a b ...)) -> (+ (* c a) (* c b) ...)
        //
        // Only applies when the multiplication is exactly "constant * sum" (no other factors).
        if (sort == Sort::Int || sort == Sort::Real) && result_args.len() == 2 {
            let a0 = result_args[0];
            let a1 = result_args[1];

            let const_and_sum = if sort == Sort::Int {
                if self.get_int(a0).is_some() {
                    Some((a0, a1))
                } else if self.get_int(a1).is_some() {
                    Some((a1, a0))
                } else {
                    None
                }
            } else if sort == Sort::Real {
                if self.get_rational(a0).is_some() {
                    Some((a0, a1))
                } else if self.get_rational(a1).is_some() {
                    Some((a1, a0))
                } else {
                    None
                }
            } else {
                None
            };

            if let Some((const_term, sum_term)) = const_and_sum {
                let sum_args = match self.get(sum_term) {
                    TermData::App(Symbol::Named(name), args) if name == "+" && args.len() >= 2 => {
                        Some(args.clone())
                    }
                    _ => None,
                };

                if let Some(sum_args) = sum_args {
                    let mut distributed = Vec::with_capacity(sum_args.len());
                    for t in sum_args {
                        distributed.push(self.mk_mul(vec![const_term, t]));
                    }
                    return self.mk_add(distributed);
                }
            }
        }

        // Final result
        if result_args.is_empty() {
            return if sort == Sort::Int {
                self.mk_int(BigInt::one())
            } else {
                self.mk_rational(BigRational::one())
            };
        }
        if result_args.len() == 1 {
            return result_args[0];
        }

        self.intern(TermData::App(Symbol::named("*"), result_args), sort)
    }
}
