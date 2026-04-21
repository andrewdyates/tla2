// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Core arithmetic term constructors: negation and addition.
//!
//! Subtraction and multiplication are in `arithmetic_sub_mul`.
//! Division, modulo, abs, min/max, conversions, and comparisons are in `arith_div_cmp`.

use super::*;
use num_traits::One;

impl TermStore {
    // =======================================================================
    // Arithmetic operations with constant folding
    // =======================================================================

    /// Helper: extract integer constant value
    pub(super) fn get_int(&self, id: TermId) -> Option<&BigInt> {
        match self.get(id) {
            TermData::Const(Constant::Int(n)) => Some(n),
            _ => None,
        }
    }

    /// Helper: extract rational constant value
    pub(super) fn get_rational(&self, id: TermId) -> Option<&BigRational> {
        match self.get(id) {
            TermData::Const(Constant::Rational(r)) => Some(&r.0),
            _ => None,
        }
    }

    /// Extract an integer constant from a term, handling Int literals,
    /// Rational literals with denominator 1, and unary negation.
    pub fn extract_integer_constant(&self, term: TermId) -> Option<BigInt> {
        match self.get(term) {
            TermData::Const(Constant::Int(n)) => Some(n.clone()),
            TermData::Const(Constant::Rational(r)) if r.0.denom().is_one() => {
                Some(r.0.numer().clone())
            }
            TermData::App(Symbol::Named(name), args) if name == "-" && args.len() == 1 => {
                self.extract_integer_constant(args[0]).map(|n| -n)
            }
            _ => None,
        }
    }

    /// Helper: check if all arguments are integer constants
    pub(super) fn all_int_consts(&self, args: &[TermId]) -> bool {
        args.iter().all(|&id| self.get_int(id).is_some())
    }

    /// Helper: check if all arguments are rational constants
    pub(super) fn all_rational_consts(&self, args: &[TermId]) -> bool {
        args.iter().all(|&id| self.get_rational(id).is_some())
    }

    fn extract_coeff<T, F, G>(
        &mut self,
        id: TermId,
        get_coeff: F,
        one_coeff: T,
        neg_one_coeff: T,
        mk_one: G,
    ) -> (T, TermId)
    where
        F: Fn(&Self, TermId) -> Option<T>,
        G: Fn(&mut Self) -> TermId,
    {
        // Check for negation: (- x) → (-1, x)
        if let TermData::App(Symbol::Named(name), args) = self.get(id) {
            if name == "-" && args.len() == 1 {
                return (neg_one_coeff, args[0]);
            }
        }

        // Check for multiplication with a constant anywhere in the args.
        // Note: mk_mul puts constants at the end, so we check last position first.
        if let TermData::App(Symbol::Named(name), args) = self.get(id) {
            if name == "*" && !args.is_empty() {
                let args_cloned = args.clone();

                // Find the first constant in the multiplication.
                for (i, &arg) in args_cloned.iter().enumerate() {
                    if let Some(coeff) = get_coeff(self, arg) {
                        // Get the remaining factors (excluding the constant).
                        let remainder: Vec<TermId> = args_cloned
                            .iter()
                            .enumerate()
                            .filter(|&(j, _)| j != i)
                            .map(|(_, &term)| term)
                            .collect();

                        if remainder.is_empty() {
                            // Just a constant, shouldn't happen in practice.
                            return (coeff, mk_one(self));
                        }
                        if remainder.len() == 1 {
                            return (coeff, remainder[0]);
                        }
                        return (coeff, self.mk_mul(remainder));
                    }
                }
            }
        }

        // Default: coefficient is 1.
        (one_coeff, id)
    }

    /// Helper: extract coefficient and base term from an integer expression.
    /// Returns (coefficient, base_term) where:
    /// - (* ... c) or (* c ...) → (c, (* rest)) when c is an integer constant
    /// - (- x) → (-1, x)
    /// - x → (1, x) for any other term
    fn extract_int_coeff(&mut self, id: TermId) -> (BigInt, TermId) {
        self.extract_coeff(
            id,
            |store, term| store.get_int(term).cloned(),
            BigInt::one(),
            BigInt::from(-1),
            |store| store.mk_int(BigInt::one()),
        )
    }

    /// Helper: extract coefficient and base term from a real (rational) expression.
    /// Returns (coefficient, base_term) where:
    /// - (* ... c) or (* c ...) → (c, (* rest)) when c is a rational constant
    /// - (- x) → (-1, x)
    /// - x → (1, x) for any other term
    fn extract_real_coeff(&mut self, id: TermId) -> (BigRational, TermId) {
        self.extract_coeff(
            id,
            |store, term| store.get_rational(term).cloned(),
            BigRational::one(),
            BigRational::from(BigInt::from(-1)),
            |store| store.mk_rational(BigRational::one()),
        )
    }

    /// Create negation (unary minus) with constant folding
    pub fn mk_neg(&mut self, arg: TermId) -> TermId {
        debug_assert!(
            matches!(self.sort(arg), Sort::Int | Sort::Real),
            "BUG: mk_neg expects Int or Real, got {:?}",
            self.sort(arg)
        );
        let sort = self.sort(arg).clone();

        // Constant folding for integers
        if let Some(n) = self.get_int(arg) {
            return self.mk_int(-n.clone());
        }

        // Constant folding for rationals
        if let Some(r) = self.get_rational(arg) {
            return self.mk_rational(-r.clone());
        }

        // Double negation: -(-x) = x
        if let TermData::App(Symbol::Named(name), args) = self.get(arg) {
            if name == "-" && args.len() == 1 {
                return args[0];
            }
        }

        // Distribute negation over addition: -(a + b) → (-a) + (-b)
        // This enables coefficient collection on the result
        if let TermData::App(Symbol::Named(name), args) = self.get(arg) {
            if name == "+" {
                let args_clone = args.clone();
                let negated_args: Vec<TermId> =
                    args_clone.iter().map(|&a| self.mk_neg(a)).collect();
                return self.mk_add(negated_args);
            }
        }

        // Factor negation into multiplication: -(... * c) → (... * (-c)) for constant c
        // Note: mk_mul places constants at the end of the args list, so we check the last argument
        // This normalizes negation to appear as coefficient, enabling further simplification
        if let TermData::App(Symbol::Named(name), args) = self.get(arg) {
            if name == "*" && !args.is_empty() {
                let args_clone = args.clone();
                // Check if last argument is a constant (mk_mul places constants last)
                // Safety: args.is_empty() check above guarantees last() returns Some
                let last = *args_clone
                    .last()
                    .expect("mk_neg: args verified non-empty above");
                if self.get_int(last).is_some() || self.get_rational(last).is_some() {
                    // -(rest * c) → (rest * (-c))
                    let neg_last = self.mk_neg(last);
                    let mut new_args: Vec<TermId> = args_clone[..args_clone.len() - 1].to_vec();
                    new_args.push(neg_last);
                    return self.mk_mul(new_args);
                }
            }
        }

        self.intern(TermData::App(Symbol::named("-"), vec![arg]), sort)
    }

    /// Create addition with constant folding
    #[allow(clippy::needless_pass_by_value)]
    pub fn mk_add(&mut self, args: Vec<TermId>) -> TermId {
        if args.is_empty() {
            return self.mk_int(BigInt::zero());
        }
        if args.len() == 1 {
            return args[0];
        }

        debug_assert!(
            args.iter()
                .all(|&a| matches!(self.sort(a), Sort::Int | Sort::Real)),
            "BUG: mk_add expects Int or Real args"
        );
        debug_assert!(
            args.windows(2).all(|w| self.sort(w[0]) == self.sort(w[1])),
            "BUG: mk_add expects same sort args"
        );

        let sort = self.sort(args[0]).clone();

        // Phase 1: Flatten nested additions
        // (+ (+ a b) c) -> (+ a b c)
        let mut flattened = Vec::new();
        for &arg in &args {
            match self.get(arg) {
                TermData::App(Symbol::Named(name), nested_args) if name == "+" => {
                    // Flatten: extract nested addition arguments
                    let nested = nested_args.clone();
                    flattened.extend(nested);
                }
                _ => flattened.push(arg),
            }
        }

        // Phase 2: Constant folding for integers (all constants)
        if sort == Sort::Int && self.all_int_consts(&flattened) {
            let mut sum = BigInt::zero();
            for &id in &flattened {
                if let Some(n) = self.get_int(id) {
                    sum += n;
                }
            }
            return self.mk_int(sum);
        }

        // Constant folding for rationals (all constants)
        if sort == Sort::Real && self.all_rational_consts(&flattened) {
            let mut sum = BigRational::zero();
            for &id in &flattened {
                if let Some(r) = self.get_rational(id) {
                    sum += r;
                }
            }
            return self.mk_rational(sum);
        }

        // Phase 3: Identity elimination (x + 0 = x) and partial constant folding
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
        if !consts.is_empty() {
            if sort == Sort::Int {
                let mut sum = BigInt::zero();
                for &id in &consts {
                    if let Some(n) = self.get_int(*id) {
                        sum += n;
                    }
                }
                // Only add if non-zero (identity elimination)
                if !sum.is_zero() {
                    result_args.push(self.mk_int(sum));
                }
            } else if sort == Sort::Real {
                let mut sum = BigRational::zero();
                for &id in &consts {
                    if let Some(r) = self.get_rational(*id) {
                        sum += r;
                    }
                }
                // Only add if non-zero (identity elimination)
                if !sum.is_zero() {
                    result_args.push(self.mk_rational(sum));
                }
            }
        }

        // Phase 4: Additive inverse detection — collect negated terms, cancel a + (-a) = 0
        let mut negated_map: Vec<(TermId, TermId)> = Vec::new(); // (neg_term, inner)
        for &arg in &result_args {
            if let TermData::App(Symbol::Named(name), inner_args) = self.get(arg) {
                if name == "-" && inner_args.len() == 1 {
                    negated_map.push((arg, inner_args[0]));
                }
            }
        }

        // Remove canceling pairs (HashSet for O(n) lookup instead of O(n²) Vec::contains)
        let result_set: std::collections::HashSet<TermId> = result_args.iter().copied().collect();
        let mut to_remove = std::collections::HashSet::new();
        for &(neg_term, inner) in &negated_map {
            if result_set.contains(&inner) && !to_remove.contains(&inner) {
                to_remove.insert(neg_term);
                to_remove.insert(inner);
            }
        }

        if !to_remove.is_empty() {
            result_args.retain(|t| !to_remove.contains(t));
        }

        // Phase 5: Coefficient collection for integers
        // (+ (* 2 a) (* 3 a)) → (* 5 a)
        if sort == Sort::Int && result_args.len() >= 2 {
            use std::collections::HashMap;
            let mut coeff_map: HashMap<TermId, BigInt> = HashMap::new();

            for &arg in &result_args {
                let (coeff, base) = self.extract_int_coeff(arg);
                *coeff_map.entry(base).or_insert_with(BigInt::zero) += coeff;
            }

            // Check if any coefficients were combined (i.e., same base appeared multiple times)
            if coeff_map.len() < result_args.len() {
                result_args.clear();

                // Sort by TermId for deterministic ordering (improves hash-consing and reproducibility)
                let mut sorted_entries: Vec<_> = coeff_map.into_iter().collect();
                sorted_entries.sort_by_key(|(base, _)| *base);

                for (base, coeff) in sorted_entries {
                    if coeff.is_zero() {
                        // Skip: coefficient is zero
                    } else if coeff.is_one() {
                        result_args.push(base);
                    } else if coeff == BigInt::from(-1) {
                        result_args.push(self.mk_neg(base));
                    } else {
                        // (* coeff base)
                        let coeff_term = self.mk_int(coeff);
                        result_args.push(self.mk_mul(vec![coeff_term, base]));
                    }
                }

                // Re-check for empty or single result
                if result_args.is_empty() {
                    return self.mk_int(BigInt::zero());
                }
                if result_args.len() == 1 {
                    return result_args[0];
                }
            }
        }

        // Phase 6: Coefficient collection for reals
        // (+ (* 2.0 a) (* 3.0 a)) → (* 5.0 a)
        if sort == Sort::Real && result_args.len() >= 2 {
            use std::collections::HashMap;
            let mut coeff_map: HashMap<TermId, BigRational> = HashMap::new();

            for &arg in &result_args {
                let (coeff, base) = self.extract_real_coeff(arg);
                *coeff_map.entry(base).or_insert_with(BigRational::zero) += coeff;
            }

            // Check if any coefficients were combined (i.e., same base appeared multiple times)
            if coeff_map.len() < result_args.len() {
                result_args.clear();
                let zero = BigRational::zero();
                let one = BigRational::one();
                let neg_one = BigRational::from(BigInt::from(-1));

                // Sort by TermId for deterministic ordering (improves hash-consing and reproducibility)
                let mut sorted_entries: Vec<_> = coeff_map.into_iter().collect();
                sorted_entries.sort_by_key(|(base, _)| *base);

                for (base, coeff) in sorted_entries {
                    if coeff == zero {
                        // Skip: coefficient is zero
                    } else if coeff == one {
                        result_args.push(base);
                    } else if coeff == neg_one {
                        result_args.push(self.mk_neg(base));
                    } else {
                        // (* coeff base)
                        let coeff_term = self.mk_rational(coeff);
                        result_args.push(self.mk_mul(vec![coeff_term, base]));
                    }
                }

                // Re-check for empty or single result
                if result_args.is_empty() {
                    return self.mk_rational(BigRational::zero());
                }
                if result_args.len() == 1 {
                    return result_args[0];
                }
            }
        }

        // Final result
        if result_args.is_empty() {
            return if sort == Sort::Int {
                self.mk_int(BigInt::zero())
            } else {
                self.mk_rational(BigRational::zero())
            };
        }
        if result_args.len() == 1 {
            return result_args[0];
        }

        self.intern(TermData::App(Symbol::named("+"), result_args), sort)
    }
}
