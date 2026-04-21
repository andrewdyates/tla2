// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bool-sorted BV predicate and substitution evaluation for model recovery.
//!
//! Evaluates Bool-sorted BV comparisons (`bvult`, `bvuge`, etc.) and
//! general Bool substitution targets (`xor`, `and`, `ite`, `=>`)
//! under a BV model. Extracted from `bv_eval.rs` for code health (#5970).

#[cfg(not(kani))]
use hashbrown::HashMap;
#[cfg(kani)]
use z4_core::kani_compat::DetHashMap as HashMap;
use z4_core::term::TermData;
use z4_core::{Sort, TermId, TermStore};

use super::super::Executor;

impl Executor {
    /// Evaluate a Bool-sorted BV predicate (e.g., `bvult`, `bvuge`) using model values (#5524).
    ///
    /// When variable substitution replaces a Bool variable with a BV comparison
    /// predicate (e.g., `p -> (bvult x #x42)`), the standard `evaluate_bv_expr`
    /// cannot recover the value because it only handles BitVec-sorted terms.
    /// This function evaluates Bool-sorted BV predicates to recover the Bool result.
    pub(crate) fn evaluate_bv_bool_predicate(
        terms: &TermStore,
        term: TermId,
        values: &HashMap<TermId, num_bigint::BigInt>,
    ) -> Option<bool> {
        use num_bigint::BigInt;

        match terms.get(term) {
            TermData::App(sym, args) if *terms.sort(term) == Sort::Bool => {
                let name = sym.name();
                match name {
                    "bvult" | "bvule" | "bvugt" | "bvuge" | "bvslt" | "bvsle" | "bvsgt"
                    | "bvsge" => {
                        if args.len() != 2 {
                            return None;
                        }
                        let lhs = Self::evaluate_bv_expr(terms, args[0], values)?;
                        let rhs = Self::evaluate_bv_expr(terms, args[1], values)?;
                        // Get width from the BV-sorted arguments
                        let width = match terms.sort(args[0]) {
                            Sort::BitVec(bv) => bv.width,
                            _ => return None,
                        };
                        let modulus = BigInt::from(1u64) << width;
                        let lhs = lhs % &modulus;
                        let rhs = rhs % &modulus;
                        match name {
                            "bvult" => Some(lhs < rhs),
                            "bvule" => Some(lhs <= rhs),
                            "bvugt" => Some(lhs > rhs),
                            "bvuge" => Some(lhs >= rhs),
                            _ => {
                                // Signed comparisons: convert to signed
                                let half = &modulus >> 1;
                                let to_signed = |v: BigInt| -> BigInt {
                                    if v >= half {
                                        v - &modulus
                                    } else {
                                        v
                                    }
                                };
                                let lhs_s = to_signed(lhs);
                                let rhs_s = to_signed(rhs);
                                match name {
                                    "bvslt" => Some(lhs_s < rhs_s),
                                    "bvsle" => Some(lhs_s <= rhs_s),
                                    "bvsgt" => Some(lhs_s > rhs_s),
                                    "bvsge" => Some(lhs_s >= rhs_s),
                                    _ => None,
                                }
                            }
                        }
                    }
                    // BV equality: (= a b) where both operands are BitVec-sorted
                    "=" if args.len() == 2 => {
                        let lhs = Self::evaluate_bv_expr(terms, args[0], values)?;
                        let rhs = Self::evaluate_bv_expr(terms, args[1], values)?;
                        Some(lhs == rhs)
                    }
                    _ => None,
                }
            }
            TermData::Not(inner) => {
                Self::evaluate_bv_bool_predicate(terms, *inner, values).map(|b| !b)
            }
            _ => None,
        }
    }

    /// Evaluate a general Bool-sorted substitution target (#5115).
    ///
    /// Extends `evaluate_bv_bool_predicate` to handle pure-Bool operations
    /// (xor, and, or, ite, =>, iff) that arise when VariableSubstitution
    /// eliminates intermediate Bool wires (e.g., `g0 -> (xor w0 w4)` in
    /// MCMPC circuit benchmarks). Without this, eliminated Bool variables
    /// linked to BV extracts via Bool gates are never recovered, causing
    /// model validation to degrade to Unknown on 458+ QF_BV benchmarks.
    ///
    /// Returns `Some(bool)` if the expression can be evaluated using
    /// available BV values and previously-resolved bool_overrides.
    pub(crate) fn evaluate_bool_substitution(
        terms: &TermStore,
        term: TermId,
        bv_values: &HashMap<TermId, num_bigint::BigInt>,
        bool_overrides: &HashMap<TermId, bool>,
    ) -> Option<bool> {
        // First try the BV predicate evaluator (handles =, bvult, etc.)
        if let Some(b) = Self::evaluate_bv_bool_predicate(terms, term, bv_values) {
            return Some(b);
        }

        match terms.get(term) {
            TermData::Const(z4_core::term::Constant::Bool(b)) => Some(*b),
            TermData::Var(_, _) if *terms.sort(term) == Sort::Bool => {
                bool_overrides.get(&term).copied()
            }
            TermData::Not(inner) => {
                Self::evaluate_bool_substitution(terms, *inner, bv_values, bool_overrides)
                    .map(|b| !b)
            }
            TermData::App(sym, args) if *terms.sort(term) == Sort::Bool => {
                let name = sym.name();
                match name {
                    "and" => {
                        let mut result = true;
                        for &arg in args.iter() {
                            result &= Self::evaluate_bool_substitution(
                                terms,
                                arg,
                                bv_values,
                                bool_overrides,
                            )?;
                        }
                        Some(result)
                    }
                    "or" => {
                        let mut result = false;
                        for &arg in args.iter() {
                            result |= Self::evaluate_bool_substitution(
                                terms,
                                arg,
                                bv_values,
                                bool_overrides,
                            )?;
                        }
                        Some(result)
                    }
                    "xor" if args.len() == 2 => {
                        let a = Self::evaluate_bool_substitution(
                            terms,
                            args[0],
                            bv_values,
                            bool_overrides,
                        )?;
                        let b = Self::evaluate_bool_substitution(
                            terms,
                            args[1],
                            bv_values,
                            bool_overrides,
                        )?;
                        Some(a ^ b)
                    }
                    "=>" if args.len() == 2 => {
                        let a = Self::evaluate_bool_substitution(
                            terms,
                            args[0],
                            bv_values,
                            bool_overrides,
                        )?;
                        let b = Self::evaluate_bool_substitution(
                            terms,
                            args[1],
                            bv_values,
                            bool_overrides,
                        )?;
                        Some(!a || b)
                    }
                    "ite" if args.len() == 3 => {
                        let cond = Self::evaluate_bool_substitution(
                            terms,
                            args[0],
                            bv_values,
                            bool_overrides,
                        )?;
                        if cond {
                            Self::evaluate_bool_substitution(
                                terms,
                                args[1],
                                bv_values,
                                bool_overrides,
                            )
                        } else {
                            Self::evaluate_bool_substitution(
                                terms,
                                args[2],
                                bv_values,
                                bool_overrides,
                            )
                        }
                    }
                    // Bool equality encoded as ITE by mk_eq
                    "=" if args.len() == 2 && *terms.sort(args[0]) == Sort::Bool => {
                        let a = Self::evaluate_bool_substitution(
                            terms,
                            args[0],
                            bv_values,
                            bool_overrides,
                        )?;
                        let b = Self::evaluate_bool_substitution(
                            terms,
                            args[1],
                            bv_values,
                            bool_overrides,
                        )?;
                        Some(a == b)
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }
}
