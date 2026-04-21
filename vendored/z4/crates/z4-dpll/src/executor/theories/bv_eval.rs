// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! BV expression evaluation for model recovery.
//!
//! Evaluates bitvector expressions under a model to recover variable values
//! eliminated by substitution. Bool-sorted BV predicates and general Bool
//! substitution evaluation are in [`bv_eval_bool`].
//!
//! Split from `bv_model.rs` for code health (#7006, #5970).

#[cfg(not(kani))]
use hashbrown::HashMap;
#[cfg(kani)]
use z4_core::kani_compat::DetHashMap as HashMap;
use z4_core::term::{Symbol, TermData};
use z4_core::{Sort, TermId, TermStore};

use super::super::Executor;

/// Red zone size for `stacker::maybe_grow` in BV model evaluation (#4602).
const EVAL_BV_STACK_RED_ZONE: usize = if cfg!(debug_assertions) {
    128 * 1024
} else {
    32 * 1024
};

/// Stack segment size allocated by stacker for BV model evaluation recursion.
const EVAL_BV_STACK_SIZE: usize = 2 * 1024 * 1024;

impl Executor {
    /// Evaluate a bitvector expression under the current model values (#1789).
    ///
    /// This handles expressions like `(bvadd x #x05)` where `x` has a value in the model.
    /// Returns None if the expression cannot be evaluated (e.g., missing variable values).
    /// Uses `stacker::maybe_grow` for stack safety on deeply nested terms (#4602).
    pub(crate) fn evaluate_bv_expr(
        terms: &TermStore,
        term: TermId,
        values: &HashMap<TermId, num_bigint::BigInt>,
    ) -> Option<num_bigint::BigInt> {
        use num_bigint::BigInt;

        stacker::maybe_grow(EVAL_BV_STACK_RED_ZONE, EVAL_BV_STACK_SIZE, || {
            match terms.get(term) {
                // Variable: look up in values
                TermData::Var(_, _) => values.get(&term).cloned(),

                // Constant: extract value directly
                TermData::Const(z4_core::term::Constant::BitVec { value, .. }) => {
                    Some(value.clone())
                }

                // Function application: evaluate based on operation
                TermData::App(sym, args) => {
                    let Sort::BitVec(bv) = terms.sort(term) else {
                        return None;
                    };
                    let width = bv.width;
                    let modulus = BigInt::from(1u64) << width;
                    let name = sym.name();

                    match name {
                        "bvadd" => {
                            let mut sum = BigInt::from(0u64);
                            for &arg in args {
                                let val = Self::evaluate_bv_expr(terms, arg, values)?;
                                sum = (sum + val) % &modulus;
                            }
                            Some(sum)
                        }
                        "bvsub" => {
                            if args.len() != 2 {
                                return None;
                            }
                            let a = Self::evaluate_bv_expr(terms, args[0], values)?;
                            let b = Self::evaluate_bv_expr(terms, args[1], values)?;
                            // Two's complement subtraction
                            Some((&modulus + a - b) % &modulus)
                        }
                        "bvmul" => {
                            let mut product = BigInt::from(1u64);
                            for &arg in args {
                                let val = Self::evaluate_bv_expr(terms, arg, values)?;
                                product = (product * val) % &modulus;
                            }
                            Some(product)
                        }
                        "bvneg" => {
                            if args.len() != 1 {
                                return None;
                            }
                            let val = Self::evaluate_bv_expr(terms, args[0], values)?;
                            // Two's complement negation
                            Some((&modulus - val) % &modulus)
                        }
                        "bvand" => {
                            if args.is_empty() {
                                return Some((BigInt::from(1u64) << width) - 1);
                            }
                            let mut result = Self::evaluate_bv_expr(terms, args[0], values)?;
                            for &arg in &args[1..] {
                                let val = Self::evaluate_bv_expr(terms, arg, values)?;
                                result &= val;
                            }
                            Some(result)
                        }
                        "bvor" => {
                            if args.is_empty() {
                                return Some(BigInt::from(0u64));
                            }
                            let mut result = Self::evaluate_bv_expr(terms, args[0], values)?;
                            for &arg in &args[1..] {
                                let val = Self::evaluate_bv_expr(terms, arg, values)?;
                                result |= val;
                            }
                            Some(result)
                        }
                        "bvxor" => {
                            if args.is_empty() {
                                return Some(BigInt::from(0u64));
                            }
                            let mut result = Self::evaluate_bv_expr(terms, args[0], values)?;
                            for &arg in &args[1..] {
                                let val = Self::evaluate_bv_expr(terms, arg, values)?;
                                result ^= val;
                            }
                            Some(result)
                        }
                        "bvnot" => {
                            if args.len() != 1 {
                                return None;
                            }
                            let val = Self::evaluate_bv_expr(terms, args[0], values)?;
                            // Bitwise NOT (XOR with all 1s)
                            let all_ones = (BigInt::from(1u64) << width) - 1;
                            Some(val ^ all_ones)
                        }
                        // Division and remainder operations (#1792)
                        "bvudiv" => {
                            if args.len() != 2 {
                                return None;
                            }
                            let a = Self::evaluate_bv_expr(terms, args[0], values)?;
                            let b = Self::evaluate_bv_expr(terms, args[1], values)?;
                            // bvudiv semantics: if b == 0, result is all 1s
                            if b == BigInt::from(0u64) {
                                Some((BigInt::from(1u64) << width) - 1)
                            } else {
                                Some(&a / &b)
                            }
                        }
                        "bvurem" => {
                            if args.len() != 2 {
                                return None;
                            }
                            let a = Self::evaluate_bv_expr(terms, args[0], values)?;
                            let b = Self::evaluate_bv_expr(terms, args[1], values)?;
                            // bvurem semantics: if b == 0, result is a
                            if b == BigInt::from(0u64) {
                                Some(a)
                            } else {
                                Some(&a % &b)
                            }
                        }
                        "bvsdiv" => {
                            if args.len() != 2 {
                                return None;
                            }
                            let a = Self::evaluate_bv_expr(terms, args[0], values)?;
                            let b = Self::evaluate_bv_expr(terms, args[1], values)?;
                            // Convert to signed, divide, convert back to unsigned
                            let half = BigInt::from(1u64) << (width - 1);
                            let signed_a = if a >= half { &a - &modulus } else { a };
                            let signed_b = if b >= half { &b - &modulus } else { b };
                            // bvsdiv semantics: if b == 0, result depends on sign of a
                            if signed_b == BigInt::from(0i64) {
                                if signed_a >= BigInt::from(0i64) {
                                    Some((BigInt::from(1u64) << width) - 1) // -1 unsigned
                                } else {
                                    Some(BigInt::from(1u64)) // 1
                                }
                            } else {
                                let result = &signed_a / &signed_b;
                                // Convert back to unsigned
                                Some(if result < BigInt::from(0i64) {
                                    (result + &modulus) % &modulus
                                } else {
                                    result % &modulus
                                })
                            }
                        }
                        "bvsrem" => {
                            if args.len() != 2 {
                                return None;
                            }
                            let a = Self::evaluate_bv_expr(terms, args[0], values)?;
                            let b = Self::evaluate_bv_expr(terms, args[1], values)?;
                            // Convert to signed
                            let half = BigInt::from(1u64) << (width - 1);
                            let signed_a = if a >= half { &a - &modulus } else { a.clone() };
                            let signed_b = if b >= half { &b - &modulus } else { b };
                            // bvsrem semantics: if b == 0, result is a
                            if signed_b == BigInt::from(0i64) {
                                Some(a)
                            } else {
                                // Sign of remainder matches sign of dividend
                                let result = &signed_a % &signed_b;
                                Some(if result < BigInt::from(0i64) {
                                    (result + &modulus) % &modulus
                                } else {
                                    result % &modulus
                                })
                            }
                        }
                        "bvsmod" => {
                            if args.len() != 2 {
                                return None;
                            }
                            let a = Self::evaluate_bv_expr(terms, args[0], values)?;
                            let b = Self::evaluate_bv_expr(terms, args[1], values)?;
                            // Convert to signed
                            let half = BigInt::from(1u64) << (width - 1);
                            let signed_a = if a >= half { &a - &modulus } else { a.clone() };
                            let signed_b = if b >= half { &b - &modulus } else { b };
                            // bvsmod semantics: if b == 0, result is a
                            if signed_b == BigInt::from(0i64) {
                                Some(a)
                            } else {
                                // Sign of result matches sign of divisor (different from bvsrem)
                                let rem = &signed_a % &signed_b;
                                let result = if rem != BigInt::from(0i64)
                                    && ((signed_a < BigInt::from(0i64))
                                        != (signed_b < BigInt::from(0i64)))
                                {
                                    rem + &signed_b
                                } else {
                                    rem
                                };
                                Some(if result < BigInt::from(0i64) {
                                    (result + &modulus) % &modulus
                                } else {
                                    result % &modulus
                                })
                            }
                        }
                        // Concat operation (#1790)
                        // concat combines high bits (first arg) with low bits (second arg)
                        "concat" => {
                            if args.len() != 2 {
                                return None;
                            }
                            let high = Self::evaluate_bv_expr(terms, args[0], values)?;
                            let low = Self::evaluate_bv_expr(terms, args[1], values)?;
                            // Get the width of the low part to know how much to shift
                            let Sort::BitVec(low_bv) = terms.sort(args[1]) else {
                                return None;
                            };
                            // Result = (high << low_width) | low
                            Some((high << low_bv.width) | low)
                        }
                        // Extract operation: ((_ extract hi lo) x) extracts bits hi..lo from x
                        "extract" => {
                            if args.len() != 1 {
                                return None;
                            }
                            // Get the extract indices from the indexed symbol
                            // The symbol should be Indexed("extract", [hi, lo])
                            if let Symbol::Indexed(_, indices) = sym {
                                if indices.len() != 2 {
                                    return None;
                                }
                                let hi = indices[0] as usize;
                                let lo = indices[1] as usize;
                                let val = Self::evaluate_bv_expr(terms, args[0], values)?;
                                // Extract bits hi..lo (inclusive)
                                let mask = (BigInt::from(1u64) << (hi - lo + 1)) - 1;
                                Some((val >> lo) & mask)
                            } else {
                                None
                            }
                        }
                        // Rotate left: (_ rotate_left n)
                        "rotate_left" => {
                            if args.len() != 1 {
                                return None;
                            }
                            if let Symbol::Indexed(_, indices) = sym {
                                let n = *indices.first()? as usize;
                                let val = Self::evaluate_bv_expr(terms, args[0], values)?;
                                if width == 0 {
                                    return Some(val);
                                }
                                let k = n % width as usize;
                                if k == 0 {
                                    return Some(val);
                                }
                                let left = (&val << k) % &modulus;
                                let right = &val >> (width as usize - k);
                                Some(left | right)
                            } else {
                                None
                            }
                        }
                        // Rotate right: (_ rotate_right n)
                        "rotate_right" => {
                            if args.len() != 1 {
                                return None;
                            }
                            if let Symbol::Indexed(_, indices) = sym {
                                let n = *indices.first()? as usize;
                                let val = Self::evaluate_bv_expr(terms, args[0], values)?;
                                if width == 0 {
                                    return Some(val);
                                }
                                let k = n % width as usize;
                                if k == 0 {
                                    return Some(val);
                                }
                                let right = &val >> k;
                                let left = (&val << (width as usize - k)) % &modulus;
                                Some(left | right)
                            } else {
                                None
                            }
                        }
                        // Sign extend: (_ sign_extend n) — extend to width by
                        // replicating the sign bit of the original value (#5627).
                        "sign_extend" => {
                            if args.len() != 1 {
                                return None;
                            }
                            let val = Self::evaluate_bv_expr(terms, args[0], values)?;
                            let Sort::BitVec(orig_bv) = terms.sort(args[0]) else {
                                return None;
                            };
                            let orig_width = orig_bv.width;
                            if orig_width == 0 {
                                return Some(BigInt::from(0u64));
                            }
                            // Normalize to original width range
                            let orig_modulus = BigInt::from(1u64) << orig_width;
                            let normalized =
                                ((&val % &orig_modulus) + &orig_modulus) % &orig_modulus;
                            // Convert to signed at original width
                            let sign_bit = BigInt::from(1u64) << (orig_width - 1);
                            let signed = if normalized >= sign_bit {
                                &normalized - &orig_modulus
                            } else {
                                normalized
                            };
                            // Normalize to result width (unsigned)
                            Some(((&signed % &modulus) + &modulus) % &modulus)
                        }
                        // Zero extend: (_ zero_extend n) — pad with zeros (#5627).
                        "zero_extend" => {
                            if args.len() != 1 {
                                return None;
                            }
                            Self::evaluate_bv_expr(terms, args[0], values)
                        }
                        // Repeat: (_ repeat n) — concatenate n copies (#5627).
                        "repeat" => {
                            if args.len() != 1 {
                                return None;
                            }
                            if let Symbol::Indexed(_, indices) = sym {
                                let count = *indices.first()? as usize;
                                let val = Self::evaluate_bv_expr(terms, args[0], values)?;
                                let Sort::BitVec(orig_bv) = terms.sort(args[0]) else {
                                    return None;
                                };
                                let orig_width = orig_bv.width as usize;
                                let mut result = val.clone();
                                for _ in 1..count {
                                    result = (&result << orig_width) | &val;
                                }
                                Some(result)
                            } else {
                                None
                            }
                        }
                        // Shift left: bvshl (#5115)
                        "bvshl" => {
                            if args.len() != 2 {
                                return None;
                            }
                            let val = Self::evaluate_bv_expr(terms, args[0], values)?;
                            let shift = Self::evaluate_bv_expr(terms, args[1], values)?;
                            let shift_u32: u32 = shift.try_into().unwrap_or(width);
                            if shift_u32 >= width {
                                Some(BigInt::from(0u64))
                            } else {
                                Some((&val << shift_u32 as usize) % &modulus)
                            }
                        }
                        // Logical shift right: bvlshr (#5115)
                        "bvlshr" => {
                            if args.len() != 2 {
                                return None;
                            }
                            let val = Self::evaluate_bv_expr(terms, args[0], values)?;
                            let shift = Self::evaluate_bv_expr(terms, args[1], values)?;
                            let shift_u32: u32 = shift.try_into().unwrap_or(width);
                            if shift_u32 >= width {
                                Some(BigInt::from(0u64))
                            } else {
                                Some(&val >> shift_u32 as usize)
                            }
                        }
                        // Arithmetic shift right: bvashr (#5115)
                        "bvashr" => {
                            if args.len() != 2 {
                                return None;
                            }
                            let val = Self::evaluate_bv_expr(terms, args[0], values)?;
                            let shift = Self::evaluate_bv_expr(terms, args[1], values)?;
                            let shift_u32: u32 = shift.try_into().unwrap_or(width);
                            // Convert to signed
                            let half = BigInt::from(1u64) << (width - 1);
                            let signed = if val >= half { &val - &modulus } else { val };
                            if shift_u32 >= width {
                                // Fill with sign bit
                                if signed < BigInt::from(0i64) {
                                    Some(&modulus - 1) // all 1s
                                } else {
                                    Some(BigInt::from(0u64))
                                }
                            } else {
                                let result = &signed >> shift_u32 as usize;
                                Some(((&result % &modulus) + &modulus) % &modulus)
                            }
                        }
                        // Bitwise NAND/NOR/XNOR (#5115)
                        "bvnand" => {
                            if args.len() != 2 {
                                return None;
                            }
                            let a = Self::evaluate_bv_expr(terms, args[0], values)?;
                            let b = Self::evaluate_bv_expr(terms, args[1], values)?;
                            let all_ones = (BigInt::from(1u64) << width) - 1;
                            Some((&a & &b) ^ &all_ones)
                        }
                        "bvnor" => {
                            if args.len() != 2 {
                                return None;
                            }
                            let a = Self::evaluate_bv_expr(terms, args[0], values)?;
                            let b = Self::evaluate_bv_expr(terms, args[1], values)?;
                            let all_ones = (BigInt::from(1u64) << width) - 1;
                            Some((&a | &b) ^ &all_ones)
                        }
                        "bvxnor" => {
                            if args.len() != 2 {
                                return None;
                            }
                            let a = Self::evaluate_bv_expr(terms, args[0], values)?;
                            let b = Self::evaluate_bv_expr(terms, args[1], values)?;
                            let all_ones = (BigInt::from(1u64) << width) - 1;
                            Some((&a ^ &b) ^ &all_ones)
                        }
                        // bvcomp: 1-bit equality comparison (#5115)
                        "bvcomp" => {
                            if args.len() != 2 {
                                return None;
                            }
                            let a = Self::evaluate_bv_expr(terms, args[0], values)?;
                            let b = Self::evaluate_bv_expr(terms, args[1], values)?;
                            Some(if a == b {
                                BigInt::from(1u64)
                            } else {
                                BigInt::from(0u64)
                            })
                        }
                        // ITE for BV-sorted results (#5115)
                        "ite" => {
                            if args.len() != 3 {
                                return None;
                            }
                            // Condition is Bool, evaluate using bool evaluator
                            let cond = Self::evaluate_bv_bool_predicate(terms, args[0], values)?;
                            let branch = if cond { args[1] } else { args[2] };
                            Self::evaluate_bv_expr(terms, branch, values)
                        }
                        _ => None, // Unsupported operation
                    }
                }
                _ => None,
            }
        }) // stacker::maybe_grow
    }
}
