// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Floating-point evaluation helpers for model evaluation.
//!
//! Extracted from `mod.rs` to reduce file size (Wave C1 of #2998 module splits).
//! All methods are `impl Executor` — they share the same method namespace.

use num_bigint::BigInt;
use num_traits::{One, ToPrimitive, Zero};
use z4_core::term::{Symbol, TermData};
use z4_core::{Sort, TermId};
use z4_fp::FpModelValue;

use super::{EvalValue, Executor, Model};

impl Executor {
    fn is_rne_rounding_mode(&self, rm_term: TermId) -> bool {
        match self.ctx.terms.get(rm_term) {
            TermData::App(sym, _) if sym.name() == "RNE" => true,
            TermData::Var(name, _) if name == "RNE" => true,
            _ => false,
        }
    }

    /// Convert an `f64` result back to an `EvalValue::Fp`, inheriting the
    /// format (eb, sb) from a reference operand. Returns `Unknown` for
    /// formats wider than Float64 (eb=11, sb=53).
    fn f64_to_fp_eval(&self, val: f64, reference: &FpModelValue) -> EvalValue {
        let eb = reference.eb();
        let sb = reference.sb();
        if eb > 11 || sb > 53 {
            return EvalValue::Unknown;
        }
        if val.is_nan() {
            return EvalValue::Fp(FpModelValue::NaN { eb, sb });
        }
        if val.is_infinite() {
            return if val.is_sign_positive() {
                EvalValue::Fp(FpModelValue::PosInf { eb, sb })
            } else {
                EvalValue::Fp(FpModelValue::NegInf { eb, sb })
            };
        }
        if val == 0.0 {
            return if val.is_sign_negative() {
                EvalValue::Fp(FpModelValue::NegZero { eb, sb })
            } else {
                EvalValue::Fp(FpModelValue::PosZero { eb, sb })
            };
        }
        // Decompose into IEEE 754 components
        let bits = val.to_bits();
        let sign = (bits >> 63) != 0;
        let f64_exp = ((bits >> 52) & 0x7FF) as i64;
        let f64_frac = bits & 0x000F_FFFF_FFFF_FFFF;

        let bias = (1i64 << (eb - 1)) - 1;
        let stored_bits = sb - 1;

        if f64_exp == 0 {
            // Subnormal in f64 — try to represent in target format
            // The actual exponent is 1 - 1023 = -1022 for f64 subnormals
            let f64_bias: i64 = 1023;
            let actual_exp = 1 - f64_bias;
            let target_exp_biased = actual_exp + bias;
            if target_exp_biased <= 0 {
                // Subnormal in target format too
                let shift = i64::from(stored_bits) - 52 + (1 - target_exp_biased);
                let sig = if shift >= 0 {
                    f64_frac << shift as u64
                } else {
                    f64_frac >> (-shift) as u64
                };
                EvalValue::Fp(FpModelValue::Fp {
                    sign,
                    exponent: 0,
                    significand: sig,
                    eb,
                    sb,
                })
            } else {
                // Normalizes in target format — punt to Unknown for now
                EvalValue::Unknown
            }
        } else {
            // Normal in f64
            let f64_bias: i64 = 1023;
            let actual_exp = f64_exp - f64_bias;
            let target_exp_biased = actual_exp + bias;
            let max_exp = (1i64 << eb) - 1;
            if target_exp_biased >= max_exp {
                // Overflow to infinity in target format
                return if sign {
                    EvalValue::Fp(FpModelValue::NegInf { eb, sb })
                } else {
                    EvalValue::Fp(FpModelValue::PosInf { eb, sb })
                };
            }
            if target_exp_biased <= 0 {
                // Underflow to subnormal or zero in target format
                // Shift significand right by (1 - target_exp_biased) places
                let hidden = 1u64 << 52;
                let full_sig = f64_frac | hidden;
                let right_shift = (1 - target_exp_biased) as u64;
                let shift_to_target = if stored_bits >= 52 {
                    i64::from(stored_bits - 52)
                } else {
                    -i64::from(52 - stored_bits)
                };
                let sig = if shift_to_target >= 0 {
                    (full_sig >> right_shift) << shift_to_target as u64
                } else {
                    full_sig >> (right_shift + (-shift_to_target) as u64)
                };
                if sig == 0 {
                    return if sign {
                        EvalValue::Fp(FpModelValue::NegZero { eb, sb })
                    } else {
                        EvalValue::Fp(FpModelValue::PosZero { eb, sb })
                    };
                }
                return EvalValue::Fp(FpModelValue::Fp {
                    sign,
                    exponent: 0,
                    significand: sig,
                    eb,
                    sb,
                });
            }
            // Normal in target format: shift significand with RNE rounding (#6203)
            let sig = if stored_bits >= 52 {
                f64_frac << (stored_bits - 52)
            } else {
                let shift = 52 - stored_bits;
                let truncated = f64_frac >> shift;
                // RNE: check guard, round, sticky bits
                let guard = (f64_frac >> (shift - 1)) & 1;
                let sticky = if shift >= 2 {
                    (f64_frac & ((1u64 << (shift - 1)) - 1)) != 0
                } else {
                    false
                };
                // Round up if: guard=1 AND (sticky=1 OR truncated is odd)
                if guard == 1 && (sticky || (truncated & 1) == 1) {
                    truncated + 1
                } else {
                    truncated
                }
            };
            // Handle significand overflow from rounding (e.g., 0b1111...1 + 1)
            let max_sig = (1u64 << stored_bits) - 1;
            if sig > max_sig {
                let new_exp = target_exp_biased + 1;
                if new_exp >= max_exp {
                    return if sign {
                        EvalValue::Fp(FpModelValue::NegInf { eb, sb })
                    } else {
                        EvalValue::Fp(FpModelValue::PosInf { eb, sb })
                    };
                }
                EvalValue::Fp(FpModelValue::Fp {
                    sign,
                    exponent: new_exp as u64,
                    significand: 0, // carry into exponent
                    eb,
                    sb,
                })
            } else {
                EvalValue::Fp(FpModelValue::Fp {
                    sign,
                    exponent: target_exp_biased as u64,
                    significand: sig,
                    eb,
                    sb,
                })
            }
        }
    }

    /// Evaluate a floating-point application term.
    ///
    /// Handles all `fp.*` operations, `fp` constructor, `to_fp`, `to_fp_unsigned`,
    /// and FP conversion operations (`fp.to_ubv`, `fp.to_sbv`, `fp.to_real`, `fp.to_ieee_bv`).
    pub(super) fn evaluate_fp_app(
        &self,
        model: &Model,
        _sym: &Symbol,
        name: &str,
        args: &[TermId],
        sort: &Sort,
        _term_id: TermId,
    ) -> EvalValue {
        match name {
            // ===== Floating-point operations (Part of #5995) =====

            // FP classification predicates
            "fp.isNaN" if args.len() == 1 => match self.evaluate_term(model, args[0]) {
                EvalValue::Fp(v) => EvalValue::Bool(v.is_nan()),
                _ => EvalValue::Unknown,
            },
            "fp.isInfinite" if args.len() == 1 => match self.evaluate_term(model, args[0]) {
                EvalValue::Fp(v) => EvalValue::Bool(v.is_infinite()),
                _ => EvalValue::Unknown,
            },
            "fp.isZero" if args.len() == 1 => match self.evaluate_term(model, args[0]) {
                EvalValue::Fp(v) => EvalValue::Bool(v.is_zero()),
                _ => EvalValue::Unknown,
            },
            "fp.isNormal" if args.len() == 1 => match self.evaluate_term(model, args[0]) {
                EvalValue::Fp(v) => EvalValue::Bool(v.is_normal()),
                _ => EvalValue::Unknown,
            },
            "fp.isSubnormal" if args.len() == 1 => match self.evaluate_term(model, args[0]) {
                EvalValue::Fp(v) => EvalValue::Bool(v.is_subnormal()),
                _ => EvalValue::Unknown,
            },
            "fp.isPositive" if args.len() == 1 => match self.evaluate_term(model, args[0]) {
                EvalValue::Fp(v) => EvalValue::Bool(v.is_positive()),
                _ => EvalValue::Unknown,
            },
            "fp.isNegative" if args.len() == 1 => match self.evaluate_term(model, args[0]) {
                EvalValue::Fp(v) => EvalValue::Bool(v.is_negative()),
                _ => EvalValue::Unknown,
            },

            // FP unary operations
            "fp.neg" if args.len() == 1 => match self.evaluate_term(model, args[0]) {
                EvalValue::Fp(v) => EvalValue::Fp(v.negate()),
                _ => EvalValue::Unknown,
            },
            "fp.abs" if args.len() == 1 => match self.evaluate_term(model, args[0]) {
                EvalValue::Fp(v) => EvalValue::Fp(v.abs()),
                _ => EvalValue::Unknown,
            },

            // FP comparison predicates (via f64 conversion)
            "fp.eq" if args.len() == 2 => {
                match (
                    self.evaluate_term(model, args[0]),
                    self.evaluate_term(model, args[1]),
                ) {
                    (EvalValue::Fp(a), EvalValue::Fp(b)) => EvalValue::Bool(a.fp_eq(&b)),
                    _ => EvalValue::Unknown,
                }
            }
            "fp.lt" if args.len() == 2 => {
                match (
                    self.evaluate_term(model, args[0]),
                    self.evaluate_term(model, args[1]),
                ) {
                    (EvalValue::Fp(a), EvalValue::Fp(b)) => {
                        a.fp_lt(&b).map_or(EvalValue::Unknown, EvalValue::Bool)
                    }
                    _ => EvalValue::Unknown,
                }
            }
            "fp.leq" if args.len() == 2 => {
                match (
                    self.evaluate_term(model, args[0]),
                    self.evaluate_term(model, args[1]),
                ) {
                    (EvalValue::Fp(a), EvalValue::Fp(b)) => {
                        a.fp_leq(&b).map_or(EvalValue::Unknown, EvalValue::Bool)
                    }
                    _ => EvalValue::Unknown,
                }
            }
            "fp.gt" if args.len() == 2 => {
                match (
                    self.evaluate_term(model, args[0]),
                    self.evaluate_term(model, args[1]),
                ) {
                    (EvalValue::Fp(a), EvalValue::Fp(b)) => {
                        a.fp_gt(&b).map_or(EvalValue::Unknown, EvalValue::Bool)
                    }
                    _ => EvalValue::Unknown,
                }
            }
            "fp.geq" if args.len() == 2 => {
                match (
                    self.evaluate_term(model, args[0]),
                    self.evaluate_term(model, args[1]),
                ) {
                    (EvalValue::Fp(a), EvalValue::Fp(b)) => {
                        a.fp_geq(&b).map_or(EvalValue::Unknown, EvalValue::Bool)
                    }
                    _ => EvalValue::Unknown,
                }
            }

            // FP arithmetic (via f64 conversion, rounding mode arg[0])
            // f64 natively uses RNE. For non-RNE rounding modes, we
            // cannot compute the correct result via f64, so return
            // Unknown to skip model validation (#6203).
            "fp.add" if args.len() == 3 => {
                if !self.is_rne_rounding_mode(args[0]) {
                    EvalValue::Unknown
                } else {
                    match (
                        self.evaluate_term(model, args[1]),
                        self.evaluate_term(model, args[2]),
                    ) {
                        (EvalValue::Fp(a), EvalValue::Fp(b)) => match (a.to_f64(), b.to_f64()) {
                            (Some(fa), Some(fb)) => self.f64_to_fp_eval(fa + fb, &a),
                            _ => EvalValue::Unknown,
                        },
                        _ => EvalValue::Unknown,
                    }
                }
            }
            "fp.sub" if args.len() == 3 => {
                if !self.is_rne_rounding_mode(args[0]) {
                    EvalValue::Unknown
                } else {
                    match (
                        self.evaluate_term(model, args[1]),
                        self.evaluate_term(model, args[2]),
                    ) {
                        (EvalValue::Fp(a), EvalValue::Fp(b)) => match (a.to_f64(), b.to_f64()) {
                            (Some(fa), Some(fb)) => self.f64_to_fp_eval(fa - fb, &a),
                            _ => EvalValue::Unknown,
                        },
                        _ => EvalValue::Unknown,
                    }
                }
            }
            "fp.mul" if args.len() == 3 => {
                if !self.is_rne_rounding_mode(args[0]) {
                    EvalValue::Unknown
                } else {
                    match (
                        self.evaluate_term(model, args[1]),
                        self.evaluate_term(model, args[2]),
                    ) {
                        (EvalValue::Fp(a), EvalValue::Fp(b)) => match (a.to_f64(), b.to_f64()) {
                            (Some(fa), Some(fb)) => self.f64_to_fp_eval(fa * fb, &a),
                            _ => EvalValue::Unknown,
                        },
                        _ => EvalValue::Unknown,
                    }
                }
            }
            "fp.div" if args.len() == 3 => {
                if !self.is_rne_rounding_mode(args[0]) {
                    EvalValue::Unknown
                } else {
                    match (
                        self.evaluate_term(model, args[1]),
                        self.evaluate_term(model, args[2]),
                    ) {
                        (EvalValue::Fp(a), EvalValue::Fp(b)) => match (a.to_f64(), b.to_f64()) {
                            (Some(fa), Some(fb)) => self.f64_to_fp_eval(fa / fb, &a),
                            _ => EvalValue::Unknown,
                        },
                        _ => EvalValue::Unknown,
                    }
                }
            }
            "fp.rem" if args.len() == 2 => {
                // fp.rem has no rounding mode argument
                match (
                    self.evaluate_term(model, args[0]),
                    self.evaluate_term(model, args[1]),
                ) {
                    (EvalValue::Fp(a), EvalValue::Fp(b)) => match (a.to_f64(), b.to_f64()) {
                        (Some(fa), Some(fb)) => self.f64_to_fp_eval(fa % fb, &a),
                        _ => EvalValue::Unknown,
                    },
                    _ => EvalValue::Unknown,
                }
            }
            "fp.sqrt" if args.len() == 2 => {
                // args[0] = rounding mode, args[1] = x
                if !self.is_rne_rounding_mode(args[0]) {
                    EvalValue::Unknown
                } else {
                    match self.evaluate_term(model, args[1]) {
                        EvalValue::Fp(a) => match a.to_f64() {
                            Some(fa) => self.f64_to_fp_eval(fa.sqrt(), &a),
                            None => EvalValue::Unknown,
                        },
                        _ => EvalValue::Unknown,
                    }
                }
            }
            "fp.min" if args.len() == 2 => {
                match (
                    self.evaluate_term(model, args[0]),
                    self.evaluate_term(model, args[1]),
                ) {
                    (EvalValue::Fp(a), EvalValue::Fp(b)) => match (a.to_f64(), b.to_f64()) {
                        (Some(fa), Some(fb)) => self.f64_to_fp_eval(fa.min(fb), &a),
                        _ => EvalValue::Unknown,
                    },
                    _ => EvalValue::Unknown,
                }
            }
            "fp.max" if args.len() == 2 => {
                match (
                    self.evaluate_term(model, args[0]),
                    self.evaluate_term(model, args[1]),
                ) {
                    (EvalValue::Fp(a), EvalValue::Fp(b)) => match (a.to_f64(), b.to_f64()) {
                        (Some(fa), Some(fb)) => self.f64_to_fp_eval(fa.max(fb), &a),
                        _ => EvalValue::Unknown,
                    },
                    _ => EvalValue::Unknown,
                }
            }
            "fp.roundToIntegral" if args.len() == 2 => {
                // args[0] = rounding mode, args[1] = x
                if !self.is_rne_rounding_mode(args[0]) {
                    EvalValue::Unknown
                } else {
                    match self.evaluate_term(model, args[1]) {
                        EvalValue::Fp(a) => match a.to_f64() {
                            Some(fa) => self.f64_to_fp_eval(fa.round(), &a),
                            None => EvalValue::Unknown,
                        },
                        _ => EvalValue::Unknown,
                    }
                }
            }
            "fp.fma" if args.len() == 4 => {
                // args[0] = rounding mode, args[1..3] = x, y, z
                // fma(x, y, z) = x * y + z
                if !self.is_rne_rounding_mode(args[0]) {
                    EvalValue::Unknown
                } else {
                    match (
                        self.evaluate_term(model, args[1]),
                        self.evaluate_term(model, args[2]),
                        self.evaluate_term(model, args[3]),
                    ) {
                        (EvalValue::Fp(a), EvalValue::Fp(b), EvalValue::Fp(c)) => {
                            match (a.to_f64(), b.to_f64(), c.to_f64()) {
                                (Some(fa), Some(fb), Some(fc)) => {
                                    self.f64_to_fp_eval(fa.mul_add(fb, fc), &a)
                                }
                                _ => EvalValue::Unknown,
                            }
                        }
                        _ => EvalValue::Unknown,
                    }
                }
            }

            // FP constructor: (fp #bS #bE #bM) → FpModelValue
            "fp" if args.len() == 3 => {
                let sign_val = match self.evaluate_term(model, args[0]) {
                    EvalValue::BitVec { value, width: 1 } => value != BigInt::zero(),
                    _ => return EvalValue::Unknown,
                };
                let exp_val = match self.evaluate_term(model, args[1]) {
                    EvalValue::BitVec { value, width } => (value.to_u64().unwrap_or(0), width),
                    _ => return EvalValue::Unknown,
                };
                let sig_val = match self.evaluate_term(model, args[2]) {
                    EvalValue::BitVec { value, width } => (value.to_u64().unwrap_or(0), width),
                    _ => return EvalValue::Unknown,
                };
                let eb = exp_val.1;
                let sb = sig_val.1 + 1; // SMT-LIB sb includes hidden bit
                let exponent = exp_val.0;
                let significand = sig_val.0;
                let max_exponent = (1u64 << eb) - 1;
                let fp_value = if exponent == max_exponent && significand != 0 {
                    FpModelValue::NaN { eb, sb }
                } else if exponent == max_exponent && significand == 0 {
                    if sign_val {
                        FpModelValue::NegInf { eb, sb }
                    } else {
                        FpModelValue::PosInf { eb, sb }
                    }
                } else if exponent == 0 && significand == 0 {
                    if sign_val {
                        FpModelValue::NegZero { eb, sb }
                    } else {
                        FpModelValue::PosZero { eb, sb }
                    }
                } else {
                    FpModelValue::Fp {
                        sign: sign_val,
                        exponent,
                        significand,
                        eb,
                        sb,
                    }
                };
                EvalValue::Fp(fp_value)
            }

            // (_ to_fp eb sb) from BV: reinterpret bitvector as IEEE 754
            "to_fp" if args.len() == 1 => {
                let Sort::FloatingPoint(eb, sb) = sort else {
                    return EvalValue::Unknown;
                };
                match self.evaluate_term(model, args[0]) {
                    EvalValue::BitVec { value, .. } => {
                        let total_bits = eb + sb;
                        let sign_val =
                            (value.clone() >> (total_bits - 1)) & BigInt::one() != BigInt::zero();
                        let exp_mask = (BigInt::one() << eb) - 1;
                        let exponent = ((value.clone() >> (sb - 1)) & &exp_mask)
                            .to_u64()
                            .unwrap_or(0);
                        let sig_mask = (BigInt::one() << (sb - 1)) - 1;
                        let significand = (&value & &sig_mask).to_u64().unwrap_or(0);
                        let max_exponent = (1u64 << eb) - 1;
                        let fp_value = if exponent == max_exponent && significand != 0 {
                            FpModelValue::NaN { eb: *eb, sb: *sb }
                        } else if exponent == max_exponent && significand == 0 {
                            if sign_val {
                                FpModelValue::NegInf { eb: *eb, sb: *sb }
                            } else {
                                FpModelValue::PosInf { eb: *eb, sb: *sb }
                            }
                        } else if exponent == 0 && significand == 0 {
                            if sign_val {
                                FpModelValue::NegZero { eb: *eb, sb: *sb }
                            } else {
                                FpModelValue::PosZero { eb: *eb, sb: *sb }
                            }
                        } else {
                            FpModelValue::Fp {
                                sign: sign_val,
                                exponent,
                                significand,
                                eb: *eb,
                                sb: *sb,
                            }
                        };
                        EvalValue::Fp(fp_value)
                    }
                    _ => EvalValue::Unknown,
                }
            }

            // (_ to_fp eb sb) from Real/Int: convert via f64
            // args[0] = rounding mode, args[1] = real/int value
            "to_fp" if args.len() == 2 => {
                if !self.is_rne_rounding_mode(args[0]) {
                    EvalValue::Unknown
                } else {
                    let Sort::FloatingPoint(eb, sb) = sort else {
                        return EvalValue::Unknown;
                    };
                    match self.evaluate_term(model, args[1]) {
                        EvalValue::Rational(r) => {
                            // Convert rational to f64, then to target FP format
                            let f = r.numer().to_f64().unwrap_or(f64::NAN)
                                / r.denom().to_f64().unwrap_or(1.0);
                            let reference = FpModelValue::PosZero { eb: *eb, sb: *sb };
                            self.f64_to_fp_eval(f, &reference)
                        }
                        EvalValue::Fp(v) => {
                            // to_fp from FP (cast between FP formats)
                            match v.to_f64() {
                                Some(f) => {
                                    let reference = FpModelValue::PosZero { eb: *eb, sb: *sb };
                                    self.f64_to_fp_eval(f, &reference)
                                }
                                None => EvalValue::Unknown,
                            }
                        }
                        _ => EvalValue::Unknown,
                    }
                }
            }

            // (_ to_fp_unsigned eb sb) : BV → FP
            // args[0] = rounding mode, args[1] = unsigned bitvector
            "to_fp_unsigned" if args.len() == 2 => {
                if !self.is_rne_rounding_mode(args[0]) {
                    EvalValue::Unknown
                } else {
                    let Sort::FloatingPoint(eb, sb) = sort else {
                        return EvalValue::Unknown;
                    };
                    match self.evaluate_term(model, args[1]) {
                        EvalValue::BitVec { value, .. } => {
                            // Interpret BV as unsigned integer, convert to f64
                            let f = value.to_f64().unwrap_or(f64::INFINITY);
                            let reference = FpModelValue::PosZero { eb: *eb, sb: *sb };
                            self.f64_to_fp_eval(f, &reference)
                        }
                        _ => EvalValue::Unknown,
                    }
                }
            }

            // (_ fp.to_ubv m) : FP → (_ BitVec m)
            // args[0] = rounding mode, args[1] = FP value
            "fp.to_ubv" if args.len() == 2 => {
                if !self.is_rne_rounding_mode(args[0]) {
                    return EvalValue::Unknown;
                }
                let Sort::BitVec(bv) = sort else {
                    return EvalValue::Unknown;
                };
                match self.evaluate_term(model, args[1]) {
                    EvalValue::Fp(v) => {
                        if v.is_nan() || v.is_infinite() {
                            return EvalValue::Unknown;
                        }
                        match v.to_f64() {
                            Some(f) => {
                                // RNE: round to nearest, ties to even
                                let rounded = f.round_ties_even();
                                if rounded < 0.0 {
                                    return EvalValue::Unknown; // negative → undefined for unsigned
                                }
                                let width = bv.width;
                                let max_val = (BigInt::one() << width as usize) - BigInt::one();
                                let int_val = BigInt::from(rounded as u64);
                                if int_val > max_val {
                                    return EvalValue::Unknown; // overflow
                                }
                                EvalValue::BitVec {
                                    value: int_val,
                                    width,
                                }
                            }
                            None => EvalValue::Unknown,
                        }
                    }
                    _ => EvalValue::Unknown,
                }
            }

            // (_ fp.to_sbv m) : FP → (_ BitVec m) (signed)
            // args[0] = rounding mode, args[1] = FP value
            "fp.to_sbv" if args.len() == 2 => {
                if !self.is_rne_rounding_mode(args[0]) {
                    return EvalValue::Unknown;
                }
                let Sort::BitVec(bv) = sort else {
                    return EvalValue::Unknown;
                };
                match self.evaluate_term(model, args[1]) {
                    EvalValue::Fp(v) => {
                        if v.is_nan() || v.is_infinite() {
                            return EvalValue::Unknown;
                        }
                        match v.to_f64() {
                            Some(f) => {
                                // RNE: round to nearest, ties to even
                                let rounded = f.round_ties_even();
                                let width = bv.width;
                                // Signed range: [-(2^(w-1)), 2^(w-1) - 1]
                                let min_val = -(BigInt::one() << (width as usize - 1));
                                let max_val =
                                    (BigInt::one() << (width as usize - 1)) - BigInt::one();
                                let int_val = BigInt::from(rounded as i64);
                                if int_val < min_val || int_val > max_val {
                                    return EvalValue::Unknown; // overflow
                                }
                                // Two's complement encoding
                                let modulus = BigInt::one() << width as usize;
                                let val = ((int_val % &modulus) + &modulus) % &modulus;
                                EvalValue::BitVec { value: val, width }
                            }
                            None => EvalValue::Unknown,
                        }
                    }
                    _ => EvalValue::Unknown,
                }
            }

            // fp.to_real : FP → Real
            "fp.to_real" if args.len() == 1 => {
                match self.evaluate_term(model, args[0]) {
                    EvalValue::Fp(v) => {
                        // Use to_rational() for exact conversion (not to_f64()
                        // which loses precision for values not representable
                        // as f64, e.g. Float128 subnormals).
                        match v.to_rational() {
                            Some(r) => EvalValue::Rational(r),
                            None => EvalValue::Unknown,
                        }
                    }
                    _ => EvalValue::Unknown,
                }
            }

            // fp.to_ieee_bv : FP → BV (bit-pattern reinterpretation)
            "fp.to_ieee_bv" if args.len() == 1 => match self.evaluate_term(model, args[0]) {
                EvalValue::Fp(v) => {
                    let (value, width) = v.to_ieee_bv();
                    EvalValue::BitVec { value, width }
                }
                _ => EvalValue::Unknown,
            },
            _ => EvalValue::Unknown,
        }
    }
}
