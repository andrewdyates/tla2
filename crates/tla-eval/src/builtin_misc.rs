// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::{
    check_arity, eval, extract_dyadic, make_dyadic_rational, reduce_fraction, EvalCtx, EvalError,
    EvalResult, Expr, Span, Spanned, Value,
};
use crate::value::intern_string;
use num_traits::ToPrimitive;
// Built-in DyadicRationals, TLAPS, and Bitwise module operators

pub(super) fn eval_builtin_misc(
    ctx: &EvalCtx,
    name: &str,
    args: &[Spanned<Expr>],
    span: Option<Span>,
) -> EvalResult<Option<Value>> {
    match name {
        // === DyadicRationals module ===
        // Dyadic rationals are fractions with denominator = 2^n
        // Represented as records [num |-> n, den |-> d]

        // Zero - the zero dyadic rational [num |-> 0, den |-> 1]
        "Zero" if args.is_empty() => Ok(Some(make_dyadic_rational(0, 1))),

        // One - the one dyadic rational [num |-> 1, den |-> 1]
        "One" if args.is_empty() => Ok(Some(make_dyadic_rational(1, 1))),

        // IsDyadicRational(r) - check if r.den is a power of 2
        "IsDyadicRational" => {
            check_arity(name, args, 1, span)?;
            let rv = eval(ctx, &args[0])?;
            // Dyadic rationals are records with num and den fields
            let is_dyadic = if let Some(rec) = rv.as_record() {
                if let (Some(den_val), Some(_num_val)) = (rec.get("den"), rec.get("num")) {
                    if let Some(den) = den_val.to_bigint() {
                        let den_i64 = den.to_i64().unwrap_or(0);
                        // Check if den is a power of 2 (including 1 = 2^0)
                        den_i64 > 0 && (den_i64 & (den_i64 - 1)) == 0
                    } else {
                        false
                    }
                } else {
                    false
                }
            } else {
                false
            };
            Ok(Some(Value::Bool(is_dyadic)))
        }

        // Add(p, q) - add two dyadic rationals
        "Add" => {
            check_arity(name, args, 2, span)?;
            let pv = eval(ctx, &args[0])?;
            let qv = eval(ctx, &args[1])?;

            // Extract num/den from both records
            let (p_num, p_den) = extract_dyadic(&pv, span)?;
            let (q_num, q_den) = extract_dyadic(&qv, span)?;

            // Short circuit: if p is zero, return q
            if p_num == 0 {
                return Ok(Some(qv));
            }

            // For dyadic rationals, LCM of denominators is just the max
            let lcm = std::cmp::max(p_den, q_den);

            // Scale both fractions to have the same denominator
            let p_scaled = p_num * (lcm / p_den);
            let q_scaled = q_num * (lcm / q_den);

            // Add numerators
            let sum_num = p_scaled + q_scaled;

            // Reduce the fraction
            let (reduced_num, reduced_den) = reduce_fraction(sum_num, lcm);

            Ok(Some(make_dyadic_rational(reduced_num, reduced_den)))
        }

        // Half(p) - divide by 2 (double the denominator)
        "Half" => {
            check_arity(name, args, 1, span)?;
            let pv = eval(ctx, &args[0])?;
            let (num, den) = extract_dyadic(&pv, span)?;

            // Double the denominator and reduce
            let (reduced_num, reduced_den) = reduce_fraction(num, den * 2);

            Ok(Some(make_dyadic_rational(reduced_num, reduced_den)))
        }

        // PrettyPrint(p) - string representation of dyadic rational
        "PrettyPrint" => {
            check_arity(name, args, 1, span)?;
            let pv = eval(ctx, &args[0])?;
            let (num, den) = extract_dyadic(&pv, span)?;

            let s = if num == 0 {
                "0".to_string()
            } else if den == 1 {
                num.to_string()
            } else {
                format!("{num}/{den}")
            };

            Ok(Some(Value::String(intern_string(&s))))
        }

        // === TLAPS (TLA+ Proof System) Operators ===
        // All TLAPS operators return TRUE - they are proof backend pragmas
        // that TLC ignores during model checking.

        // Zero-arity TLAPS operators (SMT solvers, provers, tactics)
        "SMT"
        | "CVC3"
        | "Yices"
        | "veriT"
        | "Z3"
        | "Spass"
        | "SimpleArithmetic"
        | "Zenon"
        | "SlowZenon"
        | "SlowerZenon"
        | "VerySlowZenon"
        | "SlowestZenon"
        | "Isa"
        | "Auto"
        | "Force"
        | "Blast"
        | "SimplifyAndSolve"
        | "Simplification"
        | "AutoBlast"
        | "LS4"
        | "PTL"
        | "PropositionalTemporalLogic"
        | "AllProvers"
        | "AllSMT"
        | "AllIsa"
        | "SetExtensionality"
        | "NoSetContainsEverything"
        | "IsaWithSetExtensionality" => {
            if args.is_empty() {
                return Ok(Some(Value::Bool(true)));
            }
            // If called with args, fall through to Ok(None) for error handling
            Ok(None)
        }

        // Parameterized TLAPS operators - take 1 arg (timeout or tactic), return TRUE
        "SMTT" | "CVC3T" | "YicesT" | "veriTT" | "Z3T" | "SpassT" | "ZenonT" | "IsaT" | "IsaM"
        | "AllProversT" | "AllSMTT" | "AllIsaT" => {
            if args.len() == 1 {
                // Evaluate arg for side effects, but ignore the value
                let _ = eval(ctx, &args[0])?;
                return Ok(Some(Value::Bool(true)));
            }
            // Wrong arity - fall through for error
            Ok(None)
        }

        // IsaMT takes 2 args (tactic, timeout)
        "IsaMT" => {
            if args.len() == 2 {
                let _ = eval(ctx, &args[0])?;
                let _ = eval(ctx, &args[1])?;
                return Ok(Some(Value::Bool(true)));
            }
            Ok(None)
        }
        // === Bitwise Module (CommunityModules) ===

        // ^^ - bitwise XOR (infix)
        "^^" => {
            check_arity(name, args, 2, span)?;
            let a = eval(ctx, &args[0])?;
            let av = a
                .to_bigint()
                .ok_or_else(|| EvalError::type_error("Int", &a, Some(args[0].span)))?;
            let b = eval(ctx, &args[1])?;
            let bv = b
                .to_bigint()
                .ok_or_else(|| EvalError::type_error("Int", &b, Some(args[1].span)))?;
            // Use signed BigInt XOR which performs bitwise XOR
            // For non-negative integers, this gives the standard result
            Ok(Some(Value::big_int(av ^ bv)))
        }

        // & - bitwise AND (infix)
        "&" => {
            check_arity(name, args, 2, span)?;
            let a = eval(ctx, &args[0])?;
            let av = a
                .to_bigint()
                .ok_or_else(|| EvalError::type_error("Int", &a, Some(args[0].span)))?;
            let b = eval(ctx, &args[1])?;
            let bv = b
                .to_bigint()
                .ok_or_else(|| EvalError::type_error("Int", &b, Some(args[1].span)))?;
            Ok(Some(Value::big_int(av & bv)))
        }

        // | - bitwise OR (infix)
        "|" => {
            check_arity(name, args, 2, span)?;
            let a = eval(ctx, &args[0])?;
            let av = a
                .to_bigint()
                .ok_or_else(|| EvalError::type_error("Int", &a, Some(args[0].span)))?;
            let b = eval(ctx, &args[1])?;
            let bv = b
                .to_bigint()
                .ok_or_else(|| EvalError::type_error("Int", &b, Some(args[1].span)))?;
            Ok(Some(Value::big_int(av | bv)))
        }

        // Not(a) - bitwise NOT
        // Note: BigInt NOT is -(a+1) which gives two's complement behavior.
        // For TLA+ Bitwise module compatibility, we compute !a for non-negative a
        // as a pattern that inverts all set bits up to the highest bit position.
        // However, the standard TLA+ Bitwise module Not operation returns -(a+1).
        "Not" => {
            check_arity(name, args, 1, span)?;
            let a = eval(ctx, &args[0])?;
            let av = a
                .to_bigint()
                .ok_or_else(|| EvalError::type_error("Int", &a, Some(args[0].span)))?;
            // BigInt bitwise NOT: !a = -(a + 1) (two's complement)
            Ok(Some(Value::big_int(!av)))
        }

        // shiftR(n, pos) - logical right shift
        "shiftR" => {
            check_arity(name, args, 2, span)?;
            let n = eval(ctx, &args[0])?;
            let nv = n
                .to_bigint()
                .ok_or_else(|| EvalError::type_error("Int", &n, Some(args[0].span)))?;
            let pos = eval(ctx, &args[1])?;
            let posv = pos
                .to_bigint()
                .ok_or_else(|| EvalError::type_error("Int", &pos, Some(args[1].span)))?;
            // Convert pos to u64 for shift (TLA+ should only use reasonable shift amounts)
            use num_traits::ToPrimitive;
            let shift = posv.to_u64().ok_or_else(|| EvalError::Internal {
                message: format!("shiftR position {posv} is too large"),
                span,
            })?;
            Ok(Some(Value::big_int(nv >> shift)))
        }

        // Not handled by this domain
        _ => Ok(None),
    }
}
