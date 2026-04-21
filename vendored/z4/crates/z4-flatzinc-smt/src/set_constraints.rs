// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Set constraint handlers for FlatZinc-to-SMT-LIB translation.
// Encodes `var set of lo..hi` using boolean decomposition:
// width = hi-lo+1 boolean variables `name__bit__0` .. `name__bit__(width-1)`.
// Element i in S iff `S__bit__(i-lo)` is true.
//
// This avoids the z4 model validation bug with mixed Int/BitVec theories.

use z4_flatzinc_parser::ast::Expr;

use crate::builtins::check_args;
use crate::error::TranslateError;
use crate::translate::{set_bit_name, Context};

/// Check whether element `e` is in a set literal (list of elements).
fn set_literal_contains(elements: &[i64], e: i64) -> bool {
    elements.contains(&e)
}

fn lookup_set_domain(
    ctx: &Context,
    set_name: &str,
    opname: &str,
) -> Result<(i64, i64), TranslateError> {
    ctx.set_vars.get(set_name).copied().ok_or_else(|| {
        TranslateError::UnknownIdentifier(format!("{opname}: {set_name} is not a set var"))
    })
}

pub(crate) fn set_membership_term(
    ctx: &Context,
    set_name: &str,
    value: i64,
    opname: &str,
) -> Result<String, TranslateError> {
    let (lo, hi) = lookup_set_domain(ctx, set_name, opname)?;
    if value < lo || value > hi {
        Ok("false".to_string())
    } else {
        Ok(set_bit_name(set_name, (value - lo) as u32))
    }
}

fn resolve_set_domain3(
    ctx: &Context,
    s1: &str,
    s2: &str,
    s3: &str,
    name: &str,
) -> Result<(i64, i64), TranslateError> {
    let (lo1, hi1) = lookup_set_domain(ctx, s1, name)?;
    let (lo2, hi2) = lookup_set_domain(ctx, s2, name)?;
    let (lo3, hi3) = lookup_set_domain(ctx, s3, name)?;
    Ok((lo1.min(lo2).min(lo3), hi1.max(hi2).max(hi3)))
}

/// `set_card(S, n)` → n = popcount(S)
/// Encodes as: n = sum of (ite S__bit__i 1 0) for each bit position.
pub(crate) fn set_card(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    check_args("set_card", args, 2)?;
    let s_name = ctx.expr_to_smt(&args[0])?;
    let n = ctx.expr_to_smt(&args[1])?;

    let (lo, hi) = ctx
        .set_vars
        .get(&s_name)
        .copied()
        .ok_or_else(|| TranslateError::UnknownIdentifier(s_name.clone()))?;
    let width = (hi - lo + 1) as u32;

    let terms: Vec<String> = (0..width)
        .map(|i| {
            let bit = set_bit_name(&s_name, i);
            format!("(ite {bit} 1 0)")
        })
        .collect();

    let sum = if terms.len() == 1 {
        terms[0].clone()
    } else {
        format!("(+ {})", terms.join(" "))
    };

    ctx.emit_fmt(format_args!("(assert (= {n} {sum}))"));
    Ok(())
}

/// `set_union(S1, S2, S3)` → for each bit: S3_bit_i = S1_bit_i or S2_bit_i
pub(crate) fn set_union(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    check_args("set_union", args, 3)?;
    let s1 = ctx.expr_to_smt(&args[0])?;
    let s2 = ctx.expr_to_smt(&args[1])?;
    let s3 = ctx.expr_to_smt(&args[2])?;

    let (lo, hi) = resolve_set_domain3(ctx, &s1, &s2, &s3, "set_union")?;

    for value in lo..=hi {
        let b1 = set_membership_term(ctx, &s1, value, "set_union")?;
        let b2 = set_membership_term(ctx, &s2, value, "set_union")?;
        let b3 = set_membership_term(ctx, &s3, value, "set_union")?;
        ctx.emit_fmt(format_args!("(assert (= {b3} (or {b1} {b2})))"));
    }
    Ok(())
}

/// `set_in_reif(elem, set_var, bool)` where set_var is a set variable.
/// `elem` is a constant integer, `set_var` is a `var set of lo..hi`.
/// Encodes: bool iff S__bit__(elem-lo).
pub(crate) fn set_in_reif_var(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    check_args("set_in_reif", args, 3)?;
    let elem = ctx.resolve_int(&args[0])?;
    let s_name = ctx.expr_to_smt(&args[1])?;
    let b = ctx.expr_to_smt(&args[2])?;

    let (lo, hi) = ctx
        .set_vars
        .get(&s_name)
        .copied()
        .ok_or_else(|| TranslateError::UnknownIdentifier(s_name.clone()))?;

    if elem < lo || elem > hi {
        ctx.emit_fmt(format_args!("(assert (not {b}))"));
        return Ok(());
    }

    let bit_pos = (elem - lo) as u32;
    let membership = set_bit_name(&s_name, bit_pos);

    ctx.emit_fmt(format_args!("(assert (=> {b} {membership}))"));
    ctx.emit_fmt(format_args!("(assert (=> {membership} {b}))"));
    Ok(())
}

/// `set_in(x, S)` where S is a set variable and x is a variable integer.
/// Encodes: (or (and (= x lo) S__bit__0) (and (= x lo+1) S__bit__1) ...)
pub(crate) fn set_in_var(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    check_args("set_in", args, 2)?;
    let x = ctx.expr_to_smt(&args[0])?;
    let s_name = ctx.expr_to_smt(&args[1])?;

    let (lo, hi) = ctx
        .set_vars
        .get(&s_name)
        .copied()
        .ok_or_else(|| TranslateError::UnknownIdentifier(s_name.clone()))?;

    let conjuncts: Vec<String> = (lo..=hi)
        .map(|v| {
            let bit = set_bit_name(&s_name, (v - lo) as u32);
            format!("(and (= {x} {v}) {bit})")
        })
        .collect();

    if conjuncts.len() == 1 {
        ctx.emit_fmt(format_args!("(assert {})", conjuncts[0]));
    } else {
        let joined = conjuncts.join(" ");
        ctx.emit_fmt(format_args!("(assert (or {joined}))"));
    }
    Ok(())
}

/// `array_set_element(idx, array_param, set_var)` where array_param is a
/// parameter array of set literals. For each bit position, builds an ITE chain
/// selecting the appropriate boolean value from the set literal at index `idx`.
pub(crate) fn array_set_element(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    check_args("array_set_element", args, 3)?;
    let idx = ctx.expr_to_smt(&args[0])?;
    let s_result = ctx.expr_to_smt(&args[2])?;

    let (lo, hi) = ctx
        .set_vars
        .get(&s_result)
        .copied()
        .ok_or_else(|| TranslateError::UnknownIdentifier(s_result.clone()))?;
    let width = (hi - lo + 1) as u32;

    let arr_name = match &args[1] {
        Expr::Ident(name) => name.clone(),
        _ => return Err(TranslateError::ExpectedArray),
    };
    let (arr_lo, _arr_hi, sets) = ctx
        .array_set_params
        .get(&arr_name)
        .ok_or_else(|| TranslateError::UnknownIdentifier(arr_name.clone()))?
        .clone();

    if sets.is_empty() {
        return Ok(());
    }

    let n = sets.len();

    // For each bit position, build an ITE chain selecting the boolean value.
    for bit in 0..width {
        let elem_val = lo + i64::from(bit);
        let result_bit = set_bit_name(&s_result, bit);

        // For each set literal in the array, check if elem_val is a member.
        let bool_vals: Vec<bool> = sets
            .iter()
            .map(|s| set_literal_contains(s, elem_val))
            .collect();

        let mut ite = if bool_vals[n - 1] {
            "true".to_string()
        } else {
            "false".to_string()
        };
        for i in (0..n - 1).rev() {
            let idx_val = arr_lo + i as i64;
            let val = if bool_vals[i] { "true" } else { "false" };
            ite = format!("(ite (= {idx} {idx_val}) {val} {ite})");
        }
        ctx.emit_fmt(format_args!("(assert (= {result_bit} {ite}))"));
    }
    Ok(())
}

/// Helper: 3-set bitwise operation.  S3_bit_i = op(S1_bit_i, S2_bit_i)
/// `smt_op` is the SMT-LIB operator applied per bit: "and", "or", "xor".
/// `complement_s2` wraps S2 bits in `(not ...)` when true (for set_diff).
fn set_bitwise_op(
    ctx: &mut Context,
    args: &[Expr],
    name: &str,
    smt_op: &str,
    complement_s2: bool,
) -> Result<(), TranslateError> {
    check_args(name, args, 3)?;
    let s1 = ctx.expr_to_smt(&args[0])?;
    let s2 = ctx.expr_to_smt(&args[1])?;
    let s3 = ctx.expr_to_smt(&args[2])?;

    let (lo, hi) = resolve_set_domain3(ctx, &s1, &s2, &s3, name)?;

    for value in lo..=hi {
        let b1 = set_membership_term(ctx, &s1, value, name)?;
        let b2_raw = set_membership_term(ctx, &s2, value, name)?;
        let b2 = if complement_s2 {
            format!("(not {b2_raw})")
        } else {
            b2_raw
        };
        let b3 = set_membership_term(ctx, &s3, value, name)?;
        ctx.emit_fmt(format_args!("(assert (= {b3} ({smt_op} {b1} {b2})))"));
    }
    Ok(())
}

/// `set_intersect(S1, S2, S3)` → for each bit: S3_bit_i = S1_bit_i and S2_bit_i
pub(crate) fn set_intersect(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    set_bitwise_op(ctx, args, "set_intersect", "and", false)
}

/// `set_diff(S1, S2, S3)` → for each bit: S3_bit_i = S1_bit_i and (not S2_bit_i)
pub(crate) fn set_diff(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    set_bitwise_op(ctx, args, "set_diff", "and", true)
}

/// `set_symdiff(S1, S2, S3)` → for each bit: S3_bit_i = S1_bit_i xor S2_bit_i
pub(crate) fn set_symdiff(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    set_bitwise_op(ctx, args, "set_symdiff", "xor", false)
}

/// Helper: look up set domain from either operand (try both).
pub(crate) fn resolve_set_domain(
    ctx: &Context,
    s1: &str,
    s2: &str,
    name: &str,
) -> Result<(i64, i64), TranslateError> {
    let (lo1, hi1) = lookup_set_domain(ctx, s1, name)?;
    let (lo2, hi2) = lookup_set_domain(ctx, s2, name)?;
    Ok((lo1.min(lo2), hi1.max(hi2)))
}

/// `set_subset(S1, S2)` → for each bit: S1_bit_i => S2_bit_i
pub(crate) fn set_subset(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    check_args("set_subset", args, 2)?;
    let s1 = ctx.expr_to_smt(&args[0])?;
    let s2 = ctx.expr_to_smt(&args[1])?;

    let (lo, hi) = resolve_set_domain(ctx, &s1, &s2, "set_subset")?;

    for value in lo..=hi {
        let b1 = set_membership_term(ctx, &s1, value, "set_subset")?;
        let b2 = set_membership_term(ctx, &s2, value, "set_subset")?;
        ctx.emit_fmt(format_args!("(assert (=> {b1} {b2}))"));
    }
    Ok(())
}

/// `set_superset(S1, S2)` → for each bit: S2_bit_i => S1_bit_i (reverse of subset)
pub(crate) fn set_superset(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    check_args("set_superset", args, 2)?;
    let s1 = ctx.expr_to_smt(&args[0])?;
    let s2 = ctx.expr_to_smt(&args[1])?;

    let (lo, hi) = resolve_set_domain(ctx, &s1, &s2, "set_superset")?;

    for value in lo..=hi {
        let b1 = set_membership_term(ctx, &s1, value, "set_superset")?;
        let b2 = set_membership_term(ctx, &s2, value, "set_superset")?;
        ctx.emit_fmt(format_args!("(assert (=> {b2} {b1}))"));
    }
    Ok(())
}

/// `set_eq(S1, S2)` → for each bit: S1_bit_i = S2_bit_i
pub(crate) fn set_eq(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    check_args("set_eq", args, 2)?;
    let s1 = ctx.expr_to_smt(&args[0])?;
    let s2 = ctx.expr_to_smt(&args[1])?;

    let (lo, hi) = resolve_set_domain(ctx, &s1, &s2, "set_eq")?;

    for value in lo..=hi {
        let b1 = set_membership_term(ctx, &s1, value, "set_eq")?;
        let b2 = set_membership_term(ctx, &s2, value, "set_eq")?;
        ctx.emit_fmt(format_args!("(assert (= {b1} {b2}))"));
    }
    Ok(())
}

/// `set_ne(S1, S2)` → at least one bit position differs
pub(crate) fn set_ne(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    check_args("set_ne", args, 2)?;
    let s1 = ctx.expr_to_smt(&args[0])?;
    let s2 = ctx.expr_to_smt(&args[1])?;

    let (lo, hi) = resolve_set_domain(ctx, &s1, &s2, "set_ne")?;

    let diffs: Vec<String> = (lo..=hi)
        .map(|value| {
            let b1 = set_membership_term(ctx, &s1, value, "set_ne")?;
            let b2 = set_membership_term(ctx, &s2, value, "set_ne")?;
            Ok(format!("(xor {b1} {b2})"))
        })
        .collect::<Result<_, TranslateError>>()?;

    if diffs.len() == 1 {
        ctx.emit_fmt(format_args!("(assert {})", diffs[0]));
    } else {
        ctx.emit_fmt(format_args!("(assert (or {}))", diffs.join(" ")));
    }
    Ok(())
}

/// `set_le(S1, S2)` → S1 ≤ S2 in lexicographic (bit) order.
/// Uses chained comparison: check from lowest bit to highest.
pub(crate) fn set_le(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    check_args("set_le", args, 2)?;
    let s1 = ctx.expr_to_smt(&args[0])?;
    let s2 = ctx.expr_to_smt(&args[1])?;

    let (lo, hi) = resolve_set_domain(ctx, &s1, &s2, "set_le")?;
    let width = (hi - lo + 1) as u32;

    // Auxiliary variables for lex comparison
    // At bit i: s1[i] <= s2[i] holds if either:
    // - s1[i] = false and s2[i] = true (strictly less at this bit), OR
    // - s1[i] = s2[i] (equal, check next bit)
    // This is equivalent to: (not s1[i]) or s2[i]  for all bits (subset)
    // But set_le is actually lexicographic, not subset. In MiniZinc set ordering:
    // S1 <= S2 iff S1 is a subset of S2.
    // FlatZinc `set_le` means subset-or-equal in standard libraries.
    for i in 0..width {
        let b1 = set_bit_name(&s1, i);
        let b2 = set_bit_name(&s2, i);
        ctx.emit_fmt(format_args!("(assert (=> {b1} {b2}))"));
    }
    Ok(())
}

/// `set_lt(S1, S2)` → S1 ⊂ S2 (strict subset): S1 ⊆ S2 and S1 ≠ S2
pub(crate) fn set_lt(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    check_args("set_lt", args, 2)?;
    let s1 = ctx.expr_to_smt(&args[0])?;
    let s2 = ctx.expr_to_smt(&args[1])?;

    let (lo, hi) = resolve_set_domain(ctx, &s1, &s2, "set_lt")?;
    let width = (hi - lo + 1) as u32;

    // S1 ⊆ S2
    for i in 0..width {
        let b1 = set_bit_name(&s1, i);
        let b2 = set_bit_name(&s2, i);
        ctx.emit_fmt(format_args!("(assert (=> {b1} {b2}))"));
    }

    // S1 ≠ S2: at least one bit differs
    let diffs: Vec<String> = (0..width)
        .map(|i| {
            let b1 = set_bit_name(&s1, i);
            let b2 = set_bit_name(&s2, i);
            format!("(xor {b1} {b2})")
        })
        .collect();

    if diffs.len() == 1 {
        ctx.emit_fmt(format_args!("(assert {})", diffs[0]));
    } else {
        ctx.emit_fmt(format_args!("(assert (or {}))", diffs.join(" ")));
    }
    Ok(())
}

#[cfg(test)]
#[path = "set_constraints_tests.rs"]
mod tests;
