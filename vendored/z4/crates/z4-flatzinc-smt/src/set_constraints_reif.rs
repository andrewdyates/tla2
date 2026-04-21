// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Reified set comparison constraints for FlatZinc-to-SMT-LIB translation.
// Pattern: `constraint_reif(S1, S2, r)` → r <=> condition(S1, S2)
// Encoded as two implications: `r => condition` and `condition => r`.
// Split from set_constraints.rs to keep files under 500 lines.

use z4_flatzinc_parser::ast::Expr;

use crate::builtins::check_args;
use crate::error::TranslateError;
use crate::set_constraints::{resolve_set_domain, set_membership_term};
use crate::translate::Context;

/// `set_eq_reif(S1, S2, r)` → r <=> (for all i: S1_bit_i = S2_bit_i)
pub(crate) fn set_eq_reif(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    check_args("set_eq_reif", args, 3)?;
    let s1 = ctx.expr_to_smt(&args[0])?;
    let s2 = ctx.expr_to_smt(&args[1])?;
    let r = ctx.expr_to_smt(&args[2])?;

    let (lo, hi) = resolve_set_domain(ctx, &s1, &s2, "set_eq_reif")?;
    let eqs: Vec<String> = (lo..=hi)
        .map(|value| {
            let b1 = set_membership_term(ctx, &s1, value, "set_eq_reif")?;
            let b2 = set_membership_term(ctx, &s2, value, "set_eq_reif")?;
            Ok(format!("(= {b1} {b2})"))
        })
        .collect::<Result<_, TranslateError>>()?;

    let cond = if eqs.len() == 1 {
        eqs[0].clone()
    } else {
        format!("(and {})", eqs.join(" "))
    };

    ctx.emit_fmt(format_args!("(assert (=> {r} {cond}))"));
    ctx.emit_fmt(format_args!("(assert (=> {cond} {r}))"));
    Ok(())
}

/// `set_ne_reif(S1, S2, r)` → r <=> (exists i: S1_bit_i ≠ S2_bit_i)
pub(crate) fn set_ne_reif(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    check_args("set_ne_reif", args, 3)?;
    let s1 = ctx.expr_to_smt(&args[0])?;
    let s2 = ctx.expr_to_smt(&args[1])?;
    let r = ctx.expr_to_smt(&args[2])?;

    let (lo, hi) = resolve_set_domain(ctx, &s1, &s2, "set_ne_reif")?;
    let diffs: Vec<String> = (lo..=hi)
        .map(|value| {
            let b1 = set_membership_term(ctx, &s1, value, "set_ne_reif")?;
            let b2 = set_membership_term(ctx, &s2, value, "set_ne_reif")?;
            Ok(format!("(xor {b1} {b2})"))
        })
        .collect::<Result<_, TranslateError>>()?;

    let cond = if diffs.len() == 1 {
        diffs[0].clone()
    } else {
        format!("(or {})", diffs.join(" "))
    };

    ctx.emit_fmt(format_args!("(assert (=> {r} {cond}))"));
    ctx.emit_fmt(format_args!("(assert (=> {cond} {r}))"));
    Ok(())
}

/// `set_subset_reif(S1, S2, r)` → r <=> (for all i: S1_bit_i => S2_bit_i)
pub(crate) fn set_subset_reif(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    check_args("set_subset_reif", args, 3)?;
    let s1 = ctx.expr_to_smt(&args[0])?;
    let s2 = ctx.expr_to_smt(&args[1])?;
    let r = ctx.expr_to_smt(&args[2])?;

    let (lo, hi) = resolve_set_domain(ctx, &s1, &s2, "set_subset_reif")?;
    let impls: Vec<String> = (lo..=hi)
        .map(|value| {
            let b1 = set_membership_term(ctx, &s1, value, "set_subset_reif")?;
            let b2 = set_membership_term(ctx, &s2, value, "set_subset_reif")?;
            Ok(format!("(=> {b1} {b2})"))
        })
        .collect::<Result<_, TranslateError>>()?;

    let cond = if impls.len() == 1 {
        impls[0].clone()
    } else {
        format!("(and {})", impls.join(" "))
    };

    ctx.emit_fmt(format_args!("(assert (=> {r} {cond}))"));
    ctx.emit_fmt(format_args!("(assert (=> {cond} {r}))"));
    Ok(())
}

/// `set_le_reif(S1, S2, r)` → r <=> S1 ⊆ S2 (same as subset_reif in MiniZinc)
pub(crate) fn set_le_reif(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    set_subset_reif(ctx, args)
}

/// `set_lt_reif(S1, S2, r)` → r <=> (S1 ⊂ S2) i.e. S1 ⊆ S2 ∧ S1 ≠ S2
pub(crate) fn set_lt_reif(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    check_args("set_lt_reif", args, 3)?;
    let s1 = ctx.expr_to_smt(&args[0])?;
    let s2 = ctx.expr_to_smt(&args[1])?;
    let r = ctx.expr_to_smt(&args[2])?;

    let (lo, hi) = resolve_set_domain(ctx, &s1, &s2, "set_lt_reif")?;
    // subset condition: for all i, S1[i] => S2[i]
    let impls: Vec<String> = (lo..=hi)
        .map(|value| {
            let b1 = set_membership_term(ctx, &s1, value, "set_lt_reif")?;
            let b2 = set_membership_term(ctx, &s2, value, "set_lt_reif")?;
            Ok(format!("(=> {b1} {b2})"))
        })
        .collect::<Result<_, TranslateError>>()?;

    let subset_cond = if impls.len() == 1 {
        impls[0].clone()
    } else {
        format!("(and {})", impls.join(" "))
    };

    // not-equal condition: exists i, S1[i] ≠ S2[i]
    let diffs: Vec<String> = (lo..=hi)
        .map(|value| {
            let b1 = set_membership_term(ctx, &s1, value, "set_lt_reif")?;
            let b2 = set_membership_term(ctx, &s2, value, "set_lt_reif")?;
            Ok(format!("(xor {b1} {b2})"))
        })
        .collect::<Result<_, TranslateError>>()?;

    let ne_cond = if diffs.len() == 1 {
        diffs[0].clone()
    } else {
        format!("(or {})", diffs.join(" "))
    };

    let cond = format!("(and {subset_cond} {ne_cond})");
    ctx.emit_fmt(format_args!("(assert (=> {r} {cond}))"));
    ctx.emit_fmt(format_args!("(assert (=> {cond} {r}))"));
    Ok(())
}
