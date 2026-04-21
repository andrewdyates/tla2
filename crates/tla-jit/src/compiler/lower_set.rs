// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Set membership compilation for the JIT lowerer.
//!
//! Handles `x \in S` and `x \notin S` where `S` is an enumerated set or
//! integer range. Two strategies:
//!
//! 1. **Range domain** (`x \in a..b`): Compiles to `x >= a && x <= b`.
//! 2. **Enumerated set** (`x \in {s1, ..., sn}`): Short-circuit disjunction
//!    of equality checks.

use crate::error::JitError;
use cranelift_codegen::ir::{types, InstBuilder};
use cranelift_frontend::FunctionBuilder;
use tla_core::ast::Expr;
use tla_core::span::Spanned;

use super::lower::{compile_expr_bound, Bindings};
use super::preflight::{expect_set, preflight_const_i64, preflight_const_value};

/// Extract a finite set of i64 values from a set expression (SetEnum or Range).
///
/// Uses the preflight evaluator to constant-evaluate the set expression.
/// Returns an error if the expression is not a constant finite integer set.
pub(crate) fn extract_set_elements(expr: &Expr) -> Result<Vec<i64>, JitError> {
    let val = preflight_const_value(expr)?;
    expect_set(val)
}

/// Compile a set membership test as a chain of short-circuit equality checks.
///
/// Given `elem_val` (a Cranelift i64 Value) and a list of constant set elements,
/// produces Cranelift IR equivalent to:
///   elem == s[0] || elem == s[1] || ... || elem == s[n-1]
///
/// Uses short-circuit evaluation: as soon as one equality matches, the result
/// is 1 (true) without testing remaining elements.
///
/// The caller must handle the empty-set case before calling this function.
pub(crate) fn compile_membership_chain(
    builder: &mut FunctionBuilder,
    elem_val: cranelift_codegen::ir::Value,
    set_elements: &[i64],
) -> Result<cranelift_codegen::ir::Value, JitError> {
    use cranelift_codegen::ir::condcodes::IntCC;

    debug_assert!(
        !set_elements.is_empty(),
        "caller must handle empty set before calling compile_membership_chain"
    );

    // Single element: just a simple equality check
    if set_elements.len() == 1 {
        let set_val = builder.ins().iconst(types::I64, set_elements[0]);
        let cmp = builder.ins().icmp(IntCC::Equal, elem_val, set_val);
        return Ok(builder.ins().uextend(types::I64, cmp));
    }

    // Multiple elements: short-circuit chain
    // For each element s[i], we check elem == s[i]. If true, jump to done with 1.
    // If all fail, the result is 0.
    let done_block = builder.create_block();
    builder.append_block_param(done_block, types::I64);

    for (i, &elem) in set_elements.iter().enumerate() {
        let set_val = builder.ins().iconst(types::I64, elem);
        let is_eq = builder.ins().icmp(IntCC::Equal, elem_val, set_val);

        if i < set_elements.len() - 1 {
            // Not the last element: branch to done if match, else try next
            let next_block = builder.create_block();
            let one = builder.ins().iconst(types::I64, 1);
            builder
                .ins()
                .brif(is_eq, done_block, &[one], next_block, &[]);

            builder.switch_to_block(next_block);
            builder.seal_block(next_block);
        } else {
            // Last element: extend result and jump to done
            let result = builder.ins().uextend(types::I64, is_eq);
            builder.ins().jump(done_block, &[result]);
        }
    }

    builder.switch_to_block(done_block);
    builder.seal_block(done_block);
    Ok(builder.block_params(done_block)[0])
}

/// Try to extract constant range bounds from a `Range(lo, hi)` expression.
///
/// Returns `Some((lo_val, hi_val))` if the expression is `Range` and both
/// bounds evaluate to compile-time i64 constants. Returns `None` otherwise.
pub(crate) fn try_extract_range_bounds(expr: &Expr) -> Option<(i64, i64)> {
    if let Expr::Range(lo, hi) = expr {
        if let (Ok(lo_val), Ok(hi_val)) =
            (preflight_const_i64(&lo.node), preflight_const_i64(&hi.node))
        {
            return Some((lo_val, hi_val));
        }
    }
    None
}

/// Compile `x \in a..b` as `x >= a && x <= b`, or `x \notin a..b` as
/// `x < a || x > b`.
///
/// This is an O(1) optimization over the general membership chain (which
/// would expand a..b into N equality checks). Returns `None` if the set
/// is not a `Range` expression with constant bounds, so the caller falls
/// through to the general path.
///
/// For empty ranges (hi < lo), the result is always false for `\in` and
/// always true for `\notin`.
pub(crate) fn try_compile_range_membership(
    builder: &mut FunctionBuilder,
    elem: &Spanned<Expr>,
    set: &Spanned<Expr>,
    bindings: &Bindings<'_>,
    negate: bool,
) -> Result<Option<cranelift_codegen::ir::Value>, JitError> {
    use cranelift_codegen::ir::condcodes::IntCC;

    let (lo_val, hi_val) = match try_extract_range_bounds(&set.node) {
        Some(bounds) => bounds,
        None => return Ok(None),
    };

    // Empty range: hi < lo
    if hi_val < lo_val {
        let result = if negate { 1i64 } else { 0i64 };
        return Ok(Some(builder.ins().iconst(types::I64, result)));
    }

    let elem_val = compile_expr_bound(builder, elem, bindings)?;
    let lo = builder.ins().iconst(types::I64, lo_val);
    let hi = builder.ins().iconst(types::I64, hi_val);

    // x >= lo
    let ge_lo = builder
        .ins()
        .icmp(IntCC::SignedGreaterThanOrEqual, elem_val, lo);
    // x <= hi
    let le_hi = builder
        .ins()
        .icmp(IntCC::SignedLessThanOrEqual, elem_val, hi);

    // in_range = (x >= lo) & (x <= hi)
    let in_range = builder.ins().band(ge_lo, le_hi);
    let result = builder.ins().uextend(types::I64, in_range);

    if negate {
        // notin: 1 - in_range
        let one = builder.ins().iconst(types::I64, 1);
        Ok(Some(builder.ins().isub(one, result)))
    } else {
        Ok(Some(result))
    }
}
