// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Quantifier compilation for the JIT lowerer.
//!
//! Compiles `\A x \in S: P(x)` and `\E x \in S: P(x)` using two strategies:
//!
//! 1. **Unrolled** (|S| <= UNROLL_THRESHOLD): Each domain element is substituted
//!    at compile time and the body is compiled N times. Zero loop overhead.
//!
//! 2. **Looped** (|S| > UNROLL_THRESHOLD): Domain elements are stored in a
//!    heap-allocated array. A single compiled body is executed in a counted
//!    loop that loads each element at runtime. O(1) code size regardless of
//!    domain size, with early-exit on short-circuit.

use crate::error::JitError;
use cranelift_codegen::ir::{types, InstBuilder, MemFlags};
use cranelift_frontend::FunctionBuilder;
use std::alloc::Layout;
use tla_core::ast::Expr;
use tla_core::span::Spanned;

use super::lower::{
    compile_expr_bound, compile_expr_inner, Bindings, LEAKED_ALLOCS, UNROLL_THRESHOLD,
};
use super::lower_set::try_extract_range_bounds;
use super::preflight::{expect_set, preflight_const_i64, preflight_const_value};
use super::preflight_funcdef::substitute_ident;

/// Compile a quantifier (\A or \E) dispatcher.
///
/// Validates the bound variable, evaluates the domain, and dispatches to
/// either the unrolled strategy (small domains) or the loop strategy
/// (larger domains).
pub(crate) fn compile_quantifier(
    builder: &mut FunctionBuilder,
    bounds: &[tla_core::ast::BoundVar],
    body: &Spanned<Expr>,
    fallback_expr: &Spanned<Expr>,
    is_forall: bool,
    outer_bindings: &Bindings<'_>,
) -> Result<cranelift_codegen::ir::Value, JitError> {
    use tla_core::ast::BoundVar;

    // Validate: single bound variable, with domain, no pattern
    if bounds.len() != 1 {
        return Err(JitError::UnsupportedExpr(
            "multi-variable quantifier not yet supported in JIT".to_string(),
        ));
    }

    let BoundVar {
        name,
        domain,
        pattern,
    } = &bounds[0];

    if pattern.is_some() {
        return Err(JitError::UnsupportedExpr(
            "pattern destructuring in quantifier not supported in JIT".to_string(),
        ));
    }

    let domain_expr = domain.as_ref().ok_or_else(|| {
        JitError::UnsupportedExpr(
            "unbounded quantifier not supported in JIT (no domain)".to_string(),
        )
    })?;

    // Evaluate domain at compile time
    let domain_val = preflight_const_value(&domain_expr.node)?;
    let set = expect_set(domain_val)?;

    if set.len() > 1024 {
        return Err(JitError::CompileError(
            "quantifier domain too large for JIT expansion (>1024 elements)".to_string(),
        ));
    }

    let var_name = &name.node;

    // Empty domain: \A -> true (1), \E -> false (0)
    if set.is_empty() {
        let val = i64::from(is_forall);
        return Ok(builder.ins().iconst(types::I64, val));
    }

    // Check if body is constant (doesn't reference the bound variable).
    // If so, use the preflight result directly as a constant.
    if preflight_const_value(&body.node).is_ok() {
        let value = preflight_const_i64(&fallback_expr.node)?;
        return Ok(builder.ins().iconst(types::I64, value));
    }

    // Single element: just compile the substituted body directly
    if set.len() == 1 {
        let substituted = substitute_ident(&body.node, var_name, set[0]);
        let substituted_spanned = Spanned::new(substituted, body.span);
        return compile_expr_bound(builder, &substituted_spanned, outer_bindings);
    }

    // Range optimization: if the domain is a..b, use a counted loop from a
    // to b instead of materializing the full domain array. This avoids the
    // heap allocation and memory loads of the general loop path.
    if let Some(range_bounds) = try_extract_range_bounds(&domain_expr.node) {
        return compile_quantifier_range_loop(
            builder,
            range_bounds,
            var_name,
            body,
            is_forall,
            outer_bindings,
        );
    }

    // Dispatch based on domain size
    if set.len() <= UNROLL_THRESHOLD {
        compile_quantifier_unrolled(builder, &set, var_name, body, is_forall)
    } else {
        compile_quantifier_loop(builder, &set, var_name, body, is_forall, outer_bindings)
    }
}

/// Compile a quantifier by unrolling: one copy of the body per domain element.
///
/// For each element in the finite domain, the body expression is specialized
/// by substituting the bound variable with the element value. Each specialized
/// body is compiled to Cranelift IR. The results are chained with short-circuit
/// evaluation:
///
/// - `\A` (is_forall=true): AND chain with early exit on false.
/// - `\E` (is_forall=false): OR chain with early exit on true.
///
/// This approach generates O(|S|) blocks of native code, equivalent to:
///   \A: P(s1) && P(s2) && ... && P(sn)
///   \E: P(s1) || P(s2) || ... || P(sn)
fn compile_quantifier_unrolled(
    builder: &mut FunctionBuilder,
    set: &[i64],
    var_name: &str,
    body: &Spanned<Expr>,
    is_forall: bool,
) -> Result<cranelift_codegen::ir::Value, JitError> {
    use cranelift_codegen::ir::condcodes::IntCC;

    debug_assert!(set.len() > 1, "caller handles single-element case");

    let done_block = builder.create_block();
    builder.append_block_param(done_block, types::I64);

    for (i, &elem) in set.iter().enumerate() {
        // Substitute the bound variable with the current element
        let substituted = substitute_ident(&body.node, var_name, elem);
        let substituted_spanned = Spanned::new(substituted, body.span);

        // Compile the specialized body
        let body_val = compile_expr_inner(builder, &substituted_spanned)?;
        let body_bool = builder.ins().icmp_imm(IntCC::NotEqual, body_val, 0);

        if i < set.len() - 1 {
            // Not the last element: short-circuit branch
            let next_block = builder.create_block();
            if is_forall {
                // \A: if body is false, early exit with 0
                let zero = builder.ins().iconst(types::I64, 0);
                builder
                    .ins()
                    .brif(body_bool, next_block, &[], done_block, &[zero]);
            } else {
                // \E: if body is true, early exit with 1
                let one = builder.ins().iconst(types::I64, 1);
                builder
                    .ins()
                    .brif(body_bool, done_block, &[one], next_block, &[]);
            }

            builder.switch_to_block(next_block);
            builder.seal_block(next_block);
        } else {
            // Last element: canonicalize and jump to done
            let result = builder.ins().uextend(types::I64, body_bool);
            builder.ins().jump(done_block, &[result]);
        }
    }

    builder.switch_to_block(done_block);
    builder.seal_block(done_block);
    Ok(builder.block_params(done_block)[0])
}

/// Compile a quantifier as a native counted loop over a heap-allocated
/// domain array.
///
/// This is the key optimization for invariant checking hot paths:
/// instead of generating O(|S|) copies of the body, generates a single
/// loop body that loads each domain element from memory.
///
/// # Generated IR structure
///
/// ```text
///   entry:
///     base_ptr = iconst <leaked array address>
///     len = iconst <domain size>
///     jump loop_header(idx=0)
///
///   loop_header(idx: i64):      // loop-carried variable
///     at_end = icmp_imm idx >= len
///     brif at_end -> exit_block(default_val), loop_body
///
///   loop_body:
///     offset = imul idx, 8      // sizeof(i64) = 8
///     addr = iadd base_ptr, offset
///     elem = load.i64 [addr]
///     body_result = <compile body with elem bound to var_name>
///     // short-circuit check
///     brif body_result -> ... (depends on \A vs \E)
///     next_idx = iadd idx, 1
///     jump loop_header(next_idx)
///
///   exit_block(result: i64):
///     // result is the quantifier value
/// ```
fn compile_quantifier_loop(
    builder: &mut FunctionBuilder,
    set: &[i64],
    var_name: &str,
    body: &Spanned<Expr>,
    is_forall: bool,
    outer_bindings: &Bindings<'_>,
) -> Result<cranelift_codegen::ir::Value, JitError> {
    use cranelift_codegen::ir::condcodes::IntCC;

    debug_assert!(set.len() > 1, "caller handles single-element case");

    let len = set.len() as i64;

    // Leak a heap-allocated copy of the domain elements. The pointer is
    // stable for the lifetime of the process (intentional leak — JIT'd
    // functions live until the JITModule is dropped, and we need the data
    // to survive that long). For a 1024-element domain this is 8 KiB.
    let domain_array: Box<[i64]> = set.to_vec().into_boxed_slice();
    let base_addr = Box::into_raw(domain_array) as *const i64 as i64;
    // Track allocation for cleanup when JitContext is dropped.
    LEAKED_ALLOCS.with(|allocs| {
        // SAFETY: Layout matches the Box<[i64]> allocation above (set.len() elements of i64).
        let layout = Layout::array::<i64>(set.len()).expect("valid layout");
        allocs.borrow_mut().push((base_addr as *mut u8, layout));
    });

    // Embed the base pointer and length as constants
    let base_ptr = builder.ins().iconst(types::I64, base_addr);
    let len_val = builder.ins().iconst(types::I64, len);
    let zero_idx = builder.ins().iconst(types::I64, 0);

    // Default result if loop completes without early exit:
    // \A: true (1) — all elements satisfied. \E: false (0) — no witness.
    let default_val = i64::from(is_forall);

    // === Block layout ===
    //
    // loop_header(idx): check if idx < len
    // loop_body: load element, compile body, short-circuit check
    // continue_block: increment idx, jump back to header
    // exit_block(result): final result

    let loop_header = builder.create_block();
    builder.append_block_param(loop_header, types::I64); // idx

    let loop_body = builder.create_block();

    let continue_block = builder.create_block();

    let exit_block = builder.create_block();
    builder.append_block_param(exit_block, types::I64); // result

    // --- Entry: jump to loop header with idx=0 ---
    builder.ins().jump(loop_header, &[zero_idx]);

    // --- Loop header: check idx < len ---
    builder.switch_to_block(loop_header);
    // Do NOT seal loop_header yet — it has a back-edge from continue_block.
    let idx = builder.block_params(loop_header)[0];
    let at_end = builder
        .ins()
        .icmp(IntCC::SignedGreaterThanOrEqual, idx, len_val);
    let default_result = builder.ins().iconst(types::I64, default_val);
    builder
        .ins()
        .brif(at_end, exit_block, &[default_result], loop_body, &[]);

    // --- Loop body: load element, evaluate predicate ---
    builder.switch_to_block(loop_body);
    builder.seal_block(loop_body);

    // Calculate byte offset: idx * 8 (sizeof i64)
    let eight = builder.ins().iconst(types::I64, 8);
    let byte_offset = builder.ins().imul(idx, eight);
    let elem_addr = builder.ins().iadd(base_ptr, byte_offset);

    // Load the domain element from memory
    let elem_val = builder
        .ins()
        .load(types::I64, MemFlags::trusted(), elem_addr, 0);

    // Build bindings: inherit outer bindings + add the bound variable
    let mut loop_bindings = outer_bindings.clone();
    loop_bindings.insert(var_name, elem_val);

    // Compile the body with the bound variable resolved to the loaded element
    let body_val = compile_expr_bound(builder, body, &loop_bindings)?;
    let body_bool = builder.ins().icmp_imm(IntCC::NotEqual, body_val, 0);

    // Short-circuit: early exit if predicate fails (\A) or succeeds (\E)
    if is_forall {
        // \A: if body is false, exit with 0 immediately
        let early_exit_val = builder.ins().iconst(types::I64, 0);
        builder.ins().brif(
            body_bool,
            continue_block,
            &[],
            exit_block,
            &[early_exit_val],
        );
    } else {
        // \E: if body is true, exit with 1 immediately
        let early_exit_val = builder.ins().iconst(types::I64, 1);
        builder.ins().brif(
            body_bool,
            exit_block,
            &[early_exit_val],
            continue_block,
            &[],
        );
    }

    // --- Continue: increment index and loop back ---
    builder.switch_to_block(continue_block);
    builder.seal_block(continue_block);
    let one = builder.ins().iconst(types::I64, 1);
    let next_idx = builder.ins().iadd(idx, one);
    builder.ins().jump(loop_header, &[next_idx]);

    // Now seal loop_header — both predecessors (entry, continue) are complete
    builder.seal_block(loop_header);

    // --- Exit block ---
    builder.switch_to_block(exit_block);
    builder.seal_block(exit_block);
    Ok(builder.block_params(exit_block)[0])
}

/// Compile a quantifier as a native counted loop over a contiguous range.
///
/// For `\A x \in a..b : P(x)` or `\E x \in a..b : P(x)`, generates a
/// loop that increments the bound variable from `a` to `b` (inclusive).
/// No heap allocation or memory loads — the loop variable is a Cranelift
/// Value that increments each iteration.
///
/// # Generated IR structure
///
/// ```text
///   entry:
///     lo = iconst <a>
///     hi = iconst <b>
///     jump loop_header(x = lo)
///
///   loop_header(x: i64):
///     past_end = icmp x > hi
///     brif past_end -> exit_block(default_val), loop_body
///
///   loop_body:
///     body_result = <compile body with x bound to var_name>
///     // short-circuit check
///     brif body_result -> ... (depends on \A vs \E)
///
///   continue_block:
///     next_x = iadd x, 1
///     jump loop_header(next_x)
///
///   exit_block(result: i64):
///     // result is the quantifier value
/// ```
fn compile_quantifier_range_loop(
    builder: &mut FunctionBuilder,
    range_bounds: (i64, i64),
    var_name: &str,
    body: &Spanned<Expr>,
    is_forall: bool,
    outer_bindings: &Bindings<'_>,
) -> Result<cranelift_codegen::ir::Value, JitError> {
    use cranelift_codegen::ir::condcodes::IntCC;

    let (lo_val, hi_val) = range_bounds;

    let lo = builder.ins().iconst(types::I64, lo_val);
    let hi = builder.ins().iconst(types::I64, hi_val);

    // Default result if loop completes without early exit:
    // \A: true (1) — all elements satisfied. \E: false (0) — no witness.
    let default_val = i64::from(is_forall);

    // Block layout
    let loop_header = builder.create_block();
    builder.append_block_param(loop_header, types::I64); // x (loop variable)

    let loop_body = builder.create_block();
    let continue_block = builder.create_block();

    let exit_block = builder.create_block();
    builder.append_block_param(exit_block, types::I64); // result

    // --- Entry: jump to loop header with x = lo ---
    builder.ins().jump(loop_header, &[lo]);

    // --- Loop header: check x <= hi ---
    builder.switch_to_block(loop_header);
    // Do NOT seal loop_header yet — it has a back-edge from continue_block.
    let x = builder.block_params(loop_header)[0];
    let past_end = builder.ins().icmp(IntCC::SignedGreaterThan, x, hi);
    let default_result = builder.ins().iconst(types::I64, default_val);
    builder
        .ins()
        .brif(past_end, exit_block, &[default_result], loop_body, &[]);

    // --- Loop body: evaluate predicate with x bound ---
    builder.switch_to_block(loop_body);
    builder.seal_block(loop_body);

    // Build bindings: inherit outer bindings + add the bound variable
    let mut loop_bindings = outer_bindings.clone();
    loop_bindings.insert(var_name, x);

    // Compile the body with the bound variable resolved to the loop variable
    let body_val = compile_expr_bound(builder, body, &loop_bindings)?;
    let body_bool = builder.ins().icmp_imm(IntCC::NotEqual, body_val, 0);

    // Short-circuit: early exit if predicate fails (\A) or succeeds (\E)
    if is_forall {
        let early_exit_val = builder.ins().iconst(types::I64, 0);
        builder.ins().brif(
            body_bool,
            continue_block,
            &[],
            exit_block,
            &[early_exit_val],
        );
    } else {
        let early_exit_val = builder.ins().iconst(types::I64, 1);
        builder.ins().brif(
            body_bool,
            exit_block,
            &[early_exit_val],
            continue_block,
            &[],
        );
    }

    // --- Continue: increment x and loop back ---
    builder.switch_to_block(continue_block);
    builder.seal_block(continue_block);
    let one = builder.ins().iconst(types::I64, 1);
    let next_x = builder.ins().iadd(x, one);
    builder.ins().jump(loop_header, &[next_x]);

    // Now seal loop_header — both predecessors (entry, continue) are complete
    builder.seal_block(loop_header);

    // --- Exit block ---
    builder.switch_to_block(exit_block);
    builder.seal_block(exit_block);
    Ok(builder.block_params(exit_block)[0])
}
