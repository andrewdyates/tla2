// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Function application compilation for the JIT lowerer.
//!
//! Compiles `f[x]` where `f` is a compile-time known function and `x` may
//! be a runtime value. Two strategies:
//!
//! 1. **Direct indexing** (contiguous integer domain): O(1) array lookup
//!    via `array[arg - min_key]`.
//! 2. **Linear scan** (general domain): O(n) key-value pair scan with
//!    early exit on match.

use crate::error::JitError;
use cranelift_codegen::ir::{types, InstBuilder, MemFlags};
use cranelift_frontend::FunctionBuilder;
use std::alloc::Layout;

use super::lower::LEAKED_ALLOCS;

/// Compile a function application as a native lookup loop.
///
/// The function's key-value pairs are stored in a heap-allocated array of
/// `(key, value)` pairs. At runtime, the argument is compared against each
/// key in sequence. When a match is found, the corresponding value is
/// returned. If no match is found, returns 0 (this case should not occur
/// if the preflight evaluator validated the domain correctly).
///
/// For contiguous integer domains starting at some `min_key`, this could be
/// optimized to direct array indexing (`array[arg - min_key]`), but the
/// linear scan is correct for all domain shapes and the domains are small
/// (capped at 1024 elements by the preflight validator).
///
/// # Generated IR structure
///
/// ```text
///   entry:
///     base_ptr = iconst <leaked array address>
///     len = iconst <number of pairs>
///     jump loop_header(idx=0)
///
///   loop_header(idx: i64):
///     at_end = icmp idx >= len
///     brif at_end -> not_found(0), loop_body
///
///   loop_body:
///     pair_offset = imul idx, 16    // 2 * sizeof(i64)
///     key_addr = iadd base_ptr, pair_offset
///     key = load.i64 [key_addr]
///     found = icmp key == arg_val
///     brif found -> load_value, continue
///
///   load_value:
///     val_addr = iadd key_addr, 8
///     val = load.i64 [val_addr]
///     jump done(val)
///
///   continue:
///     next_idx = iadd idx, 1
///     jump loop_header(next_idx)
///
///   done(result: i64):
///     // result is the function value
/// ```
pub(crate) fn compile_func_apply_lookup(
    builder: &mut FunctionBuilder,
    pairs: &[(i64, i64)],
    arg_val: cranelift_codegen::ir::Value,
) -> Result<cranelift_codegen::ir::Value, JitError> {
    use cranelift_codegen::ir::condcodes::IntCC;

    if pairs.is_empty() {
        return Err(JitError::CompileError(
            "function application on empty function".to_string(),
        ));
    }

    // Check if the domain is a contiguous range — if so, use direct indexing
    // for O(1) lookup instead of O(n) linear scan.
    if let Some(result) = try_compile_direct_index_lookup(builder, pairs, arg_val) {
        return result;
    }

    let len = pairs.len() as i64;

    // Leak a heap-allocated array of (key, value) pairs.
    // Each pair is 16 bytes (2 x i64). Layout: [key0, val0, key1, val1, ...]
    let flat: Vec<i64> = pairs.iter().flat_map(|&(k, v)| [k, v]).collect();
    let flat_array: Box<[i64]> = flat.into_boxed_slice();
    let base_addr = Box::into_raw(flat_array) as *const i64 as i64;
    // Track allocation for cleanup when JitContext is dropped.
    LEAKED_ALLOCS.with(|allocs| {
        // SAFETY: Layout matches the Box<[i64]> allocation above (pairs.len() * 2 elements of i64).
        let layout = Layout::array::<i64>(pairs.len() * 2).expect("valid layout");
        allocs.borrow_mut().push((base_addr as *mut u8, layout));
    });

    let base_ptr = builder.ins().iconst(types::I64, base_addr);
    let len_val = builder.ins().iconst(types::I64, len);
    let zero_idx = builder.ins().iconst(types::I64, 0);

    // Block layout
    let loop_header = builder.create_block();
    builder.append_block_param(loop_header, types::I64); // idx

    let loop_body = builder.create_block();
    let load_value_block = builder.create_block();
    let continue_block = builder.create_block();

    let done_block = builder.create_block();
    builder.append_block_param(done_block, types::I64); // result

    // --- Entry: jump to loop header with idx=0 ---
    builder.ins().jump(loop_header, &[zero_idx]);

    // --- Loop header: check idx < len ---
    builder.switch_to_block(loop_header);
    // Don't seal yet — back-edge from continue_block
    let idx = builder.block_params(loop_header)[0];
    let at_end = builder
        .ins()
        .icmp(IntCC::SignedGreaterThanOrEqual, idx, len_val);
    // If not found, return 0 (shouldn't happen with valid domain)
    let not_found_val = builder.ins().iconst(types::I64, 0);
    builder
        .ins()
        .brif(at_end, done_block, &[not_found_val], loop_body, &[]);

    // --- Loop body: load key, compare with arg ---
    builder.switch_to_block(loop_body);
    builder.seal_block(loop_body);

    // pair_offset = idx * 16 (each pair is 2 * i64 = 16 bytes)
    let sixteen = builder.ins().iconst(types::I64, 16);
    let pair_offset = builder.ins().imul(idx, sixteen);
    let key_addr = builder.ins().iadd(base_ptr, pair_offset);

    // Load key
    let key = builder
        .ins()
        .load(types::I64, MemFlags::trusted(), key_addr, 0);
    let found = builder.ins().icmp(IntCC::Equal, key, arg_val);
    builder
        .ins()
        .brif(found, load_value_block, &[], continue_block, &[]);

    // --- Load value block: key matched, load the value ---
    builder.switch_to_block(load_value_block);
    builder.seal_block(load_value_block);

    // Value is at key_addr + 8
    let eight = builder.ins().iconst(types::I64, 8);
    let val_addr = builder.ins().iadd(key_addr, eight);
    let val = builder
        .ins()
        .load(types::I64, MemFlags::trusted(), val_addr, 0);
    builder.ins().jump(done_block, &[val]);

    // --- Continue: increment index ---
    builder.switch_to_block(continue_block);
    builder.seal_block(continue_block);
    let one = builder.ins().iconst(types::I64, 1);
    let next_idx = builder.ins().iadd(idx, one);
    builder.ins().jump(loop_header, &[next_idx]);

    // Seal loop_header now that both predecessors are complete
    builder.seal_block(loop_header);

    // --- Done block ---
    builder.switch_to_block(done_block);
    builder.seal_block(done_block);
    Ok(builder.block_params(done_block)[0])
}

/// Try to compile a function application as direct array indexing when the
/// domain is a contiguous integer range.
///
/// If the function's keys form a contiguous range `min..=max`, the values
/// are stored in a flat array indexed by `(arg - min)`. This is O(1) lookup
/// instead of O(n) linear scan.
///
/// Returns `None` if the domain is not contiguous, otherwise returns
/// `Some(Result<Value, JitError>)`.
fn try_compile_direct_index_lookup(
    builder: &mut FunctionBuilder,
    pairs: &[(i64, i64)],
    arg_val: cranelift_codegen::ir::Value,
) -> Option<Result<cranelift_codegen::ir::Value, JitError>> {
    if pairs.is_empty() {
        return None;
    }

    // Check if keys form a contiguous range
    let min_key = pairs.iter().map(|(k, _)| *k).min().unwrap();
    let max_key = pairs.iter().map(|(k, _)| *k).max().unwrap();
    let expected_len = (max_key - min_key + 1) as usize;

    if expected_len != pairs.len() {
        return None; // Not contiguous (gaps or duplicates)
    }

    // Build a dense value array indexed by (key - min_key)
    let mut values = vec![0i64; expected_len];
    for &(k, v) in pairs {
        let idx = (k - min_key) as usize;
        values[idx] = v;
    }

    // Leak the values array
    let values_array: Box<[i64]> = values.into_boxed_slice();
    let base_addr = Box::into_raw(values_array) as *const i64 as i64;
    // Track allocation for cleanup when JitContext is dropped.
    LEAKED_ALLOCS.with(|allocs| {
        // SAFETY: Layout matches the Box<[i64]> allocation above (expected_len elements of i64).
        let layout = Layout::array::<i64>(expected_len).expect("valid layout");
        allocs.borrow_mut().push((base_addr as *mut u8, layout));
    });

    use cranelift_codegen::ir::condcodes::IntCC;

    let base_ptr = builder.ins().iconst(types::I64, base_addr);
    let min_val = builder.ins().iconst(types::I64, min_key);
    let max_index = builder.ins().iconst(types::I64, max_key - min_key);

    // index = arg - min_key
    let index = builder.ins().isub(arg_val, min_val);

    // Bounds check: index must be in [0, max_key - min_key].
    // Using unsigned comparison so that negative indices (arg < min_key)
    // are caught as large positive values.  On OOB, return 0 (matching
    // the linear-scan fallback's not-found behavior).
    let in_bounds = builder
        .ins()
        .icmp(IntCC::UnsignedLessThanOrEqual, index, max_index);
    let in_bounds_block = builder.create_block();
    let done_block = builder.create_block();
    builder.append_block_param(done_block, types::I64);

    let not_found_val = builder.ins().iconst(types::I64, 0);
    builder.ins().brif(
        in_bounds,
        in_bounds_block,
        &[],
        done_block,
        &[not_found_val],
    );

    builder.switch_to_block(in_bounds_block);
    builder.seal_block(in_bounds_block);

    // byte_offset = index * 8
    let eight = builder.ins().iconst(types::I64, 8);
    let byte_offset = builder.ins().imul(index, eight);
    let addr = builder.ins().iadd(base_ptr, byte_offset);

    // Load the value (safe: bounds check above guarantees valid index)
    let val = builder.ins().load(types::I64, MemFlags::trusted(), addr, 0);
    builder.ins().jump(done_block, &[val]);

    builder.switch_to_block(done_block);
    builder.seal_block(done_block);
    Some(Ok(builder.block_params(done_block)[0]))
}
