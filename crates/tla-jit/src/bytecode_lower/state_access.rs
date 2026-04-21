// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! State variable access lowering: LoadVar, StoreVar, LoadPrime, Unchanged.
//!
//! LoadVar reads from the current state array. StoreVar writes to the successor
//! state array. LoadPrime reads from the successor state array. Unchanged
//! compares current vs successor state for a set of variables.

use crate::abi::{JitCallOut, JitRuntimeErrorKind, JitStatus};
use crate::error::JitError;
use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::{types, InstBuilder, MemFlags, Value};
use cranelift_frontend::FunctionBuilder;
use tla_tir::bytecode::Opcode;

use super::RegMap;

/// Emit a conditional branch: if `oob` is true, write TypeMismatch error
/// to out_ptr and return; otherwise continue execution.
fn branch_on_out_of_bounds(builder: &mut FunctionBuilder, oob: Value, out_ptr: Value) {
    let oob_block = builder.create_block();
    let continue_block = builder.create_block();

    builder.ins().brif(oob, oob_block, &[], continue_block, &[]);
    builder.seal_block(oob_block);
    builder.seal_block(continue_block);

    builder.switch_to_block(oob_block);
    let status_offset = std::mem::offset_of!(JitCallOut, status) as i32;
    let err_kind_offset = std::mem::offset_of!(JitCallOut, err_kind) as i32;
    let status = builder
        .ins()
        .iconst(types::I8, JitStatus::RuntimeError as i64);
    let err_kind = builder
        .ins()
        .iconst(types::I8, JitRuntimeErrorKind::TypeMismatch as i64);
    builder
        .ins()
        .store(MemFlags::trusted(), status, out_ptr, status_offset);
    builder
        .ins()
        .store(MemFlags::trusted(), err_kind, out_ptr, err_kind_offset);
    builder.ins().return_(&[]);

    builder.switch_to_block(continue_block);
}

/// Lower a state-access opcode (LoadVar).
///
/// Returns `true` if the opcode was handled.
///
/// Emits a bounds check before each load: if `var_idx >= state_len`,
/// branches to an error block that writes `TypeMismatch` to the output
/// struct and returns early.
pub(crate) fn lower_state_access(
    builder: &mut FunctionBuilder,
    op: &Opcode,
    regs: &mut RegMap,
    state_ptr: cranelift_codegen::ir::Value,
    state_len: cranelift_codegen::ir::Value,
    out_ptr: cranelift_codegen::ir::Value,
) -> Result<bool, JitError> {
    match *op {
        Opcode::LoadVar { rd, var_idx } => {
            // Bounds check: var_idx >= state_len → out of bounds
            let idx = builder.ins().iconst(types::I32, var_idx as i64);
            let oob = builder
                .ins()
                .icmp(IntCC::UnsignedGreaterThanOrEqual, idx, state_len);
            branch_on_out_of_bounds(builder, oob, out_ptr);

            // state_ptr points to an array of i64. Load state[var_idx].
            let byte_offset = (var_idx as i32) * 8; // i64 = 8 bytes
            let val = builder
                .ins()
                .load(types::I64, MemFlags::trusted(), state_ptr, byte_offset);
            regs.set(rd, val);
            Ok(true)
        }
        _ => Ok(false),
    }
}

/// Lower a next-state access opcode (StoreVar, LoadPrime, Unchanged).
///
/// `StoreVar` writes a register value to `state_out[var_idx]`.
/// `LoadPrime` reads from `state_out[var_idx]` into a register.
/// `Unchanged` compares `state_in[var_idx] == state_out[var_idx]` for a set of variables.
///
/// Emits a bounds check before each StoreVar/LoadPrime: if `var_idx >= state_len`,
/// traps via the out-of-bounds error block (same pattern as `lower_state_access`).
///
/// Returns `true` if the opcode was handled.
pub(crate) fn lower_next_state_access(
    builder: &mut FunctionBuilder,
    op: &Opcode,
    regs: &mut RegMap,
    state_in_ptr: cranelift_codegen::ir::Value,
    state_out_ptr: cranelift_codegen::ir::Value,
    state_len: cranelift_codegen::ir::Value,
    out_ptr: cranelift_codegen::ir::Value,
    unchanged_vars: &UnchangedVarMap,
) -> Result<bool, JitError> {
    match *op {
        Opcode::StoreVar { var_idx, rs } => {
            // Bounds check: var_idx >= state_len → out of bounds
            let idx = builder.ins().iconst(types::I32, var_idx as i64);
            let oob = builder
                .ins()
                .icmp(IntCC::UnsignedGreaterThanOrEqual, idx, state_len);
            branch_on_out_of_bounds(builder, oob, out_ptr);

            let val = regs.get(rs);
            let offset = (var_idx as i32) * 8; // i64 = 8 bytes
            builder
                .ins()
                .store(MemFlags::trusted(), val, state_out_ptr, offset);
            Ok(true)
        }
        Opcode::LoadPrime { rd, var_idx } => {
            // Bounds check: var_idx >= state_len → out of bounds
            let idx = builder.ins().iconst(types::I32, var_idx as i64);
            let oob = builder
                .ins()
                .icmp(IntCC::UnsignedGreaterThanOrEqual, idx, state_len);
            branch_on_out_of_bounds(builder, oob, out_ptr);

            // Load from successor state (state_out)
            let byte_offset = (var_idx as i32) * 8;
            let val =
                builder
                    .ins()
                    .load(types::I64, MemFlags::trusted(), state_out_ptr, byte_offset);
            regs.set(rd, val);
            Ok(true)
        }
        Opcode::Unchanged { rd, start, count } => {
            // Look up the var indices from the compile-time map
            let var_indices = unchanged_vars.get(&start).ok_or_else(|| {
                JitError::CompileError(format!(
                    "Unchanged: no var indices provided for const idx {start}"
                ))
            })?;
            if var_indices.len() != count as usize {
                return Err(JitError::CompileError(format!(
                    "Unchanged: expected {count} var indices, got {}",
                    var_indices.len()
                )));
            }

            if count == 0 {
                // Vacuously true
                let true_val = builder.ins().iconst(types::I64, 1);
                regs.set(rd, true_val);
                return Ok(true);
            }

            // Compare state_in[var_idx] == state_out[var_idx] for each variable,
            // AND all results together.
            let mut result = {
                let byte_offset = (var_indices[0] as i32) * 8;
                let in_val =
                    builder
                        .ins()
                        .load(types::I64, MemFlags::trusted(), state_in_ptr, byte_offset);
                let out_val =
                    builder
                        .ins()
                        .load(types::I64, MemFlags::trusted(), state_out_ptr, byte_offset);
                let eq = builder.ins().icmp(IntCC::Equal, in_val, out_val);
                // Convert i8 boolean to i64
                builder.ins().uextend(types::I64, eq)
            };

            for &var_idx in &var_indices[1..] {
                let byte_offset = (var_idx as i32) * 8;
                let in_val =
                    builder
                        .ins()
                        .load(types::I64, MemFlags::trusted(), state_in_ptr, byte_offset);
                let out_val =
                    builder
                        .ins()
                        .load(types::I64, MemFlags::trusted(), state_out_ptr, byte_offset);
                let eq = builder.ins().icmp(IntCC::Equal, in_val, out_val);
                let eq_i64 = builder.ins().uextend(types::I64, eq);
                result = builder.ins().band(result, eq_i64);
            }

            regs.set(rd, result);
            Ok(true)
        }
        _ => Ok(false),
    }
}

/// Pre-materialized variable indices for `Unchanged` opcode compilation.
///
/// Maps the `start` constant pool index to the list of `VarIdx` values
/// that the `Unchanged` opcode references. The caller is responsible for
/// extracting these from the constant pool at compile time.
pub type UnchangedVarMap = std::collections::HashMap<u16, Vec<u16>>;
