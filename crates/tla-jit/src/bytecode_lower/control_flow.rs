// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Control flow lowering: Jump, JumpTrue, JumpFalse, CondMove, Ret.
//!
//! Bytecode uses relative jump offsets. We pre-scan the instruction stream
//! to find all jump targets and create a Cranelift `Block` for each one.

use crate::abi::JitCallOut;
use crate::error::JitError;
use cranelift_codegen::ir::{types, Block, InstBuilder};
use cranelift_frontend::FunctionBuilder;
use std::collections::BTreeSet;
use tla_tir::bytecode::Opcode;

use super::RegMap;

/// Collect all PCs that are jump targets in the instruction stream.
///
/// Returns a sorted set of target PCs. PC 0 is always a target (entry block).
pub(crate) fn collect_jump_targets(instructions: &[Opcode]) -> BTreeSet<usize> {
    let mut targets = BTreeSet::new();
    targets.insert(0); // entry block

    for (pc, op) in instructions.iter().enumerate() {
        match *op {
            Opcode::Jump { offset } => {
                let target = resolve_target(pc, offset);
                targets.insert(target);
            }
            Opcode::JumpTrue { offset, .. } | Opcode::JumpFalse { offset, .. } => {
                let target = resolve_target(pc, offset);
                targets.insert(target);
                // Fallthrough is the next instruction
                targets.insert(pc + 1);
            }
            _ => {}
        }
    }

    // Also collect quantifier loop targets (body start, exit, back-edge)
    super::quantifier_loops::collect_quantifier_targets(instructions, &mut targets);

    targets
}

/// Resolve a relative jump offset from a given PC.
fn resolve_target(pc: usize, offset: i32) -> usize {
    ((pc as i64) + (offset as i64)) as usize
}

/// Lower a control-flow opcode into Cranelift IR.
///
/// Returns `true` if the opcode was handled.
pub(crate) fn lower_control_flow(
    builder: &mut FunctionBuilder,
    op: &Opcode,
    pc: usize,
    regs: &mut RegMap,
    block_map: &[Option<Block>],
    out_ptr: cranelift_codegen::ir::Value,
) -> Result<bool, JitError> {
    match *op {
        Opcode::Jump { offset } => {
            let target_pc = resolve_target(pc, offset);
            let target_block = block_map[target_pc].ok_or_else(|| {
                JitError::CompileError(format!("Jump target PC {target_pc} has no block"))
            })?;
            let incoming = regs.values().to_vec();
            builder.ins().jump(target_block, &incoming);
            Ok(true)
        }
        Opcode::JumpTrue { rs, offset } => {
            let cond = regs.get(rs);
            let cond_bool =
                builder
                    .ins()
                    .icmp_imm(cranelift_codegen::ir::condcodes::IntCC::NotEqual, cond, 0);
            let target_pc = resolve_target(pc, offset);
            let target_block = block_map[target_pc].ok_or_else(|| {
                JitError::CompileError(format!("JumpTrue target PC {target_pc} has no block"))
            })?;
            let fallthrough_block = block_map[pc + 1].ok_or_else(|| {
                JitError::CompileError(format!("JumpTrue fallthrough PC {} has no block", pc + 1))
            })?;
            let incoming = regs.values().to_vec();
            builder.ins().brif(
                cond_bool,
                target_block,
                &incoming,
                fallthrough_block,
                &incoming,
            );
            Ok(true)
        }
        Opcode::JumpFalse { rs, offset } => {
            let cond = regs.get(rs);
            let cond_bool =
                builder
                    .ins()
                    .icmp_imm(cranelift_codegen::ir::condcodes::IntCC::NotEqual, cond, 0);
            let target_pc = resolve_target(pc, offset);
            let target_block = block_map[target_pc].ok_or_else(|| {
                JitError::CompileError(format!("JumpFalse target PC {target_pc} has no block"))
            })?;
            let fallthrough_block = block_map[pc + 1].ok_or_else(|| {
                JitError::CompileError(format!("JumpFalse fallthrough PC {} has no block", pc + 1))
            })?;
            // JumpFalse: branch to target if FALSE, fallthrough if TRUE
            let incoming = regs.values().to_vec();
            builder.ins().brif(
                cond_bool,
                fallthrough_block,
                &incoming,
                target_block,
                &incoming,
            );
            Ok(true)
        }
        Opcode::CondMove { rd, cond, rs } => {
            let cond_val = regs.get(cond);
            let src_val = regs.get(rs);
            let dst_val = regs.get(rd);
            let cond_bool = builder.ins().icmp_imm(
                cranelift_codegen::ir::condcodes::IntCC::NotEqual,
                cond_val,
                0,
            );
            let result = builder.ins().select(cond_bool, src_val, dst_val);
            regs.set(rd, result);
            Ok(true)
        }
        Opcode::Ret { rs } => {
            let val = regs.get(rs);
            // Write result to JitCallOut via out_ptr:
            // out.status = JitStatus::Ok (0)
            // out.value = val
            let status_offset = std::mem::offset_of!(JitCallOut, status) as i32;
            let value_offset = std::mem::offset_of!(JitCallOut, value) as i32;
            let zero = builder.ins().iconst(types::I8, 0); // JitStatus::Ok = 0
            builder.ins().store(
                cranelift_codegen::ir::MemFlags::trusted(),
                zero,
                out_ptr,
                status_offset,
            );
            builder.ins().store(
                cranelift_codegen::ir::MemFlags::trusted(),
                val,
                out_ptr,
                value_offset,
            );
            builder.ins().return_(&[]);
            Ok(true)
        }
        Opcode::Nop => Ok(true),

        // Not a control flow op
        _ => Ok(false),
    }
}
