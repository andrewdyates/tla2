// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared lowering core for JIT compilation targets.
//!
//! Extracts common patterns from `compile_invariant_inner` and
//! `compile_next_state_with_layout`:
//! - Block map construction from jump targets
//! - Function finalization (define → clear → finalize → get pointer)
//! - Shared bytecode analysis (LoadVar/StoreVar index collection)
//!
//! Part of #3995: Extract shared lowering core.

use crate::error::JitError;
use crate::jit_native::{FuncId, JITModule, Module};
use cranelift_codegen::ir::{types, Block};
use cranelift_codegen::Context;
use cranelift_frontend::FunctionBuilder;
use rustc_hash::FxHashSet;
use tla_tir::bytecode::{BytecodeFunction, Opcode};

use super::control_flow::collect_jump_targets;

/// Build a block map from bytecode instructions.
///
/// Scans the instruction stream for jump targets and creates a Cranelift
/// `Block` for each. Interior blocks (not entry, not past-the-end) get
/// `reg_count` I64 block parameters to carry register state across edges.
///
/// Returns a `Vec<Option<Block>>` of length `num_instructions + 1`.
/// `block_map[pc]` is `Some(block)` if `pc` is a jump target or entry point.
///
/// Part of #3995: shared across invariant and next-state compilation.
pub(crate) fn build_block_map(
    builder: &mut FunctionBuilder,
    instructions: &[Opcode],
    reg_count: usize,
) -> Vec<Option<Block>> {
    let targets = collect_jump_targets(instructions);
    let num_instructions = instructions.len();

    let mut block_map: Vec<Option<Block>> = vec![None; num_instructions + 1];
    for &target_pc in &targets {
        if target_pc <= num_instructions {
            let block = builder.create_block();
            if target_pc > 0 && target_pc < num_instructions {
                for _ in 0..reg_count {
                    builder.append_block_param(block, types::I64);
                }
            }
            block_map[target_pc] = Some(block);
        }
    }

    block_map
}

/// Seal all blocks in the block map and finalize the function builder.
///
/// Part of #3995: shared across invariant and next-state compilation.
pub(crate) fn seal_and_finalize(mut builder: FunctionBuilder, block_map: &[Option<Block>]) {
    for block_opt in block_map {
        if let Some(block) = block_opt {
            builder.seal_block(*block);
        }
    }
    builder.finalize();
}

/// Define, finalize, and extract a native function pointer from the JIT module.
///
/// This is the common post-build sequence shared by both invariant and
/// next-state compilation:
/// 1. `module.define_function(func_id, ctx)` — register the compiled IR
/// 2. `module.clear_context(ctx)` — release IR memory
/// 3. `module.finalize_definitions()` — emit machine code to W^X pages
/// 4. `module.get_finalized_function(func_id)` — get the code pointer
///
/// Returns a raw `*const u8` that the caller transmutes to the appropriate
/// function pointer type (`JitInvariantFn` or `JitNextStateFn`).
///
/// # Safety Contract for Callers
///
/// The returned pointer is safe to transmute to a matching `extern "C"` fn
/// pointer **if and only if**:
/// - The Cranelift IR signature matches the target fn pointer's parameter
///   types and return type exactly (caller responsibility).
/// - The `module` (and its code pages) outlives the fn pointer.
/// - The calling convention is `isa().default_call_conv()` (guaranteed by
///   `module.make_signature()` which all callers use).
///
/// Part of #3995: shared across invariant and next-state compilation.
/// Part of #3966: safety documentation for JIT code pointer transmutes.
pub(crate) fn finalize_and_get_ptr(
    module: &mut JITModule,
    ctx: &mut Context,
    func_id: FuncId,
) -> Result<*const u8, JitError> {
    module.define_function(func_id, ctx).map_err(|e| {
        module.clear_context(ctx);
        JitError::CompileError(e.to_string())
    })?;

    module.clear_context(ctx);
    module
        .finalize_definitions()
        .map_err(|e| JitError::CompileError(format!("Failed to finalize: {e}")))?;

    Ok(module.get_finalized_function(func_id))
}

/// Collect the set of `VarIdx` values referenced by `LoadVar` opcodes
/// in a bytecode function.
///
/// Returns a sorted, deduplicated list of variable indices that the
/// function actually reads. Used by both invariant and next-state caches
/// to determine which state variables need to be flattened.
///
/// Part of #3995: shared across invariant_cache and next_state_cache.
pub(crate) fn collect_loadvar_indices(func: &BytecodeFunction) -> Vec<u16> {
    let mut seen = FxHashSet::default();
    let mut indices = Vec::new();
    for op in &func.instructions {
        if let Opcode::LoadVar { var_idx, .. } = *op {
            if seen.insert(var_idx) {
                indices.push(var_idx);
            }
        }
    }
    indices.sort_unstable();
    indices
}

/// Collect the set of `VarIdx` values written by `StoreVar` opcodes
/// in a bytecode function.
///
/// Returns a sorted, deduplicated list of variable indices that the
/// function writes. Used by next-state caches to track which variables
/// are modified by JIT-compiled actions.
///
/// Part of #3995: shared across compilation targets.
pub(crate) fn collect_storevar_indices(func: &BytecodeFunction) -> Vec<u16> {
    let mut seen = FxHashSet::default();
    let mut indices = Vec::new();
    for op in &func.instructions {
        if let Opcode::StoreVar { var_idx, .. } = *op {
            if seen.insert(var_idx) {
                indices.push(var_idx);
            }
        }
    }
    indices.sort_unstable();
    indices
}

#[cfg(test)]
mod tests {
    use super::*;
    use tla_tir::bytecode::BytecodeFunction;

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_collect_loadvar_indices_empty() {
        let func = BytecodeFunction::new("test".to_string(), 0);
        assert_eq!(collect_loadvar_indices(&func), Vec::<u16>::new());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_collect_loadvar_indices_dedup_and_sort() {
        let mut func = BytecodeFunction::new("test".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 5 });
        func.emit(Opcode::LoadVar { rd: 1, var_idx: 2 });
        func.emit(Opcode::LoadVar { rd: 2, var_idx: 5 }); // duplicate
        func.emit(Opcode::LoadImm { rd: 3, value: 42 }); // not LoadVar
        func.emit(Opcode::Ret { rs: 0 });
        assert_eq!(collect_loadvar_indices(&func), vec![2, 5]);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_collect_storevar_indices_dedup_and_sort() {
        let mut func = BytecodeFunction::new("test".to_string(), 0);
        func.emit(Opcode::StoreVar { var_idx: 3, rs: 0 });
        func.emit(Opcode::StoreVar { var_idx: 1, rs: 1 });
        func.emit(Opcode::StoreVar { var_idx: 3, rs: 2 }); // duplicate
        func.emit(Opcode::Ret { rs: 0 });
        assert_eq!(collect_storevar_indices(&func), vec![1, 3]);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_collect_loadvar_indices_ignores_other_opcodes() {
        let mut func = BytecodeFunction::new("test".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 42 });
        func.emit(Opcode::StoreVar { var_idx: 0, rs: 0 });
        func.emit(Opcode::LoadBool { rd: 1, value: true });
        func.emit(Opcode::Ret { rs: 1 });
        assert_eq!(collect_loadvar_indices(&func), Vec::<u16>::new());
    }
}
