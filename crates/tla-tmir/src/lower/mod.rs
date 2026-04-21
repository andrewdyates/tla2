// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Bytecode-to-tMIR IR lowering.
//!
//! Mirrors the structure of `tla-llvm/src/lower.rs` but targets tmir types
//! instead of LLVM IR text. Each bytecode register is backed by an alloca;
//! the tMIR optimizer can promote these to SSA form later.
//!
//! This module is split across several files:
//! - `mod.rs` — public API, Ctx struct, register/block/state helpers, dispatch
//! - `arithmetic.rs` — overflow-checked arithmetic (Add, Sub, Mul, Neg, Div, Mod)
//! - `logic.rs` — comparison and boolean ops (Eq, And, Or, Not, Implies, etc.)
//! - `set_ops.rs` — set operations (SetEnum, SetIn, Union, Intersect, etc.)
//! - `sequences.rs` — sequences, tuples, records, cardinality, seq builtins
//! - `quantifiers.rs` — ForAll, Exists, Choose
//! - `functions.rs` — FuncApply, Domain, FuncExcept, FuncDef
//! - `constants.rs` — LoadConst, FuncSet, Unchanged
//! - `calls.rs` — inter-function Call
//! - `tests.rs` — all tests

mod arithmetic;
mod calls;
mod constants;
mod functions;
mod logic;
mod quantifiers;
mod sequences;
mod set_ops;
#[cfg(test)]
mod tests;

use crate::TmirError;
use std::collections::BTreeSet;
use std::collections::HashMap;
use tla_jit::abi::{JitCallOut, JitRuntimeErrorKind, JitStatus};
use tla_tir::bytecode::{BytecodeChunk, BytecodeFunction, ConstantPool, Opcode};
use tmir::inst::*;
use tmir::ty::Ty;
use tmir::value::{BlockId, FuncId, ValueId};
use tmir::{Block, Constant, InstrNode, Module};

const STATUS_OFFSET: usize = std::mem::offset_of!(JitCallOut, status);
const VALUE_OFFSET: usize = std::mem::offset_of!(JitCallOut, value);
const ERR_KIND_OFFSET: usize = std::mem::offset_of!(JitCallOut, err_kind);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum LoweringMode {
    Invariant,
    NextState,
}

/// Lower a bytecode invariant function to a tmir::Module.
///
/// The generated function has the signature:
///   `fn(out: *mut JitCallOut, state: *const i64, state_len: u32) -> void`
pub fn lower_invariant(
    func: &BytecodeFunction,
    name: &str,
) -> Result<Module, TmirError> {
    lower_function(func, name, LoweringMode::Invariant, None)
}

/// Lower a bytecode invariant function to a tmir::Module, with constant pool.
///
/// Same as [`lower_invariant`] but accepts a [`ConstantPool`] for resolving
/// `LoadConst` opcodes.
pub fn lower_invariant_with_constants(
    func: &BytecodeFunction,
    name: &str,
    const_pool: &ConstantPool,
) -> Result<Module, TmirError> {
    lower_function(func, name, LoweringMode::Invariant, Some(const_pool))
}

/// Lower a bytecode next-state function to a tmir::Module.
///
/// The generated function has the signature:
///   `fn(out: *mut JitCallOut, state_in: *const i64, state_out: *mut i64, state_len: u32) -> void`
pub fn lower_next_state(
    func: &BytecodeFunction,
    name: &str,
) -> Result<Module, TmirError> {
    lower_function(func, name, LoweringMode::NextState, None)
}

/// Lower a bytecode next-state function to a tmir::Module, with constant pool.
///
/// Same as [`lower_next_state`] but accepts a [`ConstantPool`] for resolving
/// `LoadConst` and `Unchanged` opcodes.
pub fn lower_next_state_with_constants(
    func: &BytecodeFunction,
    name: &str,
    const_pool: &ConstantPool,
) -> Result<Module, TmirError> {
    lower_function(func, name, LoweringMode::NextState, Some(const_pool))
}

/// Lower a multi-function bytecode chunk to a tmir::Module.
///
/// The entrypoint function (at `entry_idx` in the chunk) is lowered with the
/// given mode (Invariant or NextState). All functions reachable via `Call`
/// opcodes are transitively lowered as callee functions with the signature
/// `fn(arg0: i64, ..., argN: i64) -> i64`.
///
/// This is the primary entry point for compiling real TLA+ specs where
/// operators call other operators.
pub fn lower_module_invariant(
    chunk: &BytecodeChunk,
    entry_idx: u16,
    name: &str,
) -> Result<Module, TmirError> {
    lower_module(chunk, entry_idx, name, LoweringMode::Invariant)
}

/// Lower a multi-function bytecode chunk for next-state evaluation.
///
/// Same as [`lower_module_invariant`] but the entrypoint has the next-state
/// signature: `fn(out, state_in, state_out, state_len) -> void`.
pub fn lower_module_next_state(
    chunk: &BytecodeChunk,
    entry_idx: u16,
    name: &str,
) -> Result<Module, TmirError> {
    lower_module(chunk, entry_idx, name, LoweringMode::NextState)
}

fn lower_module(
    chunk: &BytecodeChunk,
    entry_idx: u16,
    module_name: &str,
    mode: LoweringMode,
) -> Result<Module, TmirError> {
    let entry_func = chunk
        .functions
        .get(entry_idx as usize)
        .ok_or_else(|| TmirError::Emission(format!(
            "entry function index {entry_idx} out of range (chunk has {} functions)",
            chunk.functions.len()
        )))?;

    let mut ctx = Ctx::new(entry_func, module_name, mode, None)?;

    // Lower the entrypoint body.
    ctx.lower_body(entry_func)?;

    // Iteratively lower callees until fixpoint. Each lowered callee may
    // reference further callees via Call opcodes.
    loop {
        let pending: Vec<u16> = ctx.pending_callees();
        if pending.is_empty() {
            break;
        }

        for op_idx in pending {
            let callee_func = chunk
                .functions
                .get(op_idx as usize)
                .ok_or_else(|| TmirError::Emission(format!(
                    "Call references function index {op_idx} but chunk has only {} functions",
                    chunk.functions.len()
                )))?;

            ctx.lower_callee(callee_func, op_idx)?;
        }
    }

    Ok(ctx.finish())
}

fn lower_function<'cp>(
    func: &BytecodeFunction,
    func_name: &str,
    mode: LoweringMode,
    const_pool: Option<&'cp ConstantPool>,
) -> Result<Module, TmirError> {
    let mut ctx = Ctx::new(func, func_name, mode, const_pool)?;
    ctx.lower_body(func)?;
    Ok(ctx.finish())
}

/// State shared between a quantifier's Begin and Next opcodes.
///
/// The Begin opcode initializes the iterator (alloca for index, domain pointer,
/// domain length) and the header block. The Next opcode uses these to advance
/// the iterator and implement short-circuit logic.
struct QuantifierLoopState {
    /// Alloca holding the current iteration index (i64).
    idx_alloca: ValueId,
    /// tMIR block index for the loop header (bounds check + element load).
    header_block: usize,
    /// tMIR block index for the exit point (after the loop).
    exit_block: usize,
}

/// Lowering context that builds tMIR directly.
///
/// Strategy: allocate one `alloca i64` per bytecode register. Opcodes
/// load from / store to these allocas. This is identical to the approach
/// in tla-llvm and produces correct code; mem2reg in the tMIR optimizer
/// converts to true SSA.
struct Ctx<'cp> {
    module: Module,
    mode: LoweringMode,
    instruction_len: usize,

    /// One alloca ValueId per bytecode register.
    register_file: Vec<ValueId>,
    /// Map from bytecode PC to tMIR block index (into the function's blocks vec).
    block_map: HashMap<usize, usize>,
    /// The function index in module.functions.
    func_idx: usize,

    /// Whether this Ctx is lowering a callee function (not the entrypoint).
    /// Callee functions return i64 directly instead of writing to JitCallOut.
    is_callee: bool,

    /// Parameter ValueIds (entrypoint only; unused for callees).
    out_ptr: ValueId,
    state_in_ptr: ValueId,
    state_out_ptr: Option<ValueId>,

    /// Next SSA value ID (monotonically increasing across all functions in the module).
    next_value: u32,
    /// Counter for auxiliary blocks (per-function, reset for each callee).
    next_aux_block: u32,

    /// Map from TIR OpIdx to tMIR FuncId for already-lowered callees.
    callee_map: HashMap<u16, FuncId>,
    /// TIR OpIdx values referenced by Call but not yet lowered.
    pending_callee_indices: Vec<u16>,

    /// Active quantifier loops, keyed by destination register (`rd`).
    /// Populated by `*Begin` opcodes, consumed by `*Next` opcodes.
    quantifier_loops: HashMap<u8, QuantifierLoopState>,

    /// Stack of active FuncDefBegin loops. LoopNext does not carry `rd`,
    /// so we use a stack to match it to the innermost active FuncDefBegin.
    /// Each entry is `(rd, QuantifierLoopState)`.
    func_def_stack: Vec<(u8, QuantifierLoopState)>,

    /// Optional constant pool for resolving `LoadConst` and `Unchanged` opcodes.
    const_pool: Option<&'cp ConstantPool>,
}

impl<'cp> Ctx<'cp> {
    fn new(
        bytecode_func: &BytecodeFunction,
        func_name: &str,
        mode: LoweringMode,
        const_pool: Option<&'cp ConstantPool>,
    ) -> Result<Self, TmirError> {
        if bytecode_func.instructions.is_empty() {
            return Err(TmirError::NotEligible {
                reason: "empty bytecode function".to_owned(),
            });
        }

        if bytecode_func.arity != 0 {
            return Err(TmirError::NotEligible {
                reason: format!(
                    "tMIR lowering requires arity 0 entrypoints, got arity {}",
                    bytecode_func.arity
                ),
            });
        }

        let block_targets = collect_block_targets(&bytecode_func.instructions)?;

        let mut module = Module::new(func_name);

        // Define the function type.
        let func_ty = match mode {
            LoweringMode::Invariant => tmir::ty::FuncTy {
                params: vec![Ty::Ptr, Ty::Ptr, Ty::I32],
                returns: vec![],
                is_vararg: false,
            },
            LoweringMode::NextState => tmir::ty::FuncTy {
                params: vec![Ty::Ptr, Ty::Ptr, Ty::Ptr, Ty::I32],
                returns: vec![],
                is_vararg: false,
            },
        };
        let ft_id = module.add_func_type(func_ty);

        // Allocate parameter value IDs.
        let mut next_value: u32 = 0;
        let mut alloc_val = || {
            let v = ValueId::new(next_value);
            next_value += 1;
            v
        };

        let out_ptr = alloc_val();
        let state_in_ptr = alloc_val();
        let state_out_ptr = if mode == LoweringMode::NextState {
            Some(alloc_val())
        } else {
            None
        };
        let _state_len = alloc_val(); // state_len parameter (unused but part of signature)

        // Create entry block with parameter bindings.
        let entry_block_id = BlockId::new(0);
        let mut entry_params = vec![
            (out_ptr, Ty::Ptr),
            (state_in_ptr, Ty::Ptr),
        ];
        if let Some(sop) = state_out_ptr {
            entry_params.push((sop, Ty::Ptr));
        }
        entry_params.push((_state_len, Ty::I32));

        let mut entry_block = Block::new(entry_block_id);
        entry_block.params = entry_params;

        // Create blocks for all bytecode branch targets.
        // Block 0 = entry, then one block per branch target PC.
        let mut blocks = vec![entry_block];
        let mut block_map = HashMap::new();
        block_map.insert(0_usize, 0_usize); // PC 0 -> block index 0

        let mut next_block_idx = 1_u32;
        for &target_pc in block_targets.iter() {
            if target_pc == 0 {
                continue;
            }
            let block_id = BlockId::new(next_block_idx);
            let block = Block::new(block_id);
            let idx = blocks.len();
            blocks.push(block);
            block_map.insert(target_pc, idx);
            next_block_idx += 1;
        }

        // Allocate register file: one alloca i64 per bytecode register.
        let mut register_file = Vec::new();
        let mut alloca_insts = Vec::new();
        for _reg in 0..=bytecode_func.max_register {
            let alloca_val = ValueId::new(next_value);
            next_value += 1;
            register_file.push(alloca_val);
            alloca_insts.push(
                InstrNode::new(Inst::Alloca { ty: Ty::I64, count: None })
                    .with_result(alloca_val),
            );
        }

        // Prepend alloca instructions to the entry block.
        let entry = &mut blocks[0];
        // Insert allocas at the beginning of the entry block body.
        for inst in alloca_insts.into_iter().rev() {
            entry.body.insert(0, inst);
        }

        // Build the function.
        let func = tmir::Function::new(
            tmir::value::FuncId::new(0),
            func_name,
            ft_id,
            entry_block_id,
        );
        // We'll set the blocks later.
        module.functions.push(tmir::Function {
            blocks,
            ..func
        });

        Ok(Self {
            module,
            mode,
            instruction_len: bytecode_func.instructions.len(),
            register_file,
            block_map,
            func_idx: 0,
            is_callee: false,
            out_ptr,
            state_in_ptr,
            state_out_ptr,
            next_value,
            next_aux_block: next_block_idx,
            callee_map: HashMap::new(),
            pending_callee_indices: Vec::new(),
            quantifier_loops: HashMap::new(),
            func_def_stack: Vec::new(),
            const_pool,
        })
    }

    fn finish(self) -> Module {
        self.module
    }

    pub(super) fn require_const_pool(&self) -> Result<&'cp ConstantPool, TmirError> {
        self.const_pool.ok_or_else(|| {
            TmirError::UnsupportedOpcode(
                "LoadConst/Unchanged requires a constant pool; use lower_*_with_constants()"
                    .to_owned(),
            )
        })
    }

    // =====================================================================
    // Multi-function module support
    // =====================================================================

    /// Return pending callee OpIdx values that have been referenced by Call
    /// opcodes but not yet lowered.
    fn pending_callees(&mut self) -> Vec<u16> {
        let pending: Vec<u16> = self.pending_callee_indices.drain(..).collect();
        pending
    }

    /// Lower a callee function and add it to the module.
    ///
    /// Callee functions have the signature `fn(arg0: i64, ...) -> i64`.
    /// Unlike entrypoint functions, they return i64 directly and do not
    /// interact with `JitCallOut`, `state_in`, or `state_out`.
    fn lower_callee(
        &mut self,
        callee_func: &BytecodeFunction,
        op_idx: u16,
    ) -> Result<(), TmirError> {
        if callee_func.instructions.is_empty() {
            return Err(TmirError::Emission(format!(
                "callee function '{}' (idx={op_idx}) has empty instruction stream",
                callee_func.name
            )));
        }

        // The FuncId was pre-allocated when the Call opcode was first seen.
        let tmir_func_id = *self.callee_map.get(&op_idx).ok_or_else(|| {
            TmirError::Emission(format!(
                "callee function idx={op_idx} not found in callee_map"
            ))
        })?;

        // Build the callee function type. Callees receive the same context
        // pointers as the entrypoint (out_ptr, state_in, [state_out,]
        // state_len) plus their own i64 arguments, and return i64.
        let arity = callee_func.arity as usize;
        let mut callee_params = match self.mode {
            LoweringMode::Invariant => vec![Ty::Ptr, Ty::Ptr, Ty::I32],
            LoweringMode::NextState => vec![Ty::Ptr, Ty::Ptr, Ty::Ptr, Ty::I32],
        };
        for _ in 0..arity {
            callee_params.push(Ty::I64);
        }
        let callee_ty = tmir::ty::FuncTy {
            params: callee_params,
            returns: vec![Ty::I64],
            is_vararg: false,
        };
        let ft_id = self.module.add_func_type(callee_ty);

        let block_targets = collect_block_targets(&callee_func.instructions)?;

        // Allocate parameter ValueIds for the callee's context + user args.
        let callee_out_ptr = self.alloc_value();
        let callee_state_in = self.alloc_value();
        let callee_state_out = if self.mode == LoweringMode::NextState {
            Some(self.alloc_value())
        } else {
            None
        };
        let _callee_state_len = self.alloc_value();

        let mut user_arg_vals = Vec::with_capacity(arity);
        for _ in 0..arity {
            user_arg_vals.push(self.alloc_value());
        }

        // Create entry block with parameter bindings.
        let entry_block_id = BlockId::new(self.next_aux_block);
        self.next_aux_block += 1;

        let mut entry_params = vec![
            (callee_out_ptr, Ty::Ptr),
            (callee_state_in, Ty::Ptr),
        ];
        if let Some(sop) = callee_state_out {
            entry_params.push((sop, Ty::Ptr));
        }
        entry_params.push((_callee_state_len, Ty::I32));
        for &arg_val in &user_arg_vals {
            entry_params.push((arg_val, Ty::I64));
        }

        let mut entry_block = Block::new(entry_block_id);
        entry_block.params = entry_params;

        // Create blocks for branch targets.
        let mut blocks = vec![entry_block];
        let mut block_map = HashMap::new();
        block_map.insert(0_usize, 0_usize);

        for &target_pc in block_targets.iter() {
            if target_pc == 0 {
                continue;
            }
            let block_id = BlockId::new(self.next_aux_block);
            self.next_aux_block += 1;
            let block = Block::new(block_id);
            let idx = blocks.len();
            blocks.push(block);
            block_map.insert(target_pc, idx);
        }

        // Allocate register file: one alloca i64 per bytecode register.
        let mut register_file = Vec::new();
        let mut alloca_insts = Vec::new();
        for _reg in 0..=callee_func.max_register {
            let alloca_val = self.alloc_value();
            register_file.push(alloca_val);
            alloca_insts.push(
                InstrNode::new(Inst::Alloca { ty: Ty::I64, count: None })
                    .with_result(alloca_val),
            );
        }

        // Store user arguments into their register allocas. Parameters
        // occupy registers 0..arity-1 (matching bytecode calling convention).
        let mut param_stores = Vec::new();
        for (i, &param_val) in user_arg_vals.iter().enumerate() {
            if let Some(&alloca) = register_file.get(i) {
                param_stores.push(InstrNode::new(Inst::Store {
                    ty: Ty::I64,
                    ptr: alloca,
                    value: param_val,
                }));
            }
        }

        // Prepend allocas + param stores to entry block.
        let entry = &mut blocks[0];
        let mut init_insts: Vec<InstrNode> = alloca_insts;
        init_insts.extend(param_stores);
        for inst in init_insts.into_iter().rev() {
            entry.body.insert(0, inst);
        }

        // Build the tMIR function.
        let func = tmir::Function::new(
            tmir_func_id,
            &callee_func.name,
            ft_id,
            entry_block_id,
        );
        let tmir_function = tmir::Function {
            blocks,
            ..func
        };
        self.module.functions.push(tmir_function);
        let callee_func_module_idx = self.module.functions.len() - 1;

        // Save and swap context for lowering the callee body.
        let saved_register_file = std::mem::replace(&mut self.register_file, register_file);
        let saved_block_map = std::mem::replace(&mut self.block_map, block_map);
        let saved_func_idx = std::mem::replace(&mut self.func_idx, callee_func_module_idx);
        let saved_instruction_len = std::mem::replace(
            &mut self.instruction_len,
            callee_func.instructions.len(),
        );
        let saved_is_callee = std::mem::replace(&mut self.is_callee, true);
        let saved_out_ptr = std::mem::replace(&mut self.out_ptr, callee_out_ptr);
        let saved_state_in = std::mem::replace(&mut self.state_in_ptr, callee_state_in);
        let saved_state_out = std::mem::replace(&mut self.state_out_ptr, callee_state_out);
        let saved_quantifier_loops = std::mem::take(&mut self.quantifier_loops);
        let saved_func_def_stack = std::mem::take(&mut self.func_def_stack);

        // Lower the callee body.
        let result = self.lower_body(callee_func);

        // Restore context.
        self.register_file = saved_register_file;
        self.block_map = saved_block_map;
        self.func_idx = saved_func_idx;
        self.instruction_len = saved_instruction_len;
        self.is_callee = saved_is_callee;
        self.out_ptr = saved_out_ptr;
        self.state_in_ptr = saved_state_in;
        self.state_out_ptr = saved_state_out;
        self.quantifier_loops = saved_quantifier_loops;
        self.func_def_stack = saved_func_def_stack;

        result
    }

    /// Register a Call target. Pre-allocates a FuncId if not yet seen.
    /// Returns the tMIR FuncId for the callee.
    ///
    /// FuncId assignment: entrypoint is always FuncId(0). Callees get
    /// FuncId(1), FuncId(2), etc. in the order they are first referenced.
    pub(super) fn register_call_target(&mut self, op_idx: u16) -> FuncId {
        if let Some(&func_id) = self.callee_map.get(&op_idx) {
            return func_id;
        }
        // Allocate the next available FuncId. The entrypoint occupies
        // FuncId(0), so callees start at FuncId(1).
        let func_id = FuncId::new(1 + self.callee_map.len() as u32);
        self.callee_map.insert(op_idx, func_id);
        self.pending_callee_indices.push(op_idx);
        func_id
    }

    // =====================================================================
    // Value allocation
    // =====================================================================

    pub(super) fn alloc_value(&mut self) -> ValueId {
        let v = ValueId::new(self.next_value);
        self.next_value += 1;
        v
    }

    // =====================================================================
    // Block management
    // =====================================================================

    pub(super) fn new_aux_block(&mut self, _prefix: &str) -> usize {
        let block_id = BlockId::new(self.next_aux_block);
        self.next_aux_block += 1;
        let block = Block::new(block_id);
        let func = &mut self.module.functions[self.func_idx];
        let idx = func.blocks.len();
        func.blocks.push(block);
        idx
    }

    pub(super) fn emit(&mut self, block_idx: usize, node: InstrNode) {
        let func = &mut self.module.functions[self.func_idx];
        func.blocks[block_idx].body.push(node);
    }

    pub(super) fn emit_with_result(&mut self, block_idx: usize, inst: Inst) -> ValueId {
        let result = self.alloc_value();
        self.emit(block_idx, InstrNode::new(inst).with_result(result));
        result
    }

    pub(super) fn block_is_terminated(&self, block_idx: usize) -> bool {
        let func = &self.module.functions[self.func_idx];
        func.blocks[block_idx]
            .body
            .last()
            .map_or(false, |n| n.is_terminator())
    }

    pub(super) fn block_id_of(&self, block_idx: usize) -> BlockId {
        self.module.functions[self.func_idx].blocks[block_idx].id
    }

    pub(super) fn block_index_for_pc(&self, pc: usize) -> Result<usize, TmirError> {
        self.block_map.get(&pc).copied().ok_or_else(|| {
            TmirError::Emission(format!("missing basic block for bytecode pc {pc}"))
        })
    }

    // =====================================================================
    // Register file access
    // =====================================================================

    pub(super) fn reg_ptr(&self, reg: u8) -> Result<ValueId, TmirError> {
        self.register_file.get(usize::from(reg)).copied().ok_or_else(|| {
            TmirError::Emission(format!(
                "register r{reg} is outside allocated register file (size={})",
                self.register_file.len()
            ))
        })
    }

    pub(super) fn load_reg(&mut self, block_idx: usize, reg: u8) -> Result<ValueId, TmirError> {
        let ptr = self.reg_ptr(reg)?;
        Ok(self.emit_with_result(block_idx, Inst::Load { ty: Ty::I64, ptr }))
    }

    pub(super) fn store_reg_imm(&mut self, block_idx: usize, reg: u8, value: i64) -> Result<(), TmirError> {
        let ptr = self.reg_ptr(reg)?;
        let const_val = self.emit_with_result(
            block_idx,
            Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(i128::from(value)),
            },
        );
        self.emit(
            block_idx,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr,
                value: const_val,
            }),
        );
        Ok(())
    }

    pub(super) fn store_reg_value(
        &mut self,
        block_idx: usize,
        reg: u8,
        value: ValueId,
    ) -> Result<(), TmirError> {
        let ptr = self.reg_ptr(reg)?;
        self.emit(
            block_idx,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr,
                value,
            }),
        );
        Ok(())
    }

    // =====================================================================
    // State variable access
    // =====================================================================

    pub(super) fn emit_state_slot_ptr(
        &mut self,
        block_idx: usize,
        state_ptr: ValueId,
        var_idx: u16,
    ) -> ValueId {
        let idx_val = self.emit_with_result(
            block_idx,
            Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(i128::from(var_idx)),
            },
        );
        self.emit_with_result(
            block_idx,
            Inst::GEP {
                pointee_ty: Ty::I64,
                base: state_ptr,
                indices: vec![idx_val],
            },
        )
    }

    fn lower_load_var(&mut self, block_idx: usize, rd: u8, var_idx: u16) -> Result<(), TmirError> {
        let state_ptr = self.state_in_ptr;
        let ptr = self.emit_state_slot_ptr(block_idx, state_ptr, var_idx);
        let value = self.emit_with_result(block_idx, Inst::Load { ty: Ty::I64, ptr });
        self.store_reg_value(block_idx, rd, value)
    }

    fn lower_load_from_state_ptr(
        &mut self,
        block_idx: usize,
        state_ptr: ValueId,
        rd: u8,
        var_idx: u16,
    ) -> Result<(), TmirError> {
        let ptr = self.emit_state_slot_ptr(block_idx, state_ptr, var_idx);
        let value = self.emit_with_result(block_idx, Inst::Load { ty: Ty::I64, ptr });
        self.store_reg_value(block_idx, rd, value)
    }

    fn lower_store_var(&mut self, block_idx: usize, var_idx: u16, rs: u8) -> Result<(), TmirError> {
        let value = self.load_reg(block_idx, rs)?;
        let state_out = self.state_out_ptr.ok_or_else(|| {
            TmirError::Emission("state_out pointer requested outside next-state lowering".to_owned())
        })?;
        let ptr = self.emit_state_slot_ptr(block_idx, state_out, var_idx);
        self.emit(
            block_idx,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr,
                value,
            }),
        );
        Ok(())
    }

    // =====================================================================
    // Out-pointer field access
    // =====================================================================

    pub(super) fn emit_out_field_ptr(&mut self, block_idx: usize, offset: usize) -> ValueId {
        let offset_val = self.emit_with_result(
            block_idx,
            Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(offset as i128),
            },
        );
        self.emit_with_result(
            block_idx,
            Inst::GEP {
                pointee_ty: Ty::I8,
                base: self.out_ptr,
                indices: vec![offset_val],
            },
        )
    }

    // =====================================================================
    // Return / error emission
    // =====================================================================

    pub(super) fn emit_success_return(&mut self, block_idx: usize, rs: u8) -> Result<(), TmirError> {
        let result = self.load_reg(block_idx, rs)?;

        // Store status = Ok
        let status_ptr = self.emit_out_field_ptr(block_idx, STATUS_OFFSET);
        let status_val = self.emit_with_result(
            block_idx,
            Inst::Const {
                ty: Ty::I8,
                value: Constant::Int(i128::from(JitStatus::Ok as u8)),
            },
        );
        self.emit(
            block_idx,
            InstrNode::new(Inst::Store {
                ty: Ty::I8,
                ptr: status_ptr,
                value: status_val,
            }),
        );

        // Store value
        let value_ptr = self.emit_out_field_ptr(block_idx, VALUE_OFFSET);
        self.emit(
            block_idx,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: value_ptr,
                value: result,
            }),
        );

        // Return void
        self.emit(block_idx, InstrNode::new(Inst::Return { values: vec![] }));
        Ok(())
    }

    pub(super) fn emit_runtime_error_and_return(
        &mut self,
        block_idx: usize,
        kind: JitRuntimeErrorKind,
    ) {
        // Store status = RuntimeError
        let status_ptr = self.emit_out_field_ptr(block_idx, STATUS_OFFSET);
        let status_val = self.emit_with_result(
            block_idx,
            Inst::Const {
                ty: Ty::I8,
                value: Constant::Int(i128::from(JitStatus::RuntimeError as u8)),
            },
        );
        self.emit(
            block_idx,
            InstrNode::new(Inst::Store {
                ty: Ty::I8,
                ptr: status_ptr,
                value: status_val,
            }),
        );

        // Store err_kind
        let err_kind_ptr = self.emit_out_field_ptr(block_idx, ERR_KIND_OFFSET);
        let err_kind_val = self.emit_with_result(
            block_idx,
            Inst::Const {
                ty: Ty::I8,
                value: Constant::Int(i128::from(kind as u8)),
            },
        );
        self.emit(
            block_idx,
            InstrNode::new(Inst::Store {
                ty: Ty::I8,
                ptr: err_kind_ptr,
                value: err_kind_val,
            }),
        );

        // Return void
        self.emit(block_idx, InstrNode::new(Inst::Return { values: vec![] }));
    }


    // =====================================================================
    // Aggregate helpers (sets, sequences, records)
    // =====================================================================
    //
    // TLA+ compound types (sets, sequences, records) are represented in tMIR as
    // heap-allocated aggregates. Each aggregate is a contiguous block of i64
    // slots allocated via `alloca`:
    //
    //   Sets/Sequences: slot[0] = length, slot[1..=N] = elements
    //   Records: slot[0..N] = field values (no length header, count is static)
    //
    // The aggregate pointer is cast to i64 (PtrToInt) and stored in the bytecode
    // register file. When accessed, it is cast back (IntToPtr). This keeps the
    // register file uniformly i64-typed while allowing compound values.
    /// Allocate a contiguous block of `count` i64 slots and return the pointer.
    pub(super) fn alloc_aggregate(&mut self, block_idx: usize, count: u32) -> ValueId {
        let count_val = self.emit_with_result(
            block_idx,
            Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(i128::from(count)),
            },
        );
        self.emit_with_result(
            block_idx,
            Inst::Alloca {
                ty: Ty::I64,
                count: Some(count_val),
            },
        )
    }

    /// Store a pointer value into a bytecode register as i64 (PtrToInt).
    pub(super) fn store_reg_ptr(
        &mut self,
        block_idx: usize,
        reg: u8,
        ptr: ValueId,
    ) -> Result<(), TmirError> {
        let as_int = self.emit_with_result(
            block_idx,
            Inst::Cast {
                op: CastOp::PtrToInt,
                src_ty: Ty::Ptr,
                dst_ty: Ty::I64,
                operand: ptr,
            },
        );
        self.store_reg_value(block_idx, reg, as_int)
    }

    /// Load a pointer from a bytecode register (IntToPtr of stored i64).
    pub(super) fn load_reg_as_ptr(&mut self, block_idx: usize, reg: u8) -> Result<ValueId, TmirError> {
        let int_val = self.load_reg(block_idx, reg)?;
        Ok(self.emit_with_result(
            block_idx,
            Inst::Cast {
                op: CastOp::IntToPtr,
                src_ty: Ty::I64,
                dst_ty: Ty::Ptr,
                operand: int_val,
            },
        ))
    }

    /// Store an i64 value at a given offset within an aggregate pointer.
    pub(super) fn store_at_offset(
        &mut self,
        block_idx: usize,
        base: ValueId,
        offset: u32,
        value: ValueId,
    ) {
        let idx = self.emit_with_result(
            block_idx,
            Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(i128::from(offset)),
            },
        );
        let ptr = self.emit_with_result(
            block_idx,
            Inst::GEP {
                pointee_ty: Ty::I64,
                base,
                indices: vec![idx],
            },
        );
        self.emit(
            block_idx,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr,
                value,
            }),
        );
    }

    /// Load an i64 value from a given offset within an aggregate pointer.
    pub(super) fn load_at_offset(
        &mut self,
        block_idx: usize,
        base: ValueId,
        offset: u32,
    ) -> ValueId {
        let idx = self.emit_with_result(
            block_idx,
            Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(i128::from(offset)),
            },
        );
        let ptr = self.emit_with_result(
            block_idx,
            Inst::GEP {
                pointee_ty: Ty::I64,
                base,
                indices: vec![idx],
            },
        );
        self.emit_with_result(block_idx, Inst::Load { ty: Ty::I64, ptr })
    }

    /// Load an i64 value at a dynamic index within an aggregate pointer.
    pub(super) fn load_at_dynamic_offset(
        &mut self,
        block_idx: usize,
        base: ValueId,
        index: ValueId,
    ) -> ValueId {
        // index is i64, truncate to i32 for GEP index
        let idx_i32 = self.emit_with_result(
            block_idx,
            Inst::Cast {
                op: CastOp::Trunc,
                src_ty: Ty::I64,
                dst_ty: Ty::I32,
                operand: index,
            },
        );
        let ptr = self.emit_with_result(
            block_idx,
            Inst::GEP {
                pointee_ty: Ty::I64,
                base,
                indices: vec![idx_i32],
            },
        );
        self.emit_with_result(block_idx, Inst::Load { ty: Ty::I64, ptr })
    }

    /// Store an i64 value at a dynamic index within an aggregate pointer.
    pub(super) fn store_at_dynamic_offset(
        &mut self,
        block_idx: usize,
        base: ValueId,
        index: ValueId,
        value: ValueId,
    ) {
        let idx_i32 = self.emit_with_result(
            block_idx,
            Inst::Cast {
                op: CastOp::Trunc,
                src_ty: Ty::I64,
                dst_ty: Ty::I32,
                operand: index,
            },
        );
        let ptr = self.emit_with_result(
            block_idx,
            Inst::GEP {
                pointee_ty: Ty::I64,
                base,
                indices: vec![idx_i32],
            },
        );
        self.emit(
            block_idx,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr,
                value,
            }),
        );
    }

    /// Emit an i64 constant.
    pub(super) fn emit_i64_const(&mut self, block_idx: usize, value: i64) -> ValueId {
        self.emit_with_result(
            block_idx,
            Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(i128::from(value)),
            },
        )
    }

    // =====================================================================
    // Body lowering
    // =====================================================================

    fn lower_body(&mut self, bytecode_func: &BytecodeFunction) -> Result<(), TmirError> {
        let mut current_block: Option<usize> = Some(self.block_index_for_pc(0)?);

        for (pc, opcode) in bytecode_func.instructions.iter().enumerate() {
            // Check if this PC starts a new basic block.
            if let Some(&target_block) = self.block_map.get(&pc) {
                match current_block {
                    Some(block) if block != target_block => {
                        // Emit fallthrough branch if the current block isn't terminated.
                        if !self.block_is_terminated(block) {
                            let target_id = self.block_id_of(target_block);
                            self.emit(
                                block,
                                InstrNode::new(Inst::Br {
                                    target: target_id,
                                    args: vec![],
                                }),
                            );
                        }
                        current_block = Some(target_block);
                    }
                    None => {
                        current_block = Some(target_block);
                    }
                    _ => {}
                }
            }

            let Some(block) = current_block else {
                continue;
            };

            current_block = self.lower_opcode(pc, opcode, block)?;

            // Handle fallthrough to next block.
            if let Some(block) = current_block {
                if let Some(&next_block) = self.block_map.get(&(pc + 1)) {
                    if next_block != block && !self.block_is_terminated(block) {
                        let next_id = self.block_id_of(next_block);
                        self.emit(
                            block,
                            InstrNode::new(Inst::Br {
                                target: next_id,
                                args: vec![],
                            }),
                        );
                        current_block = Some(next_block);
                    }
                }
            }
        }

        // Verify the function ends with a terminator.
        if let Some(block) = current_block {
            if !self.block_is_terminated(block) {
                return Err(TmirError::Emission(format!(
                    "function reaches end of body without a terminator"
                )));
            }
        }

        Ok(())
    }

    fn lower_opcode(
        &mut self,
        pc: usize,
        opcode: &Opcode,
        block: usize,
    ) -> Result<Option<usize>, TmirError> {
        match *opcode {
            Opcode::LoadImm { rd, value } => {
                self.store_reg_imm(block, rd, value)?;
                Ok(Some(block))
            }
            Opcode::LoadBool { rd, value } => {
                self.store_reg_imm(block, rd, i64::from(value))?;
                Ok(Some(block))
            }
            Opcode::LoadConst { rd, idx } => {
                self.lower_load_const(block, rd, idx)
            }
            Opcode::LoadVar { rd, var_idx } => {
                self.lower_load_var(block, rd, var_idx)?;
                Ok(Some(block))
            }
            Opcode::LoadPrime { rd, var_idx } => match self.mode {
                LoweringMode::Invariant => Err(TmirError::NotEligible {
                    reason: "LoadPrime requires next-state lowering".to_owned(),
                }),
                LoweringMode::NextState => {
                    let state_out = self.state_out_ptr.ok_or_else(|| {
                        TmirError::Emission(
                            "missing state_out parameter for next-state lowering".to_owned(),
                        )
                    })?;
                    self.lower_load_from_state_ptr(block, state_out, rd, var_idx)?;
                    Ok(Some(block))
                }
            },
            Opcode::StoreVar { var_idx, rs } => match self.mode {
                LoweringMode::Invariant => Err(TmirError::NotEligible {
                    reason: "StoreVar requires next-state lowering".to_owned(),
                }),
                LoweringMode::NextState => {
                    self.lower_store_var(block, var_idx, rs)?;
                    Ok(Some(block))
                }
            },
            Opcode::Move { rd, rs } => {
                let value = self.load_reg(block, rs)?;
                self.store_reg_value(block, rd, value)?;
                Ok(Some(block))
            }

            // Arithmetic
            Opcode::AddInt { rd, r1, r2 } => {
                self.lower_checked_binary_overflow(block, rd, r1, r2, OverflowOp::AddOverflow)
            }
            Opcode::SubInt { rd, r1, r2 } => {
                self.lower_checked_binary_overflow(block, rd, r1, r2, OverflowOp::SubOverflow)
            }
            Opcode::MulInt { rd, r1, r2 } => {
                self.lower_checked_binary_overflow(block, rd, r1, r2, OverflowOp::MulOverflow)
            }
            Opcode::IntDiv { rd, r1, r2 } => {
                self.lower_checked_division(block, rd, r1, r2, true)
            }
            Opcode::ModInt { rd, r1, r2 } => {
                self.lower_checked_division(block, rd, r1, r2, false)
            }
            Opcode::DivInt { rd, r1, r2 } => {
                self.lower_real_division(block, rd, r1, r2)
            }
            Opcode::NegInt { rd, rs } => {
                self.lower_checked_negation(block, rd, rs)
            }

            // Comparison
            Opcode::Eq { rd, r1, r2 } => {
                self.lower_comparison(block, rd, r1, r2, ICmpOp::Eq)?;
                Ok(Some(block))
            }
            Opcode::Neq { rd, r1, r2 } => {
                self.lower_comparison(block, rd, r1, r2, ICmpOp::Ne)?;
                Ok(Some(block))
            }
            Opcode::LtInt { rd, r1, r2 } => {
                self.lower_comparison(block, rd, r1, r2, ICmpOp::Slt)?;
                Ok(Some(block))
            }
            Opcode::LeInt { rd, r1, r2 } => {
                self.lower_comparison(block, rd, r1, r2, ICmpOp::Sle)?;
                Ok(Some(block))
            }
            Opcode::GtInt { rd, r1, r2 } => {
                self.lower_comparison(block, rd, r1, r2, ICmpOp::Sgt)?;
                Ok(Some(block))
            }
            Opcode::GeInt { rd, r1, r2 } => {
                self.lower_comparison(block, rd, r1, r2, ICmpOp::Sge)?;
                Ok(Some(block))
            }

            // Boolean
            Opcode::And { rd, r1, r2 } => {
                self.lower_boolean_binary(block, rd, r1, r2, BinOp::And)?;
                Ok(Some(block))
            }
            Opcode::Or { rd, r1, r2 } => {
                self.lower_boolean_binary(block, rd, r1, r2, BinOp::Or)?;
                Ok(Some(block))
            }
            Opcode::Not { rd, rs } => {
                self.lower_not(block, rd, rs)?;
                Ok(Some(block))
            }
            Opcode::Implies { rd, r1, r2 } => {
                self.lower_implies(block, rd, r1, r2)?;
                Ok(Some(block))
            }
            Opcode::Equiv { rd, r1, r2 } => {
                self.lower_equiv(block, rd, r1, r2)?;
                Ok(Some(block))
            }

            // Control flow
            Opcode::Jump { offset } => {
                let target_pc = self.resolve_forward_target(pc, offset, "Jump")?;
                let target_block = self.block_index_for_pc(target_pc)?;
                let target_id = self.block_id_of(target_block);
                self.emit(
                    block,
                    InstrNode::new(Inst::Br {
                        target: target_id,
                        args: vec![],
                    }),
                );
                Ok(None)
            }
            Opcode::JumpTrue { rs, offset } => {
                let target_pc = self.resolve_forward_target(pc, offset, "JumpTrue")?;
                let fallthrough_pc = pc + 1;
                let cond = self.load_reg(block, rs)?;
                let zero = self.emit_with_result(
                    block,
                    Inst::Const {
                        ty: Ty::I64,
                        value: Constant::Int(0),
                    },
                );
                let cond_bool = self.emit_with_result(
                    block,
                    Inst::ICmp {
                        op: ICmpOp::Ne,
                        ty: Ty::I64,
                        lhs: cond,
                        rhs: zero,
                    },
                );
                let target_block = self.block_index_for_pc(target_pc)?;
                let fallthrough_block = self.block_index_for_pc(fallthrough_pc)?;
                let target_id = self.block_id_of(target_block);
                let fallthrough_id = self.block_id_of(fallthrough_block);
                self.emit(
                    block,
                    InstrNode::new(Inst::CondBr {
                        cond: cond_bool,
                        then_target: target_id,
                        then_args: vec![],
                        else_target: fallthrough_id,
                        else_args: vec![],
                    }),
                );
                Ok(None)
            }
            Opcode::JumpFalse { rs, offset } => {
                let target_pc = self.resolve_forward_target(pc, offset, "JumpFalse")?;
                let fallthrough_pc = pc + 1;
                let cond = self.load_reg(block, rs)?;
                let zero = self.emit_with_result(
                    block,
                    Inst::Const {
                        ty: Ty::I64,
                        value: Constant::Int(0),
                    },
                );
                let cond_bool = self.emit_with_result(
                    block,
                    Inst::ICmp {
                        op: ICmpOp::Ne,
                        ty: Ty::I64,
                        lhs: cond,
                        rhs: zero,
                    },
                );
                let target_block = self.block_index_for_pc(target_pc)?;
                let fallthrough_block = self.block_index_for_pc(fallthrough_pc)?;
                let target_id = self.block_id_of(target_block);
                let fallthrough_id = self.block_id_of(fallthrough_block);
                // JumpFalse: branch to target when FALSE, fallthrough when TRUE
                self.emit(
                    block,
                    InstrNode::new(Inst::CondBr {
                        cond: cond_bool,
                        then_target: fallthrough_id,
                        then_args: vec![],
                        else_target: target_id,
                        else_args: vec![],
                    }),
                );
                Ok(None)
            }
            Opcode::CondMove { rd, cond, rs } => {
                self.lower_cond_move(block, rd, cond, rs)?;
                Ok(Some(block))
            }
            Opcode::Ret { rs } => {
                if self.is_callee {
                    // Callee functions return i64 directly.
                    let result = self.load_reg(block, rs)?;
                    self.emit(
                        block,
                        InstrNode::new(Inst::Return { values: vec![result] }),
                    );
                } else {
                    // Entrypoint functions write to JitCallOut.
                    self.emit_success_return(block, rs)?;
                }
                Ok(None)
            }
            Opcode::Halt => {
                self.emit_runtime_error_and_return(block, JitRuntimeErrorKind::TypeMismatch);
                Ok(None)
            }
            Opcode::Nop => Ok(Some(block)),

            // Set operations
            Opcode::SetEnum { rd, start, count } => {
                self.lower_set_enum(block, rd, start, count)?;
                Ok(Some(block))
            }
            Opcode::SetIn { rd, elem, set } => {
                self.lower_set_in(block, rd, elem, set)
            }
            Opcode::SetUnion { rd, r1, r2 } => {
                self.lower_set_union(block, rd, r1, r2)
            }
            Opcode::SetIntersect { rd, r1, r2 } => {
                self.lower_set_intersect(block, rd, r1, r2)
            }
            Opcode::SetDiff { rd, r1, r2 } => {
                self.lower_set_diff(block, rd, r1, r2)
            }
            Opcode::Subseteq { rd, r1, r2 } => {
                self.lower_subseteq(block, rd, r1, r2)
            }
            Opcode::Range { rd, lo, hi } => {
                self.lower_range(block, rd, lo, hi)
            }

            // Sequence operations
            Opcode::SeqNew { rd, start, count } => {
                self.lower_seq_new(block, rd, start, count)?;
                Ok(Some(block))
            }

            // Tuple operations
            Opcode::TupleNew { rd, start, count } => {
                self.lower_tuple_new(block, rd, start, count)?;
                Ok(Some(block))
            }
            Opcode::TupleGet { rd, rs, idx } => {
                self.lower_tuple_get(block, rd, rs, idx)?;
                Ok(Some(block))
            }

            // Record operations
            Opcode::RecordNew { rd, fields_start, values_start, count } => {
                self.lower_record_new(block, rd, fields_start, values_start, count)?;
                Ok(Some(block))
            }
            Opcode::RecordGet { rd, rs, field_idx } => {
                self.lower_record_get(block, rd, rs, field_idx)?;
                Ok(Some(block))
            }

            // Builtin operations (Cardinality, Len, Head, Tail, Append)
            Opcode::CallBuiltin { rd, builtin, args_start, argc } => {
                use tla_tir::bytecode::BuiltinOp;
                match builtin {
                    BuiltinOp::Cardinality => {
                        if argc != 1 {
                            return Err(TmirError::Emission(format!(
                                "Cardinality expects 1 argument, got {argc}"
                            )));
                        }
                        self.lower_cardinality(block, rd, args_start)?;
                        Ok(Some(block))
                    }
                    BuiltinOp::Len => {
                        if argc != 1 {
                            return Err(TmirError::Emission(format!(
                                "Len expects 1 argument, got {argc}"
                            )));
                        }
                        self.lower_seq_len(block, rd, args_start)?;
                        Ok(Some(block))
                    }
                    BuiltinOp::Head => {
                        if argc != 1 {
                            return Err(TmirError::Emission(format!(
                                "Head expects 1 argument, got {argc}"
                            )));
                        }
                        self.lower_seq_head(block, rd, args_start)?;
                        Ok(Some(block))
                    }
                    BuiltinOp::Tail => {
                        if argc != 1 {
                            return Err(TmirError::Emission(format!(
                                "Tail expects 1 argument, got {argc}"
                            )));
                        }
                        self.lower_seq_tail(block, rd, args_start)
                    }
                    BuiltinOp::Append => {
                        if argc != 2 {
                            return Err(TmirError::Emission(format!(
                                "Append expects 2 arguments, got {argc}"
                            )));
                        }
                        self.lower_seq_append(block, rd, args_start, args_start + 1)
                    }
                    other_builtin => Err(TmirError::UnsupportedOpcode(format!(
                        "CallBuiltin({other_builtin:?})"
                    ))),
                }
            }

            // Quantifier operations
            Opcode::ForallBegin { rd, r_binding, r_domain, loop_end } => {
                self.lower_forall_begin(pc, block, rd, r_binding, r_domain, loop_end)
            }
            Opcode::ForallNext { rd, r_binding, r_body, .. } => {
                self.lower_forall_next(pc, block, rd, r_binding, r_body)
            }
            Opcode::ExistsBegin { rd, r_binding, r_domain, loop_end } => {
                self.lower_exists_begin(pc, block, rd, r_binding, r_domain, loop_end)
            }
            Opcode::ExistsNext { rd, r_binding, r_body, .. } => {
                self.lower_exists_next(pc, block, rd, r_binding, r_body)
            }
            Opcode::ChooseBegin { rd, r_binding, r_domain, loop_end } => {
                self.lower_choose_begin(pc, block, rd, r_binding, r_domain, loop_end)
            }
            Opcode::ChooseNext { rd, r_binding, r_body, .. } => {
                self.lower_choose_next(pc, block, rd, r_binding, r_body)
            }

            // Phase 4: Function operations
            Opcode::FuncApply { rd, func, arg } => {
                self.lower_func_apply(block, rd, func, arg)
            }
            Opcode::Domain { rd, rs } => {
                self.lower_domain(block, rd, rs)
            }
            Opcode::FuncExcept { rd, func, path, val } => {
                self.lower_func_except(block, rd, func, path, val)
            }
            Opcode::FuncDefBegin { rd, r_binding, r_domain, loop_end } => {
                self.lower_func_def_begin(pc, block, rd, r_binding, r_domain, loop_end)
            }
            Opcode::LoopNext { r_binding, r_body, .. } => {
                // LoopNext is used by FuncDefBegin. Pop from the func_def_stack
                // to get the matching FuncDefBegin's rd and loop state.
                self.lower_loop_next_func_def(pc, block, r_binding, r_body)
            }

            // Phase 5: Constants and frame conditions
            Opcode::Unchanged { rd, start, count } => {
                self.lower_unchanged(block, rd, start, count)
            }

            // Phase 6: Function sets
            Opcode::FuncSet { rd, domain, range } => {
                self.lower_func_set(block, rd, domain, range)?;
                Ok(Some(block))
            }

            // Inter-function call
            Opcode::Call { rd, op_idx, args_start, argc } => {
                self.lower_call(block, rd, op_idx, args_start, argc)?;
                Ok(Some(block))
            }

            other => Err(TmirError::UnsupportedOpcode(format!("{other:?}"))),
        }
    }

}

// =========================================================================
// Free functions
// =========================================================================

fn collect_block_targets(instructions: &[Opcode]) -> Result<BTreeSet<usize>, TmirError> {
    let mut targets = BTreeSet::new();
    targets.insert(0);

    for (pc, opcode) in instructions.iter().enumerate() {
        match *opcode {
            Opcode::Jump { offset } => {
                let target = validate_forward_target(pc, offset, instructions.len(), "Jump")?;
                targets.insert(target);
            }
            Opcode::JumpTrue { offset, .. } => {
                let target =
                    validate_forward_target(pc, offset, instructions.len(), "JumpTrue")?;
                let fallthrough = pc + 1;
                if fallthrough >= instructions.len() {
                    return Err(TmirError::NotEligible {
                        reason: format!("JumpTrue at pc {pc} has no fallthrough instruction"),
                    });
                }
                targets.insert(target);
                targets.insert(fallthrough);
            }
            Opcode::JumpFalse { offset, .. } => {
                let target =
                    validate_forward_target(pc, offset, instructions.len(), "JumpFalse")?;
                let fallthrough = pc + 1;
                if fallthrough >= instructions.len() {
                    return Err(TmirError::NotEligible {
                        reason: format!("JumpFalse at pc {pc} has no fallthrough instruction"),
                    });
                }
                targets.insert(target);
                targets.insert(fallthrough);
            }
            // Quantifier/loop Begin opcodes: fallthrough (pc+1) is the body start,
            // loop_end target is the exit block.
            Opcode::ForallBegin { loop_end, .. }
            | Opcode::ExistsBegin { loop_end, .. }
            | Opcode::ChooseBegin { loop_end, .. }
            | Opcode::FuncDefBegin { loop_end, .. } => {
                let exit_target =
                    validate_forward_target(pc, loop_end, instructions.len(), "QuantBegin")?;
                let fallthrough = pc + 1;
                if fallthrough >= instructions.len() {
                    return Err(TmirError::NotEligible {
                        reason: format!("QuantBegin at pc {pc} has no fallthrough instruction"),
                    });
                }
                targets.insert(exit_target);
                targets.insert(fallthrough);
            }
            // Quantifier/loop Next opcodes: loop_begin is a backward jump to the body,
            // fallthrough (pc+1) is the exit block.
            Opcode::ForallNext { loop_begin, .. }
            | Opcode::ExistsNext { loop_begin, .. }
            | Opcode::ChooseNext { loop_begin, .. }
            | Opcode::LoopNext { loop_begin, .. } => {
                let body_target = validate_any_target(pc, loop_begin, instructions.len(), "QuantNext")?;
                let fallthrough = pc + 1;
                if fallthrough < instructions.len() {
                    targets.insert(fallthrough);
                }
                targets.insert(body_target);
            }
            _ => {}
        }
    }

    Ok(targets)
}

fn validate_forward_target(
    pc: usize,
    offset: i32,
    len: usize,
    opcode_name: &str,
) -> Result<usize, TmirError> {
    let target = resolve_target(pc, offset)?;
    if target <= pc {
        return Err(TmirError::NotEligible {
            reason: format!(
                "{opcode_name} at pc {pc} must target a later instruction (offset {offset})"
            ),
        });
    }
    if target >= len {
        return Err(TmirError::NotEligible {
            reason: format!(
                "{opcode_name} at pc {pc} targets {target}, outside body len {len}"
            ),
        });
    }
    Ok(target)
}

/// Validate a jump target that may go backward (used by quantifier Next opcodes).
fn validate_any_target(
    pc: usize,
    offset: i32,
    len: usize,
    opcode_name: &str,
) -> Result<usize, TmirError> {
    let target = resolve_target(pc, offset)?;
    if target >= len {
        return Err(TmirError::NotEligible {
            reason: format!(
                "{opcode_name} at pc {pc} targets {target}, outside body len {len}"
            ),
        });
    }
    Ok(target)
}

fn resolve_target(pc: usize, offset: i32) -> Result<usize, TmirError> {
    let target = (pc as i64) + i64::from(offset);
    usize::try_from(target).map_err(|_| TmirError::NotEligible {
        reason: format!("jump target before start of function: pc {pc}, offset {offset}"),
    })
}
