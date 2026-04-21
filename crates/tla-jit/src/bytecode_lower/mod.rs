// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bytecode → Cranelift JIT lowerer.
//!
//! Compiles eligible `BytecodeFunction`s to native code via Cranelift.
//! Only type-monomorphic int/bool functions pass the eligibility gate;
//! compound-type functions fall back to the bytecode VM interpreter.
//!
//! # Pipeline
//!
//! ```text
//! BytecodeFunction → eligibility check → block scan → Cranelift IR → native code
//! ```

pub(crate) mod compile_common;
mod control_flow;
mod eligibility;
mod func_record_ops;
pub(crate) mod inner_exists_expansion;
pub(crate) mod inliner;
mod invariant_cache;
mod next_state_cache;
pub(crate) mod quantifier_loops;
pub(crate) mod scalar_ops;
mod set_ops;
mod state_access;
pub mod string_intern;

#[cfg(test)]
mod tests;

pub use eligibility::{
    check_eligibility, check_eligibility_with_constants, check_opcode_eligibility,
    check_opcode_eligibility_with_constants,
};
pub use invariant_cache::{JitDispatchCounters, JitInvariantCache, JitInvariantResult};
pub(crate) use inner_exists_expansion::{
    can_expand_inner_exists, expand_inner_exists_preserving_offsets, ExpandedAction,
    InnerExistsInfo, MAX_INNER_DOMAIN_SIZE,
};
pub use next_state_cache::{
    bindings_to_jit_i64, specialized_key, value_to_jit_i64, ActionMeta, BindingSpec,
    JitActionResult, JitNextStateCache, NextStateDispatchCounters,
};
pub use quantifier_loops::QuantifierDomains;
pub use state_access::UnchangedVarMap;
pub use string_intern::StringInternTable;

use crate::abi::{JitInvariantFn, JitNextStateFn};
use crate::compound_layout::{StateLayout, VarLayout};
use crate::error::JitError;
use crate::jit_native::{JITModule, Linkage, Module};
use cranelift_codegen::ir::{types, AbiParam, InstBuilder, UserFuncName, Value};
use cranelift_codegen::Context;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use std::collections::HashMap;
use tla_tir::bytecode::{BytecodeFunction, ConstantPool, Opcode};

use inliner::{has_call_opcodes, BytecodeInliner};

use compile_common::{build_block_map, finalize_and_get_ptr, seal_and_finalize};
use control_flow::lower_control_flow;
use eligibility::check_next_state_eligibility;
use func_record_ops::{lower_func_record_op, CompoundLowerResult, CompoundRegTracker};
use quantifier_loops::{
    clear_range_tracker, collect_quantifier_domains_from_bytecode, lower_quantifier_begin,
    lower_quantifier_next, QuantifierLoopStack,
};
use scalar_ops::lower_scalar;
use set_ops::{lower_set_op, SetEnumTracker, SetOpLowerResult};
use state_access::{lower_next_state_access, lower_state_access};

/// Register file mapping: bytecode register index → Cranelift SSA Value.
///
/// Bytecode uses a small register file (max ~256 registers). Each register
/// maps to a Cranelift `Variable`, allowing Cranelift's SSA construction to
/// handle multiple assignments to the same register.
pub(crate) struct RegMap {
    values: Vec<Value>,
}

impl RegMap {
    fn new(max_register: u8, builder: &mut FunctionBuilder) -> Self {
        // Initialize all registers to zero
        let zero = builder.ins().iconst(types::I64, 0);
        let count = (max_register as usize) + 1;
        RegMap {
            values: vec![zero; count],
        }
    }

    #[inline]
    fn get(&self, reg: u8) -> cranelift_codegen::ir::Value {
        self.values[reg as usize]
    }

    #[inline]
    fn values(&self) -> &[Value] {
        &self.values
    }

    #[inline]
    fn set(&mut self, reg: u8, val: cranelift_codegen::ir::Value) {
        debug_assert!(
            (reg as usize) < self.values.len(),
            "RegMap::set: register r{} out of range (max_register={})",
            reg,
            self.values.len().saturating_sub(1)
        );
        self.values[reg as usize] = val;
    }

    fn overwrite_from_block_params(&mut self, block_params: &[Value]) {
        assert_eq!(
            block_params.len(),
            self.values.len(),
            "block param/register count mismatch"
        );
        self.values.clone_from_slice(block_params);
    }
}

/// Distinguishes invariant vs next-state lowering for the few divergent code paths.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum LoweringMode {
    /// Invariant checking: state is read-only, result is bool (pass/fail).
    Invariant,
    /// Next-state relation: reads state_in, writes state_out.
    NextState,
}

/// Lower an instruction sequence using the shared lowering loop.
///
/// This is the extracted core of both `compile_invariant_inner` and
/// `compile_next_state_with_layout`. The `mode` parameter controls the
/// few divergent code paths.
#[allow(clippy::too_many_arguments)]
pub(crate) fn lower_instruction_sequence(
    builder: &mut FunctionBuilder,
    instructions: &[Opcode],
    regs: &mut RegMap,
    block_map: &[Option<cranelift_codegen::ir::Block>],
    out_ptr: Value,
    state_ptr: Value,
    state_out_ptr: Option<Value>,
    state_len: Value,
    domains: &QuantifierDomains,
    loop_stack: &mut QuantifierLoopStack,
    set_tracker: &mut SetEnumTracker,
    compound_tracker: &mut CompoundRegTracker,
    state_layout: Option<&StateLayout>,
    var_offsets: &[Option<usize>],
    field_name_ids: &[u32],
    constants: Option<&ConstantPool>,
    unchanged_vars: Option<&UnchangedVarMap>,
    module: &mut JITModule,
    mode: LoweringMode,
    jit_diag: bool,
) -> Result<(), JitError> {
    let next_state_diag = jit_diag && mode == LoweringMode::NextState;
    let mut conjuncts_passed: u32 = 0;
    let mut in_dead_code = false;

    for (pc, op) in instructions.iter().enumerate() {
        // If this PC is a block boundary (and not the entry), switch to it
        if pc > 0 {
            if let Some(block) = block_map[pc] {
                // Check if the previous instruction was a terminator
                if !in_dead_code {
                    // Insert a fallthrough jump
                    let incoming = regs.values().to_vec();
                    builder.ins().jump(block, &incoming);
                }
                in_dead_code = false;
                builder.switch_to_block(block);
                regs.overwrite_from_block_params(builder.block_params(block));
            }
        }

        // Skip dead code (after a terminator, before the next block)
        if in_dead_code {
            continue;
        }

        let current_conjuncts_passed = match mode {
            LoweringMode::Invariant => conjuncts_passed,
            LoweringMode::NextState => 0,
        };

        // Try each lowering module in order.
        // Quantifier begin/next checked before general control flow.
        if lower_scalar(
            builder,
            op,
            regs,
            out_ptr,
            &mut *module,
            constants,
            Some(&mut *compound_tracker),
            jit_diag,
        )? {
            // scalar handled
        } else if mode == LoweringMode::NextState
            && lower_next_state_access(
                builder,
                op,
                regs,
                state_ptr,
                state_out_ptr.expect("next-state lowering requires state_out_ptr"),
                state_len,
                out_ptr,
                unchanged_vars.expect("next-state lowering requires unchanged_vars"),
            )?
        {
            // StoreVar / LoadPrime / Unchanged handled
        } else {
            // Set operations: may emit FallbackNeeded + return for
            // unsupported cases (untracked registers, Range LHS in
            // Subseteq), in which case subsequent instructions are dead.
            let set_result = lower_set_op(
                builder,
                op,
                regs,
                set_tracker,
                out_ptr,
                Some(&mut *module),
                Some(state_ptr),
                Some(&mut *compound_tracker),
                current_conjuncts_passed,
            )?;
            if set_result == SetOpLowerResult::FallbackEmitted {
                if next_state_diag {
                    eprintln!("[jit-diag] pc={pc} FallbackEmitted by set_op: {op:?}");
                }
                in_dead_code = true;
            } else if set_result == SetOpLowerResult::Handled {
                // set operation handled (SetEnum / SetIn / Range / Subseteq)
            } else if lower_state_access(builder, op, regs, state_ptr, state_len, out_ptr)? {
                // state access handled — populate compound tracker if applicable
                if let Opcode::LoadVar { rd, var_idx } = *op {
                    populate_compound_tracker(
                        rd,
                        var_idx as usize,
                        state_layout,
                        var_offsets,
                        compound_tracker,
                    );
                    if next_state_diag {
                        let tracked = compound_tracker.get(rd).is_some();
                        eprintln!(
                            "[jit-diag] pc={pc} LoadVar rd=r{rd} var_idx={var_idx} compound_tracked={tracked}"
                        );
                    }
                }
            } else if lower_quantifier_begin(
                builder,
                op,
                pc,
                regs,
                block_map,
                domains,
                loop_stack,
                out_ptr,
                instructions,
                current_conjuncts_passed,
                Some(&*compound_tracker),
            )? {
                // quantifier begin is a terminator
                in_dead_code = true;
            } else if lower_quantifier_next(builder, op, pc, regs, block_map, loop_stack, out_ptr)?
            {
                // quantifier next is a terminator
                in_dead_code = true;
            } else {
                match lower_func_record_op(
                    builder,
                    op,
                    regs,
                    out_ptr,
                    Some(state_ptr),
                    compound_tracker,
                    field_name_ids,
                    Some(&mut *module),
                    current_conjuncts_passed,
                    constants,
                    state_layout,
                    jit_diag,
                )? {
                    CompoundLowerResult::NativeHandled => {
                        if next_state_diag {
                            eprintln!("[jit-diag] pc={pc} NativeHandled by func_record_op: {op:?}");
                        }
                    }
                    CompoundLowerResult::FallbackEmitted => {
                        if next_state_diag {
                            eprintln!(
                                "[jit-diag] pc={pc} FallbackEmitted by func_record_op: {op:?}"
                            );
                        }
                        in_dead_code = true;
                    }
                    CompoundLowerResult::NotHandled => {
                        if lower_control_flow(builder, op, pc, regs, block_map, out_ptr)? {
                            // Track conjunction progress for partial JIT
                            if mode == LoweringMode::Invariant
                                && matches!(op, Opcode::JumpFalse { .. })
                            {
                                conjuncts_passed += 1;
                            }
                        } else {
                            return Err(JitError::UnsupportedOpcode(format!("{op:?}")));
                        }
                    }
                }
            }
        }

        // After a terminator, enter dead code mode until next block boundary
        if is_terminator(op) {
            in_dead_code = true;
        }
    }

    Ok(())
}

/// Bytecode-to-Cranelift JIT lowerer.
///
/// Manages a Cranelift JIT module and compiles eligible bytecode functions
/// to native code.
pub struct BytecodeLowerer {
    module: JITModule,
    ctx: Context,
    builder_ctx: FunctionBuilderContext,
    func_counter: u32,
}

impl BytecodeLowerer {
    /// Create a new bytecode lowerer.
    pub fn new() -> Result<Self, JitError> {
        let module = crate::create_jit_module()?;
        let ctx = module.make_context();

        Ok(BytecodeLowerer {
            module,
            ctx,
            builder_ctx: FunctionBuilderContext::new(),
            func_counter: 0,
        })
    }

    /// Check whether a bytecode function is eligible for JIT compilation.
    pub fn is_eligible(&self, func: &BytecodeFunction) -> bool {
        check_eligibility(func).is_ok()
    }

    /// Check eligibility with access to the constant pool (enables LoadConst scalars + PowInt).
    pub fn is_eligible_with_constants(
        &self,
        func: &BytecodeFunction,
        constants: &ConstantPool,
    ) -> bool {
        check_eligibility_with_constants(func, Some(constants)).is_ok()
    }

    /// Compile a bytecode function to a native invariant function.
    ///
    /// Returns `Err(JitError::NotEligible)` if the function is not eligible
    /// for JIT compilation. Returns `Err` on compilation failure (should not
    /// happen for eligible functions).
    pub fn compile_invariant(
        &mut self,
        func: &BytecodeFunction,
    ) -> Result<Option<JitInvariantFn>, JitError> {
        let empty_domains = QuantifierDomains::new();
        self.compile_invariant_inner(func, &empty_domains, None, None, &[])
    }

    /// Compile a bytecode function with constant pool access.
    ///
    /// Enables JIT compilation of `LoadConst` for scalar constants (SmallInt, Bool)
    /// and `PowInt` for exponentiation.
    pub fn compile_invariant_with_constants(
        &mut self,
        func: &BytecodeFunction,
        constants: &ConstantPool,
    ) -> Result<Option<JitInvariantFn>, JitError> {
        let empty_domains = QuantifierDomains::new();
        self.compile_invariant_inner(func, &empty_domains, Some(constants), None, &[])
    }

    /// Compile a bytecode function with pre-materialized quantifier domains.
    ///
    /// `domains` maps the `r_domain` register of each `ForallBegin`/`ExistsBegin`
    /// to the pre-evaluated domain elements. Functions without quantifiers can
    /// pass an empty map (or use `compile_invariant`).
    pub fn compile_invariant_with_domains(
        &mut self,
        func: &BytecodeFunction,
        domains: &QuantifierDomains,
    ) -> Result<Option<JitInvariantFn>, JitError> {
        self.compile_invariant_inner(func, domains, None, None, &[])
    }

    /// Compile a bytecode function with state layout information for native
    /// compound-value access.
    ///
    /// When `state_layout` is provided, `RecordGet`, `FuncApply`, and
    /// `TupleGet` opcodes can be lowered to native code instead of emitting
    /// `FallbackNeeded`. This requires:
    /// - A `StateLayout` describing each state variable's type and structure
    /// - `field_name_ids` from the bytecode chunk's `ConstantPool::field_ids`
    ///   (maps `FieldIdx` to `NameId.0`)
    pub fn compile_invariant_with_layout(
        &mut self,
        func: &BytecodeFunction,
        domains: &QuantifierDomains,
        state_layout: &StateLayout,
        field_name_ids: &[u32],
    ) -> Result<Option<JitInvariantFn>, JitError> {
        self.compile_invariant_inner(func, domains, None, Some(state_layout), field_name_ids)
    }

    /// Compile a bytecode function with both constant pool and state layout.
    ///
    /// Combines `compile_invariant_with_constants` and
    /// `compile_invariant_with_layout`: enables `LoadConst` for scalar constants
    /// AND native `RecordGet`/`FuncApply`/`TupleGet` via compound layout info.
    ///
    /// Part of #3909.
    pub fn compile_invariant_with_constants_and_layout(
        &mut self,
        func: &BytecodeFunction,
        constants: &ConstantPool,
        state_layout: &StateLayout,
        field_name_ids: &[u32],
    ) -> Result<Option<JitInvariantFn>, JitError> {
        let empty_domains = QuantifierDomains::new();
        self.compile_invariant_inner(
            func,
            &empty_domains,
            Some(constants),
            Some(state_layout),
            field_name_ids,
        )
    }

    /// Core invariant compilation with optional constant pool, layout, and domains.
    fn compile_invariant_inner(
        &mut self,
        func: &BytecodeFunction,
        domains: &QuantifierDomains,
        constants: Option<&ConstantPool>,
        state_layout: Option<&StateLayout>,
        field_name_ids: &[u32],
    ) -> Result<Option<JitInvariantFn>, JitError> {
        // Check eligibility (with or without constant pool)
        if let Err(reason) = check_eligibility_with_constants(func, constants) {
            return Err(JitError::NotEligible { reason });
        }

        // Clear per-compilation range tracker state
        clear_range_tracker();

        // Auto-materialize quantifier domains from the bytecode constant pool,
        // just like the next-state path does. Without this, invariant quantifiers
        // like `\A i \in Proc : ...` would always emit FallbackNeeded because
        // their domain register has no entry in the externally-provided `domains`.
        let mut merged_domains =
            collect_quantifier_domains_from_bytecode(&func.instructions, constants);
        // External domains take precedence over auto-detected ones.
        for (k, v) in domains {
            merged_domains.insert(*k, v.clone());
        }

        // Precompute variable offsets if layout is available.
        // Each entry is Some(offset) if the variable's position is statically known.
        let var_offsets: Vec<Option<usize>> = state_layout
            .map(|layout| layout.compute_var_offsets())
            .unwrap_or_default();

        // Build function signature: (out: *mut JitCallOut, state: *const i64, state_len: u32)
        let ptr_type = self.module.target_config().pointer_type();
        let mut sig = self.module.make_signature();
        sig.params.push(AbiParam::new(ptr_type)); // out
        sig.params.push(AbiParam::new(ptr_type)); // state
        sig.params.push(AbiParam::new(types::I32)); // state_len

        let func_name = format!("bc_inv_{}", self.func_counter);
        self.func_counter += 1;
        let func_id = self
            .module
            .declare_function(&func_name, Linkage::Local, &sig)?;

        self.ctx.func.signature = sig;
        self.ctx.func.name = UserFuncName::user(0, func_id.as_u32());

        {
            let mut builder = FunctionBuilder::new(&mut self.ctx.func, &mut self.builder_ctx);

            let reg_count = (func.max_register as usize) + 1;
            let block_map = build_block_map(&mut builder, &func.instructions, reg_count);

            // Entry block (PC 0) gets function parameters
            let entry_block = block_map[0].expect("PC 0 must have a block");
            builder.append_block_params_for_function_params(entry_block);
            builder.switch_to_block(entry_block);

            // Extract function parameters
            let out_ptr = builder.block_params(entry_block)[0];
            let state_ptr = builder.block_params(entry_block)[1];
            let state_len = builder.block_params(entry_block)[2];

            // Initialize register map
            let mut regs = RegMap::new(func.max_register, &mut builder);

            // Compound register tracker for native RecordGet/FuncApply/TupleGet
            let mut compound_tracker = CompoundRegTracker::new(func.max_register);

            // Quantifier loop stack for nested quantifier support
            let mut loop_stack: QuantifierLoopStack = Vec::new();

            // Set enum tracker for inline set membership expansion
            let mut set_tracker = SetEnumTracker::new();

            // Cache TLA2_JIT_DIAG env var once per compilation (not per instruction).
            let jit_diag = std::env::var("TLA2_JIT_DIAG").is_ok();

            lower_instruction_sequence(
                &mut builder,
                &func.instructions,
                &mut regs,
                &block_map,
                out_ptr,
                state_ptr,
                None,
                state_len,
                &merged_domains,
                &mut loop_stack,
                &mut set_tracker,
                &mut compound_tracker,
                state_layout,
                &var_offsets,
                field_name_ids,
                constants,
                None,
                &mut self.module,
                LoweringMode::Invariant,
                jit_diag,
            )?;

            seal_and_finalize(builder, &block_map);
        }

        // Compile to machine code and extract function pointer
        let code_ptr = finalize_and_get_ptr(&mut self.module, &mut self.ctx, func_id)?;
        // SAFETY: The transmute from `*const u8` to `JitInvariantFn` is sound because:
        // 1. Calling convention: Cranelift uses `isa().default_call_conv()` (platform C
        //    ABI). `JitInvariantFn` is `unsafe extern "C" fn(...)`, matching exactly.
        // 2. Signature: The Cranelift IR function takes (ptr, ptr, I32) with no return
        //    value, matching `JitInvariantFn`'s `(*mut JitCallOut, *const i64, u32)`.
        //    Params declared at lines 278-280 above.
        // 3. Lifetime: Code buffer owned by `self.module`, outlives the returned fn ptr.
        // 4. Validity: `finalize_and_get_ptr` calls `finalize_definitions()` and returns
        //    a non-null pointer to executable W^X memory.
        debug_assert!(!code_ptr.is_null(), "JIT invariant code pointer is null");
        let jit_fn: JitInvariantFn = unsafe { std::mem::transmute(code_ptr) };

        Ok(Some(jit_fn))
    }

    /// Try to compile a bytecode function. Returns `None` if not eligible
    /// (without error), `Some(fn)` on success, or `Err` on compilation failure.
    pub fn try_compile_invariant(
        &mut self,
        func: &BytecodeFunction,
    ) -> Result<Option<JitInvariantFn>, JitError> {
        if !self.is_eligible(func) {
            return Ok(None);
        }
        self.compile_invariant(func)
    }

    /// Try to compile a bytecode function with quantifier domains.
    /// Returns `None` if not eligible (without error), `Some(fn)` on success,
    /// or `Err` on compilation failure.
    pub fn try_compile_invariant_with_domains(
        &mut self,
        func: &BytecodeFunction,
        domains: &QuantifierDomains,
    ) -> Result<Option<JitInvariantFn>, JitError> {
        if !self.is_eligible(func) {
            return Ok(None);
        }
        self.compile_invariant_with_domains(func, domains)
    }

    /// Try to compile a bytecode function, using inlining if needed.
    ///
    /// Strategy:
    /// 1. If the function is directly eligible, compile it.
    /// 2. If ineligible due to `Call` opcodes, inline callees and re-check.
    /// 3. If still ineligible after inlining, return `None`.
    ///
    /// `callees` maps `op_idx` to the callee `BytecodeFunction` for inlining.
    /// `max_inline_depth` controls nested inlining depth (default: 3).
    pub fn try_compile_with_inlining(
        &mut self,
        func: &BytecodeFunction,
        callees: &HashMap<u16, BytecodeFunction>,
        max_inline_depth: usize,
    ) -> Result<Option<JitInvariantFn>, JitError> {
        // Fast path: already eligible
        if self.is_eligible(func) {
            return self.compile_invariant(func);
        }

        // Only attempt inlining if the function has Call opcodes
        if !has_call_opcodes(func) {
            return Ok(None);
        }

        // Try inlining
        let inlined = match BytecodeInliner::inline(func, callees, max_inline_depth) {
            Ok(f) => f,
            Err(_) => return Ok(None),
        };

        // Re-check eligibility after inlining
        if self.is_eligible(&inlined) {
            self.compile_invariant(&inlined)
        } else {
            Ok(None)
        }
    }

    /// Try to compile a bytecode function with inlining and quantifier domains.
    ///
    /// Combines inlining (to eliminate `Call` opcodes) with domain pre-materialization
    /// (for quantifier loops).
    pub fn try_compile_with_inlining_and_domains(
        &mut self,
        func: &BytecodeFunction,
        callees: &HashMap<u16, BytecodeFunction>,
        max_inline_depth: usize,
        domains: &QuantifierDomains,
    ) -> Result<Option<JitInvariantFn>, JitError> {
        // Fast path: already eligible
        if self.is_eligible(func) {
            return self.compile_invariant_with_domains(func, domains);
        }

        // Only attempt inlining if the function has Call opcodes
        if !has_call_opcodes(func) {
            return Ok(None);
        }

        // Try inlining
        let inlined = match BytecodeInliner::inline(func, callees, max_inline_depth) {
            Ok(f) => f,
            Err(_) => return Ok(None),
        };

        // Re-check eligibility after inlining
        if self.is_eligible(&inlined) {
            self.compile_invariant_with_domains(&inlined, domains)
        } else {
            Ok(None)
        }
    }

    /// Check whether a bytecode function is eligible for next-state JIT compilation.
    pub fn is_next_state_eligible(&self, func: &BytecodeFunction) -> bool {
        check_next_state_eligibility(func).is_ok()
    }

    /// Compile a bytecode function to a native next-state relation function.
    ///
    /// The compiled function takes 4 arguments:
    /// - `out: *mut JitCallOut` — status/error output (value = 1 for enabled, 0 for disabled)
    /// - `state_in: *const i64` — current state array (read via LoadVar)
    /// - `state_out: *mut i64` — successor state array (written via StoreVar)
    /// - `state_len: u32` — number of state variables
    pub fn compile_next_state(
        &mut self,
        func: &BytecodeFunction,
    ) -> Result<Option<JitNextStateFn>, JitError> {
        let empty_unchanged = UnchangedVarMap::new();
        self.compile_next_state_with_unchanged_and_constants(func, &empty_unchanged, None)
    }

    /// Compile a next-state function with pre-materialized Unchanged variable indices.
    pub fn compile_next_state_with_unchanged(
        &mut self,
        func: &BytecodeFunction,
        unchanged_vars: &UnchangedVarMap,
    ) -> Result<Option<JitNextStateFn>, JitError> {
        self.compile_next_state_with_unchanged_and_constants(func, unchanged_vars, None)
    }

    /// Compile a next-state function with Unchanged maps and constant pool access.
    pub fn compile_next_state_with_unchanged_and_constants(
        &mut self,
        func: &BytecodeFunction,
        unchanged_vars: &UnchangedVarMap,
        constants: Option<&ConstantPool>,
    ) -> Result<Option<JitNextStateFn>, JitError> {
        self.compile_next_state_with_layout(func, unchanged_vars, constants, None)
    }

    /// Compile a next-state function with compound state layout information.
    ///
    /// When `state_layout` is provided, `LoadVar` instructions for compound
    /// variables (records, functions, sequences) populate the compound register
    /// tracker, enabling native lowering of `FuncApply`, `RecordGet`, and
    /// `TupleGet` instead of falling back to the interpreter.
    ///
    /// Part of #3958: Enable native compound access in JIT next-state dispatch.
    pub fn compile_next_state_with_layout(
        &mut self,
        func: &BytecodeFunction,
        unchanged_vars: &UnchangedVarMap,
        constants: Option<&ConstantPool>,
        state_layout: Option<&StateLayout>,
    ) -> Result<Option<JitNextStateFn>, JitError> {
        if let Err(reason) =
            eligibility::check_next_state_eligibility_with_constants(func, constants)
        {
            return Err(JitError::NotEligible { reason });
        }

        // Clear per-compilation range tracker state
        clear_range_tracker();

        // Precompute variable offsets if layout is available.
        let var_offsets: Vec<Option<usize>> = state_layout
            .map(|layout| layout.compute_var_offsets())
            .unwrap_or_default();

        let ptr_type = self.module.target_config().pointer_type();
        let mut sig = self.module.make_signature();
        sig.params.push(AbiParam::new(ptr_type)); // out
        sig.params.push(AbiParam::new(ptr_type)); // state_in
        sig.params.push(AbiParam::new(ptr_type)); // state_out
        sig.params.push(AbiParam::new(types::I32)); // state_len

        let func_name = format!("bc_nxt_{}", self.func_counter);
        self.func_counter += 1;
        let func_id = self
            .module
            .declare_function(&func_name, Linkage::Local, &sig)?;

        self.ctx.func.signature = sig;
        self.ctx.func.name = UserFuncName::user(0, func_id.as_u32());

        {
            let mut builder = FunctionBuilder::new(&mut self.ctx.func, &mut self.builder_ctx);

            let reg_count = (func.max_register as usize) + 1;
            let block_map = build_block_map(&mut builder, &func.instructions, reg_count);

            let entry_block = block_map[0].expect("PC 0 must have a block");
            builder.append_block_params_for_function_params(entry_block);
            builder.switch_to_block(entry_block);

            let out_ptr = builder.block_params(entry_block)[0];
            let state_in_ptr = builder.block_params(entry_block)[1];
            let state_out_ptr = builder.block_params(entry_block)[2];
            let state_len = builder.block_params(entry_block)[3];

            let mut regs = RegMap::new(func.max_register, &mut builder);
            // Auto-materialize quantifier domains from SetEnum opcodes in the
            // bytecode. This enables JIT compilation of actions that quantify
            // over model constants (e.g., \E node \in Nodes: ...).
            let auto_domains =
                collect_quantifier_domains_from_bytecode(&func.instructions, constants);
            let mut loop_stack: QuantifierLoopStack = Vec::new();
            let mut set_tracker = SetEnumTracker::new();
            let mut compound_tracker = CompoundRegTracker::new(func.max_register);
            let field_ids: &[u32] = constants.map(|c| c.field_ids()).unwrap_or(&[]);

            // Cache TLA2_JIT_DIAG env var once per compilation (not per instruction).
            let jit_diag = std::env::var("TLA2_JIT_DIAG").is_ok();

            lower_instruction_sequence(
                &mut builder,
                &func.instructions,
                &mut regs,
                &block_map,
                out_ptr,
                state_in_ptr,
                Some(state_out_ptr),
                state_len,
                &auto_domains,
                &mut loop_stack,
                &mut set_tracker,
                &mut compound_tracker,
                state_layout,
                &var_offsets,
                field_ids,
                constants,
                Some(unchanged_vars),
                &mut self.module,
                LoweringMode::NextState,
                jit_diag,
            )?;

            seal_and_finalize(builder, &block_map);
        }

        // Compile to machine code and extract function pointer
        let code_ptr = finalize_and_get_ptr(&mut self.module, &mut self.ctx, func_id)?;
        // SAFETY: The transmute from `*const u8` to `JitNextStateFn` is sound because:
        // 1. Calling convention: Cranelift uses `isa().default_call_conv()` (platform C
        //    ABI). `JitNextStateFn` is `unsafe extern "C" fn(...)`, matching exactly.
        // 2. Signature: The Cranelift IR function takes (ptr, ptr, ptr, I32) with no
        //    return value, matching `JitNextStateFn`'s
        //    `(*mut JitCallOut, *const i64, *mut i64, u32)`.
        //    Params declared at lines 664-668 above.
        // 3. Lifetime: Code buffer owned by `self.module`, outlives the returned fn ptr.
        // 4. Validity: `finalize_and_get_ptr` calls `finalize_definitions()` and returns
        //    a non-null pointer to executable W^X memory.
        debug_assert!(!code_ptr.is_null(), "JIT next-state code pointer is null");
        let jit_fn: JitNextStateFn = unsafe { std::mem::transmute(code_ptr) };

        Ok(Some(jit_fn))
    }

    /// Try to compile a next-state function. Returns `None` if not eligible.
    pub fn try_compile_next_state(
        &mut self,
        func: &BytecodeFunction,
    ) -> Result<Option<JitNextStateFn>, JitError> {
        if !self.is_next_state_eligible(func) {
            return Ok(None);
        }
        self.compile_next_state(func)
    }
}

/// Populate the compound register tracker after a LoadVar instruction.
///
/// If the loaded variable has a compound layout (Record, Function, Tuple, etc.)
/// with a known starting slot offset, records this in the tracker so that
/// subsequent RecordGet/FuncApply/TupleGet can emit native code.
fn populate_compound_tracker(
    rd: u8,
    var_idx: usize,
    state_layout: Option<&StateLayout>,
    var_offsets: &[Option<usize>],
    compound_tracker: &mut CompoundRegTracker,
) {
    let layout = match state_layout {
        Some(sl) => sl,
        None => return,
    };
    let var_layout = match layout.var_layout(var_idx) {
        Some(vl) => vl,
        None => return,
    };
    let base_slot = match var_offsets.get(var_idx).copied().flatten() {
        Some(s) => s,
        None => return,
    };

    if let VarLayout::Compound(cl) = var_layout {
        compound_tracker.set(
            rd,
            func_record_ops::CompoundRegInfo {
                layout: cl.clone(),
                base_slot,
                is_direct_ptr: false,
                direct_ptr_val: None,
            },
        );
    }
}

/// Check if an opcode is a block terminator (ends control flow).
fn is_terminator(op: &Opcode) -> bool {
    matches!(
        op,
        Opcode::Jump { .. }
            | Opcode::JumpTrue { .. }
            | Opcode::JumpFalse { .. }
            | Opcode::Ret { .. }
            | Opcode::ForallBegin { .. }
            | Opcode::ExistsBegin { .. }
            | Opcode::ForallNext { .. }
            | Opcode::ExistsNext { .. }
            | Opcode::ChooseBegin { .. }
            | Opcode::ChooseNext { .. }
    )
}
