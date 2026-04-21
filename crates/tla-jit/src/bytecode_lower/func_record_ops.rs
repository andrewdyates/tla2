// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Function application, record field access, tuple index, and domain lowering.
//!
//! When the state layout is known at JIT compile time and the compound value
//! has a fixed serialized size with scalar fields, these opcodes are lowered
//! to native i64 loads from the state buffer — no fallback needed.
//!
//! When the layout is unknown or the compound has nested compound fields,
//! the JIT emits a `FallbackNeeded` status write and returns immediately.
//! The caller (e.g., `JitInvariantCache`) sees `FallbackNeeded` and
//! re-evaluates the entire expression using the bytecode VM or tree-walker.
//!
//! # Serialized compound format (from compound_layout.rs)
//!
//! ```text
//! Record [a |-> 1, b |-> TRUE]:
//!   slot[0] = TAG_RECORD (1)
//!   slot[1] = 2 (field count)
//!   slot[2] = name_id("a")
//!   slot[3] = TAG_INT (5)
//!   slot[4] = 1
//!   slot[5] = name_id("b")
//!   slot[6] = TAG_BOOL (6)
//!   slot[7] = 1 (TRUE)
//! ```
//!
//! Each scalar field occupies: 1 (name_id) + 2 (TAG + value) = 3 slots.
//! The value for field at sorted-position `i` is at:
//!   `base + 2 + sum(1 + field_j_size for j in 0..i) + 1 + 1`
//! which for all-scalar fields simplifies to:
//!   `base + 2 + i * 3 + 1 + 1` = `base + 4 + i * 3`
//!
//! Part of #3798.

use crate::abi::{JitCallOut, JitStatus};
use crate::compound_layout::CompoundLayout;
use crate::error::JitError;
use crate::jit_native::{JITModule, Linkage, Module};
use cranelift_codegen::ir::{types, AbiParam, InstBuilder, MemFlags, Value};
use cranelift_frontend::FunctionBuilder;
use tla_core::NameId;
use tla_tir::bytecode::{BuiltinOp, Opcode};

use super::RegMap;

/// Metadata about a register holding a compound value loaded from the state buffer.
///
/// When `LoadVar` loads a compound state variable, we record the variable's
/// byte offset in the state array and its layout. `RecordGet`, `FuncApply`,
/// and `TupleGet` on that register can then emit direct loads instead of
/// falling back to the interpreter.
#[derive(Debug, Clone)]
pub(crate) struct CompoundRegInfo {
    /// The layout of the compound value in this register.
    pub(crate) layout: CompoundLayout,
    /// The starting slot index within the state buffer (in i64 units).
    pub(crate) base_slot: usize,
    /// When true, the register holds a direct pointer to the serialized data
    /// (e.g., a stack-allocated buffer from LoadConst). When false (default),
    /// the data lives in the state buffer at `state_ptr + base_slot * 8`.
    pub(crate) is_direct_ptr: bool,
    /// When set, this Cranelift IR Value is used as the base pointer for field
    /// access instead of `regs.get(rs)`. This is needed when the register value
    /// holds a scratch buffer offset (for StoreVar compatibility) but compound
    /// access needs a direct pointer to inline stack-allocated data.
    /// Part of #3949.
    pub(crate) direct_ptr_val: Option<Value>,
}

impl CompoundRegInfo {
    /// Create a CompoundRegInfo with default `direct_ptr_val: None`.
    pub(crate) fn new(layout: CompoundLayout, base_slot: usize, is_direct_ptr: bool) -> Self {
        Self {
            layout,
            base_slot,
            is_direct_ptr,
            direct_ptr_val: None,
        }
    }

    /// Create with an explicit direct_ptr_val for inline-stack compounds.
    pub(crate) fn with_direct_ptr(
        layout: CompoundLayout,
        base_slot: usize,
        ptr_val: Value,
    ) -> Self {
        Self {
            layout,
            base_slot,
            is_direct_ptr: true,
            direct_ptr_val: Some(ptr_val),
        }
    }
}

/// Tracks which registers hold compound values with known layouts.
///
/// This is populated by `LoadVar` when the state layout indicates a compound
/// variable, and consumed by `RecordGet`/`FuncApply`/`TupleGet`.
#[derive(Debug, Default)]
pub(crate) struct CompoundRegTracker {
    /// Map from register index to compound info.
    /// None means the register does not hold a known compound value.
    entries: Vec<Option<CompoundRegInfo>>,
}

impl CompoundRegTracker {
    pub(crate) fn new(max_register: u8) -> Self {
        CompoundRegTracker {
            entries: vec![None; (max_register as usize) + 1],
        }
    }

    /// Record that register `reg` holds a compound value from the state buffer.
    pub(crate) fn set(&mut self, reg: u8, info: CompoundRegInfo) {
        debug_assert!(
            (reg as usize) < self.entries.len(),
            "CompoundRegTracker: register {} beyond max {}",
            reg,
            self.entries.len()
        );
        if (reg as usize) < self.entries.len() {
            self.entries[reg as usize] = Some(info);
        }
    }

    /// Get compound info for a register, if it holds a known compound value.
    pub(crate) fn get(&self, reg: u8) -> Option<&CompoundRegInfo> {
        self.entries.get(reg as usize).and_then(|e| e.as_ref())
    }

    /// Clear compound tracking for a register (e.g., when overwritten by
    /// a non-compound operation).
    pub(crate) fn clear(&mut self, reg: u8) {
        debug_assert!(
            (reg as usize) < self.entries.len(),
            "CompoundRegTracker: register {} beyond max {}",
            reg,
            self.entries.len()
        );
        if (reg as usize) < self.entries.len() {
            self.entries[reg as usize] = None;
        }
    }
}

/// Write `FallbackNeeded` or `PartialPass` status to the JitCallOut struct and return.
///
/// This is the JIT-side implementation of the "call back to interpreter"
/// pattern: rather than actually calling the interpreter from native code
/// (which would require complex ABI bridging), we signal the caller that
/// this state needs interpreter evaluation.
///
/// When `conjuncts_passed > 0`, emits `PartialPass` instead of `FallbackNeeded`,
/// indicating that some top-level conjuncts of an invariant conjunction were
/// already verified by JIT. The caller can skip those conjuncts when falling
/// back to the interpreter.
pub(crate) fn emit_fallback_and_return(
    builder: &mut FunctionBuilder,
    out_ptr: Value,
    conjuncts_passed: u32,
) {
    let status_offset = std::mem::offset_of!(JitCallOut, status) as i32;
    if conjuncts_passed > 0 {
        // Emit PartialPass with conjunct count
        let status = builder
            .ins()
            .iconst(types::I8, JitStatus::PartialPass as i64);
        builder
            .ins()
            .store(MemFlags::trusted(), status, out_ptr, status_offset);

        let conjuncts_offset = std::mem::offset_of!(JitCallOut, conjuncts_passed) as i32;
        let count = builder.ins().iconst(types::I32, conjuncts_passed as i64);
        builder
            .ins()
            .store(MemFlags::trusted(), count, out_ptr, conjuncts_offset);
    } else {
        // Emit FallbackNeeded (no conjuncts verified)
        let status = builder
            .ins()
            .iconst(types::I8, JitStatus::FallbackNeeded as i64);
        builder
            .ins()
            .store(MemFlags::trusted(), status, out_ptr, status_offset);
    }
    builder.ins().return_(&[]);
}

// ============================================================================
// Runtime helper call emission
// ============================================================================

/// Emit a call to `jit_record_get_i64` runtime helper for dynamic record field access.
///
/// Used when the record layout is not fully known at compile time (e.g., dynamic
/// field layouts or nested compound fields), but the compound tracker knows the
/// register holds a record from the state buffer.
///
/// Returns `(found_val, result_val)` where `found_val` is 1 if field found, 0 if not.
/// The caller should check `found_val` and emit fallback if the field was not found.
fn emit_record_get_helper(
    builder: &mut FunctionBuilder,
    module: &mut JITModule,
    state_ptr: Value,
    base_slot: usize,
    field_name_id: u32,
    out_ptr: Value,
) -> Result<(Value, Value), JitError> {
    let mut sig = module.make_signature();
    let ptr_type = module.target_config().pointer_type();
    sig.params.push(AbiParam::new(ptr_type)); // state_ptr
    sig.params.push(AbiParam::new(types::I64)); // record_base_slot
    sig.params.push(AbiParam::new(types::I64)); // field_name_id
    sig.params.push(AbiParam::new(ptr_type)); // found_out ptr
    sig.returns.push(AbiParam::new(types::I64)); // result value

    let func_id = module
        .declare_function("jit_record_get_i64", Linkage::Import, &sig)
        .map_err(|e| JitError::CompileError(e.to_string()))?;
    let func_ref = module.declare_func_in_func(func_id, builder.func);

    let base_val = builder.ins().iconst(types::I64, base_slot as i64);
    let name_val = builder.ins().iconst(types::I64, field_name_id as i64);

    // Allocate stack slot for found_out
    use cranelift_codegen::ir::StackSlotData;
    let slot = builder.create_sized_stack_slot(StackSlotData::new(
        cranelift_codegen::ir::StackSlotKind::ExplicitSlot,
        8, // i64 = 8 bytes
        0,
    ));
    let found_ptr = builder.ins().stack_addr(ptr_type, slot, 0);

    let call = builder
        .ins()
        .call(func_ref, &[state_ptr, base_val, name_val, found_ptr]);
    let result_val = builder.inst_results(call)[0];

    // Load found_out from the stack slot
    let found_val = builder
        .ins()
        .load(types::I64, MemFlags::trusted(), found_ptr, 0);

    // If not found, emit fallback
    let found_block = builder.create_block();
    let not_found_block = builder.create_block();

    let zero = builder.ins().iconst(types::I64, 0);
    let is_not_found = builder.ins().icmp(
        cranelift_codegen::ir::condcodes::IntCC::Equal,
        found_val,
        zero,
    );
    builder
        .ins()
        .brif(is_not_found, not_found_block, &[], found_block, &[]);

    // not_found_block: fallback to interpreter for proper error handling
    builder.switch_to_block(not_found_block);
    // Error path: field not found — always FallbackNeeded (not PartialPass)
    emit_fallback_and_return(builder, out_ptr, 0);

    builder.seal_block(not_found_block);
    builder.seal_block(found_block);

    // found_block: continue with result
    builder.switch_to_block(found_block);

    Ok((found_val, result_val))
}

/// Emit a call to `jit_func_apply_i64` runtime helper for function lookup.
///
/// Used when the function layout is not suitable for the compile-time unrolled
/// loop (e.g., non-scalar values or unknown pair count at compile time), but
/// the compound tracker knows the register holds a function.
///
/// Returns `(found_val, result_val)` where `found_val` is 1 if key found, 0 if not.
fn emit_func_apply_helper(
    builder: &mut FunctionBuilder,
    module: &mut JITModule,
    state_ptr: Value,
    base_slot: usize,
    key_val: Value,
    out_ptr: Value,
) -> Result<(Value, Value), JitError> {
    let mut sig = module.make_signature();
    let ptr_type = module.target_config().pointer_type();
    sig.params.push(AbiParam::new(ptr_type)); // state_ptr
    sig.params.push(AbiParam::new(types::I64)); // func_base_slot
    sig.params.push(AbiParam::new(types::I64)); // key_value
    sig.params.push(AbiParam::new(ptr_type)); // found_out ptr
    sig.returns.push(AbiParam::new(types::I64)); // result value

    let func_id = module
        .declare_function("jit_func_apply_i64", Linkage::Import, &sig)
        .map_err(|e| JitError::CompileError(e.to_string()))?;
    let func_ref = module.declare_func_in_func(func_id, builder.func);

    let base_val = builder.ins().iconst(types::I64, base_slot as i64);

    // Allocate stack slot for found_out
    use cranelift_codegen::ir::StackSlotData;
    let slot = builder.create_sized_stack_slot(StackSlotData::new(
        cranelift_codegen::ir::StackSlotKind::ExplicitSlot,
        8, // i64 = 8 bytes
        0,
    ));
    let found_ptr = builder.ins().stack_addr(ptr_type, slot, 0);

    let call = builder
        .ins()
        .call(func_ref, &[state_ptr, base_val, key_val, found_ptr]);
    let result_val = builder.inst_results(call)[0];

    // Load found_out from the stack slot
    let found_val = builder
        .ins()
        .load(types::I64, MemFlags::trusted(), found_ptr, 0);

    // If not found, emit fallback
    let found_block = builder.create_block();
    let not_found_block = builder.create_block();

    let zero = builder.ins().iconst(types::I64, 0);
    let is_not_found = builder.ins().icmp(
        cranelift_codegen::ir::condcodes::IntCC::Equal,
        found_val,
        zero,
    );
    builder
        .ins()
        .brif(is_not_found, not_found_block, &[], found_block, &[]);

    // not_found_block: fallback to interpreter for proper error handling
    builder.switch_to_block(not_found_block);
    // Error path: key not found — always FallbackNeeded (not PartialPass)
    emit_fallback_and_return(builder, out_ptr, 0);

    builder.seal_block(not_found_block);
    builder.seal_block(found_block);

    // found_block: continue with result
    builder.switch_to_block(found_block);

    Ok((found_val, result_val))
}

/// Emit a call to `jit_compound_count` runtime helper.
///
/// Reads the count field at `base_slot + 1` of any compound value
/// (set, sequence, function).
fn emit_compound_count_helper(
    builder: &mut FunctionBuilder,
    module: &mut JITModule,
    state_ptr: Value,
    base_slot: usize,
) -> Result<Value, JitError> {
    let mut sig = module.make_signature();
    let ptr_type = module.target_config().pointer_type();
    sig.params.push(AbiParam::new(ptr_type)); // state_ptr
    sig.params.push(AbiParam::new(types::I64)); // base_slot
    sig.returns.push(AbiParam::new(types::I64)); // count

    let func_id = module
        .declare_function("jit_compound_count", Linkage::Import, &sig)
        .map_err(|e| JitError::CompileError(e.to_string()))?;
    let func_ref = module.declare_func_in_func(func_id, builder.func);

    let base_val = builder.ins().iconst(types::I64, base_slot as i64);
    let call = builder.ins().call(func_ref, &[state_ptr, base_val]);
    Ok(builder.inst_results(call)[0])
}

/// Emit a call to `jit_seq_get_i64` runtime helper for sequence element access.
///
/// Parameters:
///   - `state_ptr`: pointer to the flat i64 state buffer
///   - `base_slot`: slot index where TAG_SEQ begins
///   - `index_val`: the 0-based element index (Cranelift SSA value)
///   - `out_ptr`: JitCallOut pointer for fallback emission on not-found
///
/// Returns `(found_val, result_val)` where `found_val` is 1 if index is in bounds, 0 if not.
/// The caller should check `found_val` and emit fallback if the index was out of bounds.
fn emit_seq_get_helper(
    builder: &mut FunctionBuilder,
    module: &mut JITModule,
    state_ptr: Value,
    base_slot: usize,
    index_val: Value,
    out_ptr: Value,
) -> Result<(Value, Value), JitError> {
    let mut sig = module.make_signature();
    let ptr_type = module.target_config().pointer_type();
    sig.params.push(AbiParam::new(ptr_type)); // state_ptr
    sig.params.push(AbiParam::new(types::I64)); // seq_base_slot
    sig.params.push(AbiParam::new(types::I64)); // index
    sig.params.push(AbiParam::new(ptr_type)); // found_out ptr
    sig.returns.push(AbiParam::new(types::I64)); // result value

    let func_id = module
        .declare_function("jit_seq_get_i64", Linkage::Import, &sig)
        .map_err(|e| JitError::CompileError(e.to_string()))?;
    let func_ref = module.declare_func_in_func(func_id, builder.func);

    let base_val = builder.ins().iconst(types::I64, base_slot as i64);

    // Allocate stack slot for found_out
    use cranelift_codegen::ir::StackSlotData;
    let slot = builder.create_sized_stack_slot(StackSlotData::new(
        cranelift_codegen::ir::StackSlotKind::ExplicitSlot,
        8, // i64 = 8 bytes
        0,
    ));
    let found_ptr = builder.ins().stack_addr(ptr_type, slot, 0);

    let call = builder
        .ins()
        .call(func_ref, &[state_ptr, base_val, index_val, found_ptr]);
    let result_val = builder.inst_results(call)[0];

    // Load found_out from the stack slot
    let found_val = builder
        .ins()
        .load(types::I64, MemFlags::trusted(), found_ptr, 0);

    // If not found, emit fallback
    let found_block = builder.create_block();
    let not_found_block = builder.create_block();

    let zero = builder.ins().iconst(types::I64, 0);
    let is_not_found = builder.ins().icmp(
        cranelift_codegen::ir::condcodes::IntCC::Equal,
        found_val,
        zero,
    );
    builder
        .ins()
        .brif(is_not_found, not_found_block, &[], found_block, &[]);

    // not_found_block: fallback to interpreter for proper error handling
    builder.switch_to_block(not_found_block);
    // Error path: index out of bounds — always FallbackNeeded (not PartialPass)
    emit_fallback_and_return(builder, out_ptr, 0);

    builder.seal_block(not_found_block);
    builder.seal_block(found_block);

    // found_block: continue with result
    builder.switch_to_block(found_block);

    Ok((found_val, result_val))
}

// ============================================================================
// RecordGet native lowering
// ============================================================================

/// Result of resolving a record field's position within a serialized record.
///
/// Contains the field's starting tag offset (from record base), the field's
/// layout, and the value offset (past the tag) for scalar access.
struct RecordFieldResolution<'a> {
    /// Offset from record base to the field's TAG slot.
    tag_offset: usize,
    /// Offset from record base to the field's VALUE slot (tag_offset + 1 for scalars).
    value_offset: usize,
    /// The layout of this field.
    layout: &'a CompoundLayout,
}

/// Compute the slot offset (from record base) of a field's TAG and VALUE,
/// along with its layout descriptor.
///
/// Like `compute_record_field_value_offset`, but also returns the tag offset
/// and layout reference so the caller can decide whether to propagate compound
/// tracking for non-scalar fields.
fn resolve_record_field<'a>(
    fields: &'a [(NameId, CompoundLayout)],
    target_name_id: NameId,
) -> Option<RecordFieldResolution<'a>> {
    let mut offset = 2; // skip TAG_RECORD + field_count
    for (name_id, field_layout) in fields {
        offset += 1; // name_id slot
        let field_size = field_layout.fixed_serialized_slots()?;
        if *name_id == target_name_id {
            return Some(RecordFieldResolution {
                tag_offset: offset,
                value_offset: offset + 1,
                layout: field_layout,
            });
        }
        offset += field_size;
    }
    None
}

/// Try to emit native RecordGet. Returns true if handled natively.
///
/// Handles the case where:
/// - The source register holds a compound record loaded from the state buffer
/// - All preceding fields have fixed serialized sizes (for offset computation)
/// - The target field NameId can be resolved
///
/// For scalar fields, loads the value directly from the state buffer.
/// For compound fields (record, tuple, function, sequence, set), loads the
/// tag slot and propagates compound tracking so chained access patterns
/// like `state[var].field.subfield` can also be resolved natively.
fn try_lower_record_get_native(
    builder: &mut FunctionBuilder,
    rd: u8,
    rs: u8,
    field_name_id: NameId,
    regs: &mut RegMap,
    compound_tracker: &mut CompoundRegTracker,
    state_ptr: Value,
) -> bool {
    let info = match compound_tracker.get(rs) {
        Some(info) => info.clone(),
        None => return false,
    };

    let fields = match &info.layout {
        CompoundLayout::Record { fields } => fields,
        _ => return false,
    };

    // Resolve the field position and layout within the serialized record
    let resolution = match resolve_record_field(fields, field_name_id) {
        Some(r) => r,
        None => return false,
    };

    // Determine the base pointer for field access:
    // 1. direct_ptr_val: explicit IR Value from inline stack serialization (RecordNew)
    // 2. is_direct_ptr: register holds direct pointer (LoadConst)
    // 3. Otherwise: use state_ptr (LoadVar)
    // Part of #3949.
    let base_ptr = if let Some(ptr_val) = info.direct_ptr_val {
        ptr_val
    } else if info.is_direct_ptr {
        regs.get(rs)
    } else {
        state_ptr
    };

    if resolution.layout.is_scalar() {
        // Scalar field: load the value directly (past the tag)
        let abs_slot = info.base_slot + resolution.value_offset;
        let byte_offset = (abs_slot as i32) * 8;
        let val = builder
            .ins()
            .load(types::I64, MemFlags::trusted(), base_ptr, byte_offset);
        regs.set(rd, val);
        compound_tracker.clear(rd);
    } else {
        // Compound field: load the tag slot and propagate compound tracking.
        let abs_tag_slot = info.base_slot + resolution.tag_offset;
        let byte_offset = (abs_tag_slot as i32) * 8;
        let val = builder
            .ins()
            .load(types::I64, MemFlags::trusted(), base_ptr, byte_offset);
        regs.set(rd, val);

        // Propagate compound tracking: preserve is_direct_ptr and direct_ptr_val
        // so nested access continues to use the correct base pointer.
        compound_tracker.set(
            rd,
            CompoundRegInfo {
                layout: resolution.layout.clone(),
                base_slot: abs_tag_slot,
                is_direct_ptr: info.is_direct_ptr,
                direct_ptr_val: info.direct_ptr_val,
            },
        );
    }

    true
}

// ============================================================================
// FuncApply native lowering
// ============================================================================

/// Try to emit native FuncApply for functions with known layout.
///
/// Two strategies:
///
/// 1. **Direct-index** (O(1)): When the function has a contiguous integer domain
///    `[lo..lo+n-1 -> T]`, compiles `f[k]` to a single indexed load:
///    `load(state_ptr, base + 2 + (k - lo) * pair_slots + key_slots)`.
///    This is the SPIN-class optimization from #3985 Phase 2.
///
/// 2. **Linear scan** (O(n)): For other scalar-key/scalar-value functions,
///    emits a runtime loop comparing each key until a match is found.
///
/// Part of #3985: Phase 2 compound layout wiring.
fn try_lower_func_apply_native(
    builder: &mut FunctionBuilder,
    rd: u8,
    func_reg: u8,
    arg_reg: u8,
    regs: &mut RegMap,
    compound_tracker: &mut CompoundRegTracker,
    state_ptr: Value,
    out_ptr: Value,
) -> bool {
    let info = match compound_tracker.get(func_reg) {
        Some(info) => info.clone(),
        None => return false,
    };

    // Part of #4030: Handle Sequence FuncApply natively.
    //
    // TLA+ sequences are 1-indexed: seq[i] accesses the i-th element (1-based).
    // Serialized format: [TAG_SEQ, n, TAG_elem, elem_0_val, TAG_elem, elem_1_val, ...]
    // So seq[i] value is at: base_slot + 2 + (i-1) * elem_slots + 1
    //
    // For sequences with scalar elements, this is a direct O(1) index load,
    // identical to Function direct-index with domain_lo=1.
    //
    // For sequences with compound elements, we propagate compound tracking
    // so subsequent FuncApply/RecordGet on the result can also be lowered natively.
    if let CompoundLayout::Sequence {
        element_layout,
        element_count,
    } = &info.layout
    {
        let elem_slots = match element_layout.fixed_serialized_slots() {
            Some(s) => s,
            None => return false,
        };
        // Need known element count for bounds checking.
        let len = match element_count {
            Some(n) if *n > 0 => *n,
            _ => return false,
        };

        // Determine base pointer: direct_ptr_val > is_direct_ptr > state_ptr.
        let base_ptr = if let Some(ptr_val) = info.direct_ptr_val {
            ptr_val
        } else if info.is_direct_ptr {
            regs.get(func_reg)
        } else {
            state_ptr
        };

        let arg_val = regs.get(arg_reg);

        // TLA+ sequences are 1-indexed: convert to 0-based.
        let one = builder.ins().iconst(types::I64, 1);
        let index = builder.ins().isub(arg_val, one);

        // Bounds check: 0 <= index < len (unsigned comparison catches negatives)
        let max_idx = builder.ins().iconst(types::I64, (len - 1) as i64);
        let oob = builder.ins().icmp(
            cranelift_codegen::ir::condcodes::IntCC::UnsignedGreaterThan,
            index,
            max_idx,
        );

        let in_bounds_block = builder.create_block();
        let oob_block = builder.create_block();

        builder
            .ins()
            .brif(oob, oob_block, &[], in_bounds_block, &[]);

        // Out-of-bounds: fallback to interpreter for domain error.
        builder.switch_to_block(oob_block);
        emit_fallback_and_return(builder, out_ptr, 0);
        builder.seal_block(oob_block);

        builder.switch_to_block(in_bounds_block);

        if element_layout.is_scalar() {
            // Scalar element: load the value directly.
            // Value is at: base_slot + 2 + index * elem_slots + 1
            // (skip: TAG_SEQ, count, then index*elem_slots elements, then tag byte)
            let elem_size_c = builder.ins().iconst(types::I64, elem_slots as i64);
            let elem_offset = builder.ins().imul(index, elem_size_c);
            // value_slot = base_slot + 2 + elem_offset + 1 (skip element tag)
            let base_offset = builder
                .ins()
                .iconst(types::I64, (info.base_slot + 2 + 1) as i64);
            let value_slot = builder.ins().iadd(base_offset, elem_offset);
            let eight = builder.ins().iconst(types::I64, 8);
            let byte_offset = builder.ins().imul(value_slot, eight);
            let addr = builder.ins().iadd(base_ptr, byte_offset);
            let loaded_val = builder.ins().load(types::I64, MemFlags::trusted(), addr, 0);

            regs.set(rd, loaded_val);
            compound_tracker.clear(rd);
        } else {
            // Compound element: compute the base slot of the inner compound value
            // and propagate compound tracking so subsequent accesses can be lowered.
            //
            // Inner element starts at: base_slot + 2 + index * elem_slots
            let elem_size_c = builder.ins().iconst(types::I64, elem_slots as i64);
            let elem_offset = builder.ins().imul(index, elem_size_c);
            let base_offset = builder
                .ins()
                .iconst(types::I64, (info.base_slot + 2) as i64);
            let inner_base_slot = builder.ins().iadd(base_offset, elem_offset);

            // Store the computed base slot in the register for potential
            // downstream compound access. The value itself is at the base slot.
            regs.set(rd, inner_base_slot);
            compound_tracker.set(
                rd,
                CompoundRegInfo {
                    layout: (**element_layout).clone(),
                    // base_slot is dynamic (depends on index), so we use 0 and
                    // rely on the register holding the actual slot offset.
                    // But the downstream compound access uses base_slot as a fixed
                    // offset — this won't work for dynamic indexing.
                    //
                    // For now, we can handle the case where the index is a constant
                    // (LoadImm), but for general dynamic indexing, the compound
                    // tracker's static base_slot model doesn't support it.
                    // Fall through to FallbackNeeded for truly dynamic nested access.
                    base_slot: 0,
                    is_direct_ptr: false,
                    direct_ptr_val: None,
                },
            );
        }

        builder.seal_block(in_bounds_block);
        return true;
    }

    let (key_layout, value_layout) = match &info.layout {
        CompoundLayout::Function {
            key_layout,
            value_layout,
            ..
        } => (key_layout.as_ref(), value_layout.as_ref()),
        _ => return false,
    };

    // Only handle scalar key + scalar value functions.
    if !key_layout.is_scalar() || !value_layout.is_scalar() {
        return false;
    }

    // Determine base pointer: direct_ptr_val > is_direct_ptr > state_ptr.
    // Part of #3949.
    let base_ptr = if let Some(ptr_val) = info.direct_ptr_val {
        ptr_val
    } else if info.is_direct_ptr {
        regs.get(func_reg)
    } else {
        state_ptr
    };

    let key_size = match key_layout.fixed_serialized_slots() {
        Some(s) => s,
        None => return false,
    };
    let value_size = match value_layout.fixed_serialized_slots() {
        Some(s) => s,
        None => return false,
    };
    let pair_slot_size = key_size + value_size; // e.g., 4 for int->int

    let arg_val = regs.get(arg_reg);

    // ---- Strategy 1: Direct-index for contiguous integer domains ----
    // When the layout tells us `[lo..lo+n-1 -> T]`, we can compute the
    // value offset at compile time: f[k] = slots[base + 2 + (k-lo)*pair_slots + key_slots + 1].
    // This eliminates the O(n) linear scan entirely.
    //
    // Part of #3985: Phase 2 — FuncApply on [1..N -> T] => load(base + arg - domain_low).
    if let Some((lo, len)) = info.layout.int_array_bounds() {
        // Emit: index = arg - lo
        let lo_const = builder.ins().iconst(types::I64, lo);
        let index = builder.ins().isub(arg_val, lo_const);

        // Bounds check: 0 <= index < len (unsigned comparison catches negatives)
        let max_idx = builder.ins().iconst(types::I64, (len - 1) as i64);
        let oob = builder.ins().icmp(
            cranelift_codegen::ir::condcodes::IntCC::UnsignedGreaterThan,
            index,
            max_idx,
        );

        let in_bounds_block = builder.create_block();
        let oob_block = builder.create_block();

        builder
            .ins()
            .brif(oob, oob_block, &[], in_bounds_block, &[]);

        // Out-of-bounds: fallback to interpreter for domain error.
        builder.switch_to_block(oob_block);
        emit_fallback_and_return(builder, out_ptr, 0);
        builder.seal_block(oob_block);

        // In-bounds: compute value slot and load.
        // Value is at: base_slot + 2 + index * pair_slot_size + key_size + 1
        // (skip: TAG_FUNC, count, then index*pair_size pairs, then key tag+val, then val tag)
        builder.switch_to_block(in_bounds_block);

        let pair_size_c = builder.ins().iconst(types::I64, pair_slot_size as i64);
        let pair_offset = builder.ins().imul(index, pair_size_c);
        // value_slot = base_slot + 2 + pair_offset + key_size + 1
        let base_offset = builder
            .ins()
            .iconst(types::I64, (info.base_slot + 2 + key_size + 1) as i64);
        let value_slot = builder.ins().iadd(base_offset, pair_offset);
        let eight = builder.ins().iconst(types::I64, 8);
        let byte_offset = builder.ins().imul(value_slot, eight);
        let addr = builder.ins().iadd(base_ptr, byte_offset);
        let loaded_val = builder.ins().load(types::I64, MemFlags::trusted(), addr, 0);

        regs.set(rd, loaded_val);
        compound_tracker.clear(rd);

        builder.seal_block(in_bounds_block);
        return true;
    }

    // ---- Strategy 2: Linear scan for general scalar functions ----
    // Load pair_count from buffer: base_ptr[base_slot + 1]
    let count_slot = (info.base_slot + 1) as i32;
    let pair_count_val =
        builder
            .ins()
            .load(types::I64, MemFlags::trusted(), base_ptr, count_slot * 8);

    let loop_header = builder.create_block();
    let loop_body = builder.create_block();
    let found_block = builder.create_block();
    let not_found_block = builder.create_block();
    let merge_block = builder.create_block();

    builder.append_block_param(loop_header, types::I64);
    builder.append_block_param(found_block, types::I64);
    builder.append_block_param(merge_block, types::I64);

    let zero = builder.ins().iconst(types::I64, 0);
    builder.ins().jump(loop_header, &[zero]);

    // === loop_header ===
    builder.switch_to_block(loop_header);
    let idx = builder.block_params(loop_header)[0];
    let done = builder.ins().icmp(
        cranelift_codegen::ir::condcodes::IntCC::SignedGreaterThanOrEqual,
        idx,
        pair_count_val,
    );
    builder
        .ins()
        .brif(done, not_found_block, &[], loop_body, &[]);

    // === loop_body ===
    builder.switch_to_block(loop_body);
    let pair_slot_size_const = builder.ins().iconst(types::I64, pair_slot_size as i64);
    let pair_offset_slots = builder.ins().imul(idx, pair_slot_size_const);
    let base_plus_header = builder
        .ins()
        .iconst(types::I64, (info.base_slot + 2) as i64);
    let pair_start = builder.ins().iadd(base_plus_header, pair_offset_slots);
    let one = builder.ins().iconst(types::I64, 1);
    let key_slot = builder.ins().iadd(pair_start, one);
    let eight = builder.ins().iconst(types::I64, 8);
    let key_byte_offset = builder.ins().imul(key_slot, eight);
    let key_addr = builder.ins().iadd(base_ptr, key_byte_offset);
    let loaded_key = builder
        .ins()
        .load(types::I64, MemFlags::trusted(), key_addr, 0);

    let key_match = builder.ins().icmp(
        cranelift_codegen::ir::condcodes::IntCC::Equal,
        loaded_key,
        arg_val,
    );

    let no_match_block = builder.create_block();
    let key_size_const = builder.ins().iconst(types::I64, key_size as i64);
    let val_tag_slot = builder.ins().iadd(pair_start, key_size_const);
    let val_slot = builder.ins().iadd(val_tag_slot, one);
    let val_byte_offset = builder.ins().imul(val_slot, eight);
    let val_addr = builder.ins().iadd(base_ptr, val_byte_offset);
    let loaded_val = builder
        .ins()
        .load(types::I64, MemFlags::trusted(), val_addr, 0);

    builder
        .ins()
        .brif(key_match, found_block, &[loaded_val], no_match_block, &[]);

    builder.switch_to_block(no_match_block);
    let next_idx = builder.ins().iadd_imm(idx, 1);
    builder.ins().jump(loop_header, &[next_idx]);

    builder.switch_to_block(found_block);
    let result = builder.block_params(found_block)[0];
    builder.ins().jump(merge_block, &[result]);

    builder.switch_to_block(not_found_block);
    emit_fallback_and_return(builder, out_ptr, 0);

    builder.seal_block(loop_header);
    builder.seal_block(loop_body);
    builder.seal_block(found_block);
    builder.seal_block(not_found_block);
    builder.seal_block(no_match_block);
    builder.seal_block(merge_block);

    builder.switch_to_block(merge_block);
    let merge_result = builder.block_params(merge_block)[0];
    regs.set(rd, merge_result);
    compound_tracker.clear(rd);

    true
}

// ============================================================================
// FuncExcept native lowering
// ============================================================================

/// Try to emit native FuncExcept for `[f EXCEPT ![k] = v]`.
///
/// Handles the case where:
/// - The func register holds a function loaded from the state buffer with known layout
/// - The function has scalar keys and scalar values
/// - The path and val registers hold scalar values
///
/// Emits a copy-and-modify loop:
/// 1. Copy the entire serialized function from the input region
///    (using state_ptr[base_slot]) into the output section of state_ptr
///    (at a "shadow" offset after the primary slots, mirroring the input layout).
/// 2. Scan the copied pairs to find the key matching `path`.
/// 3. Overwrite the value at the found position with `val`.
/// 4. Register `rd` gets the base slot offset of the copied data.
///
/// Part of #3958: native FuncExcept enables JIT for TLA+ EXCEPT operations.
fn try_lower_func_except_native(
    builder: &mut FunctionBuilder,
    rd: u8,
    func_reg: u8,
    path_reg: u8,
    val_reg: u8,
    regs: &mut RegMap,
    compound_tracker: &mut CompoundRegTracker,
    state_ptr: Value,
    out_ptr: Value,
) -> bool {
    let info = match compound_tracker.get(func_reg) {
        Some(info) => info.clone(),
        None => return false,
    };

    // Part of #4030: Handle Sequence EXCEPT natively.
    //
    // [seq EXCEPT ![i] = v] modifies the i-th element (1-based) of a sequence.
    // Serialized format: [TAG_SEQ, n, TAG_elem, elem_0, TAG_elem, elem_1, ...]
    // Element value at position i (1-based) is at: base_slot + 2 + (i-1) * elem_slots + 1
    if let CompoundLayout::Sequence {
        element_layout,
        element_count,
    } = &info.layout
    {
        // Only handle scalar-element sequences for EXCEPT.
        if !element_layout.is_scalar() {
            return false;
        }
        let elem_slots = match element_layout.fixed_serialized_slots() {
            Some(s) => s,
            None => return false,
        };
        let len = match element_count {
            Some(n) if *n > 0 => *n,
            _ => return false,
        };

        let path_val = regs.get(path_reg);
        let new_val = regs.get(val_reg);

        // TLA+ sequences are 1-indexed: convert to 0-based.
        let one = builder.ins().iconst(types::I64, 1);
        let index = builder.ins().isub(path_val, one);

        // Bounds check
        let max_idx = builder.ins().iconst(types::I64, (len - 1) as i64);
        let oob = builder.ins().icmp(
            cranelift_codegen::ir::condcodes::IntCC::UnsignedGreaterThan,
            index,
            max_idx,
        );

        let in_bounds_block = builder.create_block();
        let oob_block = builder.create_block();
        let merge_block = builder.create_block();

        builder
            .ins()
            .brif(oob, oob_block, &[], in_bounds_block, &[]);

        builder.switch_to_block(oob_block);
        emit_fallback_and_return(builder, out_ptr, 0);
        builder.seal_block(oob_block);

        builder.switch_to_block(in_bounds_block);

        // Compute the value slot and store in-place.
        // Value is at: base_slot + 2 + index * elem_slots + 1 (skip element tag)
        let elem_size_c = builder.ins().iconst(types::I64, elem_slots as i64);
        let elem_offset = builder.ins().imul(index, elem_size_c);
        let base_offset = builder
            .ins()
            .iconst(types::I64, (info.base_slot + 2 + 1) as i64);
        let value_slot = builder.ins().iadd(base_offset, elem_offset);
        let eight = builder.ins().iconst(types::I64, 8);
        let byte_offset = builder.ins().imul(value_slot, eight);
        let addr = builder.ins().iadd(state_ptr, byte_offset);
        builder.ins().store(MemFlags::trusted(), new_val, addr, 0);
        builder.ins().jump(merge_block, &[]);

        builder.seal_block(in_bounds_block);
        builder.seal_block(merge_block);

        builder.switch_to_block(merge_block);

        // rd gets the base_slot offset (sequence modified in-place)
        let base_val = builder.ins().iconst(types::I64, info.base_slot as i64);
        regs.set(rd, base_val);
        compound_tracker.set(
            rd,
            CompoundRegInfo {
                layout: info.layout.clone(),
                base_slot: info.base_slot,
                is_direct_ptr: info.is_direct_ptr,
                direct_ptr_val: info.direct_ptr_val,
            },
        );
        return true;
    }

    let (key_layout, value_layout) = match &info.layout {
        CompoundLayout::Function {
            key_layout,
            value_layout,
            ..
        } => (key_layout.as_ref(), value_layout.as_ref()),
        _ => return false,
    };

    // Only handle scalar-key, scalar-value functions.
    if !key_layout.is_scalar() || !value_layout.is_scalar() {
        return false;
    }

    let key_size = match key_layout.fixed_serialized_slots() {
        Some(s) => s,
        None => return false,
    };
    let value_size = match value_layout.fixed_serialized_slots() {
        Some(s) => s,
        None => return false,
    };
    let pair_slot_size = key_size + value_size;

    let path_val = regs.get(path_reg);
    let new_val = regs.get(val_reg);

    // ---- Strategy 1: Direct-index store for contiguous integer domains ----
    // [f EXCEPT ![k] = v] with domain [lo..lo+n-1] becomes a single store:
    //   store(state_ptr, base + 2 + (k-lo)*pair_slots + key_size + 1, v)
    //
    // Part of #3985: Phase 2 — FuncExcept on [1..N -> T] => store(base + offset, value).
    if let Some((lo, len)) = info.layout.int_array_bounds() {
        let lo_const = builder.ins().iconst(types::I64, lo);
        let index = builder.ins().isub(path_val, lo_const);

        // Bounds check
        let max_idx = builder.ins().iconst(types::I64, (len - 1) as i64);
        let oob = builder.ins().icmp(
            cranelift_codegen::ir::condcodes::IntCC::UnsignedGreaterThan,
            index,
            max_idx,
        );

        let in_bounds_block = builder.create_block();
        let oob_block = builder.create_block();
        let merge_block = builder.create_block();

        builder
            .ins()
            .brif(oob, oob_block, &[], in_bounds_block, &[]);

        builder.switch_to_block(oob_block);
        emit_fallback_and_return(builder, out_ptr, 0);
        builder.seal_block(oob_block);

        builder.switch_to_block(in_bounds_block);

        // Compute the value slot and store in-place.
        let pair_size_c = builder.ins().iconst(types::I64, pair_slot_size as i64);
        let pair_offset = builder.ins().imul(index, pair_size_c);
        let base_offset = builder
            .ins()
            .iconst(types::I64, (info.base_slot + 2 + key_size + 1) as i64);
        let value_slot = builder.ins().iadd(base_offset, pair_offset);
        let eight = builder.ins().iconst(types::I64, 8);
        let byte_offset = builder.ins().imul(value_slot, eight);
        let addr = builder.ins().iadd(state_ptr, byte_offset);
        builder.ins().store(MemFlags::trusted(), new_val, addr, 0);
        builder.ins().jump(merge_block, &[]);

        builder.seal_block(in_bounds_block);
        builder.seal_block(merge_block);

        builder.switch_to_block(merge_block);

        // rd gets the base_slot offset (function modified in-place)
        let base_val = builder.ins().iconst(types::I64, info.base_slot as i64);
        regs.set(rd, base_val);
        compound_tracker.set(
            rd,
            CompoundRegInfo {
                layout: info.layout.clone(),
                base_slot: info.base_slot,
                is_direct_ptr: info.is_direct_ptr,
                direct_ptr_val: info.direct_ptr_val,
            },
        );
        return true;
    }

    // ---- Strategy 2: Linear search-and-modify loop ----
    // Load pair_count from state buffer: state_ptr[base_slot + 1]
    let count_slot = (info.base_slot + 1) as i32;
    let pair_count_val =
        builder
            .ins()
            .load(types::I64, MemFlags::trusted(), state_ptr, count_slot * 8);

    // The action reads state_in, modifies it, and writes to state_out.
    // For compound variables, the serialized data lives in the state_in buffer.
    // We modify the data in-place in state_in (safe because each state is processed
    // once), then StoreVar writes the offset to state_out.

    let loop_header = builder.create_block();
    let loop_body = builder.create_block();
    let found_block = builder.create_block();
    let not_found_block = builder.create_block();
    let no_match_block = builder.create_block();
    let merge_block = builder.create_block();

    builder.append_block_param(loop_header, types::I64);

    let zero = builder.ins().iconst(types::I64, 0);
    builder.ins().jump(loop_header, &[zero]);

    // === loop_header: check if index < pair_count ===
    builder.switch_to_block(loop_header);
    let idx = builder.block_params(loop_header)[0];
    let done = builder.ins().icmp(
        cranelift_codegen::ir::condcodes::IntCC::SignedGreaterThanOrEqual,
        idx,
        pair_count_val,
    );
    builder
        .ins()
        .brif(done, not_found_block, &[], loop_body, &[]);

    // === loop_body: compare key, modify if match ===
    builder.switch_to_block(loop_body);
    let pair_slot_size_c = builder.ins().iconst(types::I64, pair_slot_size as i64);
    let pair_offset = builder.ins().imul(idx, pair_slot_size_c);
    let base_plus_header = builder
        .ins()
        .iconst(types::I64, (info.base_slot + 2) as i64);
    let pair_start = builder.ins().iadd(base_plus_header, pair_offset);
    let one = builder.ins().iconst(types::I64, 1);
    let key_slot = builder.ins().iadd(pair_start, one);
    let eight = builder.ins().iconst(types::I64, 8);
    let key_byte_offset = builder.ins().imul(key_slot, eight);
    let key_addr = builder.ins().iadd(state_ptr, key_byte_offset);
    let loaded_key = builder
        .ins()
        .load(types::I64, MemFlags::trusted(), key_addr, 0);

    let key_match = builder.ins().icmp(
        cranelift_codegen::ir::condcodes::IntCC::Equal,
        loaded_key,
        path_val,
    );
    builder
        .ins()
        .brif(key_match, found_block, &[], no_match_block, &[]);

    builder.switch_to_block(no_match_block);
    let next_idx = builder.ins().iadd_imm(idx, 1);
    builder.ins().jump(loop_header, &[next_idx]);

    // === found_block: overwrite the value at the found position ===
    builder.switch_to_block(found_block);
    let key_size_c = builder.ins().iconst(types::I64, key_size as i64);
    let val_tag_slot = builder.ins().iadd(pair_start, key_size_c);
    let val_slot = builder.ins().iadd(val_tag_slot, one);
    let val_byte_offset = builder.ins().imul(val_slot, eight);
    let val_addr = builder.ins().iadd(state_ptr, val_byte_offset);
    builder
        .ins()
        .store(MemFlags::trusted(), new_val, val_addr, 0);
    builder.ins().jump(merge_block, &[]);

    // === not_found_block: key not in domain — fallback ===
    builder.switch_to_block(not_found_block);
    emit_fallback_and_return(builder, out_ptr, 0);

    builder.seal_block(loop_header);
    builder.seal_block(loop_body);
    builder.seal_block(found_block);
    builder.seal_block(not_found_block);
    builder.seal_block(no_match_block);
    builder.seal_block(merge_block);

    // === merge_block: result ===
    builder.switch_to_block(merge_block);
    // rd gets the base_slot offset (the function is now modified in-place)
    let base_offset = builder.ins().iconst(types::I64, info.base_slot as i64);
    regs.set(rd, base_offset);

    // Track rd as holding the same compound layout at the same offset
    compound_tracker.set(
        rd,
        CompoundRegInfo {
            layout: info.layout.clone(),
            base_slot: info.base_slot,
            is_direct_ptr: info.is_direct_ptr,
            direct_ptr_val: info.direct_ptr_val,
        },
    );

    true
}

// ============================================================================
// TupleGet native lowering
// ============================================================================

/// Try to emit native TupleGet for tuples with known layout.
///
/// Handles the case where:
/// - The source register holds a compound tuple loaded from the state buffer
/// - All preceding elements have fixed serialized sizes (for offset computation)
/// - The index is within bounds
///
/// For scalar elements, loads the value directly (past the tag).
/// For compound elements, loads the tag slot and propagates compound tracking
/// so chained access patterns like `tuple[1].field` work natively.
fn try_lower_tuple_get_native(
    builder: &mut FunctionBuilder,
    rd: u8,
    rs: u8,
    idx: u16,
    regs: &mut RegMap,
    compound_tracker: &mut CompoundRegTracker,
    state_ptr: Value,
) -> bool {
    let info = match compound_tracker.get(rs) {
        Some(info) => info.clone(),
        None => return false,
    };

    let element_layouts = match &info.layout {
        CompoundLayout::Tuple { element_layouts } => element_layouts,
        _ => return false,
    };

    // TupleGet idx is 1-indexed per TLA+ convention
    let zero_idx = match (idx as usize).checked_sub(1) {
        Some(i) => i,
        None => return false,
    };
    if zero_idx >= element_layouts.len() {
        return false;
    }

    // Compute slot offset: skip TAG_TUPLE + elem_count, then skip preceding elements
    let mut offset = 2; // TAG + count
    for elem_layout in &element_layouts[..zero_idx] {
        let elem_size = match elem_layout.fixed_serialized_slots() {
            Some(s) => s,
            None => return false,
        };
        offset += elem_size;
    }

    // Check the target element has a known fixed size (needed to confirm
    // the offset computation is valid even for non-scalar elements).
    if element_layouts[zero_idx].fixed_serialized_slots().is_none() {
        return false;
    }

    let target_layout = &element_layouts[zero_idx];
    let abs_tag_slot = info.base_slot + offset;

    // Determine base pointer: direct_ptr_val > is_direct_ptr > state_ptr.
    // Part of #3949.
    let base_ptr = if let Some(ptr_val) = info.direct_ptr_val {
        ptr_val
    } else if info.is_direct_ptr {
        regs.get(rs)
    } else {
        state_ptr
    };

    if target_layout.is_scalar() {
        // Scalar element: load the value (past the tag)
        let value_slot = abs_tag_slot + 1;
        let byte_offset = (value_slot as i32) * 8;
        let val = builder
            .ins()
            .load(types::I64, MemFlags::trusted(), base_ptr, byte_offset);
        regs.set(rd, val);
        compound_tracker.clear(rd);
    } else {
        // Compound element: load the tag slot and propagate tracking
        let byte_offset = (abs_tag_slot as i32) * 8;
        let val = builder
            .ins()
            .load(types::I64, MemFlags::trusted(), base_ptr, byte_offset);
        regs.set(rd, val);
        // Preserve is_direct_ptr and direct_ptr_val for nested compound access.
        compound_tracker.set(
            rd,
            CompoundRegInfo {
                layout: target_layout.clone(),
                base_slot: abs_tag_slot,
                is_direct_ptr: info.is_direct_ptr,
                direct_ptr_val: info.direct_ptr_val,
            },
        );
    }

    true
}

// ============================================================================
// CallBuiltin lowering (Len, Cardinality, IsFiniteSet, Head)
// ============================================================================

/// Lower a `CallBuiltin` opcode.
///
/// - **IsFiniteSet**: In model checking, all sets are finite. Emits `iconst 1`
///   (TRUE) directly — no compound access needed.
/// - **Len / Cardinality**: When the argument register has a known compound
///   layout (from `LoadVar` with a `StateLayout`), the count field is read
///   directly from the serialized state buffer at `base_slot + 1`. Without
///   layout info, emits `FallbackNeeded`.
/// - **Head**: When the argument register holds a Sequence with scalar elements
///   and the layout is known, loads the first element's value directly from
///   `base_slot + 3` (skip TAG_SEQ + count + element_TAG). Emits a runtime
///   length check: if the sequence is empty, falls back to the interpreter
///   (which will produce the proper "Head of empty sequence" error).
/// - **Tail / Append / SubSeq**: Always emit `FallbackNeeded` because they
///   produce new sequences (compound values) that cannot be represented as
///   a single i64 in the JIT register file.
/// - **ToString**: Always emits `FallbackNeeded` (returns a string/compound).
///
/// Part of #3909 item 2.3.
fn lower_call_builtin(
    builder: &mut FunctionBuilder,
    rd: u8,
    builtin: BuiltinOp,
    args_start: u8,
    _argc: u8,
    regs: &mut RegMap,
    out_ptr: Value,
    state_ptr: Option<Value>,
    compound_tracker: &mut CompoundRegTracker,
    conjuncts_passed: u32,
    module: Option<&mut JITModule>,
) -> Result<CompoundLowerResult, JitError> {
    match builtin {
        // IsFiniteSet: in TLA+ model checking, all materialized sets are finite.
        // No need to inspect the argument — always return TRUE (1).
        BuiltinOp::IsFiniteSet => {
            let one = builder.ins().iconst(types::I64, 1);
            regs.set(rd, one);
            compound_tracker.clear(rd);
            Ok(CompoundLowerResult::NativeHandled)
        }

        // Len and Cardinality: read the count field from the serialized
        // compound value in the state buffer.
        //
        // Serialized format for Set/Sequence/Function:
        //   slot[base + 0] = TAG  (TAG_SET / TAG_SEQ / TAG_FUNC)
        //   slot[base + 1] = count (element count / pair count)
        //   slot[base + 2..] = elements
        //
        // When the compound layout is known (the arg register was loaded via
        // LoadVar with a StateLayout), we can emit a direct i64 load from
        // state_ptr[base_slot + 1].
        BuiltinOp::Len | BuiltinOp::Cardinality => {
            let arg_reg = args_start;
            if let Some(sp) = state_ptr {
                if let Some(info) = compound_tracker.get(arg_reg) {
                    // Verify the layout is a type that has a count field at offset 1
                    let has_count = matches!(
                        &info.layout,
                        CompoundLayout::Set { .. }
                            | CompoundLayout::Sequence { .. }
                            | CompoundLayout::Function { .. }
                    );
                    if has_count {
                        let count_slot = (info.base_slot + 1) as i32;
                        let byte_offset = count_slot * 8; // i64 = 8 bytes
                        let count_val =
                            builder
                                .ins()
                                .load(types::I64, MemFlags::trusted(), sp, byte_offset);
                        regs.set(rd, count_val);
                        compound_tracker.clear(rd);
                        return Ok(CompoundLowerResult::NativeHandled);
                    }
                }
            }
            // No layout info or unsupported compound type — fallback
            emit_fallback_and_return(builder, out_ptr, conjuncts_passed);
            Ok(CompoundLowerResult::FallbackEmitted)
        }

        // Head(seq): extract the first element of a sequence.
        //
        // Serialized sequence format:
        //   slot[base + 0] = TAG_SEQ
        //   slot[base + 1] = count (number of elements)
        //   slot[base + 2] = TAG of element 0
        //   slot[base + 3] = value of element 0
        //   ...
        //
        // When the sequence has a known layout with scalar elements (Int, Bool,
        // String — 2 slots each: TAG + value), the first element's value is at
        // base_slot + 3. We emit a runtime check that count > 0; if zero, we
        // fall back to the interpreter for proper error reporting.
        //
        // Part of #3909.
        BuiltinOp::Head => {
            let arg_reg = args_start;
            if let Some(sp) = state_ptr {
                if let Some(info) = compound_tracker.get(arg_reg) {
                    let info = info.clone();
                    if let CompoundLayout::Sequence {
                        ref element_layout, ..
                    } = info.layout
                    {
                        if element_layout.is_scalar() {
                            return lower_head_native(
                                builder,
                                rd,
                                &info,
                                regs,
                                out_ptr,
                                sp,
                                compound_tracker,
                            );
                        }
                    }
                }
            }
            // No layout info, non-scalar elements, or not a sequence — fallback
            emit_fallback_and_return(builder, out_ptr, conjuncts_passed);
            Ok(CompoundLowerResult::FallbackEmitted)
        }

        // Tail(seq): return all elements except the first.
        //
        // When the argument register holds a Sequence with scalar elements
        // and a known layout, calls the `jit_seq_tail` runtime helper which
        // writes the result to the compound scratch buffer. The helper returns
        // an encoded offset that downstream StoreVar can write to state_out.
        //
        // Falls back to interpreter if: no layout info, non-scalar elements,
        // or not a sequence.
        //
        // Part of #4030: JIT native Tail support.
        BuiltinOp::Tail => {
            let arg_reg = args_start;
            if let Some(sp) = state_ptr {
                if let Some(info) = compound_tracker.get(arg_reg) {
                    let info = info.clone();
                    if let CompoundLayout::Sequence {
                        ref element_layout, ..
                    } = info.layout
                    {
                        if element_layout.is_scalar() {
                            return lower_tail_native(
                                builder,
                                rd,
                                &info,
                                regs,
                                out_ptr,
                                sp,
                                compound_tracker,
                                module,
                            );
                        }
                    }
                }
            }
            emit_fallback_and_return(builder, out_ptr, conjuncts_passed);
            Ok(CompoundLowerResult::FallbackEmitted)
        }

        // Append(seq, elem): append an element to a sequence.
        //
        // When the sequence register holds a Sequence with scalar elements
        // and the value to append is scalar, calls the `jit_seq_append`
        // runtime helper which writes the result to the compound scratch buffer.
        //
        // Part of #4030: JIT native Append support.
        BuiltinOp::Append => {
            let seq_reg = args_start;
            let elem_reg = args_start + 1;
            if let Some(sp) = state_ptr {
                if let Some(info) = compound_tracker.get(seq_reg) {
                    let info = info.clone();
                    if let CompoundLayout::Sequence {
                        ref element_layout, ..
                    } = info.layout
                    {
                        if element_layout.is_scalar() {
                            return lower_append_native(
                                builder,
                                rd,
                                &info,
                                seq_reg,
                                elem_reg,
                                regs,
                                out_ptr,
                                sp,
                                compound_tracker,
                                module,
                                element_layout,
                            );
                        }
                    }
                }
            }
            emit_fallback_and_return(builder, out_ptr, conjuncts_passed);
            Ok(CompoundLowerResult::FallbackEmitted)
        }

        // SubSeq: always fallback (complex slicing with variable bounds).
        BuiltinOp::SubSeq => {
            emit_fallback_and_return(builder, out_ptr, conjuncts_passed);
            Ok(CompoundLowerResult::FallbackEmitted)
        }

        // ToString: always fallback (produces a string/compound value).
        BuiltinOp::ToString => {
            emit_fallback_and_return(builder, out_ptr, conjuncts_passed);
            Ok(CompoundLowerResult::FallbackEmitted)
        }

        // Seq: always fallback (produces a set of sequences — compound value).
        // Part of #3967.
        BuiltinOp::Seq => {
            emit_fallback_and_return(builder, out_ptr, conjuncts_passed);
            Ok(CompoundLowerResult::FallbackEmitted)
        }
    }
}

/// Emit native Head lowering for a sequence with scalar elements.
///
/// Emits:
///   1. Load count from state_ptr[base_slot + 1]
///   2. If count == 0, emit FallbackNeeded + return (interpreter handles error)
///   3. Otherwise, load the first element's value from state_ptr[base_slot + 3]
///
/// The first element of a scalar sequence occupies slots [base+2, base+3]:
///   slot[base+2] = element TAG (TAG_INT / TAG_BOOL / TAG_STRING)
///   slot[base+3] = element value
fn lower_head_native(
    builder: &mut FunctionBuilder,
    rd: u8,
    info: &CompoundRegInfo,
    regs: &mut RegMap,
    out_ptr: Value,
    state_ptr: Value,
    compound_tracker: &mut CompoundRegTracker,
) -> Result<CompoundLowerResult, JitError> {
    // Load the sequence length from the state buffer
    let count_byte_offset = ((info.base_slot + 1) as i32) * 8;
    let count_val = builder.ins().load(
        types::I64,
        MemFlags::trusted(),
        state_ptr,
        count_byte_offset,
    );

    // Create blocks for the empty check
    let nonempty_block = builder.create_block();
    let empty_block = builder.create_block();

    // Branch: if count == 0, go to empty_block (fallback); else nonempty_block
    let zero = builder.ins().iconst(types::I64, 0);
    let is_empty = builder.ins().icmp(
        cranelift_codegen::ir::condcodes::IntCC::Equal,
        count_val,
        zero,
    );
    builder
        .ins()
        .brif(is_empty, empty_block, &[], nonempty_block, &[]);

    // === empty_block: sequence is empty, Head is an error — fallback ===
    builder.switch_to_block(empty_block);
    // Error path: empty sequence — always FallbackNeeded (not PartialPass)
    emit_fallback_and_return(builder, out_ptr, 0);

    // === nonempty_block: load the first element's value ===
    builder.switch_to_block(nonempty_block);
    // First element value is at base_slot + 3 (TAG_SEQ + count + elem_TAG + value)
    let value_byte_offset = ((info.base_slot + 3) as i32) * 8;
    let head_val = builder.ins().load(
        types::I64,
        MemFlags::trusted(),
        state_ptr,
        value_byte_offset,
    );
    regs.set(rd, head_val);
    compound_tracker.clear(rd);

    // Seal both blocks
    builder.seal_block(empty_block);
    builder.seal_block(nonempty_block);

    // Execution continues from nonempty_block — the empty path returned.
    Ok(CompoundLowerResult::NativeHandled)
}

// ============================================================================
// Tail native lowering
// ============================================================================

/// Emit native Tail lowering for a sequence with scalar elements.
///
/// Calls the `jit_seq_tail` runtime helper which:
///   1. Checks the sequence is non-empty (returns 0 if empty)
///   2. Constructs a new sequence in the compound scratch buffer
///   3. Returns an encoded scratch offset
///
/// The result register gets the scratch offset, which downstream StoreVar
/// writes to state_out. The unflatten path reads from the scratch buffer
/// when it sees a COMPOUND_SCRATCH_BASE-encoded offset.
///
/// Part of #4030: JIT native Tail support.
fn lower_tail_native(
    builder: &mut FunctionBuilder,
    rd: u8,
    info: &CompoundRegInfo,
    regs: &mut RegMap,
    out_ptr: Value,
    state_ptr: Value,
    compound_tracker: &mut CompoundRegTracker,
    module: Option<&mut JITModule>,
) -> Result<CompoundLowerResult, JitError> {
    let mod_ref = match module {
        Some(m) => m,
        None => {
            emit_fallback_and_return(builder, out_ptr, 0);
            return Ok(CompoundLowerResult::FallbackEmitted);
        }
    };

    let ptr_type = mod_ref.target_config().pointer_type();
    let mut sig = mod_ref.make_signature();
    sig.params.push(AbiParam::new(ptr_type)); // state_ptr
    sig.params.push(AbiParam::new(types::I64)); // seq_base_slot
    sig.params.push(AbiParam::new(types::I64)); // is_direct_ptr
    sig.returns.push(AbiParam::new(types::I64)); // result offset (or 0)

    let func_id = mod_ref
        .declare_function("jit_seq_tail", Linkage::Import, &sig)
        .map_err(|e| JitError::CompileError(e.to_string()))?;
    let func_ref = mod_ref.declare_func_in_func(func_id, builder.func);

    let base_ptr = if info.is_direct_ptr {
        regs.get(rd) // When direct_ptr, the register holds the pointer
    } else {
        state_ptr
    };
    let base_val = builder.ins().iconst(types::I64, info.base_slot as i64);
    let is_direct = builder
        .ins()
        .iconst(types::I64, if info.is_direct_ptr { 1 } else { 0 });

    let call = builder
        .ins()
        .call(func_ref, &[base_ptr, base_val, is_direct]);
    let result = builder.inst_results(call)[0];

    // Check if result is 0 (error: empty sequence or compound elements)
    let zero = builder.ins().iconst(types::I64, 0);
    let is_error = builder.ins().icmp(
        cranelift_codegen::ir::condcodes::IntCC::Equal,
        result,
        zero,
    );

    let ok_block = builder.create_block();
    let err_block = builder.create_block();

    builder
        .ins()
        .brif(is_error, err_block, &[], ok_block, &[]);

    // Error: fallback to interpreter
    builder.switch_to_block(err_block);
    emit_fallback_and_return(builder, out_ptr, 0);

    builder.seal_block(err_block);
    builder.seal_block(ok_block);

    // OK: result is the scratch offset
    builder.switch_to_block(ok_block);
    regs.set(rd, result);
    // Clear compound tracker — result is a scratch buffer reference, not a
    // state buffer compound. Downstream operations that need compound access
    // on the tail result will need interpreter fallback.
    compound_tracker.clear(rd);

    Ok(CompoundLowerResult::NativeHandled)
}

// ============================================================================
// Append native lowering
// ============================================================================

/// Emit native Append lowering for a sequence with scalar elements.
///
/// Calls the `jit_seq_append` runtime helper which:
///   1. Copies all existing elements from the original sequence
///   2. Appends the new element
///   3. Returns an encoded scratch offset
///
/// Part of #4030: JIT native Append support.
fn lower_append_native(
    builder: &mut FunctionBuilder,
    rd: u8,
    info: &CompoundRegInfo,
    _seq_reg: u8,
    elem_reg: u8,
    regs: &mut RegMap,
    out_ptr: Value,
    state_ptr: Value,
    compound_tracker: &mut CompoundRegTracker,
    module: Option<&mut JITModule>,
    element_layout: &CompoundLayout,
) -> Result<CompoundLowerResult, JitError> {
    let mod_ref = match module {
        Some(m) => m,
        None => {
            emit_fallback_and_return(builder, out_ptr, 0);
            return Ok(CompoundLowerResult::FallbackEmitted);
        }
    };

    let ptr_type = mod_ref.target_config().pointer_type();
    let mut sig = mod_ref.make_signature();
    sig.params.push(AbiParam::new(ptr_type)); // state_ptr
    sig.params.push(AbiParam::new(types::I64)); // seq_base_slot
    sig.params.push(AbiParam::new(types::I64)); // is_direct_ptr
    sig.params.push(AbiParam::new(types::I64)); // elem_tag
    sig.params.push(AbiParam::new(types::I64)); // elem_val
    sig.returns.push(AbiParam::new(types::I64)); // result offset (or 0)

    let func_id = mod_ref
        .declare_function("jit_seq_append", Linkage::Import, &sig)
        .map_err(|e| JitError::CompileError(e.to_string()))?;
    let func_ref = mod_ref.declare_func_in_func(func_id, builder.func);

    let base_ptr = if info.is_direct_ptr {
        regs.get(rd)
    } else {
        state_ptr
    };
    let base_val = builder.ins().iconst(types::I64, info.base_slot as i64);
    let is_direct = builder
        .ins()
        .iconst(types::I64, if info.is_direct_ptr { 1 } else { 0 });

    // Determine the element tag from the layout
    let elem_tag_val = match element_layout {
        CompoundLayout::Int => crate::compound_layout::TAG_INT,
        CompoundLayout::Bool => crate::compound_layout::TAG_BOOL,
        CompoundLayout::String => crate::compound_layout::TAG_STRING,
        _ => {
            emit_fallback_and_return(builder, out_ptr, 0);
            return Ok(CompoundLowerResult::FallbackEmitted);
        }
    };
    let tag_const = builder.ins().iconst(types::I64, elem_tag_val);
    let elem_val = regs.get(elem_reg);

    let call = builder
        .ins()
        .call(func_ref, &[base_ptr, base_val, is_direct, tag_const, elem_val]);
    let result = builder.inst_results(call)[0];

    // Check if result is 0 (error)
    let zero = builder.ins().iconst(types::I64, 0);
    let is_error = builder.ins().icmp(
        cranelift_codegen::ir::condcodes::IntCC::Equal,
        result,
        zero,
    );

    let ok_block = builder.create_block();
    let err_block = builder.create_block();

    builder
        .ins()
        .brif(is_error, err_block, &[], ok_block, &[]);

    builder.switch_to_block(err_block);
    emit_fallback_and_return(builder, out_ptr, 0);

    builder.seal_block(err_block);
    builder.seal_block(ok_block);

    builder.switch_to_block(ok_block);
    regs.set(rd, result);
    compound_tracker.clear(rd);

    Ok(CompoundLowerResult::NativeHandled)
}

// ============================================================================
// RecordNew native lowering
// ============================================================================

/// Lower RecordNew with access to the constant pool.
///
/// This is the actual implementation that resolves field names from the
/// constant pool and emits the `jit_record_new_scalar` runtime helper call.
fn lower_record_new_with_constants(
    builder: &mut FunctionBuilder,
    module: &mut JITModule,
    rd: u8,
    fields_start: u16,
    values_start: u8,
    count: u8,
    regs: &mut RegMap,
    compound_tracker: &mut CompoundRegTracker,
    constants: &tla_tir::bytecode::ConstantPool,
) -> Result<CompoundLowerResult, JitError> {
    use cranelift_codegen::ir::StackSlotData;
    let n = count as usize;

    // Resolve field name IDs from the constant pool.
    // The constant pool stores Value::String(name) at indices
    // fields_start..fields_start+count. We intern each name to get NameId.
    let mut name_ids = Vec::with_capacity(n);
    for i in 0..n {
        let const_idx = fields_start + i as u16;
        let val = constants.get_value(const_idx);
        match val {
            tla_value::Value::String(s) => {
                let nid = tla_core::intern_name(s);
                name_ids.push(nid);
            }
            _ => {
                // Not a string constant — can't resolve field name
                return Ok(CompoundLowerResult::NotHandled);
            }
        }
    }

    // Sort field name IDs to match the serialization order.
    // RecordValue stores fields sorted by NameId, and the serialized format
    // must match. We need to also sort the corresponding value registers.
    let mut field_order: Vec<usize> = (0..n).collect();
    field_order.sort_by_key(|&i| name_ids[i]);

    let ptr_type = module.target_config().pointer_type();

    if n == 0 {
        // Empty record: emit inline. Just TAG_RECORD(1) + count(0).
        // Call the runtime helper with count=0.
        let mut sig = module.make_signature();
        sig.params.push(AbiParam::new(ptr_type)); // name_ids_ptr
        sig.params.push(AbiParam::new(ptr_type)); // values_ptr
        sig.params.push(AbiParam::new(ptr_type)); // tags_ptr
        sig.params.push(AbiParam::new(types::I64)); // count
        sig.returns.push(AbiParam::new(types::I64)); // encoded offset

        let func_id = module
            .declare_function("jit_record_new_scalar", Linkage::Import, &sig)
            .map_err(|e| JitError::CompileError(e.to_string()))?;
        let func_ref = module.declare_func_in_func(func_id, builder.func);

        // For empty record, pass null pointers and count=0
        let null = builder.ins().iconst(ptr_type, 0);
        let zero = builder.ins().iconst(types::I64, 0);
        let call = builder.ins().call(func_ref, &[null, null, null, zero]);
        let result = builder.inst_results(call)[0];
        regs.set(rd, result);
        compound_tracker.clear(rd);
        return Ok(CompoundLowerResult::NativeHandled);
    }

    // Serialize the record inline on the JIT stack frame.
    // Format: [TAG_RECORD, count, name_id_0, TAG_INT, val_0, name_id_1, TAG_INT, val_1, ...]
    // Total: 2 + 3*n slots, each 8 bytes.
    // This enables compound tracking with is_direct_ptr=true so subsequent
    // RecordGet on this register can use native access. Part of #3949.
    //
    // Note: Uses TAG_INT for all fields since type info is unavailable.
    // For boolean/string fields, the deserialized type will be SmallInt
    // instead of Bool/String, which may cause state mismatch. The caller
    // should prefer `lower_record_new_with_layout_tags` when tags are known.
    let total_slots = 2 + 3 * n;
    let inline_slot = builder.create_sized_stack_slot(StackSlotData::new(
        cranelift_codegen::ir::StackSlotKind::ExplicitSlot,
        (total_slots * 8) as u32,
        8, // alignment
    ));
    let inline_ptr = builder.ins().stack_addr(ptr_type, inline_slot, 0);

    // Write header: TAG_RECORD, count
    let tag_record = builder
        .ins()
        .iconst(types::I64, crate::compound_layout::TAG_RECORD);
    builder.ins().stack_store(tag_record, inline_slot, 0);
    let count_val = builder.ins().iconst(types::I64, n as i64);
    builder.ins().stack_store(count_val, inline_slot, 8);

    // Build CompoundLayout::Record fields for compound tracking.
    let mut layout_fields: Vec<(NameId, CompoundLayout)> = Vec::with_capacity(n);

    // Write each field in sorted-by-NameId order: name_id, TAG_INT, value
    for (out_idx, &src_idx) in field_order.iter().enumerate() {
        let base_byte_offset = ((2 + out_idx * 3) as i32) * 8;

        // Write name_id
        let sorted_nid = name_ids[src_idx];
        let nid_val = builder.ins().iconst(types::I64, sorted_nid.0 as i64);
        builder
            .ins()
            .stack_store(nid_val, inline_slot, base_byte_offset);

        // Write TAG_INT (default tag when type info is unavailable)
        let tag_val = builder
            .ins()
            .iconst(types::I64, crate::compound_layout::TAG_INT);
        builder
            .ins()
            .stack_store(tag_val, inline_slot, base_byte_offset + 8);

        // Write value from register
        let reg_idx = values_start + src_idx as u8;
        let field_val = regs.get(reg_idx);
        builder
            .ins()
            .stack_store(field_val, inline_slot, base_byte_offset + 16);

        // Build the field layout for compound tracking (all Int since no type info)
        layout_fields.push((sorted_nid, CompoundLayout::Int));
    }

    // Call the runtime helper to write to the scratch buffer for StoreVar
    // compatibility. The scratch buffer persists after the JIT function returns.
    // Build parallel arrays for the runtime helper: name_ids, values, tags.
    let name_ids_slot = builder.create_sized_stack_slot(
        cranelift_codegen::ir::StackSlotData::new(
            cranelift_codegen::ir::StackSlotKind::ExplicitSlot,
            (n * 8) as u32,
            8,
        ),
    );
    let values_slot = builder.create_sized_stack_slot(
        cranelift_codegen::ir::StackSlotData::new(
            cranelift_codegen::ir::StackSlotKind::ExplicitSlot,
            (n * 8) as u32,
            8,
        ),
    );
    let tags_slot = builder.create_sized_stack_slot(
        cranelift_codegen::ir::StackSlotData::new(
            cranelift_codegen::ir::StackSlotKind::ExplicitSlot,
            (n * 8) as u32,
            8,
        ),
    );

    for (out_idx, &src_idx) in field_order.iter().enumerate() {
        let sorted_nid = name_ids[src_idx];
        let nid_val = builder.ins().iconst(types::I64, sorted_nid.0 as i64);
        builder
            .ins()
            .stack_store(nid_val, name_ids_slot, (out_idx * 8) as i32);

        let tag_int = builder
            .ins()
            .iconst(types::I64, crate::compound_layout::TAG_INT);
        builder
            .ins()
            .stack_store(tag_int, tags_slot, (out_idx * 8) as i32);

        let reg_idx = values_start + src_idx as u8;
        let val = regs.get(reg_idx);
        builder
            .ins()
            .stack_store(val, values_slot, (out_idx * 8) as i32);
    }

    let mut sig = module.make_signature();
    sig.params.push(AbiParam::new(ptr_type)); // name_ids_ptr
    sig.params.push(AbiParam::new(ptr_type)); // values_ptr
    sig.params.push(AbiParam::new(ptr_type)); // tags_ptr
    sig.params.push(AbiParam::new(types::I64)); // count
    sig.returns.push(AbiParam::new(types::I64)); // encoded offset

    let func_id = module
        .declare_function("jit_record_new_scalar", Linkage::Import, &sig)
        .map_err(|e| JitError::CompileError(e.to_string()))?;
    let func_ref = module.declare_func_in_func(func_id, builder.func);

    let names_ptr = builder.ins().stack_addr(ptr_type, name_ids_slot, 0);
    let vals_ptr = builder.ins().stack_addr(ptr_type, values_slot, 0);
    let tags_ptr = builder.ins().stack_addr(ptr_type, tags_slot, 0);
    let count_arg = builder.ins().iconst(types::I64, n as i64);

    let call = builder
        .ins()
        .call(func_ref, &[names_ptr, vals_ptr, tags_ptr, count_arg]);
    let scratch_offset = builder.inst_results(call)[0];

    // Set register to scratch buffer offset (for StoreVar to persist beyond function return).
    // Compound tracker uses direct_ptr_val pointing to inline stack data (for RecordGet).
    regs.set(rd, scratch_offset);
    compound_tracker.set(
        rd,
        CompoundRegInfo {
            layout: CompoundLayout::Record {
                fields: layout_fields,
            },
            base_slot: 0,
            is_direct_ptr: true,
            direct_ptr_val: Some(inline_ptr),
        },
    );

    Ok(CompoundLowerResult::NativeHandled)
}

/// Lower RecordNew with field type tags derived from state layout.
///
/// When the target variable has a known Record layout (from CompoundLayout),
/// we can determine the correct type tag (TAG_INT, TAG_BOOL, TAG_STRING) for
/// each field. This ensures the serialized record matches the expected format
/// and deserializes correctly.
fn lower_record_new_with_layout_tags(
    builder: &mut FunctionBuilder,
    module: &mut JITModule,
    rd: u8,
    fields_start: u16,
    values_start: u8,
    count: u8,
    regs: &mut RegMap,
    compound_tracker: &mut CompoundRegTracker,
    constants: &tla_tir::bytecode::ConstantPool,
    field_tags: &[i64],
) -> Result<CompoundLowerResult, JitError> {
    use cranelift_codegen::ir::StackSlotData;
    let n = count as usize;

    if n == 0 || field_tags.len() < n {
        return lower_record_new_with_constants(
            builder,
            module,
            rd,
            fields_start,
            values_start,
            count,
            regs,
            compound_tracker,
            constants,
        );
    }

    // Resolve field name IDs from the constant pool.
    let mut name_ids = Vec::with_capacity(n);
    for i in 0..n {
        let const_idx = fields_start + i as u16;
        let val = constants.get_value(const_idx);
        match val {
            tla_value::Value::String(s) => {
                let nid = tla_core::intern_name(s);
                name_ids.push(nid);
            }
            _ => return Ok(CompoundLowerResult::NotHandled),
        }
    }

    // Sort by NameId and build the sorted field_order
    let mut field_order: Vec<usize> = (0..n).collect();
    field_order.sort_by_key(|&i| name_ids[i]);

    let ptr_type = module.target_config().pointer_type();

    // Serialize the record inline on the JIT stack frame.
    // Format: [TAG_RECORD, count, name_id_0, tag_0, val_0, name_id_1, tag_1, val_1, ...]
    // Total: 2 + 3*n slots, each 8 bytes.
    // This enables compound tracking with is_direct_ptr=true so subsequent
    // RecordGet on this register can use native access. Part of #3949.
    let total_slots = 2 + 3 * n;
    let inline_slot = builder.create_sized_stack_slot(StackSlotData::new(
        cranelift_codegen::ir::StackSlotKind::ExplicitSlot,
        (total_slots * 8) as u32,
        8, // alignment
    ));
    let inline_ptr = builder.ins().stack_addr(ptr_type, inline_slot, 0);

    // Write header: TAG_RECORD, count
    let tag_record = builder
        .ins()
        .iconst(types::I64, crate::compound_layout::TAG_RECORD);
    builder.ins().stack_store(tag_record, inline_slot, 0);
    let count_val = builder.ins().iconst(types::I64, n as i64);
    builder.ins().stack_store(count_val, inline_slot, 8);

    // Build CompoundLayout::Record fields for compound tracking.
    let mut layout_fields: Vec<(NameId, CompoundLayout)> = Vec::with_capacity(n);

    // Write each field in sorted-by-NameId order: name_id, tag, value
    for (out_idx, &src_idx) in field_order.iter().enumerate() {
        let base_byte_offset = ((2 + out_idx * 3) as i32) * 8;

        // Write name_id
        let sorted_nid = name_ids[src_idx];
        let nid_val = builder.ins().iconst(types::I64, sorted_nid.0 as i64);
        builder
            .ins()
            .stack_store(nid_val, inline_slot, base_byte_offset);

        // Write tag
        let tag = field_tags[out_idx];
        let tag_val = builder.ins().iconst(types::I64, tag);
        builder
            .ins()
            .stack_store(tag_val, inline_slot, base_byte_offset + 8);

        // Write value from register
        let reg_idx = values_start + src_idx as u8;
        let field_val = regs.get(reg_idx);
        builder
            .ins()
            .stack_store(field_val, inline_slot, base_byte_offset + 16);

        // Build the field layout for compound tracking
        let field_layout = match tag {
            crate::compound_layout::TAG_BOOL => CompoundLayout::Bool,
            crate::compound_layout::TAG_STRING => CompoundLayout::String,
            _ => CompoundLayout::Int, // TAG_INT or unknown — default to Int
        };
        layout_fields.push((sorted_nid, field_layout));
    }

    // Call the runtime helper to write to the scratch buffer for StoreVar
    // compatibility. The scratch buffer persists after the JIT function returns.
    let name_ids_slot = builder.create_sized_stack_slot(
        cranelift_codegen::ir::StackSlotData::new(
            cranelift_codegen::ir::StackSlotKind::ExplicitSlot,
            (n * 8) as u32,
            8,
        ),
    );
    let values_slot = builder.create_sized_stack_slot(
        cranelift_codegen::ir::StackSlotData::new(
            cranelift_codegen::ir::StackSlotKind::ExplicitSlot,
            (n * 8) as u32,
            8,
        ),
    );
    let tags_slot_rt = builder.create_sized_stack_slot(
        cranelift_codegen::ir::StackSlotData::new(
            cranelift_codegen::ir::StackSlotKind::ExplicitSlot,
            (n * 8) as u32,
            8,
        ),
    );

    for (out_idx, &src_idx) in field_order.iter().enumerate() {
        let sorted_nid = name_ids[src_idx];
        let nid_val = builder.ins().iconst(types::I64, sorted_nid.0 as i64);
        builder
            .ins()
            .stack_store(nid_val, name_ids_slot, (out_idx * 8) as i32);

        let tag = field_tags[out_idx];
        let tag_val = builder.ins().iconst(types::I64, tag);
        builder
            .ins()
            .stack_store(tag_val, tags_slot_rt, (out_idx * 8) as i32);

        let reg_idx = values_start + src_idx as u8;
        let val = regs.get(reg_idx);
        builder
            .ins()
            .stack_store(val, values_slot, (out_idx * 8) as i32);
    }

    let mut sig = module.make_signature();
    sig.params.push(AbiParam::new(ptr_type)); // name_ids_ptr
    sig.params.push(AbiParam::new(ptr_type)); // values_ptr
    sig.params.push(AbiParam::new(ptr_type)); // tags_ptr
    sig.params.push(AbiParam::new(types::I64)); // count
    sig.returns.push(AbiParam::new(types::I64)); // encoded offset

    let func_id = module
        .declare_function("jit_record_new_scalar", Linkage::Import, &sig)
        .map_err(|e| JitError::CompileError(e.to_string()))?;
    let func_ref = module.declare_func_in_func(func_id, builder.func);

    let names_ptr = builder.ins().stack_addr(ptr_type, name_ids_slot, 0);
    let vals_ptr = builder.ins().stack_addr(ptr_type, values_slot, 0);
    let tags_ptr_rt = builder.ins().stack_addr(ptr_type, tags_slot_rt, 0);
    let count_arg = builder.ins().iconst(types::I64, n as i64);

    let call = builder
        .ins()
        .call(func_ref, &[names_ptr, vals_ptr, tags_ptr_rt, count_arg]);
    let scratch_offset = builder.inst_results(call)[0];

    // Set register to scratch buffer offset (for StoreVar to persist beyond function return).
    // Compound tracker uses direct_ptr_val pointing to inline stack data (for RecordGet).
    regs.set(rd, scratch_offset);
    compound_tracker.set(
        rd,
        CompoundRegInfo {
            layout: CompoundLayout::Record {
                fields: layout_fields,
            },
            base_slot: 0,
            is_direct_ptr: true,
            direct_ptr_val: Some(inline_ptr),
        },
    );

    Ok(CompoundLowerResult::NativeHandled)
}

// ============================================================================
// RecordNew field tag resolution
// ============================================================================

/// Resolve the type tags for RecordNew fields by matching against the state layout.
///
/// Looks at all Record-typed variables in the state layout. If one has the same
/// field names (by NameId) as the fields in this RecordNew, returns the per-field
/// type tags in sorted-by-NameId order.
///
/// Returns `None` if no matching layout is found or if any field has a non-scalar
/// layout (we only handle all-scalar records natively).
fn resolve_record_field_tags(
    fields_start: u16,
    count: u8,
    constants: &tla_tir::bytecode::ConstantPool,
    state_layout: Option<&crate::compound_layout::StateLayout>,
) -> Option<Vec<i64>> {
    let layout = state_layout?;
    let n = count as usize;

    // Resolve field name IDs from the constant pool
    let mut name_ids = Vec::with_capacity(n);
    for i in 0..n {
        let const_idx = fields_start + i as u16;
        let val = constants.get_value(const_idx);
        match val {
            tla_value::Value::String(s) => {
                let nid = tla_core::intern_name(s);
                name_ids.push(nid);
            }
            _ => return None,
        }
    }

    // Sort by NameId (records are stored sorted)
    let mut sorted_nids = name_ids.clone();
    sorted_nids.sort();

    // Search all state variables for a matching Record layout
    for var_idx in 0..layout.var_count() {
        if let Some(crate::compound_layout::VarLayout::Compound(CompoundLayout::Record {
            fields,
        })) = layout.var_layout(var_idx)
        {
            if fields.len() != n {
                continue;
            }

            // Check if all field names match (both are sorted by NameId)
            let all_match = fields
                .iter()
                .zip(sorted_nids.iter())
                .all(|((fid, _), nid)| fid == nid);

            if all_match {
                // Extract the type tags from the field layouts
                let mut tags = Vec::with_capacity(n);
                for (_, field_layout) in fields {
                    let tag = match field_layout {
                        CompoundLayout::Int => crate::compound_layout::TAG_INT,
                        CompoundLayout::Bool => crate::compound_layout::TAG_BOOL,
                        CompoundLayout::String => crate::compound_layout::TAG_STRING,
                        _ => return None, // Non-scalar field — can't handle natively
                    };
                    tags.push(tag);
                }
                return Some(tags);
            }
        }
    }

    None
}

// ============================================================================
// Public dispatch
// ============================================================================

/// Result of lowering a compound-value opcode.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CompoundLowerResult {
    /// Opcode was not a compound-value opcode; try another lowering module.
    NotHandled,
    /// Opcode was handled with native code (no terminator emitted).
    /// Execution continues to the next instruction.
    NativeHandled,
    /// Opcode was handled by emitting FallbackNeeded + return (terminator).
    /// Subsequent instructions are dead code until the next block boundary.
    FallbackEmitted,
}

/// Lower a function application, record field access, tuple index, or domain opcode.
///
/// When compound layout information is available (via `compound_tracker` and
/// `field_name_ids`), native code is emitted for direct state buffer access.
/// Otherwise, `FallbackNeeded` status is written and the function returns.
///
/// `Domain` always emits FallbackNeeded because it produces a set (compound value)
/// that cannot be represented as a single i64 in the JIT register file.
///
/// When `conjuncts_passed > 0`, fallback emissions write `PartialPass` instead of
/// `FallbackNeeded`, indicating that some conjunction conjuncts were already
/// verified by JIT before this compound op was reached.
pub(crate) fn lower_func_record_op(
    builder: &mut FunctionBuilder,
    op: &Opcode,
    regs: &mut RegMap,
    out_ptr: Value,
    state_ptr: Option<Value>,
    compound_tracker: &mut CompoundRegTracker,
    field_name_ids: &[u32],
    module: Option<&mut JITModule>,
    conjuncts_passed: u32,
    constants: Option<&tla_tir::bytecode::ConstantPool>,
    state_layout: Option<&crate::compound_layout::StateLayout>,
    jit_diag: bool,
) -> Result<CompoundLowerResult, JitError> {
    match *op {
        Opcode::RecordGet { rd, rs, field_idx } => {
            // Try native access if layout info is available
            if let Some(sp) = state_ptr {
                // Resolve field_idx to a NameId
                if let Some(&name_id_raw) = field_name_ids.get(field_idx as usize) {
                    let name_id = NameId(name_id_raw);
                    if try_lower_record_get_native(
                        builder,
                        rd,
                        rs,
                        name_id,
                        regs,
                        compound_tracker,
                        sp,
                    ) {
                        return Ok(CompoundLowerResult::NativeHandled);
                    }

                    // Direct offset load failed — try runtime helper if compound tracker
                    // knows this register holds a record from the state buffer.
                    if let Some(mod_ref) = module {
                        if let Some(info) = compound_tracker.get(rs) {
                            if matches!(info.layout, CompoundLayout::Record { .. }) {
                                // emit_record_get_helper handles found/not-found
                                // branching internally: if not found, it emits
                                // FallbackNeeded + return. We continue in the
                                // found_block with the result value.
                                let (_found, result) = emit_record_get_helper(
                                    builder,
                                    mod_ref,
                                    sp,
                                    info.base_slot,
                                    name_id_raw,
                                    out_ptr,
                                )?;

                                regs.set(rd, result);
                                compound_tracker.clear(rd);
                                return Ok(CompoundLowerResult::NativeHandled);
                            }
                        }
                    }
                }
            }
            // Fallback: emit FallbackNeeded and return
            emit_fallback_and_return(builder, out_ptr, conjuncts_passed);
            Ok(CompoundLowerResult::FallbackEmitted)
        }
        Opcode::FuncApply { rd, func, arg } => {
            // Try native access if layout info is available
            if let Some(sp) = state_ptr {
                if try_lower_func_apply_native(
                    builder,
                    rd,
                    func,
                    arg,
                    regs,
                    compound_tracker,
                    sp,
                    out_ptr,
                ) {
                    return Ok(CompoundLowerResult::NativeHandled);
                }

                // Compile-time loop failed — try runtime helper for functions
                // tracked by compound tracker.
                if let Some(mod_ref) = module {
                    if let Some(info) = compound_tracker.get(func) {
                        if matches!(info.layout, CompoundLayout::Function { .. }) {
                            let key_val = regs.get(arg);
                            let (_found, result) = emit_func_apply_helper(
                                builder,
                                mod_ref,
                                sp,
                                info.base_slot,
                                key_val,
                                out_ptr,
                            )?;
                            regs.set(rd, result);
                            compound_tracker.clear(rd);
                            return Ok(CompoundLowerResult::NativeHandled);
                        } else if jit_diag {
                            // Part of #4030: Sequences should now be handled by
                            // try_lower_func_apply_native above. If we reach here,
                            // the sequence had dynamic element count or unknown layout.
                            eprintln!(
                                "[jit-diag] FuncApply r{rd}: tracked as {:?}, not handled by native lowering",
                                info.layout
                            );
                        }
                    } else if jit_diag {
                        eprintln!("[jit-diag] FuncApply r{rd}: func r{func} NOT compound-tracked");
                    }
                } else if jit_diag {
                    eprintln!("[jit-diag] FuncApply r{rd}: module is None");
                }
            } else if jit_diag {
                eprintln!("[jit-diag] FuncApply r{rd}: state_ptr is None");
            }
            // Fallback: emit FallbackNeeded and return
            emit_fallback_and_return(builder, out_ptr, conjuncts_passed);
            Ok(CompoundLowerResult::FallbackEmitted)
        }
        Opcode::TupleGet { rd, rs, idx } => {
            // Try native access if layout info is available
            if let Some(sp) = state_ptr {
                if try_lower_tuple_get_native(builder, rd, rs, idx, regs, compound_tracker, sp) {
                    return Ok(CompoundLowerResult::NativeHandled);
                }
            }
            // Fallback: emit FallbackNeeded and return
            emit_fallback_and_return(builder, out_ptr, conjuncts_passed);
            Ok(CompoundLowerResult::FallbackEmitted)
        }
        Opcode::Domain { .. } => {
            // Domain produces a set (compound value) which cannot be represented
            // as a single i64 in the JIT register file. Always emit FallbackNeeded
            // so the caller re-evaluates using the interpreter.
            emit_fallback_and_return(builder, out_ptr, conjuncts_passed);
            Ok(CompoundLowerResult::FallbackEmitted)
        }
        Opcode::CallBuiltin {
            rd,
            builtin,
            args_start,
            argc,
        } => lower_call_builtin(
            builder,
            rd,
            builtin,
            args_start,
            argc,
            regs,
            out_ptr,
            state_ptr,
            compound_tracker,
            conjuncts_passed,
            module,
        ),
        // === Compound-producing opcodes: emit FallbackNeeded ===
        // These produce compound values (sets, sequences, records, functions)
        // that cannot be represented as i64 in JIT registers. The JIT accepts
        // them for eligibility but falls back to the interpreter at runtime.
        // Part of #3909 Phase 2.

        // SetDiff: native lowering when both operands are tracked compound sets
        // with scalar elements. Calls jit_set_diff_i64 runtime helper.
        Opcode::SetDiff { rd, r1, r2 } => {
            if let Some(mod_ref) = module {
                // Check if both operands are tracked compound sets
                let info1 = compound_tracker.get(r1).cloned();
                let info2 = compound_tracker.get(r2).cloned();

                if let (Some(ref i1), Some(ref i2)) = (&info1, &info2) {
                    if let (
                        CompoundLayout::Set {
                            ref element_layout, ..
                        },
                        CompoundLayout::Set { .. },
                    ) = (&i1.layout, &i2.layout)
                    {
                        if element_layout.is_scalar() {
                            // Both sets have scalar elements — emit runtime helper call.
                            // The helper writes the result into a stack-allocated output buffer.

                            // Get the pointers to the set data. For sets loaded from state,
                            // the pointer is state_ptr. For sets from LoadConst (stack-inlined),
                            // the register holds the stack pointer directly (is_direct_ptr).
                            let set1_ptr = if i1.is_direct_ptr {
                                // Stack-inlined constant or prior SetDiff result:
                                // register holds the pointer directly.
                                regs.get(r1)
                            } else if let Some(sp) = state_ptr {
                                sp
                            } else {
                                emit_fallback_and_return(builder, out_ptr, conjuncts_passed);
                                return Ok(CompoundLowerResult::FallbackEmitted);
                            };

                            let set2_ptr = if i2.is_direct_ptr {
                                regs.get(r2)
                            } else if let Some(sp) = state_ptr {
                                sp
                            } else {
                                emit_fallback_and_return(builder, out_ptr, conjuncts_passed);
                                return Ok(CompoundLowerResult::FallbackEmitted);
                            };

                            // Allocate output buffer on the stack.
                            // Worst case: all elements of set1 survive (same size as set1).
                            // For a set with element_count, size = 2 + count * 2 slots.
                            // We use a generous upper bound based on set1's layout.
                            let max_slots = i1.layout.fixed_serialized_slots().unwrap_or(34);
                            let ptr_type = mod_ref.target_config().pointer_type();

                            use cranelift_codegen::ir::StackSlotData;
                            let out_slot = builder.create_sized_stack_slot(StackSlotData::new(
                                cranelift_codegen::ir::StackSlotKind::ExplicitSlot,
                                (max_slots * 8) as u32,
                                8,
                            ));
                            let out_stack_ptr = builder.ins().stack_addr(ptr_type, out_slot, 0);

                            // Declare and call jit_set_diff_i64
                            let mut sig = mod_ref.make_signature();
                            sig.params.push(AbiParam::new(ptr_type)); // set1_ptr
                            sig.params.push(AbiParam::new(types::I64)); // set1_base
                            sig.params.push(AbiParam::new(ptr_type)); // set2_ptr
                            sig.params.push(AbiParam::new(types::I64)); // set2_base
                            sig.params.push(AbiParam::new(ptr_type)); // out_ptr
                            sig.returns.push(AbiParam::new(types::I64)); // slots_written

                            let func_id = mod_ref
                                .declare_function("jit_set_diff_i64", Linkage::Import, &sig)
                                .map_err(|e| JitError::CompileError(e.to_string()))?;
                            let func_ref = mod_ref.declare_func_in_func(func_id, builder.func);

                            let base1_val = builder.ins().iconst(types::I64, i1.base_slot as i64);
                            let base2_val = builder.ins().iconst(types::I64, i2.base_slot as i64);

                            let _call = builder.ins().call(
                                func_ref,
                                &[set1_ptr, base1_val, set2_ptr, base2_val, out_stack_ptr],
                            );

                            // rd gets the pointer to the output buffer
                            regs.set(rd, out_stack_ptr);

                            // Track rd as a Set with scalar elements, base_slot=0
                            // (data starts at the beginning of the stack buffer)
                            compound_tracker.set(
                                rd,
                                CompoundRegInfo {
                                    layout: CompoundLayout::Set {
                                        element_layout: element_layout.clone(),
                                        element_count: None, // dynamic at runtime
                                    },
                                    base_slot: 0,
                                    is_direct_ptr: true,
                                    direct_ptr_val: None,
                                },
                            );

                            return Ok(CompoundLowerResult::NativeHandled);
                        }
                    }
                }
            }
            // Cannot lower natively — fallback
            emit_fallback_and_return(builder, out_ptr, conjuncts_passed);
            Ok(CompoundLowerResult::FallbackEmitted)
        }

        // SetUnion: native lowering when both operands are tracked compound sets
        // with scalar elements. Calls jit_set_union_i64 runtime helper which
        // writes the result to the compound scratch buffer.
        // Part of #4030: JIT native SetUnion support.
        Opcode::SetUnion { rd, r1, r2 } => {
            if let Some(mod_ref) = module {
                let info1 = compound_tracker.get(r1).cloned();
                let info2 = compound_tracker.get(r2).cloned();

                if let (Some(ref i1), Some(ref i2)) = (&info1, &info2) {
                    if let (
                        CompoundLayout::Set {
                            ref element_layout, ..
                        },
                        CompoundLayout::Set { .. },
                    ) = (&i1.layout, &i2.layout)
                    {
                        if element_layout.is_scalar() {
                            let set1_ptr = if i1.is_direct_ptr {
                                regs.get(r1)
                            } else if let Some(sp) = state_ptr {
                                sp
                            } else {
                                emit_fallback_and_return(builder, out_ptr, conjuncts_passed);
                                return Ok(CompoundLowerResult::FallbackEmitted);
                            };

                            let set2_ptr = if i2.is_direct_ptr {
                                regs.get(r2)
                            } else if let Some(sp) = state_ptr {
                                sp
                            } else {
                                emit_fallback_and_return(builder, out_ptr, conjuncts_passed);
                                return Ok(CompoundLowerResult::FallbackEmitted);
                            };

                            let ptr_type = mod_ref.target_config().pointer_type();

                            // Declare and call jit_set_union_i64
                            let mut sig = mod_ref.make_signature();
                            sig.params.push(AbiParam::new(ptr_type)); // set1_ptr
                            sig.params.push(AbiParam::new(types::I64)); // set1_base
                            sig.params.push(AbiParam::new(ptr_type)); // set2_ptr
                            sig.params.push(AbiParam::new(types::I64)); // set2_base
                            sig.returns.push(AbiParam::new(types::I64)); // result offset

                            let func_id = mod_ref
                                .declare_function("jit_set_union_i64", Linkage::Import, &sig)
                                .map_err(|e| JitError::CompileError(e.to_string()))?;
                            let func_ref = mod_ref.declare_func_in_func(func_id, builder.func);

                            let base1_val = builder.ins().iconst(types::I64, i1.base_slot as i64);
                            let base2_val = builder.ins().iconst(types::I64, i2.base_slot as i64);

                            let call = builder.ins().call(
                                func_ref,
                                &[set1_ptr, base1_val, set2_ptr, base2_val],
                            );
                            let result = builder.inst_results(call)[0];

                            // Check if result is 0 (compound elements not supported)
                            let zero = builder.ins().iconst(types::I64, 0);
                            let is_error = builder.ins().icmp(
                                cranelift_codegen::ir::condcodes::IntCC::Equal,
                                result,
                                zero,
                            );

                            let ok_block = builder.create_block();
                            let err_block = builder.create_block();

                            builder.ins().brif(
                                is_error,
                                err_block,
                                &[],
                                ok_block,
                                &[],
                            );

                            builder.switch_to_block(err_block);
                            emit_fallback_and_return(builder, out_ptr, 0);

                            builder.seal_block(err_block);
                            builder.seal_block(ok_block);

                            builder.switch_to_block(ok_block);
                            regs.set(rd, result);
                            // Track as a set — but with is_direct_ptr=false since
                            // the result is in the scratch buffer (not reachable via
                            // state_ptr + offset). Actually, the scratch offset is
                            // already encoded in the result value. Clear tracking
                            // so downstream ops fall back if needed.
                            compound_tracker.clear(rd);

                            return Ok(CompoundLowerResult::NativeHandled);
                        }
                    }
                }
            }
            emit_fallback_and_return(builder, out_ptr, conjuncts_passed);
            Ok(CompoundLowerResult::FallbackEmitted)
        }

        // Other set operations that produce sets
        Opcode::SetIntersect { .. }
        | Opcode::Powerset { .. }
        | Opcode::BigUnion { .. }
        | Opcode::KSubset { .. } => {
            emit_fallback_and_return(builder, out_ptr, conjuncts_passed);
            Ok(CompoundLowerResult::FallbackEmitted)
        }

        // Set/function builder loops (produce compound values)
        Opcode::SetBuilderBegin { .. }
        | Opcode::SetFilterBegin { .. }
        | Opcode::FuncDefBegin { .. }
        | Opcode::LoopNext { .. } => {
            emit_fallback_and_return(builder, out_ptr, conjuncts_passed);
            Ok(CompoundLowerResult::FallbackEmitted)
        }

        // FuncExcept: try native copy-and-modify for scalar-key/scalar-value functions
        // Part of #3958: native FuncExcept enables JIT for actions using EXCEPT.
        Opcode::FuncExcept {
            rd,
            func,
            path,
            val,
        } => {
            if let Some(sp) = state_ptr {
                if try_lower_func_except_native(
                    builder,
                    rd,
                    func,
                    path,
                    val,
                    regs,
                    compound_tracker,
                    sp,
                    out_ptr,
                ) {
                    return Ok(CompoundLowerResult::NativeHandled);
                }
            }
            emit_fallback_and_return(builder, out_ptr, conjuncts_passed);
            Ok(CompoundLowerResult::FallbackEmitted)
        }

        // RecordNew: try native lowering via runtime helper
        Opcode::RecordNew {
            rd,
            fields_start,
            values_start,
            count,
        } => {
            if let (Some(mod_ref), Some(consts)) = (module, constants) {
                // Try to determine field type tags from the state layout.
                let field_tags =
                    resolve_record_field_tags(fields_start, count, consts, state_layout);

                if let Some(tags) = field_tags {
                    let result = lower_record_new_with_layout_tags(
                        builder,
                        mod_ref,
                        rd,
                        fields_start,
                        values_start,
                        count,
                        regs,
                        compound_tracker,
                        consts,
                        &tags,
                    )?;
                    if result != CompoundLowerResult::NotHandled {
                        return Ok(result);
                    }
                } else {
                    // No layout info for tags — use TAG_INT defaults
                    let result = lower_record_new_with_constants(
                        builder,
                        mod_ref,
                        rd,
                        fields_start,
                        values_start,
                        count,
                        regs,
                        compound_tracker,
                        consts,
                    )?;
                    if result != CompoundLowerResult::NotHandled {
                        return Ok(result);
                    }
                }
            }
            emit_fallback_and_return(builder, out_ptr, conjuncts_passed);
            Ok(CompoundLowerResult::FallbackEmitted)
        }

        // Other compound value construction (no native lowering yet)
        Opcode::RecordSet { .. }
        | Opcode::FuncDef { .. }
        | Opcode::FuncSet { .. }
        | Opcode::TupleNew { .. }
        | Opcode::Times { .. }
        | Opcode::SeqNew { .. }
        | Opcode::StrConcat { .. }
        | Opcode::Concat { .. } => {
            emit_fallback_and_return(builder, out_ptr, conjuncts_passed);
            Ok(CompoundLowerResult::FallbackEmitted)
        }

        // Operator calls: fallback to interpreter
        Opcode::Call { .. }
        | Opcode::ValueApply { .. }
        | Opcode::CallExternal { .. }
        | Opcode::MakeClosure { .. } => {
            emit_fallback_and_return(builder, out_ptr, conjuncts_passed);
            Ok(CompoundLowerResult::FallbackEmitted)
        }

        // Unchanged in invariant context: fallback (natively handled in
        // next-state context via lower_next_state_access)
        Opcode::Unchanged { .. } => {
            emit_fallback_and_return(builder, out_ptr, conjuncts_passed);
            Ok(CompoundLowerResult::FallbackEmitted)
        }

        // SetPrimeMode: fallback (used in next-state UNCHANGED fallback paths)
        Opcode::SetPrimeMode { .. } => {
            emit_fallback_and_return(builder, out_ptr, conjuncts_passed);
            Ok(CompoundLowerResult::FallbackEmitted)
        }

        // Halt: emit RuntimeError (CHOOSE with no match, Assert failure, etc.)
        Opcode::Halt => {
            let status_offset = std::mem::offset_of!(JitCallOut, status) as i32;
            let err_kind_offset = std::mem::offset_of!(JitCallOut, err_kind) as i32;
            let status = builder
                .ins()
                .iconst(types::I8, JitStatus::RuntimeError as i64);
            let err_kind = builder.ins().iconst(
                types::I8,
                crate::abi::JitRuntimeErrorKind::TypeMismatch as i64,
            );
            builder
                .ins()
                .store(MemFlags::trusted(), status, out_ptr, status_offset);
            builder
                .ins()
                .store(MemFlags::trusted(), err_kind, out_ptr, err_kind_offset);
            builder.ins().return_(&[]);
            Ok(CompoundLowerResult::FallbackEmitted)
        }

        _ => Ok(CompoundLowerResult::NotHandled),
    }
}
