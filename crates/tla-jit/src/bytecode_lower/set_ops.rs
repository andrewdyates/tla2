// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Set operation lowering: SetEnum, SetIn, Range, and Subseteq.
//!
//! For the JIT, we do not construct actual set values. Instead:
//!
//! - `SetEnum { rd, start, count }` is recorded as metadata: register `rd`
//!   holds a "virtual set" whose elements are in registers `start..start+count`.
//!
//! - `Range { rd, lo, hi }` is recorded as metadata: register `rd` holds a
//!   "virtual range set" representing the integer interval `lo..hi`.
//!
//! - `SetIn { rd, elem, set }` is expanded inline:
//!   - For enumerated sets: a chain of equality comparisons OR'd together.
//!   - For range sets: `lo <= elem /\ elem <= hi`.
//!
//! - `Subseteq { rd, r1, r2 }` is expanded inline when both operands are
//!   tracked enumerated sets: every element of r1 must appear in r2.
//!
//! This avoids materializing set values entirely, converting set operations
//! into pure scalar comparisons that Cranelift can optimize.

use crate::compound_layout::CompoundLayout;
use crate::error::JitError;
use crate::jit_native::{JITModule, Linkage, Module};
use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::{types, AbiParam, InstBuilder, MemFlags, Value};
use cranelift_frontend::FunctionBuilder;
use std::collections::HashMap;
use tla_tir::bytecode::Opcode;

use super::func_record_ops::{CompoundRegInfo, CompoundRegTracker};
use super::RegMap;

/// Maximum number of elements in a SetEnum for JIT eligibility.
///
/// Sets larger than this fall back to the interpreter. 16 elements means
/// at most 16 equality comparisons in a membership test — well within
/// the range where inline expansion beats a hash lookup.
pub(crate) const MAX_SET_ENUM_SIZE: u8 = 16;

/// Describes a tracked virtual set: either enumerated elements or a range.
#[derive(Clone, Copy, Debug)]
enum TrackedSet {
    /// Enumerated set: elements are in registers `start..start+count`.
    Enum { start: u8, count: u8 },
    /// Integer range set: lo..hi (inclusive on both ends, matching TLA+ semantics).
    Range { lo: u8, hi: u8 },
    /// Function set `[domain -> range]`: domain register and range register.
    /// Used for peephole optimization of `x \in [A -> B]` patterns.
    FuncSet { domain: u8, range: u8 },
}

/// Tracks registers that hold virtual sets (enumerated or range).
///
/// When `SetEnum` or `Range` is lowered, we record metadata about the register.
/// This metadata is consumed by `SetIn` and `Subseteq` to expand operations inline.
pub(crate) struct SetEnumTracker {
    sets: HashMap<u8, TrackedSet>,
}

impl SetEnumTracker {
    pub(crate) fn new() -> Self {
        SetEnumTracker {
            sets: HashMap::new(),
        }
    }

    /// Record that register `rd` holds an enumerated set with elements from
    /// registers `start..start+count`.
    fn record_enum(&mut self, rd: u8, start: u8, count: u8) {
        self.sets.insert(rd, TrackedSet::Enum { start, count });
    }

    /// Record that register `rd` holds a range set `lo..hi`.
    fn record_range(&mut self, rd: u8, lo: u8, hi: u8) {
        self.sets.insert(rd, TrackedSet::Range { lo, hi });
    }

    /// Record that register `rd` holds a function set `[domain -> range]`.
    fn record_func_set(&mut self, rd: u8, domain: u8, range: u8) {
        self.sets.insert(rd, TrackedSet::FuncSet { domain, range });
    }

    /// Look up a tracked set by register.
    fn get(&self, reg: u8) -> Option<TrackedSet> {
        self.sets.get(&reg).copied()
    }
}

/// Result of lowering a set operation opcode.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SetOpLowerResult {
    /// Opcode was not a set operation; try another lowering module.
    NotHandled,
    /// Opcode was handled with native code. Execution continues.
    Handled,
    /// Opcode could not be lowered natively; FallbackNeeded + return emitted.
    /// Subsequent instructions are dead code until the next block boundary.
    FallbackEmitted,
}

/// Write `FallbackNeeded` or `PartialPass` status to the JitCallOut struct and return.
///
/// Used when a set operation passes eligibility but cannot be lowered natively
/// at runtime (e.g., `SetIn` on an untracked register, or `Subseteq` with a
/// range LHS). The caller sees `FallbackNeeded`/`PartialPass` and re-evaluates
/// via the interpreter.
///
/// When `conjuncts_passed > 0`, emits `PartialPass` instead of `FallbackNeeded`.
fn emit_set_fallback_and_return(
    builder: &mut FunctionBuilder,
    out_ptr: Value,
    conjuncts_passed: u32,
) {
    // Delegate to the canonical implementation in func_record_ops
    super::func_record_ops::emit_fallback_and_return(builder, out_ptr, conjuncts_passed);
}

/// Emit the membership test `elem_val \in` an enumerated set whose elements
/// are in registers `start..start+count`. Returns an i8 boolean SSA value.
fn emit_enum_membership(
    builder: &mut FunctionBuilder,
    regs: &RegMap,
    elem_val: Value,
    start: u8,
    count: u8,
) -> Value {
    if count == 0 {
        // Empty set: always false (i8).
        builder.ins().iconst(types::I8, 0)
    } else {
        let first_cmp = builder.ins().icmp(IntCC::Equal, elem_val, regs.get(start));
        let mut accum = first_cmp;
        for i in 1..count {
            let reg_idx = start + i;
            let cmp = builder
                .ins()
                .icmp(IntCC::Equal, elem_val, regs.get(reg_idx));
            accum = builder.ins().bor(accum, cmp);
        }
        accum
    }
}

/// Emit the membership test `elem_val \in lo..hi` (inclusive range).
/// Returns an i8 boolean SSA value: `lo <= elem /\ elem <= hi`.
fn emit_range_membership(
    builder: &mut FunctionBuilder,
    regs: &RegMap,
    elem_val: Value,
    lo: u8,
    hi: u8,
) -> Value {
    let lo_val = regs.get(lo);
    let hi_val = regs.get(hi);
    // lo <= elem
    let ge_lo = builder
        .ins()
        .icmp(IntCC::SignedGreaterThanOrEqual, elem_val, lo_val);
    // elem <= hi
    let le_hi = builder
        .ins()
        .icmp(IntCC::SignedLessThanOrEqual, elem_val, hi_val);
    // lo <= elem /\ elem <= hi
    builder.ins().band(ge_lo, le_hi)
}

/// Emit a call to the `jit_set_contains_i64` runtime helper for set membership
/// on a compound set loaded from the state buffer.
///
/// Parameters:
///   - `state_ptr`: Cranelift SSA value pointing to the flat i64 state buffer
///   - `base_slot`: the starting slot index of the serialized set in the buffer
///   - `elem_val`: the scalar element value to search for
///
/// Returns an i64 SSA value: 1 if found, 0 if not found.
fn emit_compound_set_membership(
    builder: &mut FunctionBuilder,
    module: &mut JITModule,
    state_ptr: Value,
    base_slot: usize,
    elem_val: Value,
) -> Result<Value, JitError> {
    // Declare the extern "C" helper: fn(state_ptr: *const i64, set_base_slot: i64, elem_value: i64) -> i64
    let mut sig = module.make_signature();
    let ptr_type = module.target_config().pointer_type();
    sig.params.push(AbiParam::new(ptr_type)); // state_ptr
    sig.params.push(AbiParam::new(types::I64)); // set_base_slot
    sig.params.push(AbiParam::new(types::I64)); // elem_value
    sig.returns.push(AbiParam::new(types::I64)); // 1 if found, 0 if not

    let func_id = module
        .declare_function("jit_set_contains_i64", Linkage::Import, &sig)
        .map_err(|e| JitError::CompileError(e.to_string()))?;
    let func_ref = module.declare_func_in_func(func_id, builder.func);

    let base_slot_val = builder.ins().iconst(types::I64, base_slot as i64);
    let call = builder
        .ins()
        .call(func_ref, &[state_ptr, base_slot_val, elem_val]);
    Ok(builder.inst_results(call)[0])
}

/// Try to emit a function-set membership check: `x \in [A -> B]`.
///
/// When `x` is a compound function from the state buffer (tracked by the
/// compound register tracker) and both the domain set `A` and range set `B`
/// are tracked virtual sets (SetEnum or Range), we emit a call to the runtime
/// helper `jit_func_set_membership_check`.
///
/// The helper validates:
///   1. `x` has TAG_FUNC at its base slot
///   2. The pair count of `x` matches the expected domain size
///   3. Every key in `x` is a member of `A`
///   4. Every value in `x` is a member of `B`
///
/// For BOOLEAN range (`{TRUE, FALSE}` via SetEnum with values 0 and 1), this
/// reduces to checking that all values are 0 or 1 — very fast.
///
/// Returns `Some(i64 SSA value)` (1 = member, 0 = not) on success, or `None`
/// if the pattern cannot be lowered natively (caller should emit fallback).
#[allow(clippy::too_many_arguments)]
fn try_emit_func_set_membership(
    builder: &mut FunctionBuilder,
    regs: &RegMap,
    tracker: &SetEnumTracker,
    elem_reg: u8,
    domain_reg: u8,
    range_reg: u8,
    module: Option<&mut JITModule>,
    state_ptr: Option<Value>,
    compound_tracker: Option<&CompoundRegTracker>,
) -> Result<Option<Value>, JitError> {
    // We need the compound tracker to know where the function is in the state buffer
    let ct = match compound_tracker {
        Some(ct) => ct,
        None => return Ok(None),
    };
    let sp = match state_ptr {
        Some(sp) => sp,
        None => return Ok(None),
    };
    let mod_ref = match module {
        Some(m) => m,
        None => return Ok(None),
    };

    // The element being tested must be a compound function (from state buffer or LoadConst)
    let func_info = match ct.get(elem_reg) {
        Some(info) if matches!(info.layout, CompoundLayout::Function { .. }) => info.clone(),
        _ => return Ok(None),
    };

    // Determine effective pointer: direct_ptr_val > is_direct_ptr > state_ptr.
    // Part of #3949.
    let effective_ptr = if let Some(ptr_val) = func_info.direct_ptr_val {
        ptr_val
    } else if func_info.is_direct_ptr {
        regs.get(elem_reg)
    } else {
        sp
    };

    // Encode domain constraint: we need to know what A looks like so the runtime
    // helper can validate keys. We support:
    //   - SetEnum: pass the elements as a pointer (or inline small counts)
    //   - Range: pass lo/hi bounds
    //   - BOOLEAN shortcut: SetEnum {0, 1} or SetEnum {1, 0}
    let domain_tracked = tracker.get(domain_reg);
    let range_tracked = tracker.get(range_reg);

    // Both domain and range must be tracked virtual sets (not FuncSet — no nesting)
    let domain_info = match domain_tracked {
        Some(TrackedSet::Enum { start, count }) => (start, count),
        Some(TrackedSet::Range { .. }) => {
            // Range domain: we need the domain size = hi - lo + 1.
            // For now, only support SetEnum domains.
            return Ok(None);
        }
        _ => return Ok(None),
    };

    let range_info = match range_tracked {
        Some(TrackedSet::Range { lo, hi }) => FuncSetRangeKind::Range { lo, hi },
        Some(TrackedSet::Enum { start, count }) => {
            // Check for BOOLEAN shortcut: exactly 2 elements {0, 1} or {1, 0}
            // We don't know the values at JIT compile time, so we encode the
            // enum elements and let the runtime helper compare.
            FuncSetRangeKind::Enum { start, count }
        }
        _ => return Ok(None),
    };

    // Emit the call to jit_func_set_membership_check.
    //
    // Signature:
    //   fn(state_ptr: *const i64, func_base_slot: i64,
    //      domain_elems_ptr: *const i64, domain_count: i64,
    //      range_kind: i64, range_lo_or_ptr: i64, range_hi_or_count: i64) -> i64
    //
    // range_kind: 0 = Enum (range_lo_or_ptr = pointer to i64 array, range_hi_or_count = count)
    //             1 = Range (range_lo_or_ptr = lo, range_hi_or_count = hi)
    //
    // For both domain and range enum, we write the element values to a
    // stack-allocated array that the runtime helper reads.

    let ptr_type = mod_ref.target_config().pointer_type();

    // --- Build domain elements array on the stack ---
    let (d_start, d_count) = domain_info;
    let d_count_usize = d_count as usize;
    if d_count_usize == 0 {
        // [A -> B] where A is empty: only the empty function is a member.
        // The runtime helper handles this, but we can short-circuit: check pair_count == 0.
        // Load pair count from the function data (state buffer or direct ptr)
        let count_byte_offset = ((func_info.base_slot + 1) as i32) * 8;
        let pair_count = builder.ins().load(
            types::I64,
            MemFlags::trusted(),
            effective_ptr,
            count_byte_offset,
        );
        let zero = builder.ins().iconst(types::I64, 0);
        let is_empty = builder.ins().icmp(IntCC::Equal, pair_count, zero);
        let result = builder.ins().uextend(types::I64, is_empty);
        return Ok(Some(result));
    }

    // Allocate stack space for domain elements: d_count * 8 bytes
    use cranelift_codegen::ir::StackSlotData;
    let domain_slot = builder.create_sized_stack_slot(StackSlotData::new(
        cranelift_codegen::ir::StackSlotKind::ExplicitSlot,
        (d_count_usize * 8) as u32,
        0,
    ));
    let domain_ptr = builder.ins().stack_addr(ptr_type, domain_slot, 0);

    // Store each domain element value
    for i in 0..d_count {
        let elem = regs.get(d_start + i);
        let offset = (i as i32) * 8;
        builder
            .ins()
            .store(MemFlags::trusted(), elem, domain_ptr, offset);
    }

    let domain_count_val = builder.ins().iconst(types::I64, d_count as i64);

    // --- Build range constraint ---
    let (range_kind_val, range_arg1, range_arg2) = match range_info {
        FuncSetRangeKind::Range { lo, hi } => {
            let lo_val = regs.get(lo);
            let hi_val = regs.get(hi);
            let kind = builder.ins().iconst(types::I64, 1); // Range
            (kind, lo_val, hi_val)
        }
        FuncSetRangeKind::Enum { start, count } => {
            let count_usize = count as usize;
            if count_usize == 0 {
                // Range is empty set: only valid if function has 0 pairs
                // (but domain is non-empty, so this is impossible — no function
                // can map a non-empty domain to an empty range in TLA+)
                // Return 0 (not a member)
                let result = builder.ins().iconst(types::I64, 0);
                return Ok(Some(result));
            }

            // Allocate stack space for range elements
            let range_slot = builder.create_sized_stack_slot(StackSlotData::new(
                cranelift_codegen::ir::StackSlotKind::ExplicitSlot,
                (count_usize * 8) as u32,
                0,
            ));
            let range_ptr = builder.ins().stack_addr(ptr_type, range_slot, 0);

            for i in 0..count {
                let elem = regs.get(start + i);
                let offset = (i as i32) * 8;
                builder
                    .ins()
                    .store(MemFlags::trusted(), elem, range_ptr, offset);
            }

            let kind = builder.ins().iconst(types::I64, 0); // Enum
            let count_val = builder.ins().iconst(types::I64, count as i64);
            (kind, range_ptr, count_val)
        }
    };

    // Declare and call the runtime helper
    let mut sig = mod_ref.make_signature();
    sig.params.push(AbiParam::new(ptr_type)); // state_ptr
    sig.params.push(AbiParam::new(types::I64)); // func_base_slot
    sig.params.push(AbiParam::new(ptr_type)); // domain_elems_ptr
    sig.params.push(AbiParam::new(types::I64)); // domain_count
    sig.params.push(AbiParam::new(types::I64)); // range_kind
    sig.params.push(AbiParam::new(types::I64)); // range_lo_or_ptr
    sig.params.push(AbiParam::new(types::I64)); // range_hi_or_count
    sig.returns.push(AbiParam::new(types::I64)); // 1 if member, 0 if not

    let func_id = mod_ref
        .declare_function("jit_func_set_membership_check", Linkage::Import, &sig)
        .map_err(|e| JitError::CompileError(e.to_string()))?;
    let func_ref = mod_ref.declare_func_in_func(func_id, builder.func);

    let base_slot_val = builder.ins().iconst(types::I64, func_info.base_slot as i64);
    let call = builder.ins().call(
        func_ref,
        &[
            effective_ptr,
            base_slot_val,
            domain_ptr,
            domain_count_val,
            range_kind_val,
            range_arg1,
            range_arg2,
        ],
    );
    Ok(Some(builder.inst_results(call)[0]))
}

/// Encoding for the range constraint in function-set membership checks.
#[derive(Clone, Copy, Debug)]
enum FuncSetRangeKind {
    /// Range set: lo..hi (inclusive).
    Range { lo: u8, hi: u8 },
    /// Enumerated set: elements in registers start..start+count.
    Enum { start: u8, count: u8 },
}

/// Lower a set operation opcode (SetEnum, SetIn, Range, FuncSet, Subseteq).
///
/// Returns `Handled` if the opcode was lowered to native code, `NotHandled`
/// if it should be dispatched to another lowering module, or `FallbackEmitted`
/// if the opcode was recognized but could not be lowered natively (in which
/// case `FallbackNeeded` status + return has been emitted and subsequent
/// instructions are dead code).
///
/// # SetEnum lowering
///
/// `SetEnum { rd, start, count }` records metadata in `tracker`.
/// The register `rd` is set to 0 (a sentinel).
///
/// # Range lowering
///
/// `Range { rd, lo, hi }` records metadata in `tracker`.
/// The register `rd` is set to 0 (a sentinel).
///
/// # SetIn lowering
///
/// For enumerated sets:
/// ```text
/// result = (elem == reg[start]) || ... || (elem == reg[start+count-1])
/// ```
///
/// For range sets:
/// ```text
/// result = (lo <= elem) && (elem <= hi)
/// ```
///
/// # Subseteq lowering
///
/// For two enumerated sets S and T:
/// ```text
/// result = forall e in S: (e \in T)
/// ```
/// Expanded as `(s0 \in T) /\ (s1 \in T) /\ ...`
///
/// For an enumerated set S and a range set T:
/// ```text
/// result = forall e in S: (lo <= e /\ e <= hi)
/// ```
pub(crate) fn lower_set_op(
    builder: &mut FunctionBuilder,
    op: &Opcode,
    regs: &mut RegMap,
    tracker: &mut SetEnumTracker,
    out_ptr: Value,
    mut module: Option<&mut JITModule>,
    state_ptr: Option<Value>,
    mut compound_tracker: Option<&mut CompoundRegTracker>,
    conjuncts_passed: u32,
) -> Result<SetOpLowerResult, JitError> {
    match *op {
        Opcode::SetEnum { rd, start, count } => {
            // Record the set metadata for later SetIn/Subseteq expansion.
            tracker.record_enum(rd, start, count);

            // Also materialize as a serialized set on the stack and register
            // in CompoundRegTracker, so SetDiff can work with this set.
            // Format: [TAG_SET=6, count, TAG_INT=1, elem0, TAG_INT=1, elem1, ...]
            // Each element occupies 2 slots (tag + value).
            if let Some(ref mut ct) = compound_tracker {
                let n = count as usize;
                let slots = 2 + n * 2;
                if let Some(mod_ref) = module.as_deref_mut() {
                    let ptr_type = mod_ref.target_config().pointer_type();
                    let stack_slot =
                        builder.create_sized_stack_slot(cranelift_codegen::ir::StackSlotData::new(
                            cranelift_codegen::ir::StackSlotKind::ExplicitSlot,
                            (slots * 8) as u32,
                            8,
                        ));
                    let stack_ptr = builder.ins().stack_addr(ptr_type, stack_slot, 0);

                    // Store TAG_SET header
                    let tag_set = builder
                        .ins()
                        .iconst(types::I64, crate::compound_layout::TAG_SET);
                    builder
                        .ins()
                        .store(MemFlags::trusted(), tag_set, stack_ptr, 0);
                    let count_val = builder.ins().iconst(types::I64, n as i64);
                    builder
                        .ins()
                        .store(MemFlags::trusted(), count_val, stack_ptr, 8);

                    // Store each element as TAG_INT + value
                    let tag_int = builder
                        .ins()
                        .iconst(types::I64, crate::compound_layout::TAG_INT);
                    for i in 0..n {
                        let elem = regs.get(start + i as u8);
                        let base_offset = (2 + i * 2) as i32 * 8;
                        builder
                            .ins()
                            .store(MemFlags::trusted(), tag_int, stack_ptr, base_offset);
                        builder
                            .ins()
                            .store(MemFlags::trusted(), elem, stack_ptr, base_offset + 8);
                    }

                    regs.set(rd, stack_ptr);
                    ct.set(
                        rd,
                        CompoundRegInfo {
                            layout: CompoundLayout::Set {
                                element_layout: Box::new(CompoundLayout::Int),
                                element_count: Some(n),
                            },
                            base_slot: 0,
                            is_direct_ptr: true,
                            direct_ptr_val: None,
                        },
                    );
                    return Ok(SetOpLowerResult::Handled);
                }
            }

            let zero = builder.ins().iconst(types::I64, 0);
            regs.set(rd, zero);
            Ok(SetOpLowerResult::Handled)
        }

        Opcode::Range { rd, lo, hi } => {
            // Record the range metadata for later SetIn expansion.
            // Set rd to 0 as a placeholder.
            tracker.record_range(rd, lo, hi);
            // Also record in the quantifier range tracker so ForAll/Exists
            // over this Range can use native counted iteration.
            super::quantifier_loops::record_range_for_quantifier(rd, lo, hi);
            let zero = builder.ins().iconst(types::I64, 0);
            regs.set(rd, zero);
            Ok(SetOpLowerResult::Handled)
        }

        Opcode::FuncSet { rd, domain, range } => {
            // Record the function set metadata for later SetIn expansion.
            // When `x \in [A -> B]` is encountered, we can check membership
            // without constructing the full cartesian product by verifying:
            //   1. x is a function with the expected domain size
            //   2. All range values of x are in B
            tracker.record_func_set(rd, domain, range);
            let zero = builder.ins().iconst(types::I64, 0);
            regs.set(rd, zero);
            Ok(SetOpLowerResult::Handled)
        }

        Opcode::SetIn { rd, elem, set } => {
            let elem_val = regs.get(elem);

            if let Some(tracked) = tracker.get(set) {
                // Virtual set (SetEnum, Range, or FuncSet) — expand inline
                match tracked {
                    TrackedSet::Enum { start, count } => {
                        let bool_result =
                            emit_enum_membership(builder, regs, elem_val, start, count);
                        let result = builder.ins().uextend(types::I64, bool_result);
                        regs.set(rd, result);
                        return Ok(SetOpLowerResult::Handled);
                    }
                    TrackedSet::Range { lo, hi } => {
                        let bool_result = emit_range_membership(builder, regs, elem_val, lo, hi);
                        let result = builder.ins().uextend(types::I64, bool_result);
                        regs.set(rd, result);
                        return Ok(SetOpLowerResult::Handled);
                    }
                    TrackedSet::FuncSet { domain, range } => {
                        // Peephole: `x \in [A -> B]` where x is a compound function
                        // from the state buffer and A, B are tracked virtual sets.
                        //
                        // Instead of constructing the full function set, we call a
                        // runtime helper that validates x's structure:
                        //   - x must be a function (TAG_FUNC)
                        //   - DOMAIN x matches A (same cardinality, all keys in A)
                        //   - \A a \in DOMAIN x: x[a] \in B
                        if let Some(result) = try_emit_func_set_membership(
                            builder,
                            regs,
                            tracker,
                            elem,
                            domain,
                            range,
                            module,
                            state_ptr,
                            compound_tracker.as_deref(),
                        )? {
                            regs.set(rd, result);
                            return Ok(SetOpLowerResult::Handled);
                        }
                        // Could not lower — fall through to fallback
                        emit_set_fallback_and_return(builder, out_ptr, conjuncts_passed);
                        return Ok(SetOpLowerResult::FallbackEmitted);
                    }
                }
            }

            // Not a virtual set — check if it's a compound set from the state buffer
            // or a stack-inlined set (LoadConst with is_direct_ptr).
            // If the compound tracker knows about this register and it's a Set layout,
            // call jit_set_contains_i64 for a native linear scan.
            if let (Some(ct), Some(sp), Some(mod_ref)) = (compound_tracker, state_ptr, module) {
                if let Some(info) = ct.get(set) {
                    if matches!(info.layout, CompoundLayout::Set { .. }) {
                        // Determine set pointer: direct_ptr_val > is_direct_ptr > state_ptr.
                        // Part of #3949.
                        let set_ptr = if let Some(ptr_val) = info.direct_ptr_val {
                            ptr_val
                        } else if info.is_direct_ptr {
                            regs.get(set)
                        } else {
                            sp
                        };
                        let result = emit_compound_set_membership(
                            builder,
                            mod_ref,
                            set_ptr,
                            info.base_slot,
                            elem_val,
                        )?;
                        regs.set(rd, result);
                        return Ok(SetOpLowerResult::Handled);
                    }
                }
            }

            // No tracking info available — emit FallbackNeeded
            emit_set_fallback_and_return(builder, out_ptr, conjuncts_passed);
            Ok(SetOpLowerResult::FallbackEmitted)
        }

        Opcode::Subseteq { rd, r1, r2 } => {
            let lhs = match tracker.get(r1) {
                Some(t) => t,
                None => {
                    // LHS register is not tracked. Emit FallbackNeeded.
                    emit_set_fallback_and_return(builder, out_ptr, conjuncts_passed);
                    return Ok(SetOpLowerResult::FallbackEmitted);
                }
            };
            let rhs = match tracker.get(r2) {
                Some(t) => t,
                None => {
                    // RHS register is not tracked. Emit FallbackNeeded.
                    emit_set_fallback_and_return(builder, out_ptr, conjuncts_passed);
                    return Ok(SetOpLowerResult::FallbackEmitted);
                }
            };

            // FuncSet operands in Subseteq are not supported — emit fallback.
            if matches!(lhs, TrackedSet::FuncSet { .. })
                || matches!(rhs, TrackedSet::FuncSet { .. })
            {
                emit_set_fallback_and_return(builder, out_ptr, conjuncts_passed);
                return Ok(SetOpLowerResult::FallbackEmitted);
            }

            match lhs {
                TrackedSet::Enum {
                    start: lhs_start,
                    count: lhs_count,
                } => {
                    if lhs_count == 0 {
                        // Empty set is a subset of everything.
                        let true_val = builder.ins().iconst(types::I64, 1);
                        regs.set(rd, true_val);
                    } else {
                        // For each element in lhs, check membership in rhs.
                        // Result = (s0 \in T) /\ (s1 \in T) /\ ...
                        let first_elem = regs.get(lhs_start);
                        let mut accum = match rhs {
                            TrackedSet::Enum { start, count } => {
                                emit_enum_membership(builder, regs, first_elem, start, count)
                            }
                            TrackedSet::Range { lo, hi } => {
                                emit_range_membership(builder, regs, first_elem, lo, hi)
                            }
                            TrackedSet::FuncSet { .. } => unreachable!("filtered above"),
                        };

                        for i in 1..lhs_count {
                            let elem = regs.get(lhs_start + i);
                            let membership = match rhs {
                                TrackedSet::Enum { start, count } => {
                                    emit_enum_membership(builder, regs, elem, start, count)
                                }
                                TrackedSet::Range { lo, hi } => {
                                    emit_range_membership(builder, regs, elem, lo, hi)
                                }
                                TrackedSet::FuncSet { .. } => unreachable!("filtered above"),
                            };
                            accum = builder.ins().band(accum, membership);
                        }

                        let result = builder.ins().uextend(types::I64, accum);
                        regs.set(rd, result);
                    }
                    Ok(SetOpLowerResult::Handled)
                }
                TrackedSet::Range { .. } | TrackedSet::FuncSet { .. } => {
                    // Range/FuncSet \subseteq T is not supported — would need
                    // to enumerate or do complex structural comparison.
                    // Emit FallbackNeeded so the interpreter handles this state.
                    emit_set_fallback_and_return(builder, out_ptr, conjuncts_passed);
                    Ok(SetOpLowerResult::FallbackEmitted)
                }
            }
        }

        _ => Ok(SetOpLowerResult::NotHandled),
    }
}
