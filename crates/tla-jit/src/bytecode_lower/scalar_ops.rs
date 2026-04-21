// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Scalar opcode lowering: int/bool arithmetic, comparison, boolean logic.

use crate::abi::{JitCallOut, JitRuntimeErrorKind, JitStatus};
use crate::compound_layout::{self, CompoundLayout};
use crate::error::JitError;
use crate::jit_native::{JITModule, Linkage, Module};
use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::{types, AbiParam, InstBuilder, MemFlags, StackSlotData, Value};
use cranelift_frontend::FunctionBuilder;
use tla_tir::bytecode::{ConstantPool, Opcode};

use super::func_record_ops::{CompoundRegInfo, CompoundRegTracker};
use super::RegMap;

/// Maximum number of i64 slots for a set constant to be inlined on the stack.
/// A set with N scalar elements occupies 2 + 2*N slots.
/// 34 slots = set with up to 16 elements (matches MAX_SET_ENUM_SIZE).
const MAX_SET_CONST_STACK_SLOTS: usize = 34;

/// Write ArithmeticOverflow error fields into the JitCallOut struct via out_ptr.
fn write_arithmetic_overflow(builder: &mut FunctionBuilder, out_ptr: Value) {
    let status_offset = std::mem::offset_of!(JitCallOut, status) as i32;
    let err_kind_offset = std::mem::offset_of!(JitCallOut, err_kind) as i32;
    let status = builder
        .ins()
        .iconst(types::I8, JitStatus::RuntimeError as i64);
    let err_kind = builder
        .ins()
        .iconst(types::I8, JitRuntimeErrorKind::ArithmeticOverflow as i64);
    builder
        .ins()
        .store(MemFlags::trusted(), status, out_ptr, status_offset);
    builder
        .ins()
        .store(MemFlags::trusted(), err_kind, out_ptr, err_kind_offset);
}

/// Write DivisionByZero error fields into the JitCallOut struct via out_ptr.
fn write_division_by_zero(builder: &mut FunctionBuilder, out_ptr: Value) {
    let status_offset = std::mem::offset_of!(JitCallOut, status) as i32;
    let err_kind_offset = std::mem::offset_of!(JitCallOut, err_kind) as i32;
    let status = builder
        .ins()
        .iconst(types::I8, JitStatus::RuntimeError as i64);
    let err_kind = builder
        .ins()
        .iconst(types::I8, JitRuntimeErrorKind::DivisionByZero as i64);
    builder
        .ins()
        .store(MemFlags::trusted(), status, out_ptr, status_offset);
    builder
        .ins()
        .store(MemFlags::trusted(), err_kind, out_ptr, err_kind_offset);
}

/// Emit a conditional branch: if `overflow` is true, write ArithmeticOverflow
/// to out_ptr and return; otherwise continue execution.
fn branch_on_arithmetic_overflow(builder: &mut FunctionBuilder, overflow: Value, out_ptr: Value) {
    let overflow_block = builder.create_block();
    let continue_block = builder.create_block();

    builder
        .ins()
        .brif(overflow, overflow_block, &[], continue_block, &[]);
    builder.seal_block(overflow_block);
    builder.seal_block(continue_block);

    builder.switch_to_block(overflow_block);
    write_arithmetic_overflow(builder, out_ptr);
    builder.ins().return_(&[]);

    builder.switch_to_block(continue_block);
}

/// Emit a conditional branch: if `divisor_is_zero` is true, write
/// DivisionByZero to out_ptr and return; otherwise continue execution.
fn branch_on_division_by_zero(
    builder: &mut FunctionBuilder,
    divisor_is_zero: Value,
    out_ptr: Value,
) {
    let division_by_zero_block = builder.create_block();
    let continue_block = builder.create_block();

    builder.ins().brif(
        divisor_is_zero,
        division_by_zero_block,
        &[],
        continue_block,
        &[],
    );
    builder.seal_block(division_by_zero_block);
    builder.seal_block(continue_block);

    builder.switch_to_block(division_by_zero_block);
    write_division_by_zero(builder, out_ptr);
    builder.ins().return_(&[]);

    builder.switch_to_block(continue_block);
}

/// External helper for integer exponentiation.
///
/// TLA+ semantics: 0^0 = 1, negative exponents return 0.
/// Uses binary exponentiation with wrapping multiplication
/// (overflow is not checked — matches TLC behavior for large results).
#[no_mangle]
pub extern "C" fn jit_pow_i64(base: i64, exp: i64) -> i64 {
    if exp < 0 {
        return 0; // TLA+ convention: negative exponents yield 0
    }
    let mut result: i64 = 1;
    let mut b = base;
    let mut e = exp as u64;
    while e > 0 {
        if e & 1 == 1 {
            result = result.wrapping_mul(b);
        }
        b = b.wrapping_mul(b);
        e >>= 1;
    }
    result
}

/// Emit a PowInt lowering: call the extern `jit_pow_i64` helper.
fn lower_pow_int(
    builder: &mut FunctionBuilder,
    module: &mut JITModule,
    regs: &mut RegMap,
    rd: u8,
    r1: u8,
    r2: u8,
) -> Result<(), JitError> {
    let base = regs.get(r1);
    let exp = regs.get(r2);

    // Declare the external helper function
    let mut sig = module.make_signature();
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    sig.returns.push(AbiParam::new(types::I64));

    let func_id = module
        .declare_function("jit_pow_i64", Linkage::Import, &sig)
        .map_err(|e| JitError::CompileError(e.to_string()))?;
    let func_ref = module.declare_func_in_func(func_id, builder.func);
    let call = builder.ins().call(func_ref, &[base, exp]);
    let result = builder.inst_results(call)[0];
    regs.set(rd, result);
    Ok(())
}

/// Emit FallbackNeeded for a compound constant that cannot be inlined.
///
/// Writes the FallbackNeeded status to out_ptr, emits a return, creates
/// a dead block for subsequent instructions, and sets a dummy register value.
fn emit_compound_const_fallback(
    builder: &mut FunctionBuilder,
    regs: &mut RegMap,
    rd: u8,
    idx: u16,
    val: &tla_value::Value,
    out_ptr: Value,
    jit_diag: bool,
) {
    if jit_diag {
        eprintln!(
            "[jit-diag] LoadConst rd=r{rd} idx={idx}: compound value {:?} -> FallbackNeeded",
            val.type_name()
        );
    }
    let status_offset = std::mem::offset_of!(JitCallOut, status) as i32;
    let status = builder
        .ins()
        .iconst(types::I8, JitStatus::FallbackNeeded as i64);
    builder
        .ins()
        .store(MemFlags::trusted(), status, out_ptr, status_offset);
    builder.ins().return_(&[]);
    // After return, Cranelift needs a new block for any following code.
    // Create a dead block so subsequent instructions have somewhere to land.
    let dead_block = builder.create_block();
    builder.switch_to_block(dead_block);
    // Seal immediately: this dead block has no predecessors (it follows a return),
    // so there are no incoming edges to wait for. Without sealing, Cranelift's
    // finalize() panics with "block not sealed". Part of #3958.
    builder.seal_block(dead_block);
    // Set register to a dummy value so later instructions don't panic.
    let dummy = builder.ins().iconst(types::I64, 0);
    regs.set(rd, dummy);
}

/// Lower a scalar arithmetic/comparison/boolean opcode.
///
/// Returns `true` if the opcode was handled, `false` if it should be
/// dispatched to another lowering module (control flow, state access).
pub(crate) fn lower_scalar(
    builder: &mut FunctionBuilder,
    op: &Opcode,
    regs: &mut RegMap,
    out_ptr: Value,
    module: &mut JITModule,
    constants: Option<&ConstantPool>,
    mut compound_tracker: Option<&mut CompoundRegTracker>,
    jit_diag: bool,
) -> Result<bool, JitError> {
    match *op {
        Opcode::LoadImm { rd, value } => {
            let v = builder.ins().iconst(types::I64, value);
            regs.set(rd, v);
            // Clear compound tracking: scalar overwrites any prior compound info.
            if let Some(ref mut tracker) = compound_tracker {
                tracker.clear(rd);
            }
            Ok(true)
        }
        Opcode::LoadBool { rd, value } => {
            let v = builder.ins().iconst(types::I64, if value { 1 } else { 0 });
            regs.set(rd, v);
            // Clear compound tracking: scalar overwrites any prior compound info.
            if let Some(ref mut tracker) = compound_tracker {
                tracker.clear(rd);
            }
            Ok(true)
        }
        Opcode::Move { rd, rs } => {
            regs.set(rd, regs.get(rs));
            // Propagate compound tracking: if the source register holds a
            // compound value (Record, Function, Tuple, etc.) with a known
            // layout and base slot, copy that info to the destination register.
            // Without this, non-state variables that receive compound values
            // via Move (e.g., LET bindings, parameter passing after inlining)
            // would lose their compound tracking, causing downstream
            // RecordGet/FuncApply/TupleGet to emit FallbackNeeded instead
            // of using native access. Part of #3949.
            if let Some(ref mut tracker) = compound_tracker {
                if let Some(info) = tracker.get(rs) {
                    let info = info.clone();
                    tracker.set(rd, info);
                } else {
                    tracker.clear(rd);
                }
            }
            Ok(true)
        }

        // LoadConst: scalar constants (SmallInt, Bool) compiled natively;
        // compound constants (strings, ranges, etc.) emit FallbackNeeded.
        Opcode::LoadConst { rd, idx } => {
            let pool = constants.ok_or_else(|| {
                JitError::UnsupportedOpcode(
                    "LoadConst requires constant pool for JIT lowering".to_string(),
                )
            })?;
            let val = pool.get_value(idx);
            match val {
                tla_value::Value::SmallInt(n) => {
                    let v = builder.ins().iconst(types::I64, *n);
                    regs.set(rd, v);
                    // Scalar overwrites any prior compound tracking.
                    if let Some(ref mut tracker) = compound_tracker {
                        tracker.clear(rd);
                    }
                    Ok(true)
                }
                tla_value::Value::Bool(b) => {
                    let v = builder.ins().iconst(types::I64, if *b { 1 } else { 0 });
                    regs.set(rd, v);
                    if let Some(ref mut tracker) = compound_tracker {
                        tracker.clear(rd);
                    }
                    Ok(true)
                }
                tla_value::Value::String(s) => {
                    // Strings are interned as NameId values in the serialized
                    // state buffer. Intern the string constant to get its
                    // NameId, then store that as i64 in the JIT register.
                    let name_id = tla_core::intern_name(s);
                    let v = builder.ins().iconst(types::I64, name_id.0 as i64);
                    regs.set(rd, v);
                    // Scalar overwrites any prior compound tracking.
                    if let Some(ref mut tracker) = compound_tracker {
                        tracker.clear(rd);
                    }
                    Ok(true)
                }
                // Set constants: serialize at compile time, store on the JIT
                // stack frame, and register in the compound tracker so downstream
                // operations (SetDiff, SetIn, Cardinality) can work natively.
                tla_value::Value::Set(_) => {
                    // Serialize the set to a flat i64 buffer at compile time.
                    let mut buf = Vec::new();
                    let ser_result = compound_layout::serialize_value(val, &mut buf);
                    match &ser_result {
                        Err(e) if jit_diag => {
                            eprintln!("[jit-diag] LoadConst rd=r{rd} idx={idx}: Set serialization FAILED: {e}");
                        }
                        Ok(slots_written)
                            if *slots_written > MAX_SET_CONST_STACK_SLOTS && jit_diag =>
                        {
                            eprintln!("[jit-diag] LoadConst rd=r{rd} idx={idx}: Set too large ({slots_written} > {MAX_SET_CONST_STACK_SLOTS})");
                        }
                        _ => {}
                    }
                    if let Ok(slots_written) = ser_result {
                        if slots_written <= MAX_SET_CONST_STACK_SLOTS {
                            // Infer the layout for compound tracking
                            let layout = compound_layout::infer_layout(val);

                            // Allocate a stack slot for the serialized set data
                            let ptr_type = module.target_config().pointer_type();
                            let stack_slot = builder.create_sized_stack_slot(StackSlotData::new(
                                cranelift_codegen::ir::StackSlotKind::ExplicitSlot,
                                (slots_written * 8) as u32, // bytes
                                8,                          // alignment
                            ));
                            let stack_ptr = builder.ins().stack_addr(ptr_type, stack_slot, 0);

                            // Emit immediate stores to populate the stack buffer
                            for (i, &word) in buf.iter().enumerate() {
                                let imm = builder.ins().iconst(types::I64, word);
                                let byte_offset = (i as i32) * 8;
                                builder.ins().store(
                                    MemFlags::trusted(),
                                    imm,
                                    stack_ptr,
                                    byte_offset,
                                );
                            }

                            // The register holds the stack pointer to the serialized set.
                            // Downstream operations (SetDiff, SetIn via compound tracker)
                            // use this as their "state_ptr" with base_slot=0.
                            regs.set(rd, stack_ptr);

                            // Register in compound tracker if available
                            if let Some(ref mut tracker) = compound_tracker {
                                tracker.set(
                                    rd,
                                    CompoundRegInfo {
                                        layout,
                                        base_slot: 0,
                                        is_direct_ptr: true,
                                        direct_ptr_val: None,
                                    },
                                );
                            }

                            if jit_diag {
                                eprintln!(
                                    "[jit-diag] LoadConst rd=r{rd} idx={idx}: Set with {slots_written} slots -> stack-inlined",
                                );
                            }
                            return Ok(true);
                        }
                    }
                    // Set too large or serialization failed — fall through to compound fallback
                    emit_compound_const_fallback(builder, regs, rd, idx, val, out_ptr, jit_diag);
                    Ok(true)
                }
                // Interval (a..b): materialize to a concrete set of integers
                // and serialize. Common in specs: Node == 0..N-1.
                tla_value::Value::Interval(iv) => {
                    use num_traits::ToPrimitive;
                    if let (Some(lo), Some(hi)) = (iv.low().to_i64(), iv.high().to_i64()) {
                        let count = if hi >= lo { (hi - lo + 1) as usize } else { 0 };
                        // TAG_SET + count + count * (TAG_INT + value) = 2 + 2*count
                        let slots_needed = 2 + 2 * count;
                        if slots_needed <= MAX_SET_CONST_STACK_SLOTS {
                            // Materialize to a concrete set Value for serialization
                            let materialized = tla_value::Value::Set(std::sync::Arc::new(
                                tla_value::SortedSet::from_iter(
                                    (lo..=hi).map(tla_value::Value::SmallInt),
                                ),
                            ));
                            let mut buf = Vec::new();
                            if let Ok(slots_written) =
                                compound_layout::serialize_value(&materialized, &mut buf)
                            {
                                let layout = compound_layout::infer_layout(&materialized);
                                let ptr_type = module.target_config().pointer_type();
                                let stack_slot =
                                    builder.create_sized_stack_slot(StackSlotData::new(
                                        cranelift_codegen::ir::StackSlotKind::ExplicitSlot,
                                        (slots_written * 8) as u32,
                                        8,
                                    ));
                                let stack_ptr = builder.ins().stack_addr(ptr_type, stack_slot, 0);
                                for (i, &word) in buf.iter().enumerate() {
                                    let imm = builder.ins().iconst(types::I64, word);
                                    let byte_offset = (i as i32) * 8;
                                    builder.ins().store(
                                        MemFlags::trusted(),
                                        imm,
                                        stack_ptr,
                                        byte_offset,
                                    );
                                }
                                regs.set(rd, stack_ptr);
                                if let Some(ref mut tracker) = compound_tracker {
                                    tracker.set(
                                        rd,
                                        CompoundRegInfo {
                                            layout,
                                            base_slot: 0,
                                            is_direct_ptr: true,
                                            direct_ptr_val: None,
                                        },
                                    );
                                }
                                if jit_diag {
                                    eprintln!(
                                        "[jit-diag] LoadConst rd=r{rd} idx={idx}: Interval {lo}..{hi} with {slots_written} slots -> stack-inlined",
                                    );
                                }
                                return Ok(true);
                            }
                        }
                    }
                    emit_compound_const_fallback(builder, regs, rd, idx, val, out_ptr, jit_diag);
                    Ok(true)
                }
                // Compound constants (Record, Func, IntFunc, Tuple, Seq):
                // serialize at compile time, store on JIT stack frame, and
                // register in compound tracker so downstream RecordGet/FuncApply/
                // TupleGet can work natively.  Part of #3949.
                tla_value::Value::Record(_)
                | tla_value::Value::Func(_)
                | tla_value::Value::IntFunc(_)
                | tla_value::Value::Tuple(_)
                | tla_value::Value::Seq(_) => {
                    let mut buf = Vec::new();
                    let ser_result = compound_layout::serialize_value(val, &mut buf);
                    if let Ok(slots_written) = ser_result {
                        if slots_written <= MAX_SET_CONST_STACK_SLOTS {
                            let layout = compound_layout::infer_layout(val);
                            let ptr_type = module.target_config().pointer_type();
                            let stack_slot = builder.create_sized_stack_slot(StackSlotData::new(
                                cranelift_codegen::ir::StackSlotKind::ExplicitSlot,
                                (slots_written * 8) as u32,
                                8,
                            ));
                            let stack_ptr = builder.ins().stack_addr(ptr_type, stack_slot, 0);
                            for (i, &word) in buf.iter().enumerate() {
                                let imm = builder.ins().iconst(types::I64, word);
                                let byte_offset = (i as i32) * 8;
                                builder.ins().store(
                                    MemFlags::trusted(),
                                    imm,
                                    stack_ptr,
                                    byte_offset,
                                );
                            }
                            regs.set(rd, stack_ptr);
                            if let Some(ref mut tracker) = compound_tracker {
                                tracker.set(
                                    rd,
                                    CompoundRegInfo {
                                        layout,
                                        base_slot: 0,
                                        is_direct_ptr: true,
                                        direct_ptr_val: None,
                                    },
                                );
                            }
                            if jit_diag {
                                eprintln!(
                                    "[jit-diag] LoadConst rd=r{rd} idx={idx}: compound value with {slots_written} slots -> stack-inlined",
                                );
                            }
                            return Ok(true);
                        }
                    }
                    emit_compound_const_fallback(builder, regs, rd, idx, val, out_ptr, jit_diag);
                    Ok(true)
                }
                _ => {
                    // Other compound constant: emit FallbackNeeded and return.
                    emit_compound_const_fallback(builder, regs, rd, idx, val, out_ptr, jit_diag);
                    Ok(true)
                }
            }
        }

        // Integer exponentiation (extern call to jit_pow_i64)
        Opcode::PowInt { rd, r1, r2 } => {
            lower_pow_int(builder, module, regs, rd, r1, r2)?;
            Ok(true)
        }

        // Integer arithmetic (with overflow detection — Part of #3817)
        Opcode::AddInt { rd, r1, r2 } => {
            let a = regs.get(r1);
            let b = regs.get(r2);
            let (result, overflow) = builder.ins().sadd_overflow(a, b);
            branch_on_arithmetic_overflow(builder, overflow, out_ptr);
            regs.set(rd, result);
            Ok(true)
        }
        Opcode::SubInt { rd, r1, r2 } => {
            let a = regs.get(r1);
            let b = regs.get(r2);
            let (result, overflow) = builder.ins().ssub_overflow(a, b);
            branch_on_arithmetic_overflow(builder, overflow, out_ptr);
            regs.set(rd, result);
            Ok(true)
        }
        Opcode::MulInt { rd, r1, r2 } => {
            let a = regs.get(r1);
            let b = regs.get(r2);
            let (result, overflow) = builder.ins().smul_overflow(a, b);
            branch_on_arithmetic_overflow(builder, overflow, out_ptr);
            regs.set(rd, result);
            Ok(true)
        }
        Opcode::DivInt { rd, r1, r2 } => {
            let a = regs.get(r1);
            let b = regs.get(r2);
            let divisor_is_zero = builder.ins().icmp_imm(IntCC::Equal, b, 0);
            branch_on_division_by_zero(builder, divisor_is_zero, out_ptr);
            let divisor_is_neg_one = builder.ins().icmp_imm(IntCC::Equal, b, -1);
            let dividend_is_min = builder.ins().icmp_imm(IntCC::Equal, a, i64::MIN);
            let overflow = builder.ins().band(divisor_is_neg_one, dividend_is_min);
            branch_on_arithmetic_overflow(builder, overflow, out_ptr);
            let result = builder.ins().sdiv(a, b);
            regs.set(rd, result);
            Ok(true)
        }
        Opcode::IntDiv { rd, r1, r2 } => {
            let a = regs.get(r1);
            let b = regs.get(r2);
            let divisor_is_zero = builder.ins().icmp_imm(IntCC::Equal, b, 0);
            branch_on_division_by_zero(builder, divisor_is_zero, out_ptr);
            let divisor_is_neg_one = builder.ins().icmp_imm(IntCC::Equal, b, -1);
            let dividend_is_min = builder.ins().icmp_imm(IntCC::Equal, a, i64::MIN);
            let overflow = builder.ins().band(divisor_is_neg_one, dividend_is_min);
            branch_on_arithmetic_overflow(builder, overflow, out_ptr);
            let q = builder.ins().sdiv(a, b);
            let r = builder.ins().srem(a, b);
            let zero = builder.ins().iconst(types::I64, 0);
            let one = builder.ins().iconst(types::I64, 1);
            let a_xor_b = builder.ins().bxor(a, b);
            let signs_differ = builder.ins().icmp(IntCC::SignedLessThan, a_xor_b, zero);
            let r_nonzero = builder.ins().icmp(IntCC::NotEqual, r, zero);
            let need_adjust = builder.ins().band(signs_differ, r_nonzero);
            let q_minus_1 = builder.ins().isub(q, one);
            let result = builder.ins().select(need_adjust, q_minus_1, q);
            regs.set(rd, result);
            Ok(true)
        }
        Opcode::ModInt { rd, r1, r2 } => {
            let a = regs.get(r1);
            let b = regs.get(r2);
            let divisor_is_zero = builder.ins().icmp_imm(IntCC::Equal, b, 0);
            branch_on_division_by_zero(builder, divisor_is_zero, out_ptr);
            let divisor_is_neg_one = builder.ins().icmp_imm(IntCC::Equal, b, -1);
            let dividend_is_min = builder.ins().icmp_imm(IntCC::Equal, a, i64::MIN);
            let overflow = builder.ins().band(divisor_is_neg_one, dividend_is_min);
            branch_on_arithmetic_overflow(builder, overflow, out_ptr);
            let r = builder.ins().srem(a, b);
            let zero = builder.ins().iconst(types::I64, 0);
            let r_neg = builder.ins().icmp(IntCC::SignedLessThan, r, zero);
            let b_neg = builder.ins().icmp(IntCC::SignedLessThan, b, zero);
            let neg_b = builder.ins().ineg(b);
            let abs_b = builder.ins().select(b_neg, neg_b, b);
            let r_adjusted = builder.ins().iadd(r, abs_b);
            let result = builder.ins().select(r_neg, r_adjusted, r);
            regs.set(rd, result);
            Ok(true)
        }
        Opcode::NegInt { rd, rs } => {
            let v = regs.get(rs);
            let overflow = builder.ins().icmp_imm(IntCC::Equal, v, i64::MIN);
            branch_on_arithmetic_overflow(builder, overflow, out_ptr);
            let result = builder.ins().ineg(v);
            regs.set(rd, result);
            Ok(true)
        }

        // Comparisons
        Opcode::Eq { rd, r1, r2 } => {
            let a = regs.get(r1);
            let b = regs.get(r2);
            let cmp = builder.ins().icmp(IntCC::Equal, a, b);
            let result = builder.ins().uextend(types::I64, cmp);
            regs.set(rd, result);
            Ok(true)
        }
        Opcode::Neq { rd, r1, r2 } => {
            let a = regs.get(r1);
            let b = regs.get(r2);
            let cmp = builder.ins().icmp(IntCC::NotEqual, a, b);
            let result = builder.ins().uextend(types::I64, cmp);
            regs.set(rd, result);
            Ok(true)
        }
        Opcode::LtInt { rd, r1, r2 } => {
            let a = regs.get(r1);
            let b = regs.get(r2);
            let cmp = builder.ins().icmp(IntCC::SignedLessThan, a, b);
            let result = builder.ins().uextend(types::I64, cmp);
            regs.set(rd, result);
            Ok(true)
        }
        Opcode::LeInt { rd, r1, r2 } => {
            let a = regs.get(r1);
            let b = regs.get(r2);
            let cmp = builder.ins().icmp(IntCC::SignedLessThanOrEqual, a, b);
            let result = builder.ins().uextend(types::I64, cmp);
            regs.set(rd, result);
            Ok(true)
        }
        Opcode::GtInt { rd, r1, r2 } => {
            let a = regs.get(r1);
            let b = regs.get(r2);
            let cmp = builder.ins().icmp(IntCC::SignedGreaterThan, a, b);
            let result = builder.ins().uextend(types::I64, cmp);
            regs.set(rd, result);
            Ok(true)
        }
        Opcode::GeInt { rd, r1, r2 } => {
            let a = regs.get(r1);
            let b = regs.get(r2);
            let cmp = builder.ins().icmp(IntCC::SignedGreaterThanOrEqual, a, b);
            let result = builder.ins().uextend(types::I64, cmp);
            regs.set(rd, result);
            Ok(true)
        }

        // Boolean operations
        // Normalize operands to canonical 0/1 before bitwise ops to handle
        // non-canonical boolean values (any non-zero value is truthy).
        Opcode::And { rd, r1, r2 } => {
            let a = regs.get(r1);
            let b = regs.get(r2);
            let a_bool = builder.ins().icmp_imm(IntCC::NotEqual, a, 0);
            let b_bool = builder.ins().icmp_imm(IntCC::NotEqual, b, 0);
            let cmp = builder.ins().band(a_bool, b_bool);
            let result = builder.ins().uextend(types::I64, cmp);
            regs.set(rd, result);
            Ok(true)
        }
        Opcode::Or { rd, r1, r2 } => {
            let a = regs.get(r1);
            let b = regs.get(r2);
            let a_bool = builder.ins().icmp_imm(IntCC::NotEqual, a, 0);
            let b_bool = builder.ins().icmp_imm(IntCC::NotEqual, b, 0);
            let cmp = builder.ins().bor(a_bool, b_bool);
            let result = builder.ins().uextend(types::I64, cmp);
            regs.set(rd, result);
            Ok(true)
        }
        Opcode::Not { rd, rs } => {
            let v = regs.get(rs);
            let cmp = builder.ins().icmp_imm(IntCC::Equal, v, 0);
            let result = builder.ins().uextend(types::I64, cmp);
            regs.set(rd, result);
            Ok(true)
        }
        Opcode::Implies { rd, r1, r2 } => {
            let a = regs.get(r1);
            let b = regs.get(r2);
            let not_a = builder.ins().icmp_imm(IntCC::Equal, a, 0);
            let b_bool = builder.ins().icmp_imm(IntCC::NotEqual, b, 0);
            let cmp = builder.ins().bor(not_a, b_bool);
            let result = builder.ins().uextend(types::I64, cmp);
            regs.set(rd, result);
            Ok(true)
        }
        Opcode::Equiv { rd, r1, r2 } => {
            let a = regs.get(r1);
            let b = regs.get(r2);
            let a_bool = builder.ins().icmp_imm(IntCC::NotEqual, a, 0);
            let b_bool = builder.ins().icmp_imm(IntCC::NotEqual, b, 0);
            let cmp = builder.ins().icmp(IntCC::Equal, a_bool, b_bool);
            let result = builder.ins().uextend(types::I64, cmp);
            regs.set(rd, result);
            Ok(true)
        }

        _ => Ok(false),
    }
}
