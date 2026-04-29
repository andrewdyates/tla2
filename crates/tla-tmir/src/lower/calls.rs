// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Inter-function call lowering.

use crate::TmirError;
use tla_jit_abi::JitStatus;
use tmir::inst::*;
use tmir::ty::Ty;
use tmir::value::ValueId;
use tmir::Constant;
use tmir::InstrNode;

use super::Ctx;

impl<'cp> Ctx<'cp> {
    // =====================================================================
    // Inter-function Call
    // =====================================================================

    /// Lower `Opcode::Call { rd, op_idx, args_start, argc }`.
    ///
    /// Loads `argc` arguments from consecutive registers starting at
    /// `args_start`, emits a tMIR `Inst::Call` to the callee's FuncId,
    /// and stores either the scalar `i64` result or the encoded caller-owned
    /// fixed-width record/sequence/function return buffer pointer into
    /// register `rd`.
    pub(super) fn lower_call(
        &mut self,
        block_idx: usize,
        rd: u8,
        op_idx: u16,
        args_start: u8,
        argc: u8,
    ) -> Result<Option<usize>, TmirError> {
        // Register the call target and get its tMIR FuncId.
        let callee_func_id = self.register_call_target(op_idx);

        let arg_shapes = self.call_arg_shapes(args_start, argc)?;
        let expected_arg_shapes = self
            .callee_arg_shapes
            .get(&op_idx)
            .cloned()
            .unwrap_or_default();

        // Load user arguments before the call. Their shapes drive
        // callsite-sensitive return materialization below.
        let mut current_block = block_idx;
        let mut user_arg_values = Vec::with_capacity(usize::from(argc));
        for i in 0..argc {
            let reg = args_start.checked_add(i).ok_or_else(|| {
                TmirError::Emission(format!(
                    "Call argument register overflow: args_start={args_start} + i={i}"
                ))
            })?;
            let expected_arg_shape = expected_arg_shapes.get(usize::from(i)).cloned().flatten();
            let val = if let Some((next_block, materialized)) = self
                .materialize_compact_helper_call_arg(
                    current_block,
                    op_idx,
                    usize::from(i),
                    reg,
                    expected_arg_shape.as_ref(),
                )? {
                current_block = next_block;
                materialized
            } else {
                self.load_reg(current_block, reg)?
            };
            user_arg_values.push(val);
        }
        let callsite_shape = if argc == 0 {
            self.callee_return_shapes.get(&op_idx).cloned().flatten()
        } else if let Some(chunk) = self.source_chunk {
            super::infer_callee_return_shape_for_args(
                chunk,
                op_idx,
                &arg_shapes,
                self.state_layout.as_ref(),
            )
        } else {
            None
        };
        let callee_lowered_shape =
            self.inferred_callee_return_shape_for_lowered_args(op_idx, usize::from(argc));
        let callsite_abi_shape = Self::compact_return_abi_shape(callsite_shape.clone());
        let completed_callee_lowered_shape = if let (Some(callee), Some(callsite_abi)) =
            (callee_lowered_shape.as_ref(), callsite_abi_shape.as_ref())
        {
            Some(
                Self::complete_inferred_compact_shape_from_expected(callee, callsite_abi)
                    .ok_or_else(|| {
                        TmirError::UnsupportedOpcode(format!(
                            "Call compact compound return shape for callee {op_idx} differs between callsite ABI and callee lowering: callsite_abi={callsite_abi:?}, callee={callee:?}"
                        ))
                    })?,
            )
        } else {
            callee_lowered_shape.clone()
        };
        let callee_abi_shape =
            Self::compact_return_abi_shape(completed_callee_lowered_shape.clone());
        let aggregate_return_shape = match (callsite_abi_shape.as_ref(), callee_abi_shape.as_ref())
        {
            (Some(callsite_abi), Some(callee_abi)) => {
                if !Self::same_compact_physical_layout(callsite_abi, callee_abi) {
                    return Err(TmirError::UnsupportedOpcode(format!(
                        "Call compact compound return ABI for callee {op_idx} differs between caller and callee: callsite_abi={callsite_abi:?}, callee_abi={callee_abi:?}"
                    )));
                }
                self.record_callee_expected_return_abi_shape(op_idx, callsite_abi)?;
                Some(callsite_abi.clone())
            }
            (Some(callsite_abi), None) => {
                self.record_callee_expected_return_abi_shape(op_idx, callsite_abi)?;
                Some(callsite_abi.clone())
            }
            (None, Some(callee_abi)) => {
                self.record_callee_expected_return_abi_shape(op_idx, callee_abi)?;
                Some(callee_abi.clone())
            }
            _ => None,
        };
        let aggregate_return = if let Some(shape) = aggregate_return_shape.as_ref() {
            Some(Self::caller_owned_return_slot_count(shape).ok_or_else(|| {
                TmirError::UnsupportedOpcode(format!(
                    "Call compact compound return requires fixed-width shape for callee {op_idx}, got {shape:?}"
                ))
            })?)
        } else {
            None
        };
        let result_shape = aggregate_return_shape
            .clone()
            .or_else(|| callsite_shape.clone())
            .or(completed_callee_lowered_shape);
        let return_ptr = self.alloc_aggregate(current_block, aggregate_return.unwrap_or(1));

        // Build the call arguments: context pointers first, then a hidden
        // caller-owned fixed-width aggregate return buffer, then user args.
        // Scalar callees ignore the buffer and keep returning i64 directly.
        let mut call_args = vec![self.out_ptr, self.state_in_ptr];
        if let Some(sop) = self.state_out_ptr {
            call_args.push(sop);
        }
        // state_len: we don't track a ValueId for it in the callee case,
        // so emit a dummy constant 0 for state_len (unused by callee ops,
        // but must be present to match the signature).
        let state_len_val = self.emit_with_result(
            current_block,
            Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(0),
            },
        );
        call_args.push(state_len_val);
        call_args.push(return_ptr);
        call_args.extend(user_arg_values);

        // Helper calls share the entrypoint JitCallOut. Native fused callers
        // preseed status with RuntimeError as a fail-closed sentinel before
        // invoking a compiled callout, while successful helper callees return
        // their scalar result or encoded hidden compact compound return-buffer
        // pointer and do not rewrite status. Reset status
        // immediately before the helper call so the post-call status check sees
        // only this callee's failure signal.
        let status_ptr = self.emit_out_field_ptr(current_block, super::STATUS_OFFSET);
        let ok = self.emit_with_result(
            current_block,
            Inst::Const {
                ty: Ty::I8,
                value: Constant::Int(i128::from(JitStatus::Ok as u8)),
            },
        );
        self.emit(
            current_block,
            InstrNode::new(Inst::Store {
                ty: Ty::I8,
                ptr: status_ptr,
                value: ok,
                align: None,
                volatile: false,
            }),
        );

        // Emit the tMIR Call instruction.
        let result = self.emit_with_result(
            current_block,
            Inst::Call {
                callee: callee_func_id,
                args: call_args,
            },
        );

        // Helper calls share the same JitCallOut as the entrypoint. If the
        // callee surfaced RuntimeError / FallbackNeeded / PartialPass, the
        // current function must stop immediately instead of continuing and
        // potentially overwriting that status with Ok.
        let status = self.emit_with_result(
            current_block,
            Inst::Load {
                ty: Ty::I8,
                ptr: status_ptr,
                align: None,
                volatile: false,
            },
        );
        let status_is_ok = self.emit_with_result(
            current_block,
            Inst::ICmp {
                op: ICmpOp::Eq,
                ty: Ty::I8,
                lhs: status,
                rhs: ok,
            },
        );

        let continue_block = self.new_aux_block("call_ok");
        let propagate_block = self.new_aux_block("call_status");
        let continue_id = self.block_id_of(continue_block);
        let propagate_id = self.block_id_of(propagate_block);
        // Store the call result before splitting on status so the successor
        // block does not consume a ValueId defined in this predecessor block.
        // Compact compound callees return the caller-owned return-buffer
        // pointer as i64; make that returned ABI value the source of truth so
        // native direct-call lowering does not need to keep the pre-call
        // alloca pointer live across the call.
        if aggregate_return.is_some() {
            self.store_reg_value(current_block, rd, result)?;
            if aggregate_return_shape
                .as_ref()
                .is_some_and(Self::is_compact_compound_aggregate)
            {
                let result_ptr = self.emit_with_result(
                    current_block,
                    Inst::Cast {
                        op: CastOp::IntToPtr,
                        src_ty: Ty::I64,
                        dst_ty: Ty::Ptr,
                        operand: result,
                    },
                );
                self.compact_state_slots.insert(
                    rd,
                    super::CompactStateSlot::pointer_backed_in_block(result_ptr, 0, current_block),
                );
            } else {
                self.compact_state_slots.remove(&rd);
            }
        } else {
            self.store_reg_value(current_block, rd, result)?;
            self.compact_state_slots.remove(&rd);
        }
        self.const_scalar_values.remove(&rd);

        self.emit(
            current_block,
            InstrNode::new(Inst::CondBr {
                cond: status_is_ok,
                then_target: continue_id,
                then_args: vec![],
                else_target: propagate_id,
                else_args: vec![],
            }),
        );

        self.emit_passthrough_status_return(propagate_block);

        if let Some(shape) = result_shape {
            if let Some(len) = shape.tracked_len() {
                self.const_set_sizes.insert(rd, len);
            } else {
                self.const_set_sizes.remove(&rd);
            }
            self.aggregate_shapes.insert(rd, shape);
        } else {
            self.aggregate_shapes.remove(&rd);
            self.const_set_sizes.remove(&rd);
        }

        Ok(Some(continue_block))
    }

    fn materialize_compact_helper_call_arg(
        &mut self,
        block_idx: usize,
        op_idx: u16,
        arg_idx: usize,
        reg: u8,
        expected_shape: Option<&super::AggregateShape>,
    ) -> Result<Option<(usize, ValueId)>, TmirError> {
        if let Some(expected_shape) = expected_shape {
            if matches!(
                expected_shape,
                super::AggregateShape::Record { .. } | super::AggregateShape::Sequence { .. }
            ) {
                let abi_shape =
                    Self::compact_return_abi_shape(Some(expected_shape.clone())).ok_or_else(
                        || {
                            TmirError::UnsupportedOpcode(format!(
                                "Call compact aggregate argument {arg_idx} for callee {op_idx} requires fixed-width ABI shape, got {expected_shape:?}"
                            ))
                        },
                    )?;
                let materialized = self.materialize_compact_aggregate_call_arg_to_abi(
                    block_idx, op_idx, arg_idx, reg, &abi_shape,
                )?;
                return Ok(Some(materialized));
            }
        }

        if let Some(value) = self.materialize_compact_function_call_arg(block_idx, reg)? {
            return Ok(Some((block_idx, value)));
        }
        if let Some(value) = self.materialize_compact_sequence_call_arg(block_idx, reg)? {
            return Ok(Some(value));
        }
        self.materialize_compact_record_call_arg(block_idx, reg)
    }

    fn materialize_compact_aggregate_call_arg_to_abi(
        &mut self,
        block_idx: usize,
        op_idx: u16,
        arg_idx: usize,
        reg: u8,
        expected_abi_shape: &super::AggregateShape,
    ) -> Result<(usize, ValueId), TmirError> {
        let expected_slots = expected_abi_shape.compact_slot_count().ok_or_else(|| {
            TmirError::UnsupportedOpcode(format!(
                "Call compact aggregate argument {arg_idx} for callee {op_idx} requires fixed-width ABI shape, got {expected_abi_shape:?}"
            ))
        })?;
        let raw_source_shape = self.aggregate_shapes.get(&reg).cloned().ok_or_else(|| {
            TmirError::UnsupportedOpcode(format!(
                "Call compact aggregate argument {arg_idx} for callee {op_idx} requires tracked source shape for r{reg}, expected {expected_abi_shape:?}"
            ))
        })?;
        let source_shape = Self::complete_inferred_compact_shape_from_expected(
            &raw_source_shape,
            expected_abi_shape,
        )
        .unwrap_or(raw_source_shape);

        let result_ptr = self.alloc_aggregate(block_idx, expected_slots);
        let copied = if self.is_flat_funcdef_pair_list(reg) {
            if !Self::can_copy_flat_aggregate_to_compact_slots(&source_shape, expected_abi_shape) {
                return Err(TmirError::UnsupportedOpcode(format!(
                    "Call compact aggregate argument {arg_idx} for callee {op_idx} requires compatible flat FuncDef source and ABI shapes for r{reg}, got {source_shape:?} -> {expected_abi_shape:?}"
                )));
            }
            let source_ptr = self.load_reg_as_ptr(block_idx, reg)?;
            self.copy_flat_aggregate_to_compact_slots(
                block_idx,
                source_ptr,
                &source_shape,
                expected_abi_shape,
                result_ptr,
                0,
                true,
            )?
        } else if let Some(source_slot) = self.compact_state_slots.get(&reg).copied() {
            if !Self::can_copy_compact_aggregate_to_compact_slots(&source_shape, expected_abi_shape)
            {
                return Err(TmirError::UnsupportedOpcode(format!(
                    "Call compact aggregate argument {arg_idx} for callee {op_idx} requires compatible compact source and ABI shapes for r{reg}, got {source_shape:?} -> {expected_abi_shape:?}"
                )));
            }
            let source_slot = if source_slot.requires_pointer_reload_in_block(block_idx) {
                let reloaded_ptr = self.load_reg_as_ptr(block_idx, reg)?;
                super::CompactStateSlot::pointer_backed_in_block(
                    reloaded_ptr,
                    source_slot.offset,
                    block_idx,
                )
            } else {
                source_slot
            };
            self.copy_compact_aggregate_to_compact_slots(
                block_idx,
                source_slot.source_ptr,
                source_slot.offset,
                &source_shape,
                expected_abi_shape,
                result_ptr,
                0,
            )?
        } else {
            if !Self::can_copy_flat_aggregate_to_compact_slots(&source_shape, expected_abi_shape) {
                return Err(TmirError::UnsupportedOpcode(format!(
                    "Call compact aggregate argument {arg_idx} for callee {op_idx} requires compatible flat source and ABI shapes for r{reg}, got {source_shape:?} -> {expected_abi_shape:?}"
                )));
            }
            let source_ptr = self.load_reg_as_ptr(block_idx, reg)?;
            self.copy_flat_aggregate_to_compact_slots(
                block_idx,
                source_ptr,
                &source_shape,
                expected_abi_shape,
                result_ptr,
                0,
                false,
            )?
        };

        if copied.slots_written != expected_slots {
            return Err(TmirError::UnsupportedOpcode(format!(
                "Call compact aggregate argument {arg_idx} for callee {op_idx} copied {} slots for r{reg}, expected {expected_slots}",
                copied.slots_written
            )));
        }

        Ok((
            copied.block_idx,
            self.ptr_to_i64(copied.block_idx, result_ptr),
        ))
    }

    fn materialize_compact_sequence_call_arg(
        &mut self,
        block_idx: usize,
        reg: u8,
    ) -> Result<Option<(usize, ValueId)>, TmirError> {
        let Some(source_slot) = self.compact_state_slots.get(&reg).copied() else {
            return Ok(None);
        };
        let Some(source_shape) = self.aggregate_shapes.get(&reg).cloned() else {
            return Ok(None);
        };
        if !matches!(&source_shape, super::AggregateShape::Sequence { .. }) {
            return Ok(None);
        }

        let abi_shape = Self::compact_return_abi_shape(Some(source_shape.clone())).ok_or_else(
            || {
                TmirError::UnsupportedOpcode(format!(
                    "Call compact sequence argument r{reg} requires fixed-width ABI shape, got {source_shape:?}"
                ))
            },
        )?;
        let slot_count = abi_shape.compact_slot_count().ok_or_else(|| {
            TmirError::UnsupportedOpcode(format!(
                "Call compact sequence argument r{reg} requires fixed-width ABI shape, got {abi_shape:?}"
            ))
        })?;

        let source_slot = if source_slot.requires_pointer_reload_in_block(block_idx) {
            let reloaded_ptr = self.load_reg_as_ptr(block_idx, reg)?;
            super::CompactStateSlot::pointer_backed_in_block(
                reloaded_ptr,
                source_slot.offset,
                block_idx,
            )
        } else {
            source_slot
        };

        let result_ptr = self.alloc_aggregate(block_idx, slot_count);
        let copied = self.copy_compact_aggregate_to_compact_slots(
            block_idx,
            source_slot.source_ptr,
            source_slot.offset,
            &source_shape,
            &abi_shape,
            result_ptr,
            0,
        )?;
        if copied.slots_written != slot_count {
            return Err(TmirError::UnsupportedOpcode(format!(
                "Call compact sequence argument r{reg} copied {} slots, expected {slot_count}",
                copied.slots_written
            )));
        }

        Ok(Some((
            copied.block_idx,
            self.ptr_to_i64(copied.block_idx, result_ptr),
        )))
    }

    fn materialize_compact_record_call_arg(
        &mut self,
        block_idx: usize,
        reg: u8,
    ) -> Result<Option<(usize, ValueId)>, TmirError> {
        let Some(source_slot) = self.compact_state_slots.get(&reg).copied() else {
            return Ok(None);
        };
        let Some(source_shape) = self.aggregate_shapes.get(&reg).cloned() else {
            return Ok(None);
        };
        if !matches!(&source_shape, super::AggregateShape::Record { .. }) {
            return Ok(None);
        }

        let abi_shape = Self::compact_return_abi_shape(Some(source_shape.clone())).ok_or_else(
            || {
                TmirError::UnsupportedOpcode(format!(
                    "Call compact record argument r{reg} requires fixed-width ABI shape, got {source_shape:?}"
                ))
            },
        )?;
        let slot_count = abi_shape.compact_slot_count().ok_or_else(|| {
            TmirError::UnsupportedOpcode(format!(
                "Call compact record argument r{reg} requires fixed-width ABI shape, got {abi_shape:?}"
            ))
        })?;

        let source_slot = if source_slot.requires_pointer_reload_in_block(block_idx) {
            let reloaded_ptr = self.load_reg_as_ptr(block_idx, reg)?;
            super::CompactStateSlot::pointer_backed_in_block(
                reloaded_ptr,
                source_slot.offset,
                block_idx,
            )
        } else {
            source_slot
        };

        let result_ptr = self.alloc_aggregate(block_idx, slot_count);
        let copied = self.copy_compact_aggregate_to_compact_slots(
            block_idx,
            source_slot.source_ptr,
            source_slot.offset,
            &source_shape,
            &abi_shape,
            result_ptr,
            0,
        )?;
        if copied.slots_written != slot_count {
            return Err(TmirError::UnsupportedOpcode(format!(
                "Call compact record argument r{reg} copied {} slots, expected {slot_count}",
                copied.slots_written
            )));
        }

        Ok(Some((
            copied.block_idx,
            self.ptr_to_i64(copied.block_idx, result_ptr),
        )))
    }

    fn materialize_compact_function_call_arg(
        &mut self,
        block_idx: usize,
        reg: u8,
    ) -> Result<Option<ValueId>, TmirError> {
        if self.is_flat_funcdef_pair_list(reg) {
            return Ok(None);
        }
        let Some(source_slot) = self.compact_state_slots.get(&reg).copied() else {
            return Ok(None);
        };
        let Some(shape) = self.aggregate_shapes.get(&reg).cloned() else {
            return Ok(None);
        };
        let super::AggregateShape::Function {
            len,
            domain_lo,
            value,
        } = shape
        else {
            return Ok(None);
        };
        let domain_lo = domain_lo.ok_or_else(|| {
            TmirError::UnsupportedOpcode(format!(
                "Call compact function argument r{reg} requires contiguous integer domain metadata"
            ))
        })?;
        let value_shape = value.ok_or_else(|| {
            TmirError::UnsupportedOpcode(format!(
                "Call compact function argument r{reg} requires tracked value shape"
            ))
        })?;
        if !value_shape.is_numeric_scalar_shape() {
            return Err(TmirError::UnsupportedOpcode(format!(
                "Call compact function argument r{reg} only supports Int values, got {value_shape:?}"
            )));
        }

        let value_stride = value_shape.compact_slot_count().ok_or_else(|| {
            TmirError::UnsupportedOpcode(format!(
                "Call compact function argument r{reg} requires fixed-width value shape, got {value_shape:?}"
            ))
        })?;
        if value_stride != 1 {
            return Err(TmirError::UnsupportedOpcode(format!(
                "Call compact function argument r{reg} only supports single-slot values, got {value_shape:?}"
            )));
        }
        let source_slot = if source_slot.is_raw_compact_slot() {
            source_slot
        } else {
            let reloaded_ptr = self.load_reg_as_ptr(block_idx, reg)?;
            super::CompactStateSlot::pointer_backed_in_block(
                reloaded_ptr,
                source_slot.offset,
                block_idx,
            )
        };

        let pair_slots = len.checked_mul(2).ok_or_else(|| {
            TmirError::UnsupportedOpcode(format!(
                "Call compact function argument r{reg} slot count overflows: {len} * 2"
            ))
        })?;
        let total_slots = pair_slots.checked_add(1).ok_or_else(|| {
            TmirError::UnsupportedOpcode(format!(
                "Call compact function argument r{reg} slot count overflows: {pair_slots} + 1"
            ))
        })?;
        let result_ptr = self.alloc_aggregate(block_idx, total_slots);

        let pair_count = self.emit_i64_const(block_idx, i64::from(len));
        self.store_at_offset(block_idx, result_ptr, 0, pair_count);

        for idx in 0..len {
            let key_slot = idx
                .checked_mul(2)
                .and_then(|slot| slot.checked_add(1))
                .ok_or_else(|| {
                    TmirError::UnsupportedOpcode(
                        "Call compact function key slot overflows u32".to_owned(),
                    )
                })?;
            let value_slot = key_slot.checked_add(1).ok_or_else(|| {
                TmirError::UnsupportedOpcode(
                    "Call compact function value slot overflows u32".to_owned(),
                )
            })?;
            let key_value = domain_lo.checked_add(i64::from(idx)).ok_or_else(|| {
                TmirError::UnsupportedOpcode(format!(
                    "Call compact function argument r{reg} key overflows: {domain_lo} + {idx}"
                ))
            })?;
            let key = self.emit_i64_const(block_idx, key_value);
            self.store_at_offset(block_idx, result_ptr, key_slot, key);

            let source_offset = source_slot
                .offset
                .checked_add(idx.checked_mul(value_stride).ok_or_else(|| {
                    TmirError::UnsupportedOpcode(
                        "Call compact function source slot overflows u32".to_owned(),
                    )
                })?)
                .ok_or_else(|| {
                    TmirError::UnsupportedOpcode(
                        "Call compact function source slot overflows u32".to_owned(),
                    )
                })?;
            let value = self.load_at_offset(block_idx, source_slot.source_ptr, source_offset);
            self.store_at_offset(block_idx, result_ptr, value_slot, value);
        }

        Ok(Some(self.ptr_to_i64(block_idx, result_ptr)))
    }
}
