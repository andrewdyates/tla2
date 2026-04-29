// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Sequence, tuple, record, and builtin lowering: SeqNew, TupleNew, TupleGet,
//! RecordNew, RecordGet, Cardinality, Len, Head, Tail, Append.

use crate::TmirError;
use tla_jit_abi::JitRuntimeErrorKind;
use tla_value::Value;
use tmir::inst::*;
use tmir::ty::Ty;
use tmir::Constant;
use tmir::InstrNode;

use super::Ctx;

impl<'cp> Ctx<'cp> {
    /// Lower SeqNew { rd, start, count }: build a sequence from consecutive regs.
    ///
    /// Same layout as sets: slot[0] = length, slot[1..=count] = elements.
    pub(super) fn lower_seq_new(
        &mut self,
        block_idx: usize,
        rd: u8,
        start: u8,
        count: u8,
    ) -> Result<(), TmirError> {
        let total_slots = u32::from(count) + 1;
        let agg_ptr = self.alloc_aggregate(block_idx, total_slots);

        let len_val = self.emit_i64_const(block_idx, i64::from(count));
        self.store_at_offset(block_idx, agg_ptr, 0, len_val);

        let mut element_shapes = Vec::with_capacity(usize::from(count));
        let mut tracked_shape = true;
        for i in 0..count {
            let reg = start.checked_add(i).ok_or_else(|| {
                TmirError::Emission(format!("SeqNew register overflow: start={start} + i={i}"))
            })?;
            let elem = self.load_reg(block_idx, reg)?;
            self.store_at_offset(block_idx, agg_ptr, u32::from(i) + 1, elem);
            element_shapes.push(self.aggregate_shapes.get(&reg).cloned());
            tracked_shape &= element_shapes.last().is_some_and(Option::is_some);
        }

        self.store_reg_ptr(block_idx, rd, agg_ptr)?;
        self.compact_state_slots.remove(&rd);
        self.clear_flat_funcdef_pair_list(rd);
        self.const_scalar_values.remove(&rd);
        if tracked_shape {
            let shape = super::AggregateShape::Sequence {
                extent: super::SequenceExtent::Exact(u32::from(count)),
                element: super::uniform_shape(&element_shapes),
            };
            if shape.compact_slot_count() == Some(total_slots) {
                self.compact_state_slots.insert(
                    rd,
                    super::CompactStateSlot::pointer_backed_in_block(agg_ptr, 0, block_idx),
                );
            }
            if let Some(len) = shape.tracked_len() {
                self.record_set_size(rd, len);
            } else {
                self.const_set_sizes.remove(&rd);
            }
            self.aggregate_shapes.insert(rd, shape);
        } else {
            self.aggregate_shapes.remove(&rd);
            self.const_set_sizes.remove(&rd);
        }
        Ok(())
    }

    /// Lower TupleNew { rd, start, count }: build a tuple from consecutive regs.
    ///
    /// Identical layout to sequences.
    pub(super) fn lower_tuple_new(
        &mut self,
        block_idx: usize,
        rd: u8,
        start: u8,
        count: u8,
    ) -> Result<(), TmirError> {
        self.lower_seq_new(block_idx, rd, start, count)
    }

    /// Lower TupleGet { rd, rs, idx }: get tuple element (1-indexed per TLA+).
    ///
    /// slot[idx] is the element (since slot[0] is length, 1-indexed access
    /// naturally maps to the array layout).
    pub(super) fn lower_tuple_get(
        &mut self,
        block_idx: usize,
        rd: u8,
        rs: u8,
        idx: u16,
    ) -> Result<(), TmirError> {
        let seq_ptr = self.load_reg_as_ptr(block_idx, rs)?;
        let elem = self.load_at_offset(block_idx, seq_ptr, u32::from(idx));
        self.store_reg_value(block_idx, rd, elem)?;
        self.compact_state_slots.remove(&rd);
        Ok(())
    }

    // =====================================================================
    // Record operations
    // =====================================================================

    /// Lower RecordNew { rd, fields_start, values_start, count }.
    ///
    /// Records are stored as flat arrays: slot[i] = value for field i.
    /// No length header needed since count is static.
    pub(super) fn lower_record_new(
        &mut self,
        block_idx: usize,
        rd: u8,
        fields_start: u16,
        values_start: u8,
        count: u8,
    ) -> Result<(), TmirError> {
        let agg_ptr = self.alloc_aggregate(block_idx, u32::from(count));

        for i in 0..count {
            let val = self.load_reg(block_idx, values_start + i)?;
            self.store_at_offset(block_idx, agg_ptr, u32::from(i), val);
        }

        self.store_reg_ptr(block_idx, rd, agg_ptr)?;
        self.compact_state_slots.remove(&rd);
        self.clear_flat_funcdef_pair_list(rd);

        if let Some(pool) = self.const_pool {
            let mut fields = Vec::with_capacity(usize::from(count));
            for i in 0..count {
                let field_name = match pool.get_value(fields_start + u16::from(i)) {
                    Value::String(name) => tla_core::intern_name(name),
                    _ => {
                        self.aggregate_shapes.remove(&rd);
                        self.const_set_sizes.remove(&rd);
                        return Ok(());
                    }
                };
                fields.push((
                    field_name,
                    self.aggregate_shapes
                        .get(&(values_start + i))
                        .cloned()
                        .map(Box::new),
                ));
            }
            let shape = super::AggregateShape::Record { fields };
            if shape.compact_slot_count() == Some(u32::from(count)) {
                self.compact_state_slots.insert(
                    rd,
                    super::CompactStateSlot::pointer_backed_in_block(agg_ptr, 0, block_idx),
                );
            } else {
                self.compact_state_slots.remove(&rd);
            }
            self.aggregate_shapes.insert(rd, shape);
            self.const_set_sizes.remove(&rd);
            self.const_scalar_values.remove(&rd);
        }

        Ok(())
    }

    /// Lower RecordSet { rd, fields_start, values_start, count }.
    ///
    /// Record sets are represented lazily as an array of field-domain values.
    /// Field names and domain shapes are tracked separately so SetIn can lower
    /// record membership without enumerating the Cartesian product.
    pub(super) fn lower_record_set(
        &mut self,
        block_idx: usize,
        rd: u8,
        fields_start: u16,
        values_start: u8,
        count: u8,
    ) -> Result<(), TmirError> {
        let pool = self.const_pool.ok_or_else(|| {
            TmirError::UnsupportedOpcode(
                "RecordSet: constant pool is required to resolve field names".to_owned(),
            )
        })?;

        let agg_ptr = self.alloc_aggregate(block_idx, u32::from(count));
        let mut fields = Vec::with_capacity(usize::from(count));

        for i in 0..count {
            let value_reg = values_start + i;
            let field_name = match pool.get_value(fields_start + u16::from(i)) {
                Value::String(name) => tla_core::intern_name(name),
                other => {
                    return Err(TmirError::UnsupportedOpcode(format!(
                        "RecordSet: field constant at {} is not a string: {other:?}",
                        fields_start + u16::from(i)
                    )));
                }
            };
            let domain_shape = self
                .aggregate_shapes
                .get(&value_reg)
                .cloned()
                .ok_or_else(|| {
                    TmirError::UnsupportedOpcode(format!(
                        "RecordSet: field {field_name:?} domain in r{value_reg} has no tracked shape"
                    ))
                })?;
            let domain_value = self.load_reg(block_idx, value_reg)?;
            self.store_at_offset(block_idx, agg_ptr, u32::from(i), domain_value);
            fields.push((field_name, domain_shape));
        }

        self.store_reg_ptr(block_idx, rd, agg_ptr)?;
        self.compact_state_slots.remove(&rd);
        self.aggregate_shapes
            .insert(rd, super::AggregateShape::RecordSet { fields });
        self.const_set_sizes.remove(&rd);
        self.const_scalar_values.remove(&rd);
        Ok(())
    }

    /// Lower RecordGet { rd, rs, field_idx }.
    ///
    /// Loads the value at the resolved field offset in the record aggregate.
    pub(super) fn lower_record_get(
        &mut self,
        block_idx: usize,
        rd: u8,
        rs: u8,
        field_idx: u16,
    ) -> Result<(), TmirError> {
        let field_name = super::record_get_field_name(self.const_pool, field_idx);
        let record_shape = self.aggregate_shapes.get(&rs).cloned();
        let result_shape =
            super::record_get_shape(record_shape.as_ref(), self.const_pool, field_idx);

        if let (
            Some(source_slot),
            Some(field_name),
            Some(record_shape @ super::AggregateShape::Record { .. }),
        ) = (
            self.compact_state_slot_for_use(block_idx, rs)?,
            field_name,
            record_shape.clone(),
        ) {
            let Some((field_offset, field_shape)) = record_shape.compact_record_field(field_name)
            else {
                return Err(TmirError::UnsupportedOpcode(format!(
                    "RecordGet: field {:?} has no fixed compact offset in r{rs}",
                    tla_core::resolve_name_id(field_name)
                )));
            };
            let Some(field_shape) = field_shape else {
                return Err(TmirError::UnsupportedOpcode(format!(
                    "RecordGet: field {:?} in r{rs} has no tracked shape",
                    tla_core::resolve_name_id(field_name)
                )));
            };
            let field_stride = field_shape.compact_slot_count().ok_or_else(|| {
                TmirError::UnsupportedOpcode(format!(
                    "RecordGet: field {:?} in r{rs} requires fixed-width shape, got {field_shape:?}",
                    tla_core::resolve_name_id(field_name)
                ))
            })?;
            if field_stride == 1 {
                let result_val = self.load_at_offset(
                    block_idx,
                    source_slot.source_ptr,
                    source_slot.offset + field_offset,
                );
                self.store_single_slot_compact_result(
                    block_idx,
                    rd,
                    result_val,
                    super::CompactStateSlot::raw(
                        source_slot.source_ptr,
                        source_slot.offset + field_offset,
                    ),
                    field_shape,
                )?;
            } else {
                let source_base =
                    self.emit_i64_const(block_idx, i64::from(source_slot.offset + field_offset));
                let result_ptr = self.copy_compact_slots_from_dynamic_base(
                    block_idx,
                    source_slot.source_ptr,
                    source_base,
                    field_stride,
                );
                self.store_compact_aggregate_result(block_idx, rd, result_ptr, field_shape)?;
            }
            return Ok(());
        }

        self.reject_raw_compact_pointer_fallback(rs, "RecordGet")?;
        let rec_ptr = self.load_reg_as_ptr(block_idx, rs)?;
        let offset = if let (Some(field_name), Some(record_shape)) = (field_name, record_shape) {
            record_shape
                .record_field(field_name)
                .map(|(offset, _)| offset)
                .ok_or_else(|| {
                    TmirError::UnsupportedOpcode(format!(
                        "RecordGet: field {:?} is not present in r{rs}",
                        tla_core::resolve_name_id(field_name)
                    ))
                })?
        } else {
            u32::from(field_idx)
        };
        let val = self.load_at_offset(block_idx, rec_ptr, offset);
        self.store_reg_value(block_idx, rd, val)?;
        self.record_aggregate_shape(rd, result_shape);
        Ok(())
    }

    // =====================================================================
    // Cardinality (CallBuiltin Cardinality)
    // =====================================================================

    /// Lower Cardinality: returns the length field (slot 0) of a set aggregate.
    pub(super) fn lower_cardinality(
        &mut self,
        block_idx: usize,
        rd: u8,
        set_reg: u8,
    ) -> Result<(), TmirError> {
        if let Some(super::AggregateShape::SetBitmask {
            universe_len,
            universe,
        }) = self.aggregate_shapes.get(&set_reg).cloned()
        {
            if matches!(universe, super::SetBitmaskUniverse::Unknown) {
                return Err(TmirError::UnsupportedOpcode(format!(
                    "Cardinality: compact SetBitmask r{set_reg} requires exact universe metadata"
                )));
            }
            let valid_mask = Self::compact_set_bitmask_valid_mask(universe_len, "Cardinality")?;
            let raw_mask = self.load_reg(block_idx, set_reg)?;
            let valid_mask_value = self.emit_i64_const(block_idx, valid_mask);
            let mask = self.emit_with_result(
                block_idx,
                Inst::BinOp {
                    op: BinOp::And,
                    ty: Ty::I64,
                    lhs: raw_mask,
                    rhs: valid_mask_value,
                },
            );
            let zero = self.emit_i64_const(block_idx, 0);
            let one = self.emit_i64_const(block_idx, 1);
            let mut count = zero;
            for idx in 0..universe_len {
                let bit = self.emit_i64_const(block_idx, 1_i64 << idx);
                let present_bits = self.emit_with_result(
                    block_idx,
                    Inst::BinOp {
                        op: BinOp::And,
                        ty: Ty::I64,
                        lhs: mask,
                        rhs: bit,
                    },
                );
                let present = self.emit_with_result(
                    block_idx,
                    Inst::ICmp {
                        op: ICmpOp::Ne,
                        ty: Ty::I64,
                        lhs: present_bits,
                        rhs: zero,
                    },
                );
                let addend = self.emit_with_result(
                    block_idx,
                    Inst::Select {
                        ty: Ty::I64,
                        cond: present,
                        then_val: one,
                        else_val: zero,
                    },
                );
                count = self.emit_with_result(
                    block_idx,
                    Inst::BinOp {
                        op: BinOp::Add,
                        ty: Ty::I64,
                        lhs: count,
                        rhs: addend,
                    },
                );
            }
            self.store_reg_value(block_idx, rd, count)?;
            self.compact_state_slots.remove(&rd);
            return Ok(());
        }

        let set_ptr = self.load_reg_as_ptr(block_idx, set_reg)?;
        let len = self.load_at_offset(block_idx, set_ptr, 0);
        self.store_reg_value(block_idx, rd, len)?;
        self.compact_state_slots.remove(&rd);
        Ok(())
    }

    // =====================================================================
    // Sequence builtins (Len, Head, Tail, Append)
    // =====================================================================

    /// Lower Len(seq): returns slot[0] of the sequence aggregate.
    pub(super) fn lower_seq_len(
        &mut self,
        block_idx: usize,
        rd: u8,
        seq_reg: u8,
    ) -> Result<(), TmirError> {
        if let Some(source_slot) = self.compact_state_slot_for_use(block_idx, seq_reg)? {
            let source_shape = self.aggregate_shapes.get(&seq_reg).cloned();
            if !matches!(source_shape, Some(super::AggregateShape::Sequence { .. })) {
                return Err(TmirError::UnsupportedOpcode(format!(
                    "Len: compact source r{seq_reg} requires a tracked sequence shape, got {source_shape:?}"
                )));
            }
            let len = self.load_at_offset(block_idx, source_slot.source_ptr, source_slot.offset);
            self.store_reg_value(block_idx, rd, len)?;
            self.compact_state_slots.remove(&rd);
            return Ok(());
        }

        let seq_ptr = self.load_reg_as_ptr(block_idx, seq_reg)?;
        let len = self.load_at_offset(block_idx, seq_ptr, 0);
        self.store_reg_value(block_idx, rd, len)?;
        self.compact_state_slots.remove(&rd);
        Ok(())
    }

    /// Lower Head(seq): returns slot[1] of the sequence aggregate.
    pub(super) fn lower_seq_head(
        &mut self,
        block_idx: usize,
        rd: u8,
        seq_reg: u8,
    ) -> Result<Option<usize>, TmirError> {
        if let Some(source_slot) = self.compact_state_slot_for_use(block_idx, seq_reg)? {
            let source_shape = self.aggregate_shapes.get(&seq_reg).cloned();
            let Some(super::AggregateShape::Sequence {
                extent,
                element: Some(element_shape),
            }) = source_shape
            else {
                return Err(TmirError::UnsupportedOpcode(format!(
                    "Head: compact source r{seq_reg} requires a tracked sequence element shape, got {source_shape:?}"
                )));
            };
            let element_stride = element_shape.compact_slot_count().ok_or_else(|| {
                TmirError::UnsupportedOpcode(format!(
                    "Head: compact sequence r{seq_reg} requires fixed-width element shape, got {element_shape:?}"
                ))
            })?;
            let capacity = extent.capacity();
            let head_offset = source_slot.offset.checked_add(1).ok_or_else(|| {
                TmirError::UnsupportedOpcode("Head: compact source slot overflows u32".to_owned())
            })?;

            let old_len =
                self.load_at_offset(block_idx, source_slot.source_ptr, source_slot.offset);
            let zero = self.emit_i64_const(block_idx, 0);
            let non_empty = self.emit_with_result(
                block_idx,
                Inst::ICmp {
                    op: ICmpOp::Sgt,
                    ty: Ty::I64,
                    lhs: old_len,
                    rhs: zero,
                },
            );

            let check_capacity_blk = self.new_aux_block("compact_head_check_capacity");
            let ok_blk = self.new_aux_block("compact_head_ok");
            let error_blk = self.new_aux_block("compact_head_error");
            let check_capacity_id = self.block_id_of(check_capacity_blk);
            let ok_id = self.block_id_of(ok_blk);
            let error_id = self.block_id_of(error_blk);
            self.emit(
                block_idx,
                InstrNode::new(Inst::CondBr {
                    cond: non_empty,
                    then_target: check_capacity_id,
                    then_args: vec![],
                    else_target: error_id,
                    else_args: vec![],
                }),
            );

            let capacity_val = self.emit_i64_const(check_capacity_blk, i64::from(capacity));
            let within_capacity = self.emit_with_result(
                check_capacity_blk,
                Inst::ICmp {
                    op: ICmpOp::Sle,
                    ty: Ty::I64,
                    lhs: old_len,
                    rhs: capacity_val,
                },
            );
            self.emit(
                check_capacity_blk,
                InstrNode::new(Inst::CondBr {
                    cond: within_capacity,
                    then_target: ok_id,
                    then_args: vec![],
                    else_target: error_id,
                    else_args: vec![],
                }),
            );
            self.emit_runtime_error_and_return(error_blk, JitRuntimeErrorKind::TypeMismatch);

            if element_stride == 1 {
                let head = self.load_at_offset(ok_blk, source_slot.source_ptr, head_offset);
                self.store_single_slot_compact_result(
                    ok_blk,
                    rd,
                    head,
                    super::CompactStateSlot::raw(source_slot.source_ptr, head_offset),
                    *element_shape,
                )?;
            } else {
                let head_base = self.emit_i64_const(ok_blk, i64::from(head_offset));
                let head_ptr = self.copy_compact_slots_from_dynamic_base(
                    ok_blk,
                    source_slot.source_ptr,
                    head_base,
                    element_stride,
                );
                self.store_compact_aggregate_result(ok_blk, rd, head_ptr, *element_shape)?;
            }
            return Ok(Some(ok_blk));
        }

        let seq_ptr = self.load_reg_as_ptr(block_idx, seq_reg)?;
        let head = self.load_at_offset(block_idx, seq_ptr, 1);
        self.store_reg_value(block_idx, rd, head)?;
        self.compact_state_slots.remove(&rd);
        Ok(Some(block_idx))
    }

    /// Lower Tail(seq): creates a new sequence with all elements except the first.
    ///
    /// Result: slot[0] = len-1, slot[1..] = original slot[2..].
    pub(super) fn lower_seq_tail(
        &mut self,
        block_idx: usize,
        rd: u8,
        seq_reg: u8,
    ) -> Result<Option<usize>, TmirError> {
        if let (
            Some(source_slot),
            Some(super::AggregateShape::Sequence {
                extent,
                element: Some(element_shape),
            }),
        ) = (
            self.compact_state_slot_for_use(block_idx, seq_reg)?,
            self.aggregate_shapes.get(&seq_reg).cloned(),
        ) {
            let capacity = extent.capacity();
            let element_stride = element_shape.compact_slot_count().ok_or_else(|| {
                TmirError::UnsupportedOpcode(format!(
                    "Tail: compact sequence r{seq_reg} requires fixed-width element shape, got {element_shape:?}"
                ))
            })?;
            let result_shape = super::AggregateShape::Sequence {
                extent,
                element: Some(element_shape.clone()),
            };
            let total_slots = result_shape.compact_slot_count().ok_or_else(|| {
                TmirError::UnsupportedOpcode(format!(
                    "Tail: compact result sequence requires fixed-width shape, got {result_shape:?}"
                ))
            })?;
            let old_len =
                self.load_at_offset(block_idx, source_slot.source_ptr, source_slot.offset);
            let zero = self.emit_i64_const(block_idx, 0);
            let one = self.emit_i64_const(block_idx, 1);
            let non_empty = self.emit_with_result(
                block_idx,
                Inst::ICmp {
                    op: ICmpOp::Sgt,
                    ty: Ty::I64,
                    lhs: old_len,
                    rhs: zero,
                },
            );

            let check_capacity_blk = self.new_aux_block("compact_tail_check_capacity");
            let ok_blk = self.new_aux_block("compact_tail_ok");
            let error_blk = self.new_aux_block("compact_tail_error");
            let check_capacity_id = self.block_id_of(check_capacity_blk);
            let ok_id = self.block_id_of(ok_blk);
            let error_id = self.block_id_of(error_blk);
            self.emit(
                block_idx,
                InstrNode::new(Inst::CondBr {
                    cond: non_empty,
                    then_target: check_capacity_id,
                    then_args: vec![],
                    else_target: error_id,
                    else_args: vec![],
                }),
            );

            let capacity_val = self.emit_i64_const(check_capacity_blk, i64::from(capacity));
            let within_capacity = self.emit_with_result(
                check_capacity_blk,
                Inst::ICmp {
                    op: ICmpOp::Sle,
                    ty: Ty::I64,
                    lhs: old_len,
                    rhs: capacity_val,
                },
            );
            self.emit(
                check_capacity_blk,
                InstrNode::new(Inst::CondBr {
                    cond: within_capacity,
                    then_target: ok_id,
                    then_args: vec![],
                    else_target: error_id,
                    else_args: vec![],
                }),
            );
            self.emit_runtime_error_and_return(error_blk, JitRuntimeErrorKind::TypeMismatch);

            let result_ptr = self.alloc_aggregate(ok_blk, total_slots);
            let new_len = self.emit_with_result(
                ok_blk,
                Inst::BinOp {
                    op: BinOp::Sub,
                    ty: Ty::I64,
                    lhs: old_len,
                    rhs: one,
                },
            );
            self.store_at_offset(ok_blk, result_ptr, 0, new_len);

            for elem_idx in 0..capacity {
                let elem_idx_val = self.emit_i64_const(ok_blk, i64::from(elem_idx));
                let is_live = self.emit_with_result(
                    ok_blk,
                    Inst::ICmp {
                        op: ICmpOp::Slt,
                        ty: Ty::I64,
                        lhs: elem_idx_val,
                        rhs: new_len,
                    },
                );
                for value_offset in 0..element_stride {
                    let value = if elem_idx + 1 < capacity {
                        let source_offset =
                            1 + (elem_idx + 1).checked_mul(element_stride).ok_or_else(|| {
                                TmirError::UnsupportedOpcode(
                                    "Tail: compact source slot overflows u32".to_owned(),
                                )
                            })? + value_offset;
                        self.load_at_offset(
                            ok_blk,
                            source_slot.source_ptr,
                            source_slot.offset + source_offset,
                        )
                    } else {
                        zero
                    };
                    let value = if elem_idx + 1 < capacity {
                        self.emit_with_result(
                            ok_blk,
                            Inst::Select {
                                ty: Ty::I64,
                                cond: is_live,
                                then_val: value,
                                else_val: zero,
                            },
                        )
                    } else {
                        value
                    };
                    let dest_offset =
                        1 + elem_idx.checked_mul(element_stride).ok_or_else(|| {
                            TmirError::UnsupportedOpcode(
                                "Tail: compact destination slot overflows u32".to_owned(),
                            )
                        })? + value_offset;
                    self.store_at_offset(ok_blk, result_ptr, dest_offset, value);
                }
            }

            self.store_compact_aggregate_result(ok_blk, rd, result_ptr, result_shape)?;
            return Ok(Some(ok_blk));
        }

        if self.compact_state_slots.contains_key(&seq_reg) {
            let source_shape = self.aggregate_shapes.get(&seq_reg);
            return Err(TmirError::UnsupportedOpcode(format!(
                "Tail: compact source r{seq_reg} requires a tracked fixed-width sequence element shape, got {source_shape:?}"
            )));
        }

        let seq_ptr = self.load_reg_as_ptr(block_idx, seq_reg)?;
        let old_len = self.load_at_offset(block_idx, seq_ptr, 0);
        let one = self.emit_i64_const(block_idx, 1);
        let new_len = self.emit_with_result(
            block_idx,
            Inst::BinOp {
                op: BinOp::Sub,
                ty: Ty::I64,
                lhs: old_len,
                rhs: one,
            },
        );

        // Allocate new aggregate: new_len + 1 slots
        let total = self.emit_with_result(
            block_idx,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: new_len,
                rhs: one,
            },
        );
        let total_i32 = self.emit_with_result(
            block_idx,
            Inst::Cast {
                op: CastOp::Trunc,
                src_ty: Ty::I64,
                dst_ty: Ty::I32,
                operand: total,
            },
        );
        let new_ptr = self.emit_with_result(
            block_idx,
            Inst::Alloca {
                ty: Ty::I64,
                count: Some(total_i32),
                align: None,
            },
        );

        // Store new length
        self.store_at_offset(block_idx, new_ptr, 0, new_len);

        // Copy loop: for i in 0..new_len, new[i+1] = old[i+2]
        let zero = self.emit_i64_const(block_idx, 0);
        let two = self.emit_i64_const(block_idx, 2);
        let i_alloca = self.emit_with_result(
            block_idx,
            Inst::Alloca {
                ty: Ty::I64,
                count: None,
                align: None,
            },
        );
        self.emit(
            block_idx,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: i_alloca,
                value: zero,
                align: None,
                volatile: false,
            }),
        );

        let loop_hdr = self.new_aux_block("tail_hdr");
        let loop_body = self.new_aux_block("tail_body");
        let loop_done = self.new_aux_block("tail_done");

        let hdr_id = self.block_id_of(loop_hdr);
        let body_id = self.block_id_of(loop_body);
        let done_id = self.block_id_of(loop_done);

        self.emit(
            block_idx,
            InstrNode::new(Inst::Br {
                target: hdr_id,
                args: vec![],
            }),
        );

        // Header
        let i_val = self.emit_with_result(
            loop_hdr,
            Inst::Load {
                ty: Ty::I64,
                ptr: i_alloca,
                align: None,
                volatile: false,
            },
        );
        let cmp = self.emit_with_result(
            loop_hdr,
            Inst::ICmp {
                op: ICmpOp::Slt,
                ty: Ty::I64,
                lhs: i_val,
                rhs: new_len,
            },
        );
        self.emit(
            loop_hdr,
            InstrNode::new(Inst::CondBr {
                cond: cmp,
                then_target: body_id,
                then_args: vec![],
                else_target: done_id,
                else_args: vec![],
            }),
        );

        // Body
        let i_val2 = self.emit_with_result(
            loop_body,
            Inst::Load {
                ty: Ty::I64,
                ptr: i_alloca,
                align: None,
                volatile: false,
            },
        );
        let src_slot = self.emit_with_result(
            loop_body,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: i_val2,
                rhs: two,
            },
        );
        let elem = self.load_at_dynamic_offset(loop_body, seq_ptr, src_slot);
        let dst_slot = self.emit_with_result(
            loop_body,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: i_val2,
                rhs: one,
            },
        );
        self.store_at_dynamic_offset(loop_body, new_ptr, dst_slot, elem);
        let next_i = self.emit_with_result(
            loop_body,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: i_val2,
                rhs: one,
            },
        );
        self.emit(
            loop_body,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: i_alloca,
                value: next_i,
                align: None,
                volatile: false,
            }),
        );
        self.emit(
            loop_body,
            InstrNode::new(Inst::Br {
                target: hdr_id,
                args: vec![],
            }),
        );

        // Done
        self.store_reg_ptr(loop_done, rd, new_ptr)?;

        Ok(Some(loop_done))
    }

    /// Lower Append(seq, elem): creates a new sequence with elem appended.
    ///
    /// Result: slot[0] = old_len+1, slot[1..=old_len] = original, slot[old_len+1] = elem.
    pub(super) fn lower_seq_append(
        &mut self,
        block_idx: usize,
        rd: u8,
        seq_reg: u8,
        elem_reg: u8,
        result_shape: Option<super::AggregateShape>,
    ) -> Result<Option<usize>, TmirError> {
        let source_shape = self.aggregate_shapes.get(&seq_reg).cloned();
        let elem_shape = self.aggregate_shapes.get(&elem_reg).cloned();
        let compact_result_shape = match (&source_shape, elem_shape.as_ref(), result_shape.clone())
        {
            (
                Some(super::AggregateShape::Sequence {
                    extent: source_extent,
                    element: Some(source_element),
                }),
                Some(elem_shape),
                Some(super::AggregateShape::Sequence {
                    extent: result_extent,
                    element: None,
                }),
            ) if result_extent == *source_extent
                && Self::compatible_compact_materialization_value(elem_shape, source_element) =>
            {
                Some(super::AggregateShape::Sequence {
                    extent: result_extent,
                    element: Some(source_element.clone()),
                })
            }
            _ => result_shape.clone(),
        };

        if let (
            Some(source_slot),
            Some(super::AggregateShape::Sequence {
                extent: source_extent,
                element: Some(source_element),
            }),
            Some(super::AggregateShape::Sequence {
                extent: result_extent,
                element: Some(result_element),
            }),
        ) = (
            self.compact_state_slot_for_use(block_idx, seq_reg)?,
            source_shape.clone(),
            compact_result_shape.clone(),
        ) {
            let result_capacity = result_extent.capacity();
            let preserves_capacity = result_extent == source_extent;
            let widens_exact_by_one = match (source_extent, result_extent) {
                (
                    super::SequenceExtent::Exact(source_len),
                    super::SequenceExtent::Exact(result_len),
                ) => source_len.checked_add(1) == Some(result_len),
                _ => false,
            };
            if (preserves_capacity || widens_exact_by_one) && *source_element == *result_element {
                let result_shape = super::AggregateShape::Sequence {
                    extent: result_extent,
                    element: Some(source_element.clone()),
                };
                let source_slots = super::AggregateShape::Sequence {
                    extent: source_extent,
                    element: Some(source_element.clone()),
                }
                .compact_slot_count()
                .ok_or_else(|| {
                    TmirError::UnsupportedOpcode(format!(
                        "Append: compact source sequence r{seq_reg} requires fixed-width shape"
                    ))
                })?;
                let result_slots = result_shape.compact_slot_count().ok_or_else(|| {
                    TmirError::UnsupportedOpcode(format!(
                        "Append: compact result sequence requires fixed-width shape, got {result_shape:?}"
                    ))
                })?;
                let element_stride = source_element.compact_slot_count().ok_or_else(|| {
                    TmirError::UnsupportedOpcode(format!(
                        "Append: compact element requires fixed-width shape, got {source_element:?}"
                    ))
                })?;

                let old_len =
                    self.load_at_offset(block_idx, source_slot.source_ptr, source_slot.offset);
                let zero = self.emit_i64_const(block_idx, 0);
                let one = self.emit_i64_const(block_idx, 1);
                let non_negative = self.emit_with_result(
                    block_idx,
                    Inst::ICmp {
                        op: ICmpOp::Sge,
                        ty: Ty::I64,
                        lhs: old_len,
                        rhs: zero,
                    },
                );

                let check_capacity_blk = self.new_aux_block("compact_append_check_capacity");
                let ok_blk = self.new_aux_block("compact_append_ok");
                let error_blk = self.new_aux_block("compact_append_error");
                let check_capacity_id = self.block_id_of(check_capacity_blk);
                let ok_id = self.block_id_of(ok_blk);
                let error_id = self.block_id_of(error_blk);
                self.emit(
                    block_idx,
                    InstrNode::new(Inst::CondBr {
                        cond: non_negative,
                        then_target: check_capacity_id,
                        then_args: vec![],
                        else_target: error_id,
                        else_args: vec![],
                    }),
                );

                let capacity_val =
                    self.emit_i64_const(check_capacity_blk, i64::from(result_capacity));
                let has_capacity = self.emit_with_result(
                    check_capacity_blk,
                    Inst::ICmp {
                        op: ICmpOp::Slt,
                        ty: Ty::I64,
                        lhs: old_len,
                        rhs: capacity_val,
                    },
                );
                self.emit(
                    check_capacity_blk,
                    InstrNode::new(Inst::CondBr {
                        cond: has_capacity,
                        then_target: ok_id,
                        then_args: vec![],
                        else_target: error_id,
                        else_args: vec![],
                    }),
                );
                self.emit_runtime_error_and_return(error_blk, JitRuntimeErrorKind::TypeMismatch);

                let result_ptr = self.alloc_aggregate(ok_blk, result_slots);
                let new_len = self.emit_with_result(
                    ok_blk,
                    Inst::BinOp {
                        op: BinOp::Add,
                        ty: Ty::I64,
                        lhs: old_len,
                        rhs: one,
                    },
                );
                self.store_at_offset(ok_blk, result_ptr, 0, new_len);

                let elem_materialized =
                    self.materialize_reg_as_compact_source(ok_blk, elem_reg, &source_element)?;
                let ok_blk = elem_materialized.block_idx;
                let elem_source = elem_materialized.slot;

                for elem_idx in 0..result_capacity {
                    let elem_idx_val = self.emit_i64_const(ok_blk, i64::from(elem_idx));
                    let before_append = self.emit_with_result(
                        ok_blk,
                        Inst::ICmp {
                            op: ICmpOp::Slt,
                            ty: Ty::I64,
                            lhs: elem_idx_val,
                            rhs: old_len,
                        },
                    );
                    let at_append = self.emit_with_result(
                        ok_blk,
                        Inst::ICmp {
                            op: ICmpOp::Eq,
                            ty: Ty::I64,
                            lhs: elem_idx_val,
                            rhs: old_len,
                        },
                    );
                    for value_offset in 0..element_stride {
                        let old_offset =
                            1 + elem_idx.checked_mul(element_stride).ok_or_else(|| {
                                TmirError::UnsupportedOpcode(
                                    "Append: compact source slot overflows u32".to_owned(),
                                )
                            })? + value_offset;
                        let result_offset =
                            1 + elem_idx.checked_mul(element_stride).ok_or_else(|| {
                                TmirError::UnsupportedOpcode(
                                    "Append: compact result slot overflows u32".to_owned(),
                                )
                            })? + value_offset;
                        let old_val = if old_offset < source_slots {
                            self.load_at_offset(
                                ok_blk,
                                source_slot.source_ptr,
                                source_slot.offset + old_offset,
                            )
                        } else {
                            zero
                        };
                        let elem_val = self.load_at_offset(
                            ok_blk,
                            elem_source.source_ptr,
                            elem_source.offset + value_offset,
                        );
                        let old_or_zero = self.emit_with_result(
                            ok_blk,
                            Inst::Select {
                                ty: Ty::I64,
                                cond: before_append,
                                then_val: old_val,
                                else_val: zero,
                            },
                        );
                        let value = self.emit_with_result(
                            ok_blk,
                            Inst::Select {
                                ty: Ty::I64,
                                cond: at_append,
                                then_val: elem_val,
                                else_val: old_or_zero,
                            },
                        );
                        self.store_at_offset(ok_blk, result_ptr, result_offset, value);
                    }
                }

                self.store_compact_aggregate_result(ok_blk, rd, result_ptr, result_shape)?;
                return Ok(Some(ok_blk));
            }
        }

        if self.compact_state_slots.contains_key(&seq_reg) {
            return Err(TmirError::UnsupportedOpcode(format!(
                "Append: compact source r{seq_reg} is incompatible with append result: source_shape={source_shape:?}, elem_shape={elem_shape:?}, result_shape={compact_result_shape:?}"
            )));
        }

        self.compact_state_slots.remove(&rd);
        let const_total_slots = match self.aggregate_shapes.get(&seq_reg) {
            Some(super::AggregateShape::Sequence { extent, .. }) => extent
                .exact_count()
                .and_then(|len| len.checked_add(2))
                .and_then(|slots| i32::try_from(slots).ok()),
            _ => None,
        };
        let seq_ptr = self.load_reg_as_ptr(block_idx, seq_reg)?;
        let elem_val = self.load_reg(block_idx, elem_reg)?;
        let old_len = self.load_at_offset(block_idx, seq_ptr, 0);
        let one = self.emit_i64_const(block_idx, 1);
        let new_len = self.emit_with_result(
            block_idx,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: old_len,
                rhs: one,
            },
        );

        // Allocate: new_len + 1 slots
        let total_i32 = if let Some(total_slots) = const_total_slots {
            self.emit_with_result(
                block_idx,
                Inst::Const {
                    ty: Ty::I32,
                    value: Constant::Int(i128::from(total_slots)),
                },
            )
        } else {
            let total = self.emit_with_result(
                block_idx,
                Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::I64,
                    lhs: new_len,
                    rhs: one,
                },
            );
            self.emit_with_result(
                block_idx,
                Inst::Cast {
                    op: CastOp::Trunc,
                    src_ty: Ty::I64,
                    dst_ty: Ty::I32,
                    operand: total,
                },
            )
        };
        let new_ptr = self.emit_with_result(
            block_idx,
            Inst::Alloca {
                ty: Ty::I64,
                count: Some(total_i32),
                align: None,
            },
        );

        // Store new length
        self.store_at_offset(block_idx, new_ptr, 0, new_len);

        // Copy old elements: for i in 0..old_len, new[i+1] = old[i+1]
        let zero = self.emit_i64_const(block_idx, 0);
        let i_alloca = self.emit_with_result(
            block_idx,
            Inst::Alloca {
                ty: Ty::I64,
                count: None,
                align: None,
            },
        );
        self.emit(
            block_idx,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: i_alloca,
                value: zero,
                align: None,
                volatile: false,
            }),
        );

        let loop_hdr = self.new_aux_block("append_hdr");
        let loop_body = self.new_aux_block("append_body");
        let loop_done = self.new_aux_block("append_done");

        let hdr_id = self.block_id_of(loop_hdr);
        let body_id = self.block_id_of(loop_body);
        let done_id = self.block_id_of(loop_done);

        self.emit(
            block_idx,
            InstrNode::new(Inst::Br {
                target: hdr_id,
                args: vec![],
            }),
        );

        // Header
        let i_val = self.emit_with_result(
            loop_hdr,
            Inst::Load {
                ty: Ty::I64,
                ptr: i_alloca,
                align: None,
                volatile: false,
            },
        );
        let cmp = self.emit_with_result(
            loop_hdr,
            Inst::ICmp {
                op: ICmpOp::Slt,
                ty: Ty::I64,
                lhs: i_val,
                rhs: old_len,
            },
        );
        self.emit(
            loop_hdr,
            InstrNode::new(Inst::CondBr {
                cond: cmp,
                then_target: body_id,
                then_args: vec![],
                else_target: done_id,
                else_args: vec![],
            }),
        );

        // Body
        let i_val2 = self.emit_with_result(
            loop_body,
            Inst::Load {
                ty: Ty::I64,
                ptr: i_alloca,
                align: None,
                volatile: false,
            },
        );
        let slot = self.emit_with_result(
            loop_body,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: i_val2,
                rhs: one,
            },
        );
        let elem_i = self.load_at_dynamic_offset(loop_body, seq_ptr, slot);
        self.store_at_dynamic_offset(loop_body, new_ptr, slot, elem_i);
        let next_i = self.emit_with_result(
            loop_body,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: i_val2,
                rhs: one,
            },
        );
        self.emit(
            loop_body,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: i_alloca,
                value: next_i,
                align: None,
                volatile: false,
            }),
        );
        self.emit(
            loop_body,
            InstrNode::new(Inst::Br {
                target: hdr_id,
                args: vec![],
            }),
        );

        // Done: store the new element at slot[old_len+1] = slot[new_len]
        let append_slot = self.emit_with_result(
            loop_done,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: old_len,
                rhs: one,
            },
        );
        self.store_at_dynamic_offset(loop_done, new_ptr, append_slot, elem_val);
        self.store_reg_ptr(loop_done, rd, new_ptr)?;

        Ok(Some(loop_done))
    }

    /// Lower Seq(S) as a lazy sequence-set domain.
    ///
    /// Runtime storage mirrors `SUBSET S`: the destination register carries
    /// the base set pointer unchanged, while shape metadata records that
    /// membership must be checked as sequence-element membership in `S`.
    pub(super) fn lower_seq_set(
        &mut self,
        block_idx: usize,
        rd: u8,
        base_reg: u8,
    ) -> Result<(), TmirError> {
        let base_shape = self
            .aggregate_shapes
            .get(&base_reg)
            .cloned()
            .ok_or_else(|| {
                TmirError::UnsupportedOpcode(
                    "Seq: base must have a tracked set/domain shape".to_owned(),
                )
            })?;
        base_shape.validate_seq_base("Seq")?;

        let base_value = self.load_reg(block_idx, base_reg)?;
        self.store_reg_value(block_idx, rd, base_value)?;
        self.compact_state_slots.remove(&rd);
        self.aggregate_shapes.insert(
            rd,
            super::AggregateShape::SeqSet {
                base: Box::new(base_shape),
            },
        );
        self.const_set_sizes.remove(&rd);
        self.const_scalar_values.remove(&rd);
        Ok(())
    }
}
