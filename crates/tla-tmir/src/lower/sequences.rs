// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Sequence, tuple, record, and builtin lowering: SeqNew, TupleNew, TupleGet,
//! RecordNew, RecordGet, Cardinality, Len, Head, Tail, Append.

use crate::TmirError;
use tmir::inst::*;
use tmir::ty::Ty;
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

        for i in 0..count {
            let elem = self.load_reg(block_idx, start + i)?;
            self.store_at_offset(block_idx, agg_ptr, u32::from(i) + 1, elem);
        }

        self.store_reg_ptr(block_idx, rd, agg_ptr)
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
        self.store_reg_value(block_idx, rd, elem)
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
        _fields_start: u16,
        values_start: u8,
        count: u8,
    ) -> Result<(), TmirError> {
        let agg_ptr = self.alloc_aggregate(block_idx, u32::from(count));

        for i in 0..count {
            let val = self.load_reg(block_idx, values_start + i)?;
            self.store_at_offset(block_idx, agg_ptr, u32::from(i), val);
        }

        self.store_reg_ptr(block_idx, rd, agg_ptr)
    }

    /// Lower RecordGet { rd, rs, field_idx }.
    ///
    /// Loads the value at the field index offset in the record aggregate.
    pub(super) fn lower_record_get(
        &mut self,
        block_idx: usize,
        rd: u8,
        rs: u8,
        field_idx: u16,
    ) -> Result<(), TmirError> {
        let rec_ptr = self.load_reg_as_ptr(block_idx, rs)?;
        let val = self.load_at_offset(block_idx, rec_ptr, u32::from(field_idx));
        self.store_reg_value(block_idx, rd, val)
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
        let set_ptr = self.load_reg_as_ptr(block_idx, set_reg)?;
        let len = self.load_at_offset(block_idx, set_ptr, 0);
        self.store_reg_value(block_idx, rd, len)
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
        let seq_ptr = self.load_reg_as_ptr(block_idx, seq_reg)?;
        let len = self.load_at_offset(block_idx, seq_ptr, 0);
        self.store_reg_value(block_idx, rd, len)
    }

    /// Lower Head(seq): returns slot[1] of the sequence aggregate.
    pub(super) fn lower_seq_head(
        &mut self,
        block_idx: usize,
        rd: u8,
        seq_reg: u8,
    ) -> Result<(), TmirError> {
        let seq_ptr = self.load_reg_as_ptr(block_idx, seq_reg)?;
        let head = self.load_at_offset(block_idx, seq_ptr, 1);
        self.store_reg_value(block_idx, rd, head)
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
        let seq_ptr = self.load_reg_as_ptr(block_idx, seq_reg)?;
        let old_len = self.load_at_offset(block_idx, seq_ptr, 0);
        let one = self.emit_i64_const(block_idx, 1);
        let new_len = self.emit_with_result(block_idx, Inst::BinOp {
            op: BinOp::Sub, ty: Ty::I64, lhs: old_len, rhs: one,
        });

        // Allocate new aggregate: new_len + 1 slots
        let total = self.emit_with_result(block_idx, Inst::BinOp {
            op: BinOp::Add, ty: Ty::I64, lhs: new_len, rhs: one,
        });
        let total_i32 = self.emit_with_result(block_idx, Inst::Cast {
            op: CastOp::Trunc, src_ty: Ty::I64, dst_ty: Ty::I32, operand: total,
        });
        let new_ptr = self.emit_with_result(block_idx, Inst::Alloca {
            ty: Ty::I64, count: Some(total_i32),
        });

        // Store new length
        self.store_at_offset(block_idx, new_ptr, 0, new_len);

        // Copy loop: for i in 0..new_len, new[i+1] = old[i+2]
        let zero = self.emit_i64_const(block_idx, 0);
        let two = self.emit_i64_const(block_idx, 2);
        let i_alloca = self.emit_with_result(block_idx, Inst::Alloca { ty: Ty::I64, count: None });
        self.emit(block_idx, InstrNode::new(Inst::Store { ty: Ty::I64, ptr: i_alloca, value: zero }));

        let loop_hdr = self.new_aux_block("tail_hdr");
        let loop_body = self.new_aux_block("tail_body");
        let loop_done = self.new_aux_block("tail_done");

        let hdr_id = self.block_id_of(loop_hdr);
        let body_id = self.block_id_of(loop_body);
        let done_id = self.block_id_of(loop_done);

        self.emit(block_idx, InstrNode::new(Inst::Br { target: hdr_id, args: vec![] }));

        // Header
        let i_val = self.emit_with_result(loop_hdr, Inst::Load { ty: Ty::I64, ptr: i_alloca });
        let cmp = self.emit_with_result(loop_hdr, Inst::ICmp {
            op: ICmpOp::Slt, ty: Ty::I64, lhs: i_val, rhs: new_len,
        });
        self.emit(loop_hdr, InstrNode::new(Inst::CondBr {
            cond: cmp,
            then_target: body_id, then_args: vec![],
            else_target: done_id, else_args: vec![],
        }));

        // Body
        let i_val2 = self.emit_with_result(loop_body, Inst::Load { ty: Ty::I64, ptr: i_alloca });
        let src_slot = self.emit_with_result(loop_body, Inst::BinOp {
            op: BinOp::Add, ty: Ty::I64, lhs: i_val2, rhs: two,
        });
        let elem = self.load_at_dynamic_offset(loop_body, seq_ptr, src_slot);
        let dst_slot = self.emit_with_result(loop_body, Inst::BinOp {
            op: BinOp::Add, ty: Ty::I64, lhs: i_val2, rhs: one,
        });
        self.store_at_dynamic_offset(loop_body, new_ptr, dst_slot, elem);
        let next_i = self.emit_with_result(loop_body, Inst::BinOp {
            op: BinOp::Add, ty: Ty::I64, lhs: i_val2, rhs: one,
        });
        self.emit(loop_body, InstrNode::new(Inst::Store { ty: Ty::I64, ptr: i_alloca, value: next_i }));
        self.emit(loop_body, InstrNode::new(Inst::Br { target: hdr_id, args: vec![] }));

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
    ) -> Result<Option<usize>, TmirError> {
        let seq_ptr = self.load_reg_as_ptr(block_idx, seq_reg)?;
        let elem_val = self.load_reg(block_idx, elem_reg)?;
        let old_len = self.load_at_offset(block_idx, seq_ptr, 0);
        let one = self.emit_i64_const(block_idx, 1);
        let new_len = self.emit_with_result(block_idx, Inst::BinOp {
            op: BinOp::Add, ty: Ty::I64, lhs: old_len, rhs: one,
        });

        // Allocate: new_len + 1 slots
        let total = self.emit_with_result(block_idx, Inst::BinOp {
            op: BinOp::Add, ty: Ty::I64, lhs: new_len, rhs: one,
        });
        let total_i32 = self.emit_with_result(block_idx, Inst::Cast {
            op: CastOp::Trunc, src_ty: Ty::I64, dst_ty: Ty::I32, operand: total,
        });
        let new_ptr = self.emit_with_result(block_idx, Inst::Alloca {
            ty: Ty::I64, count: Some(total_i32),
        });

        // Store new length
        self.store_at_offset(block_idx, new_ptr, 0, new_len);

        // Copy old elements: for i in 0..old_len, new[i+1] = old[i+1]
        let zero = self.emit_i64_const(block_idx, 0);
        let i_alloca = self.emit_with_result(block_idx, Inst::Alloca { ty: Ty::I64, count: None });
        self.emit(block_idx, InstrNode::new(Inst::Store { ty: Ty::I64, ptr: i_alloca, value: zero }));

        let loop_hdr = self.new_aux_block("append_hdr");
        let loop_body = self.new_aux_block("append_body");
        let loop_done = self.new_aux_block("append_done");

        let hdr_id = self.block_id_of(loop_hdr);
        let body_id = self.block_id_of(loop_body);
        let done_id = self.block_id_of(loop_done);

        self.emit(block_idx, InstrNode::new(Inst::Br { target: hdr_id, args: vec![] }));

        // Header
        let i_val = self.emit_with_result(loop_hdr, Inst::Load { ty: Ty::I64, ptr: i_alloca });
        let cmp = self.emit_with_result(loop_hdr, Inst::ICmp {
            op: ICmpOp::Slt, ty: Ty::I64, lhs: i_val, rhs: old_len,
        });
        self.emit(loop_hdr, InstrNode::new(Inst::CondBr {
            cond: cmp,
            then_target: body_id, then_args: vec![],
            else_target: done_id, else_args: vec![],
        }));

        // Body
        let i_val2 = self.emit_with_result(loop_body, Inst::Load { ty: Ty::I64, ptr: i_alloca });
        let slot = self.emit_with_result(loop_body, Inst::BinOp {
            op: BinOp::Add, ty: Ty::I64, lhs: i_val2, rhs: one,
        });
        let elem_i = self.load_at_dynamic_offset(loop_body, seq_ptr, slot);
        self.store_at_dynamic_offset(loop_body, new_ptr, slot, elem_i);
        let next_i = self.emit_with_result(loop_body, Inst::BinOp {
            op: BinOp::Add, ty: Ty::I64, lhs: i_val2, rhs: one,
        });
        self.emit(loop_body, InstrNode::new(Inst::Store { ty: Ty::I64, ptr: i_alloca, value: next_i }));
        self.emit(loop_body, InstrNode::new(Inst::Br { target: hdr_id, args: vec![] }));

        // Done: store the new element at slot[old_len+1] = slot[new_len]
        let append_slot = self.emit_with_result(loop_done, Inst::BinOp {
            op: BinOp::Add, ty: Ty::I64, lhs: old_len, rhs: one,
        });
        self.store_at_dynamic_offset(loop_done, new_ptr, append_slot, elem_val);
        self.store_reg_ptr(loop_done, rd, new_ptr)?;

        Ok(Some(loop_done))
    }
}
