// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Set operation lowering: SetEnum, SetIn, SetUnion, SetIntersect, SetDiff,
//! SubsetEq, Range.

use crate::TmirError;
use tmir::inst::*;
use tmir::ty::Ty;
use tmir::InstrNode;

use super::Ctx;

impl<'cp> Ctx<'cp> {
    /// Lower SetEnum { rd, start, count }: build a set from consecutive registers.
    ///
    /// Layout: alloca[0] = count, alloca[1..=count] = elements from registers.
    pub(super) fn lower_set_enum(
        &mut self,
        block_idx: usize,
        rd: u8,
        start: u8,
        count: u8,
    ) -> Result<(), TmirError> {
        let total_slots = u32::from(count) + 1; // length header + elements
        let agg_ptr = self.alloc_aggregate(block_idx, total_slots);

        // Store length
        let len_val = self.emit_i64_const(block_idx, i64::from(count));
        self.store_at_offset(block_idx, agg_ptr, 0, len_val);

        // Store each element
        for i in 0..count {
            let elem = self.load_reg(block_idx, start + i)?;
            self.store_at_offset(block_idx, agg_ptr, u32::from(i) + 1, elem);
        }

        self.store_reg_ptr(block_idx, rd, agg_ptr)
    }

    /// Lower SetIn { rd, elem, set }: set membership test.
    ///
    /// Emits a linear scan loop: for each element in the set, compare with elem.
    /// Result is 1 (found) or 0 (not found).
    ///
    /// CFG:
    ///   entry -> header
    ///   header -> body (if i < len) | not_found (if i >= len)
    ///   body -> found (if equal) | inc (if not equal)
    ///   inc -> header
    ///   found -> merge (rd = 1)
    ///   not_found -> merge (rd = 0)
    pub(super) fn lower_set_in(
        &mut self,
        block_idx: usize,
        rd: u8,
        elem_reg: u8,
        set_reg: u8,
    ) -> Result<Option<usize>, TmirError> {
        let elem_val = self.load_reg(block_idx, elem_reg)?;
        let set_ptr = self.load_reg_as_ptr(block_idx, set_reg)?;
        let set_len = self.load_at_offset(block_idx, set_ptr, 0);

        let zero = self.emit_i64_const(block_idx, 0);
        let one = self.emit_i64_const(block_idx, 1);

        let idx_alloca = self.emit_with_result(
            block_idx,
            Inst::Alloca { ty: Ty::I64, count: None, align: None },
        );
        self.emit(block_idx, InstrNode::new(Inst::Store { ty: Ty::I64, ptr: idx_alloca, value: zero, align: None, volatile: false }));

        let loop_header = self.new_aux_block("setin_header");
        let loop_body = self.new_aux_block("setin_body");
        let loop_inc = self.new_aux_block("setin_inc");
        let found_blk = self.new_aux_block("setin_found");
        let not_found_blk = self.new_aux_block("setin_not_found");
        let merge_blk = self.new_aux_block("setin_merge");

        let header_id = self.block_id_of(loop_header);
        let body_id = self.block_id_of(loop_body);
        let inc_id = self.block_id_of(loop_inc);
        let found_id = self.block_id_of(found_blk);
        let not_found_id = self.block_id_of(not_found_blk);
        let merge_id = self.block_id_of(merge_blk);

        self.emit(block_idx, InstrNode::new(Inst::Br { target: header_id, args: vec![] }));

        // Header: i < len?
        let cur_idx = self.emit_with_result(loop_header, Inst::Load { ty: Ty::I64, ptr: idx_alloca, align: None, volatile: false });
        let cmp = self.emit_with_result(loop_header, Inst::ICmp {
            op: ICmpOp::Slt, ty: Ty::I64, lhs: cur_idx, rhs: set_len,
        });
        self.emit(loop_header, InstrNode::new(Inst::CondBr {
            cond: cmp,
            then_target: body_id, then_args: vec![],
            else_target: not_found_id, else_args: vec![],
        }));

        // Body: load set[i+1], compare with elem
        let cur_idx2 = self.emit_with_result(loop_body, Inst::Load { ty: Ty::I64, ptr: idx_alloca, align: None, volatile: false });
        let slot_idx = self.emit_with_result(loop_body, Inst::BinOp {
            op: BinOp::Add, ty: Ty::I64, lhs: cur_idx2, rhs: one,
        });
        let set_elem = self.load_at_dynamic_offset(loop_body, set_ptr, slot_idx);
        let eq = self.emit_with_result(loop_body, Inst::ICmp {
            op: ICmpOp::Eq, ty: Ty::I64, lhs: set_elem, rhs: elem_val,
        });
        self.emit(loop_body, InstrNode::new(Inst::CondBr {
            cond: eq,
            then_target: found_id, then_args: vec![],
            else_target: inc_id, else_args: vec![],
        }));

        // Increment: i++, goto header
        let cur_idx3 = self.emit_with_result(loop_inc, Inst::Load { ty: Ty::I64, ptr: idx_alloca, align: None, volatile: false });
        let next_idx = self.emit_with_result(loop_inc, Inst::BinOp {
            op: BinOp::Add, ty: Ty::I64, lhs: cur_idx3, rhs: one,
        });
        self.emit(loop_inc, InstrNode::new(Inst::Store { ty: Ty::I64, ptr: idx_alloca, value: next_idx, align: None, volatile: false }));
        self.emit(loop_inc, InstrNode::new(Inst::Br { target: header_id, args: vec![] }));

        // Found: rd = 1
        self.store_reg_imm(found_blk, rd, 1)?;
        self.emit(found_blk, InstrNode::new(Inst::Br { target: merge_id, args: vec![] }));

        // Not found: rd = 0
        self.store_reg_imm(not_found_blk, rd, 0)?;
        self.emit(not_found_blk, InstrNode::new(Inst::Br { target: merge_id, args: vec![] }));

        Ok(Some(merge_blk))
    }

    /// Lower SetUnion { rd, r1, r2 }: union of two sets.
    ///
    /// Creates a new set containing all elements from both sets.
    pub(super) fn lower_set_union(
        &mut self,
        block_idx: usize,
        rd: u8,
        r1: u8,
        r2: u8,
    ) -> Result<Option<usize>, TmirError> {
        // Load both set pointers and lengths
        let set1_ptr = self.load_reg_as_ptr(block_idx, r1)?;
        let set2_ptr = self.load_reg_as_ptr(block_idx, r2)?;
        let len1 = self.load_at_offset(block_idx, set1_ptr, 0);
        let len2 = self.load_at_offset(block_idx, set2_ptr, 0);

        // Max result size = len1 + len2 + 1 (header)
        let total_elem = self.emit_with_result(block_idx, Inst::BinOp {
            op: BinOp::Add, ty: Ty::I64, lhs: len1, rhs: len2,
        });
        let one_64 = self.emit_i64_const(block_idx, 1);
        let total_slots = self.emit_with_result(block_idx, Inst::BinOp {
            op: BinOp::Add, ty: Ty::I64, lhs: total_elem, rhs: one_64,
        });
        let total_i32 = self.emit_with_result(block_idx, Inst::Cast {
            op: CastOp::Trunc, src_ty: Ty::I64, dst_ty: Ty::I32, operand: total_slots,
        });
        let result_ptr = self.emit_with_result(block_idx, Inst::Alloca {
            ty: Ty::I64, count: Some(total_i32), align: None,
        });

        // Copy all elements from set1 (slots 1..=len1)
        // For the tMIR-level representation, we use a simple loop to copy elements.
        // Store initial result length as len1 (we'll copy set1 completely first).
        let zero = self.emit_i64_const(block_idx, 0);
        let one = self.emit_i64_const(block_idx, 1);

        // Alloca for write cursor (starts at 1)
        let cursor_alloca = self.emit_with_result(block_idx, Inst::Alloca { ty: Ty::I64, count: None, align: None });
        self.emit(block_idx, InstrNode::new(Inst::Store { ty: Ty::I64, ptr: cursor_alloca, value: one, align: None, volatile: false }));

        // Copy loop for set1
        let copy1_header = self.new_aux_block("union_copy1_hdr");
        let copy1_body = self.new_aux_block("union_copy1_body");
        let copy1_done = self.new_aux_block("union_copy1_done");

        let hdr1_id = self.block_id_of(copy1_header);
        let body1_id = self.block_id_of(copy1_body);
        let done1_id = self.block_id_of(copy1_done);

        // Alloca for loop index
        let i_alloca = self.emit_with_result(block_idx, Inst::Alloca { ty: Ty::I64, count: None, align: None });
        self.emit(block_idx, InstrNode::new(Inst::Store { ty: Ty::I64, ptr: i_alloca, value: zero, align: None, volatile: false }));
        self.emit(block_idx, InstrNode::new(Inst::Br { target: hdr1_id, args: vec![] }));

        // Header: i < len1?
        let i_val = self.emit_with_result(copy1_header, Inst::Load { ty: Ty::I64, ptr: i_alloca, align: None, volatile: false });
        let cmp1 = self.emit_with_result(copy1_header, Inst::ICmp {
            op: ICmpOp::Slt, ty: Ty::I64, lhs: i_val, rhs: len1,
        });
        self.emit(copy1_header, InstrNode::new(Inst::CondBr {
            cond: cmp1,
            then_target: body1_id, then_args: vec![],
            else_target: done1_id, else_args: vec![],
        }));

        // Body: copy element
        let i_val2 = self.emit_with_result(copy1_body, Inst::Load { ty: Ty::I64, ptr: i_alloca, align: None, volatile: false });
        let src_slot = self.emit_with_result(copy1_body, Inst::BinOp {
            op: BinOp::Add, ty: Ty::I64, lhs: i_val2, rhs: one,
        });
        let elem = self.load_at_dynamic_offset(copy1_body, set1_ptr, src_slot);
        let cursor = self.emit_with_result(copy1_body, Inst::Load { ty: Ty::I64, ptr: cursor_alloca, align: None, volatile: false });
        self.store_at_dynamic_offset(copy1_body, result_ptr, cursor, elem);
        // Increment
        let next_i = self.emit_with_result(copy1_body, Inst::BinOp {
            op: BinOp::Add, ty: Ty::I64, lhs: i_val2, rhs: one,
        });
        self.emit(copy1_body, InstrNode::new(Inst::Store { ty: Ty::I64, ptr: i_alloca, value: next_i, align: None, volatile: false }));
        let next_cursor = self.emit_with_result(copy1_body, Inst::BinOp {
            op: BinOp::Add, ty: Ty::I64, lhs: cursor, rhs: one,
        });
        self.emit(copy1_body, InstrNode::new(Inst::Store { ty: Ty::I64, ptr: cursor_alloca, value: next_cursor, align: None, volatile: false }));
        self.emit(copy1_body, InstrNode::new(Inst::Br { target: hdr1_id, args: vec![] }));

        // After copying set1, copy set2 elements
        let copy2_header = self.new_aux_block("union_copy2_hdr");
        let copy2_body = self.new_aux_block("union_copy2_body");
        let finalize = self.new_aux_block("union_finalize");

        let hdr2_id = self.block_id_of(copy2_header);
        let body2_id = self.block_id_of(copy2_body);
        let finalize_id = self.block_id_of(finalize);

        // Reset loop index
        self.emit(copy1_done, InstrNode::new(Inst::Store { ty: Ty::I64, ptr: i_alloca, value: zero, align: None, volatile: false }));
        self.emit(copy1_done, InstrNode::new(Inst::Br { target: hdr2_id, args: vec![] }));

        // Header: i < len2?
        let i_val3 = self.emit_with_result(copy2_header, Inst::Load { ty: Ty::I64, ptr: i_alloca, align: None, volatile: false });
        let cmp2 = self.emit_with_result(copy2_header, Inst::ICmp {
            op: ICmpOp::Slt, ty: Ty::I64, lhs: i_val3, rhs: len2,
        });
        self.emit(copy2_header, InstrNode::new(Inst::CondBr {
            cond: cmp2,
            then_target: body2_id, then_args: vec![],
            else_target: finalize_id, else_args: vec![],
        }));

        // Body: copy element
        let i_val4 = self.emit_with_result(copy2_body, Inst::Load { ty: Ty::I64, ptr: i_alloca, align: None, volatile: false });
        let src_slot2 = self.emit_with_result(copy2_body, Inst::BinOp {
            op: BinOp::Add, ty: Ty::I64, lhs: i_val4, rhs: one,
        });
        let elem2 = self.load_at_dynamic_offset(copy2_body, set2_ptr, src_slot2);
        let cursor2 = self.emit_with_result(copy2_body, Inst::Load { ty: Ty::I64, ptr: cursor_alloca, align: None, volatile: false });
        self.store_at_dynamic_offset(copy2_body, result_ptr, cursor2, elem2);
        let next_i2 = self.emit_with_result(copy2_body, Inst::BinOp {
            op: BinOp::Add, ty: Ty::I64, lhs: i_val4, rhs: one,
        });
        self.emit(copy2_body, InstrNode::new(Inst::Store { ty: Ty::I64, ptr: i_alloca, value: next_i2, align: None, volatile: false }));
        let next_cursor2 = self.emit_with_result(copy2_body, Inst::BinOp {
            op: BinOp::Add, ty: Ty::I64, lhs: cursor2, rhs: one,
        });
        self.emit(copy2_body, InstrNode::new(Inst::Store { ty: Ty::I64, ptr: cursor_alloca, value: next_cursor2, align: None, volatile: false }));
        self.emit(copy2_body, InstrNode::new(Inst::Br { target: hdr2_id, args: vec![] }));

        // Finalize: store final length = cursor - 1
        let final_cursor = self.emit_with_result(finalize, Inst::Load { ty: Ty::I64, ptr: cursor_alloca, align: None, volatile: false });
        let final_len = self.emit_with_result(finalize, Inst::BinOp {
            op: BinOp::Sub, ty: Ty::I64, lhs: final_cursor, rhs: one,
        });
        self.store_at_offset(finalize, result_ptr, 0, final_len);
        self.store_reg_ptr(finalize, rd, result_ptr)?;

        Ok(Some(finalize))
    }

    /// Lower SetIntersect { rd, r1, r2 }: intersection of two sets.
    ///
    /// Creates a new set containing elements present in both sets.
    /// Uses nested loops: for each element in set1, scan set2 for a match.
    pub(super) fn lower_set_intersect(
        &mut self,
        block_idx: usize,
        rd: u8,
        r1: u8,
        r2: u8,
    ) -> Result<Option<usize>, TmirError> {
        let set1_ptr = self.load_reg_as_ptr(block_idx, r1)?;
        let set2_ptr = self.load_reg_as_ptr(block_idx, r2)?;
        let len1 = self.load_at_offset(block_idx, set1_ptr, 0);
        let _len2 = self.load_at_offset(block_idx, set2_ptr, 0);

        // Allocate result set with max size = len1 + 1
        let one_64 = self.emit_i64_const(block_idx, 1);
        let max_slots = self.emit_with_result(block_idx, Inst::BinOp {
            op: BinOp::Add, ty: Ty::I64, lhs: len1, rhs: one_64,
        });
        let max_i32 = self.emit_with_result(block_idx, Inst::Cast {
            op: CastOp::Trunc, src_ty: Ty::I64, dst_ty: Ty::I32, operand: max_slots,
        });
        let result_ptr = self.emit_with_result(block_idx, Inst::Alloca {
            ty: Ty::I64, count: Some(max_i32), align: None,
        });

        let zero = self.emit_i64_const(block_idx, 0);
        let one = self.emit_i64_const(block_idx, 1);

        // Write cursor for result
        let cursor_alloca = self.emit_with_result(block_idx, Inst::Alloca { ty: Ty::I64, count: None, align: None });
        self.emit(block_idx, InstrNode::new(Inst::Store { ty: Ty::I64, ptr: cursor_alloca, value: one, align: None, volatile: false }));

        // Outer loop index
        let i_alloca = self.emit_with_result(block_idx, Inst::Alloca { ty: Ty::I64, count: None, align: None });
        self.emit(block_idx, InstrNode::new(Inst::Store { ty: Ty::I64, ptr: i_alloca, value: zero, align: None, volatile: false }));

        let outer_hdr = self.new_aux_block("isect_outer_hdr");
        let outer_body = self.new_aux_block("isect_outer_body");
        let inner_hdr = self.new_aux_block("isect_inner_hdr");
        let inner_body = self.new_aux_block("isect_inner_body");
        let inner_inc = self.new_aux_block("isect_inner_inc");
        let found_blk = self.new_aux_block("isect_found");
        let outer_inc = self.new_aux_block("isect_outer_inc");
        let finalize = self.new_aux_block("isect_finalize");

        let outer_hdr_id = self.block_id_of(outer_hdr);
        let outer_body_id = self.block_id_of(outer_body);
        let inner_hdr_id = self.block_id_of(inner_hdr);
        let inner_body_id = self.block_id_of(inner_body);
        let inner_inc_id = self.block_id_of(inner_inc);
        let found_blk_id = self.block_id_of(found_blk);
        let outer_inc_id = self.block_id_of(outer_inc);
        let finalize_id = self.block_id_of(finalize);

        self.emit(block_idx, InstrNode::new(Inst::Br { target: outer_hdr_id, args: vec![] }));

        // Outer header: i < len1?
        let i_val = self.emit_with_result(outer_hdr, Inst::Load { ty: Ty::I64, ptr: i_alloca, align: None, volatile: false });
        let cmp_outer = self.emit_with_result(outer_hdr, Inst::ICmp {
            op: ICmpOp::Slt, ty: Ty::I64, lhs: i_val, rhs: len1,
        });
        self.emit(outer_hdr, InstrNode::new(Inst::CondBr {
            cond: cmp_outer,
            then_target: outer_body_id, then_args: vec![],
            else_target: finalize_id, else_args: vec![],
        }));

        // Outer body: load element from set1
        let i_val2 = self.emit_with_result(outer_body, Inst::Load { ty: Ty::I64, ptr: i_alloca, align: None, volatile: false });
        let slot = self.emit_with_result(outer_body, Inst::BinOp {
            op: BinOp::Add, ty: Ty::I64, lhs: i_val2, rhs: one,
        });
        let elem1 = self.load_at_dynamic_offset(outer_body, set1_ptr, slot);

        // Inner loop: search set2 for elem1
        let j_alloca = self.emit_with_result(outer_body, Inst::Alloca { ty: Ty::I64, count: None, align: None });
        self.emit(outer_body, InstrNode::new(Inst::Store { ty: Ty::I64, ptr: j_alloca, value: zero, align: None, volatile: false }));
        self.emit(outer_body, InstrNode::new(Inst::Br { target: inner_hdr_id, args: vec![] }));

        // Inner header: j < len2?
        let j_val = self.emit_with_result(inner_hdr, Inst::Load { ty: Ty::I64, ptr: j_alloca, align: None, volatile: false });
        let cmp_inner = self.emit_with_result(inner_hdr, Inst::ICmp {
            op: ICmpOp::Slt, ty: Ty::I64, lhs: j_val, rhs: _len2,
        });
        self.emit(inner_hdr, InstrNode::new(Inst::CondBr {
            cond: cmp_inner,
            then_target: inner_body_id, then_args: vec![],
            else_target: outer_inc_id, else_args: vec![], // not found
        }));

        // Inner body: compare
        let j_val2 = self.emit_with_result(inner_body, Inst::Load { ty: Ty::I64, ptr: j_alloca, align: None, volatile: false });
        let slot2 = self.emit_with_result(inner_body, Inst::BinOp {
            op: BinOp::Add, ty: Ty::I64, lhs: j_val2, rhs: one,
        });
        let elem2 = self.load_at_dynamic_offset(inner_body, set2_ptr, slot2);
        let eq = self.emit_with_result(inner_body, Inst::ICmp {
            op: ICmpOp::Eq, ty: Ty::I64, lhs: elem1, rhs: elem2,
        });
        self.emit(inner_body, InstrNode::new(Inst::CondBr {
            cond: eq,
            then_target: found_blk_id, then_args: vec![],
            else_target: inner_inc_id, else_args: vec![],
        }));

        // Inner increment
        let j_val3 = self.emit_with_result(inner_inc, Inst::Load { ty: Ty::I64, ptr: j_alloca, align: None, volatile: false });
        let next_j = self.emit_with_result(inner_inc, Inst::BinOp {
            op: BinOp::Add, ty: Ty::I64, lhs: j_val3, rhs: one,
        });
        self.emit(inner_inc, InstrNode::new(Inst::Store { ty: Ty::I64, ptr: j_alloca, value: next_j, align: None, volatile: false }));
        self.emit(inner_inc, InstrNode::new(Inst::Br { target: inner_hdr_id, args: vec![] }));

        // Found: add elem1 to result
        let cursor = self.emit_with_result(found_blk, Inst::Load { ty: Ty::I64, ptr: cursor_alloca, align: None, volatile: false });
        self.store_at_dynamic_offset(found_blk, result_ptr, cursor, elem1);
        let next_cursor = self.emit_with_result(found_blk, Inst::BinOp {
            op: BinOp::Add, ty: Ty::I64, lhs: cursor, rhs: one,
        });
        self.emit(found_blk, InstrNode::new(Inst::Store { ty: Ty::I64, ptr: cursor_alloca, value: next_cursor, align: None, volatile: false }));
        self.emit(found_blk, InstrNode::new(Inst::Br { target: outer_inc_id, args: vec![] }));

        // Outer increment
        let i_val3 = self.emit_with_result(outer_inc, Inst::Load { ty: Ty::I64, ptr: i_alloca, align: None, volatile: false });
        let next_i = self.emit_with_result(outer_inc, Inst::BinOp {
            op: BinOp::Add, ty: Ty::I64, lhs: i_val3, rhs: one,
        });
        self.emit(outer_inc, InstrNode::new(Inst::Store { ty: Ty::I64, ptr: i_alloca, value: next_i, align: None, volatile: false }));
        self.emit(outer_inc, InstrNode::new(Inst::Br { target: outer_hdr_id, args: vec![] }));

        // Finalize
        let final_cursor = self.emit_with_result(finalize, Inst::Load { ty: Ty::I64, ptr: cursor_alloca, align: None, volatile: false });
        let final_len = self.emit_with_result(finalize, Inst::BinOp {
            op: BinOp::Sub, ty: Ty::I64, lhs: final_cursor, rhs: one,
        });
        self.store_at_offset(finalize, result_ptr, 0, final_len);
        self.store_reg_ptr(finalize, rd, result_ptr)?;

        Ok(Some(finalize))
    }

    /// Lower SetDiff { rd, r1, r2 }: set difference (r1 \ r2).
    ///
    /// Creates a new set containing elements in r1 that are NOT in r2.
    pub(super) fn lower_set_diff(
        &mut self,
        block_idx: usize,
        rd: u8,
        r1: u8,
        r2: u8,
    ) -> Result<Option<usize>, TmirError> {
        let set1_ptr = self.load_reg_as_ptr(block_idx, r1)?;
        let set2_ptr = self.load_reg_as_ptr(block_idx, r2)?;
        let len1 = self.load_at_offset(block_idx, set1_ptr, 0);
        let len2 = self.load_at_offset(block_idx, set2_ptr, 0);

        // Allocate result set with max size = len1 + 1
        let one_64 = self.emit_i64_const(block_idx, 1);
        let max_slots = self.emit_with_result(block_idx, Inst::BinOp {
            op: BinOp::Add, ty: Ty::I64, lhs: len1, rhs: one_64,
        });
        let max_i32 = self.emit_with_result(block_idx, Inst::Cast {
            op: CastOp::Trunc, src_ty: Ty::I64, dst_ty: Ty::I32, operand: max_slots,
        });
        let result_ptr = self.emit_with_result(block_idx, Inst::Alloca {
            ty: Ty::I64, count: Some(max_i32), align: None,
        });

        let zero = self.emit_i64_const(block_idx, 0);
        let one = self.emit_i64_const(block_idx, 1);

        let cursor_alloca = self.emit_with_result(block_idx, Inst::Alloca { ty: Ty::I64, count: None, align: None });
        self.emit(block_idx, InstrNode::new(Inst::Store { ty: Ty::I64, ptr: cursor_alloca, value: one, align: None, volatile: false }));

        let i_alloca = self.emit_with_result(block_idx, Inst::Alloca { ty: Ty::I64, count: None, align: None });
        self.emit(block_idx, InstrNode::new(Inst::Store { ty: Ty::I64, ptr: i_alloca, value: zero, align: None, volatile: false }));

        let outer_hdr = self.new_aux_block("sdiff_outer_hdr");
        let outer_body = self.new_aux_block("sdiff_outer_body");
        let inner_hdr = self.new_aux_block("sdiff_inner_hdr");
        let inner_body = self.new_aux_block("sdiff_inner_body");
        let inner_inc = self.new_aux_block("sdiff_inner_inc");
        let not_found = self.new_aux_block("sdiff_not_found");
        let outer_inc = self.new_aux_block("sdiff_outer_inc");
        let finalize = self.new_aux_block("sdiff_finalize");

        let outer_hdr_id = self.block_id_of(outer_hdr);
        let outer_body_id = self.block_id_of(outer_body);
        let inner_hdr_id = self.block_id_of(inner_hdr);
        let inner_body_id = self.block_id_of(inner_body);
        let inner_inc_id = self.block_id_of(inner_inc);
        let not_found_id = self.block_id_of(not_found);
        let outer_inc_id = self.block_id_of(outer_inc);
        let finalize_id = self.block_id_of(finalize);

        self.emit(block_idx, InstrNode::new(Inst::Br { target: outer_hdr_id, args: vec![] }));

        // Outer header
        let i_val = self.emit_with_result(outer_hdr, Inst::Load { ty: Ty::I64, ptr: i_alloca, align: None, volatile: false });
        let cmp_outer = self.emit_with_result(outer_hdr, Inst::ICmp {
            op: ICmpOp::Slt, ty: Ty::I64, lhs: i_val, rhs: len1,
        });
        self.emit(outer_hdr, InstrNode::new(Inst::CondBr {
            cond: cmp_outer,
            then_target: outer_body_id, then_args: vec![],
            else_target: finalize_id, else_args: vec![],
        }));

        // Outer body: load elem from set1
        let i_val2 = self.emit_with_result(outer_body, Inst::Load { ty: Ty::I64, ptr: i_alloca, align: None, volatile: false });
        let slot = self.emit_with_result(outer_body, Inst::BinOp {
            op: BinOp::Add, ty: Ty::I64, lhs: i_val2, rhs: one,
        });
        let elem1 = self.load_at_dynamic_offset(outer_body, set1_ptr, slot);

        // Inner loop: search set2 for elem1
        let j_alloca = self.emit_with_result(outer_body, Inst::Alloca { ty: Ty::I64, count: None, align: None });
        self.emit(outer_body, InstrNode::new(Inst::Store { ty: Ty::I64, ptr: j_alloca, value: zero, align: None, volatile: false }));
        self.emit(outer_body, InstrNode::new(Inst::Br { target: inner_hdr_id, args: vec![] }));

        // Inner header
        let j_val = self.emit_with_result(inner_hdr, Inst::Load { ty: Ty::I64, ptr: j_alloca, align: None, volatile: false });
        let cmp_inner = self.emit_with_result(inner_hdr, Inst::ICmp {
            op: ICmpOp::Slt, ty: Ty::I64, lhs: j_val, rhs: len2,
        });
        self.emit(inner_hdr, InstrNode::new(Inst::CondBr {
            cond: cmp_inner,
            then_target: inner_body_id, then_args: vec![],
            else_target: not_found_id, else_args: vec![], // not found = include in result
        }));

        // Inner body
        let j_val2 = self.emit_with_result(inner_body, Inst::Load { ty: Ty::I64, ptr: j_alloca, align: None, volatile: false });
        let slot2 = self.emit_with_result(inner_body, Inst::BinOp {
            op: BinOp::Add, ty: Ty::I64, lhs: j_val2, rhs: one,
        });
        let elem2 = self.load_at_dynamic_offset(inner_body, set2_ptr, slot2);
        let eq = self.emit_with_result(inner_body, Inst::ICmp {
            op: ICmpOp::Eq, ty: Ty::I64, lhs: elem1, rhs: elem2,
        });
        self.emit(inner_body, InstrNode::new(Inst::CondBr {
            cond: eq,
            then_target: outer_inc_id, then_args: vec![], // found in set2 => skip
            else_target: inner_inc_id, else_args: vec![],
        }));

        // Inner increment
        let j_val3 = self.emit_with_result(inner_inc, Inst::Load { ty: Ty::I64, ptr: j_alloca, align: None, volatile: false });
        let next_j = self.emit_with_result(inner_inc, Inst::BinOp {
            op: BinOp::Add, ty: Ty::I64, lhs: j_val3, rhs: one,
        });
        self.emit(inner_inc, InstrNode::new(Inst::Store { ty: Ty::I64, ptr: j_alloca, value: next_j, align: None, volatile: false }));
        self.emit(inner_inc, InstrNode::new(Inst::Br { target: inner_hdr_id, args: vec![] }));

        // Not found in set2: add to result
        let cursor = self.emit_with_result(not_found, Inst::Load { ty: Ty::I64, ptr: cursor_alloca, align: None, volatile: false });
        self.store_at_dynamic_offset(not_found, result_ptr, cursor, elem1);
        let next_cursor = self.emit_with_result(not_found, Inst::BinOp {
            op: BinOp::Add, ty: Ty::I64, lhs: cursor, rhs: one,
        });
        self.emit(not_found, InstrNode::new(Inst::Store { ty: Ty::I64, ptr: cursor_alloca, value: next_cursor, align: None, volatile: false }));
        self.emit(not_found, InstrNode::new(Inst::Br { target: outer_inc_id, args: vec![] }));

        // Outer increment
        let i_val3 = self.emit_with_result(outer_inc, Inst::Load { ty: Ty::I64, ptr: i_alloca, align: None, volatile: false });
        let next_i = self.emit_with_result(outer_inc, Inst::BinOp {
            op: BinOp::Add, ty: Ty::I64, lhs: i_val3, rhs: one,
        });
        self.emit(outer_inc, InstrNode::new(Inst::Store { ty: Ty::I64, ptr: i_alloca, value: next_i, align: None, volatile: false }));
        self.emit(outer_inc, InstrNode::new(Inst::Br { target: outer_hdr_id, args: vec![] }));

        // Finalize
        let final_cursor = self.emit_with_result(finalize, Inst::Load { ty: Ty::I64, ptr: cursor_alloca, align: None, volatile: false });
        let final_len = self.emit_with_result(finalize, Inst::BinOp {
            op: BinOp::Sub, ty: Ty::I64, lhs: final_cursor, rhs: one,
        });
        self.store_at_offset(finalize, result_ptr, 0, final_len);
        self.store_reg_ptr(finalize, rd, result_ptr)?;

        Ok(Some(finalize))
    }

    /// Lower Subseteq { rd, r1, r2 }: test r1 \subseteq r2.
    ///
    /// For each element in r1, check if it exists in r2. If any element
    /// is not found, result is 0 (false). Otherwise 1 (true).
    pub(super) fn lower_subseteq(
        &mut self,
        block_idx: usize,
        rd: u8,
        r1: u8,
        r2: u8,
    ) -> Result<Option<usize>, TmirError> {
        let set1_ptr = self.load_reg_as_ptr(block_idx, r1)?;
        let set2_ptr = self.load_reg_as_ptr(block_idx, r2)?;
        let len1 = self.load_at_offset(block_idx, set1_ptr, 0);
        let len2 = self.load_at_offset(block_idx, set2_ptr, 0);

        let zero = self.emit_i64_const(block_idx, 0);
        let one = self.emit_i64_const(block_idx, 1);

        let i_alloca = self.emit_with_result(block_idx, Inst::Alloca { ty: Ty::I64, count: None, align: None });
        self.emit(block_idx, InstrNode::new(Inst::Store { ty: Ty::I64, ptr: i_alloca, value: zero, align: None, volatile: false }));

        let outer_hdr = self.new_aux_block("subseteq_outer_hdr");
        let outer_body = self.new_aux_block("subseteq_outer_body");
        let inner_hdr = self.new_aux_block("subseteq_inner_hdr");
        let inner_body = self.new_aux_block("subseteq_inner_body");
        let inner_inc = self.new_aux_block("subseteq_inner_inc");
        let not_found = self.new_aux_block("subseteq_not_found");
        let outer_inc = self.new_aux_block("subseteq_outer_inc");
        let result_true = self.new_aux_block("subseteq_true");

        let outer_hdr_id = self.block_id_of(outer_hdr);
        let outer_body_id = self.block_id_of(outer_body);
        let inner_hdr_id = self.block_id_of(inner_hdr);
        let inner_body_id = self.block_id_of(inner_body);
        let inner_inc_id = self.block_id_of(inner_inc);
        let not_found_id = self.block_id_of(not_found);
        let outer_inc_id = self.block_id_of(outer_inc);
        let result_true_id = self.block_id_of(result_true);

        self.emit(block_idx, InstrNode::new(Inst::Br { target: outer_hdr_id, args: vec![] }));

        // Outer header: i < len1?
        let i_val = self.emit_with_result(outer_hdr, Inst::Load { ty: Ty::I64, ptr: i_alloca, align: None, volatile: false });
        let cmp = self.emit_with_result(outer_hdr, Inst::ICmp {
            op: ICmpOp::Slt, ty: Ty::I64, lhs: i_val, rhs: len1,
        });
        self.emit(outer_hdr, InstrNode::new(Inst::CondBr {
            cond: cmp,
            then_target: outer_body_id, then_args: vec![],
            else_target: result_true_id, else_args: vec![],
        }));

        // Outer body
        let i_val2 = self.emit_with_result(outer_body, Inst::Load { ty: Ty::I64, ptr: i_alloca, align: None, volatile: false });
        let slot = self.emit_with_result(outer_body, Inst::BinOp {
            op: BinOp::Add, ty: Ty::I64, lhs: i_val2, rhs: one,
        });
        let elem1 = self.load_at_dynamic_offset(outer_body, set1_ptr, slot);

        let j_alloca = self.emit_with_result(outer_body, Inst::Alloca { ty: Ty::I64, count: None, align: None });
        self.emit(outer_body, InstrNode::new(Inst::Store { ty: Ty::I64, ptr: j_alloca, value: zero, align: None, volatile: false }));
        self.emit(outer_body, InstrNode::new(Inst::Br { target: inner_hdr_id, args: vec![] }));

        // Inner header
        let j_val = self.emit_with_result(inner_hdr, Inst::Load { ty: Ty::I64, ptr: j_alloca, align: None, volatile: false });
        let cmp2 = self.emit_with_result(inner_hdr, Inst::ICmp {
            op: ICmpOp::Slt, ty: Ty::I64, lhs: j_val, rhs: len2,
        });
        self.emit(inner_hdr, InstrNode::new(Inst::CondBr {
            cond: cmp2,
            then_target: inner_body_id, then_args: vec![],
            else_target: not_found_id, else_args: vec![],
        }));

        // Inner body
        let j_val2 = self.emit_with_result(inner_body, Inst::Load { ty: Ty::I64, ptr: j_alloca, align: None, volatile: false });
        let slot2 = self.emit_with_result(inner_body, Inst::BinOp {
            op: BinOp::Add, ty: Ty::I64, lhs: j_val2, rhs: one,
        });
        let elem2 = self.load_at_dynamic_offset(inner_body, set2_ptr, slot2);
        let eq = self.emit_with_result(inner_body, Inst::ICmp {
            op: ICmpOp::Eq, ty: Ty::I64, lhs: elem1, rhs: elem2,
        });
        self.emit(inner_body, InstrNode::new(Inst::CondBr {
            cond: eq,
            then_target: outer_inc_id, then_args: vec![], // found
            else_target: inner_inc_id, else_args: vec![],
        }));

        // Inner increment
        let j_val3 = self.emit_with_result(inner_inc, Inst::Load { ty: Ty::I64, ptr: j_alloca, align: None, volatile: false });
        let next_j = self.emit_with_result(inner_inc, Inst::BinOp {
            op: BinOp::Add, ty: Ty::I64, lhs: j_val3, rhs: one,
        });
        self.emit(inner_inc, InstrNode::new(Inst::Store { ty: Ty::I64, ptr: j_alloca, value: next_j, align: None, volatile: false }));
        self.emit(inner_inc, InstrNode::new(Inst::Br { target: inner_hdr_id, args: vec![] }));

        // Not found: result is false
        self.store_reg_imm(not_found, rd, 0)?;
        // We need a merge block for the final result
        let merge = self.new_aux_block("subseteq_merge");
        let merge_id = self.block_id_of(merge);
        self.emit(not_found, InstrNode::new(Inst::Br { target: merge_id, args: vec![] }));

        // Outer increment
        let i_val3 = self.emit_with_result(outer_inc, Inst::Load { ty: Ty::I64, ptr: i_alloca, align: None, volatile: false });
        let next_i = self.emit_with_result(outer_inc, Inst::BinOp {
            op: BinOp::Add, ty: Ty::I64, lhs: i_val3, rhs: one,
        });
        self.emit(outer_inc, InstrNode::new(Inst::Store { ty: Ty::I64, ptr: i_alloca, value: next_i, align: None, volatile: false }));
        self.emit(outer_inc, InstrNode::new(Inst::Br { target: outer_hdr_id, args: vec![] }));

        // Result true
        self.store_reg_imm(result_true, rd, 1)?;
        self.emit(result_true, InstrNode::new(Inst::Br { target: merge_id, args: vec![] }));

        Ok(Some(merge))
    }

    /// Lower Range { rd, lo, hi }: build the integer interval set lo..hi.
    ///
    /// Layout: slot[0] = hi - lo + 1 (length), slot[1..=len] = lo, lo+1, ..., hi.
    pub(super) fn lower_range(
        &mut self,
        block_idx: usize,
        rd: u8,
        lo_reg: u8,
        hi_reg: u8,
    ) -> Result<Option<usize>, TmirError> {
        let lo = self.load_reg(block_idx, lo_reg)?;
        let hi = self.load_reg(block_idx, hi_reg)?;

        let one = self.emit_i64_const(block_idx, 1);

        // len = hi - lo + 1
        let diff = self.emit_with_result(block_idx, Inst::BinOp {
            op: BinOp::Sub, ty: Ty::I64, lhs: hi, rhs: lo,
        });
        let len = self.emit_with_result(block_idx, Inst::BinOp {
            op: BinOp::Add, ty: Ty::I64, lhs: diff, rhs: one,
        });

        // total slots = len + 1
        let total = self.emit_with_result(block_idx, Inst::BinOp {
            op: BinOp::Add, ty: Ty::I64, lhs: len, rhs: one,
        });
        let total_i32 = self.emit_with_result(block_idx, Inst::Cast {
            op: CastOp::Trunc, src_ty: Ty::I64, dst_ty: Ty::I32, operand: total,
        });
        let agg_ptr = self.emit_with_result(block_idx, Inst::Alloca {
            ty: Ty::I64, count: Some(total_i32), align: None,
        });

        // Store length at slot 0
        self.store_at_offset(block_idx, agg_ptr, 0, len);

        // Fill loop: for i in 0..len, store lo+i at slot i+1
        let zero = self.emit_i64_const(block_idx, 0);
        let i_alloca = self.emit_with_result(block_idx, Inst::Alloca { ty: Ty::I64, count: None, align: None });
        self.emit(block_idx, InstrNode::new(Inst::Store { ty: Ty::I64, ptr: i_alloca, value: zero, align: None, volatile: false }));

        let loop_hdr = self.new_aux_block("range_hdr");
        let loop_body = self.new_aux_block("range_body");
        let loop_done = self.new_aux_block("range_done");

        let hdr_id = self.block_id_of(loop_hdr);
        let body_id = self.block_id_of(loop_body);
        let done_id = self.block_id_of(loop_done);

        self.emit(block_idx, InstrNode::new(Inst::Br { target: hdr_id, args: vec![] }));

        // Header
        let i_val = self.emit_with_result(loop_hdr, Inst::Load { ty: Ty::I64, ptr: i_alloca, align: None, volatile: false });
        let cmp = self.emit_with_result(loop_hdr, Inst::ICmp {
            op: ICmpOp::Slt, ty: Ty::I64, lhs: i_val, rhs: len,
        });
        self.emit(loop_hdr, InstrNode::new(Inst::CondBr {
            cond: cmp,
            then_target: body_id, then_args: vec![],
            else_target: done_id, else_args: vec![],
        }));

        // Body
        let i_val2 = self.emit_with_result(loop_body, Inst::Load { ty: Ty::I64, ptr: i_alloca, align: None, volatile: false });
        let elem = self.emit_with_result(loop_body, Inst::BinOp {
            op: BinOp::Add, ty: Ty::I64, lhs: lo, rhs: i_val2,
        });
        let slot = self.emit_with_result(loop_body, Inst::BinOp {
            op: BinOp::Add, ty: Ty::I64, lhs: i_val2, rhs: one,
        });
        self.store_at_dynamic_offset(loop_body, agg_ptr, slot, elem);
        let next_i = self.emit_with_result(loop_body, Inst::BinOp {
            op: BinOp::Add, ty: Ty::I64, lhs: i_val2, rhs: one,
        });
        self.emit(loop_body, InstrNode::new(Inst::Store { ty: Ty::I64, ptr: i_alloca, value: next_i, align: None, volatile: false }));
        self.emit(loop_body, InstrNode::new(Inst::Br { target: hdr_id, args: vec![] }));

        // Done
        self.store_reg_ptr(loop_done, rd, agg_ptr)?;

        Ok(Some(loop_done))
    }
}
