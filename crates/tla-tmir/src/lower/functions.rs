// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Function operation lowering: FuncApply, Domain, FuncExcept, FuncDefBegin,
//! LoopNext (FuncDef).

use crate::TmirError;
use tla_jit::abi::JitRuntimeErrorKind;
use tmir::inst::*;
use tmir::ty::Ty;
use tmir::InstrNode;

use super::{Ctx, QuantifierLoopState};

impl<'cp> Ctx<'cp> {
    // =====================================================================
    // Function operations
    // =====================================================================
    //
    // TLA+ functions are total mappings from domain keys to values.
    // Aggregate layout: slot[0] = pair_count, then interleaved key-value pairs:
    //   slot[1] = key1, slot[2] = val1, slot[3] = key2, slot[4] = val2, ...
    //
    // For a function with N pairs, total slots = 1 + 2*N.
    // Key at index i (0-based): slot[1 + 2*i]
    // Value at index i (0-based): slot[2 + 2*i]

    /// Lower FuncApply { rd, func, arg }: function application f[x].
    ///
    /// Linear scan: for each key in the function, compare with arg.
    /// If found, return the corresponding value. If not found, runtime error.
    ///
    /// CFG:
    ///   entry -> header
    ///   header -> body (if i < len) | not_found (if i >= len)
    ///   body -> found (if key == arg) | inc (if key != arg)
    ///   inc -> header
    ///   found -> merge (rd = value)
    ///   not_found -> runtime_error
    pub(super) fn lower_func_apply(
        &mut self,
        block_idx: usize,
        rd: u8,
        func_reg: u8,
        arg_reg: u8,
    ) -> Result<Option<usize>, TmirError> {
        let arg_val = self.load_reg(block_idx, arg_reg)?;
        let func_ptr = self.load_reg_as_ptr(block_idx, func_reg)?;
        let pair_count = self.load_at_offset(block_idx, func_ptr, 0);

        let zero = self.emit_i64_const(block_idx, 0);
        let one = self.emit_i64_const(block_idx, 1);
        let two = self.emit_i64_const(block_idx, 2);

        let idx_alloca = self.emit_with_result(
            block_idx,
            Inst::Alloca { ty: Ty::I64, count: None },
        );
        self.emit(block_idx, InstrNode::new(Inst::Store { ty: Ty::I64, ptr: idx_alloca, value: zero }));

        let loop_header = self.new_aux_block("fapply_header");
        let loop_body = self.new_aux_block("fapply_body");
        let loop_inc = self.new_aux_block("fapply_inc");
        let found_blk = self.new_aux_block("fapply_found");
        let not_found_blk = self.new_aux_block("fapply_not_found");
        let merge_blk = self.new_aux_block("fapply_merge");

        let header_id = self.block_id_of(loop_header);
        let body_id = self.block_id_of(loop_body);
        let inc_id = self.block_id_of(loop_inc);
        let found_id = self.block_id_of(found_blk);
        let not_found_id = self.block_id_of(not_found_blk);
        let merge_id = self.block_id_of(merge_blk);

        self.emit(block_idx, InstrNode::new(Inst::Br { target: header_id, args: vec![] }));

        // Header: i < pair_count?
        let cur_idx = self.emit_with_result(loop_header, Inst::Load { ty: Ty::I64, ptr: idx_alloca });
        let cmp = self.emit_with_result(loop_header, Inst::ICmp {
            op: ICmpOp::Slt, ty: Ty::I64, lhs: cur_idx, rhs: pair_count,
        });
        self.emit(loop_header, InstrNode::new(Inst::CondBr {
            cond: cmp,
            then_target: body_id, then_args: vec![],
            else_target: not_found_id, else_args: vec![],
        }));

        // Body: load key at slot[1 + 2*i], compare with arg
        let cur_idx2 = self.emit_with_result(loop_body, Inst::Load { ty: Ty::I64, ptr: idx_alloca });
        let key_offset = self.emit_with_result(loop_body, Inst::BinOp {
            op: BinOp::Mul, ty: Ty::I64, lhs: cur_idx2, rhs: two,
        });
        let key_slot = self.emit_with_result(loop_body, Inst::BinOp {
            op: BinOp::Add, ty: Ty::I64, lhs: key_offset, rhs: one,
        });
        let key_val = self.load_at_dynamic_offset(loop_body, func_ptr, key_slot);
        let eq = self.emit_with_result(loop_body, Inst::ICmp {
            op: ICmpOp::Eq, ty: Ty::I64, lhs: key_val, rhs: arg_val,
        });
        self.emit(loop_body, InstrNode::new(Inst::CondBr {
            cond: eq,
            then_target: found_id, then_args: vec![],
            else_target: inc_id, else_args: vec![],
        }));

        // Increment: i++, goto header
        let cur_idx3 = self.emit_with_result(loop_inc, Inst::Load { ty: Ty::I64, ptr: idx_alloca });
        let next_idx = self.emit_with_result(loop_inc, Inst::BinOp {
            op: BinOp::Add, ty: Ty::I64, lhs: cur_idx3, rhs: one,
        });
        self.emit(loop_inc, InstrNode::new(Inst::Store { ty: Ty::I64, ptr: idx_alloca, value: next_idx }));
        self.emit(loop_inc, InstrNode::new(Inst::Br { target: header_id, args: vec![] }));

        // Found: load value at slot[2 + 2*i], store to rd
        let cur_idx4 = self.emit_with_result(found_blk, Inst::Load { ty: Ty::I64, ptr: idx_alloca });
        let val_offset = self.emit_with_result(found_blk, Inst::BinOp {
            op: BinOp::Mul, ty: Ty::I64, lhs: cur_idx4, rhs: two,
        });
        let val_slot = self.emit_with_result(found_blk, Inst::BinOp {
            op: BinOp::Add, ty: Ty::I64, lhs: val_offset, rhs: two,
        });
        let result_val = self.load_at_dynamic_offset(found_blk, func_ptr, val_slot);
        self.store_reg_value(found_blk, rd, result_val)?;
        self.emit(found_blk, InstrNode::new(Inst::Br { target: merge_id, args: vec![] }));

        // Not found: runtime error (function applied to value not in domain)
        self.emit_runtime_error_and_return(not_found_blk, JitRuntimeErrorKind::TypeMismatch);

        Ok(Some(merge_blk))
    }

    /// Lower Domain { rd, rs }: extract domain set from function.
    ///
    /// Reads the function aggregate at rs and builds a new set containing
    /// all keys. Function layout: [pair_count, k1, v1, k2, v2, ...].
    /// Result set layout: [pair_count, k1, k2, ...].
    pub(super) fn lower_domain(
        &mut self,
        block_idx: usize,
        rd: u8,
        rs: u8,
    ) -> Result<Option<usize>, TmirError> {
        let func_ptr = self.load_reg_as_ptr(block_idx, rs)?;
        let pair_count = self.load_at_offset(block_idx, func_ptr, 0);

        let one = self.emit_i64_const(block_idx, 1);
        let two = self.emit_i64_const(block_idx, 2);
        let zero = self.emit_i64_const(block_idx, 0);

        // Allocate result set: pair_count + 1 slots (length header + keys)
        let total = self.emit_with_result(block_idx, Inst::BinOp {
            op: BinOp::Add, ty: Ty::I64, lhs: pair_count, rhs: one,
        });
        let total_i32 = self.emit_with_result(block_idx, Inst::Cast {
            op: CastOp::Trunc, src_ty: Ty::I64, dst_ty: Ty::I32, operand: total,
        });
        let result_ptr = self.emit_with_result(block_idx, Inst::Alloca {
            ty: Ty::I64, count: Some(total_i32),
        });

        // Store length = pair_count
        self.store_at_offset(block_idx, result_ptr, 0, pair_count);

        // Loop: for i in 0..pair_count, result[i+1] = func[1 + 2*i]
        let i_alloca = self.emit_with_result(block_idx, Inst::Alloca { ty: Ty::I64, count: None });
        self.emit(block_idx, InstrNode::new(Inst::Store { ty: Ty::I64, ptr: i_alloca, value: zero }));

        let loop_hdr = self.new_aux_block("domain_hdr");
        let loop_body = self.new_aux_block("domain_body");
        let loop_done = self.new_aux_block("domain_done");

        let hdr_id = self.block_id_of(loop_hdr);
        let body_id = self.block_id_of(loop_body);
        let done_id = self.block_id_of(loop_done);

        self.emit(block_idx, InstrNode::new(Inst::Br { target: hdr_id, args: vec![] }));

        // Header: i < pair_count?
        let i_val = self.emit_with_result(loop_hdr, Inst::Load { ty: Ty::I64, ptr: i_alloca });
        let cmp = self.emit_with_result(loop_hdr, Inst::ICmp {
            op: ICmpOp::Slt, ty: Ty::I64, lhs: i_val, rhs: pair_count,
        });
        self.emit(loop_hdr, InstrNode::new(Inst::CondBr {
            cond: cmp,
            then_target: body_id, then_args: vec![],
            else_target: done_id, else_args: vec![],
        }));

        // Body: result[i+1] = func[1 + 2*i]
        let i_val2 = self.emit_with_result(loop_body, Inst::Load { ty: Ty::I64, ptr: i_alloca });
        let key_offset = self.emit_with_result(loop_body, Inst::BinOp {
            op: BinOp::Mul, ty: Ty::I64, lhs: i_val2, rhs: two,
        });
        let key_slot = self.emit_with_result(loop_body, Inst::BinOp {
            op: BinOp::Add, ty: Ty::I64, lhs: key_offset, rhs: one,
        });
        let key_val = self.load_at_dynamic_offset(loop_body, func_ptr, key_slot);

        let dst_slot = self.emit_with_result(loop_body, Inst::BinOp {
            op: BinOp::Add, ty: Ty::I64, lhs: i_val2, rhs: one,
        });
        self.store_at_dynamic_offset(loop_body, result_ptr, dst_slot, key_val);

        let next_i = self.emit_with_result(loop_body, Inst::BinOp {
            op: BinOp::Add, ty: Ty::I64, lhs: i_val2, rhs: one,
        });
        self.emit(loop_body, InstrNode::new(Inst::Store { ty: Ty::I64, ptr: i_alloca, value: next_i }));
        self.emit(loop_body, InstrNode::new(Inst::Br { target: hdr_id, args: vec![] }));

        // Done
        self.store_reg_ptr(loop_done, rd, result_ptr)?;

        Ok(Some(loop_done))
    }

    /// Lower FuncExcept { rd, func, path, val }: [f EXCEPT ![x] = y].
    ///
    /// Creates a new function identical to func but with the value at key `path`
    /// replaced by `val`. If the key does not exist, the original function is
    /// returned unchanged (TLA+ semantics: EXCEPT on non-existent key is identity).
    ///
    /// Implementation: allocate new function aggregate of same size, copy all pairs,
    /// but when key matches `path`, store `val` instead of the original value.
    pub(super) fn lower_func_except(
        &mut self,
        block_idx: usize,
        rd: u8,
        func_reg: u8,
        path_reg: u8,
        val_reg: u8,
    ) -> Result<Option<usize>, TmirError> {
        let path_val = self.load_reg(block_idx, path_reg)?;
        let new_val = self.load_reg(block_idx, val_reg)?;
        let func_ptr = self.load_reg_as_ptr(block_idx, func_reg)?;
        let pair_count = self.load_at_offset(block_idx, func_ptr, 0);

        let zero = self.emit_i64_const(block_idx, 0);
        let one = self.emit_i64_const(block_idx, 1);
        let two = self.emit_i64_const(block_idx, 2);

        // Allocate new function: 1 + 2*pair_count slots
        let pairs_x2 = self.emit_with_result(block_idx, Inst::BinOp {
            op: BinOp::Mul, ty: Ty::I64, lhs: pair_count, rhs: two,
        });
        let total = self.emit_with_result(block_idx, Inst::BinOp {
            op: BinOp::Add, ty: Ty::I64, lhs: pairs_x2, rhs: one,
        });
        let total_i32 = self.emit_with_result(block_idx, Inst::Cast {
            op: CastOp::Trunc, src_ty: Ty::I64, dst_ty: Ty::I32, operand: total,
        });
        let result_ptr = self.emit_with_result(block_idx, Inst::Alloca {
            ty: Ty::I64, count: Some(total_i32),
        });

        // Store pair_count in new function
        self.store_at_offset(block_idx, result_ptr, 0, pair_count);

        // Loop: for i in 0..pair_count, copy key, conditionally replace value
        let i_alloca = self.emit_with_result(block_idx, Inst::Alloca { ty: Ty::I64, count: None });
        self.emit(block_idx, InstrNode::new(Inst::Store { ty: Ty::I64, ptr: i_alloca, value: zero }));

        let loop_hdr = self.new_aux_block("fexcept_hdr");
        let loop_body = self.new_aux_block("fexcept_body");
        let loop_done = self.new_aux_block("fexcept_done");

        let hdr_id = self.block_id_of(loop_hdr);
        let body_id = self.block_id_of(loop_body);
        let done_id = self.block_id_of(loop_done);

        self.emit(block_idx, InstrNode::new(Inst::Br { target: hdr_id, args: vec![] }));

        // Header: i < pair_count?
        let i_val = self.emit_with_result(loop_hdr, Inst::Load { ty: Ty::I64, ptr: i_alloca });
        let cmp = self.emit_with_result(loop_hdr, Inst::ICmp {
            op: ICmpOp::Slt, ty: Ty::I64, lhs: i_val, rhs: pair_count,
        });
        self.emit(loop_hdr, InstrNode::new(Inst::CondBr {
            cond: cmp,
            then_target: body_id, then_args: vec![],
            else_target: done_id, else_args: vec![],
        }));

        // Body: copy key, select value based on key match
        let i_val2 = self.emit_with_result(loop_body, Inst::Load { ty: Ty::I64, ptr: i_alloca });

        // Source key slot: 1 + 2*i
        let src_key_offset = self.emit_with_result(loop_body, Inst::BinOp {
            op: BinOp::Mul, ty: Ty::I64, lhs: i_val2, rhs: two,
        });
        let src_key_slot = self.emit_with_result(loop_body, Inst::BinOp {
            op: BinOp::Add, ty: Ty::I64, lhs: src_key_offset, rhs: one,
        });
        let key = self.load_at_dynamic_offset(loop_body, func_ptr, src_key_slot);

        // Source value slot: 2 + 2*i
        let src_val_slot = self.emit_with_result(loop_body, Inst::BinOp {
            op: BinOp::Add, ty: Ty::I64, lhs: src_key_offset, rhs: two,
        });
        let orig_val = self.load_at_dynamic_offset(loop_body, func_ptr, src_val_slot);

        // Select: if key == path then new_val else orig_val
        let key_match = self.emit_with_result(loop_body, Inst::ICmp {
            op: ICmpOp::Eq, ty: Ty::I64, lhs: key, rhs: path_val,
        });
        let selected_val = self.emit_with_result(loop_body, Inst::Select {
            ty: Ty::I64,
            cond: key_match,
            then_val: new_val,
            else_val: orig_val,
        });

        // Store key and selected value in result
        self.store_at_dynamic_offset(loop_body, result_ptr, src_key_slot, key);
        self.store_at_dynamic_offset(loop_body, result_ptr, src_val_slot, selected_val);

        // Increment
        let next_i = self.emit_with_result(loop_body, Inst::BinOp {
            op: BinOp::Add, ty: Ty::I64, lhs: i_val2, rhs: one,
        });
        self.emit(loop_body, InstrNode::new(Inst::Store { ty: Ty::I64, ptr: i_alloca, value: next_i }));
        self.emit(loop_body, InstrNode::new(Inst::Br { target: hdr_id, args: vec![] }));

        // Done
        self.store_reg_ptr(loop_done, rd, result_ptr)?;

        Ok(Some(loop_done))
    }

    /// Lower FuncDefBegin: initialize function builder, iterate domain.
    ///
    /// Allocates a function aggregate sized for the domain, then iterates
    /// over domain elements. For each element, the body evaluates the
    /// mapping expression, and LoopNext stores the (key, value) pair.
    ///
    /// Function layout: [pair_count, key1, val1, key2, val2, ...]
    ///
    /// CFG produced:
    ///   current_block -> header
    ///   header -> body_block (if i < len) | exit_block (if i >= len)
    pub(super) fn lower_func_def_begin(
        &mut self,
        pc: usize,
        block: usize,
        rd: u8,
        r_binding: u8,
        r_domain: u8,
        loop_end: i32,
    ) -> Result<Option<usize>, TmirError> {
        let exit_pc = self.resolve_forward_target(pc, loop_end, "FuncDefBegin")?;
        let body_pc = pc + 1;
        let exit_block = self.block_index_for_pc(exit_pc)?;
        let body_block = self.block_index_for_pc(body_pc)?;

        // Load domain pointer and length.
        let domain_ptr = self.load_reg_as_ptr(block, r_domain)?;
        let domain_len = self.load_at_offset(block, domain_ptr, 0);

        let zero = self.emit_i64_const(block, 0);
        let one = self.emit_i64_const(block, 1);
        let two = self.emit_i64_const(block, 2);

        // Allocate function aggregate: 1 + 2*domain_len slots
        let pairs_x2 = self.emit_with_result(block, Inst::BinOp {
            op: BinOp::Mul, ty: Ty::I64, lhs: domain_len, rhs: two,
        });
        let total = self.emit_with_result(block, Inst::BinOp {
            op: BinOp::Add, ty: Ty::I64, lhs: pairs_x2, rhs: one,
        });
        let total_i32 = self.emit_with_result(block, Inst::Cast {
            op: CastOp::Trunc, src_ty: Ty::I64, dst_ty: Ty::I32, operand: total,
        });
        let func_ptr = self.emit_with_result(block, Inst::Alloca {
            ty: Ty::I64, count: Some(total_i32),
        });

        // Store pair_count = domain_len
        self.store_at_offset(block, func_ptr, 0, domain_len);

        // Store function pointer in rd now (so LoopNext can access it).
        self.store_reg_ptr(block, rd, func_ptr)?;

        // Allocate index counter, initialize to 0.
        let idx_alloca = self.emit_with_result(
            block,
            Inst::Alloca { ty: Ty::I64, count: None },
        );
        self.emit(
            block,
            InstrNode::new(Inst::Store { ty: Ty::I64, ptr: idx_alloca, value: zero }),
        );

        // Create loop header block.
        let header_block = self.new_aux_block("funcdef_header");
        let header_id = self.block_id_of(header_block);
        let body_id = self.block_id_of(body_block);
        let exit_id = self.block_id_of(exit_block);

        // Branch to header.
        self.emit(block, InstrNode::new(Inst::Br { target: header_id, args: vec![] }));

        // Header: check i < domain_len.
        let cur_idx = self.emit_with_result(
            header_block,
            Inst::Load { ty: Ty::I64, ptr: idx_alloca },
        );
        let in_bounds = self.emit_with_result(
            header_block,
            Inst::ICmp { op: ICmpOp::Slt, ty: Ty::I64, lhs: cur_idx, rhs: domain_len },
        );

        let load_block = self.new_aux_block("funcdef_load");
        let load_id = self.block_id_of(load_block);

        self.emit(
            header_block,
            InstrNode::new(Inst::CondBr {
                cond: in_bounds,
                then_target: load_id,
                then_args: vec![],
                else_target: exit_id,
                else_args: vec![],
            }),
        );

        // Load element: r_binding = domain[i+1] (skip length header).
        let cur_idx2 = self.emit_with_result(
            load_block,
            Inst::Load { ty: Ty::I64, ptr: idx_alloca },
        );
        let slot_idx = self.emit_with_result(
            load_block,
            Inst::BinOp { op: BinOp::Add, ty: Ty::I64, lhs: cur_idx2, rhs: one },
        );
        let elem = self.load_at_dynamic_offset(load_block, domain_ptr, slot_idx);
        self.store_reg_value(load_block, r_binding, elem)?;

        // Also store the key into the function aggregate at slot[1 + 2*i].
        let func_ptr_reload = self.load_reg_as_ptr(load_block, rd)?;
        let key_offset = self.emit_with_result(load_block, Inst::BinOp {
            op: BinOp::Mul, ty: Ty::I64, lhs: cur_idx2, rhs: two,
        });
        let key_slot = self.emit_with_result(load_block, Inst::BinOp {
            op: BinOp::Add, ty: Ty::I64, lhs: key_offset, rhs: one,
        });
        self.store_at_dynamic_offset(load_block, func_ptr_reload, key_slot, elem);

        // Branch to the body block.
        self.emit(
            load_block,
            InstrNode::new(Inst::Br { target: body_id, args: vec![] }),
        );

        // Save loop state for LoopNext (use func_def_stack, not quantifier_loops,
        // because LoopNext does not carry rd).
        self.func_def_stack.push((rd, QuantifierLoopState {
            idx_alloca,
            header_block,
            exit_block,
        }));

        // Body block is the next PC's block — return None to let lower_body
        // transition to it naturally.
        Ok(None)
    }

    /// Lower LoopNext for FuncDef: store body result as value, advance iterator.
    ///
    /// Stores the body result (r_body) as the value for the current key in the
    /// function aggregate, then increments the index and branches back to the header.
    pub(super) fn lower_loop_next_func_def(
        &mut self,
        _pc: usize,
        block: usize,
        _r_binding: u8,
        r_body: u8,
    ) -> Result<Option<usize>, TmirError> {
        let (rd, loop_state) = self.func_def_stack.pop().ok_or_else(|| {
            TmirError::Emission("LoopNext without matching FuncDefBegin".to_owned())
        })?;

        let body_val = self.load_reg(block, r_body)?;
        let two = self.emit_i64_const(block, 2);
        let one = self.emit_i64_const(block, 1);

        // Store value at slot[2 + 2*i] in the function aggregate.
        let func_ptr = self.load_reg_as_ptr(block, rd)?;
        let cur_idx = self.emit_with_result(
            block,
            Inst::Load { ty: Ty::I64, ptr: loop_state.idx_alloca },
        );
        let val_offset = self.emit_with_result(block, Inst::BinOp {
            op: BinOp::Mul, ty: Ty::I64, lhs: cur_idx, rhs: two,
        });
        let val_slot = self.emit_with_result(block, Inst::BinOp {
            op: BinOp::Add, ty: Ty::I64, lhs: val_offset, rhs: two,
        });
        self.store_at_dynamic_offset(block, func_ptr, val_slot, body_val);

        // Advance: increment index, branch to header.
        let next_idx = self.emit_with_result(block, Inst::BinOp {
            op: BinOp::Add, ty: Ty::I64, lhs: cur_idx, rhs: one,
        });
        self.emit(
            block,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: loop_state.idx_alloca,
                value: next_idx,
            }),
        );

        let header_id = self.block_id_of(loop_state.header_block);
        self.emit(
            block,
            InstrNode::new(Inst::Br { target: header_id, args: vec![] }),
        );

        // Return None — the exit block is the next PC's block, lower_body handles it.
        Ok(None)
    }
}
