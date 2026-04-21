// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Quantifier lowering: ForAll, Exists, Choose.
//!
//! Each quantifier shares a common "typed binding frame" prelude
//! emitted by [`Ctx::emit_binding_frame_prelude`] — domain load, idx
//! alloca, header bounds check, per-iteration element load into the
//! body's binding register. This file layers the quantifier-specific
//! initial-value and short-circuit behaviour on top of that prelude.

use crate::TmirError;
use tla_jit_abi::JitRuntimeErrorKind;
use tmir::inst::*;
use tmir::ty::Ty;
use tmir::InstrNode;

use super::{resolve_target, Ctx, QuantifierLoopState};

impl<'cp> Ctx<'cp> {
    /// Lower ForallBegin: initialize iterator, store TRUE to rd, branch to header.
    ///
    /// The header checks bounds and loads the next element into r_binding.
    /// If the domain is empty, jumps directly to the exit block.
    ///
    /// CFG produced:
    ///   current_block -> header
    ///   header -> load_block (if i < len) | exit_block (if i >= len)
    ///   load_block -> body_block  (populates r_binding = domain[i+1])
    ///   [body ... ForallNext]
    pub(super) fn lower_forall_begin(
        &mut self,
        pc: usize,
        block: usize,
        rd: u8,
        r_binding: u8,
        r_domain: u8,
        loop_end: i32,
    ) -> Result<Option<usize>, TmirError> {
        // Initialize rd = TRUE (1). If domain is empty, this is the
        // result. This must come before the prelude so that the store
        // lands in the caller's block (the prelude terminates `block`
        // with a `Br` to the header).
        self.store_reg_imm(block, rd, 1)?;

        let frame = self.emit_binding_frame_prelude(
            pc,
            block,
            r_binding,
            r_domain,
            loop_end,
            "forall_header",
            "forall_load",
            "ForallBegin",
        )?;

        // Save loop state for ForallNext (keyed by rd so nested
        // quantifiers don't collide).
        self.quantifier_loops.insert(
            rd,
            QuantifierLoopState {
                idx_alloca: frame.idx_alloca,
                header_block: frame.header_block,
                exit_block: frame.exit_block,
            },
        );

        // Attach bounded_loop(N) annotation to the header CondBr when
        // the domain is compile-time bounded. Otherwise mark the
        // function unbounded so Terminates is not emitted.
        if !self.annotate_loop_bound(frame.header_block, r_domain) {
            self.mark_unbounded_loop();
        }

        // ForAll's result is boolean (TRUE/FALSE). Clobber any prior
        // set tracking on rd.
        self.invalidate_reg_tracking(rd);

        // Body block is the next PC's block — return None to let
        // lower_body transition to it naturally.
        Ok(None)
    }

    /// Lower ForallNext: check body result, short-circuit on FALSE, else advance.
    ///
    /// If r_body is FALSE: store FALSE to rd, branch to exit.
    /// Otherwise: increment index, branch back to header.
    pub(super) fn lower_forall_next(
        &mut self,
        _pc: usize,
        block: usize,
        rd: u8,
        _r_binding: u8,
        r_body: u8,
    ) -> Result<Option<usize>, TmirError> {
        let loop_state = self.quantifier_loops.remove(&rd).ok_or_else(|| {
            TmirError::Emission(format!("ForallNext for r{rd} without matching ForallBegin"))
        })?;

        let body_val = self.load_reg(block, r_body)?;
        let zero = self.emit_i64_const(block, 0);
        let is_false = self.emit_with_result(
            block,
            Inst::ICmp { op: ICmpOp::Eq, ty: Ty::I64, lhs: body_val, rhs: zero },
        );

        let short_circuit_block = self.new_aux_block("forall_false");
        let advance_block = self.new_aux_block("forall_advance");

        let short_id = self.block_id_of(short_circuit_block);
        let advance_id = self.block_id_of(advance_block);
        let header_id = self.block_id_of(loop_state.header_block);
        let exit_id = self.block_id_of(loop_state.exit_block);

        self.emit(
            block,
            InstrNode::new(Inst::CondBr {
                cond: is_false,
                then_target: short_id,
                then_args: vec![],
                else_target: advance_id,
                else_args: vec![],
            }),
        );

        // Short-circuit: rd = FALSE, branch to exit.
        self.store_reg_imm(short_circuit_block, rd, 0)?;
        self.emit(
            short_circuit_block,
            InstrNode::new(Inst::Br { target: exit_id, args: vec![] }),
        );

        // Advance: increment index, branch to header.
        self.emit_advance_loop(advance_block, loop_state.idx_alloca, header_id);

        // Return None — the exit block is the next PC's block, lower_body handles it.
        Ok(None)
    }

    /// Lower ExistsBegin: initialize iterator, store FALSE to rd, branch to header.
    pub(super) fn lower_exists_begin(
        &mut self,
        pc: usize,
        block: usize,
        rd: u8,
        r_binding: u8,
        r_domain: u8,
        loop_end: i32,
    ) -> Result<Option<usize>, TmirError> {
        // Initialize rd = FALSE (0). If domain is empty, this is the
        // result. Must come before the prelude (same reasoning as
        // ForallBegin).
        self.store_reg_imm(block, rd, 0)?;

        let frame = self.emit_binding_frame_prelude(
            pc,
            block,
            r_binding,
            r_domain,
            loop_end,
            "exists_header",
            "exists_load",
            "ExistsBegin",
        )?;

        self.quantifier_loops.insert(
            rd,
            QuantifierLoopState {
                idx_alloca: frame.idx_alloca,
                header_block: frame.header_block,
                exit_block: frame.exit_block,
            },
        );

        if !self.annotate_loop_bound(frame.header_block, r_domain) {
            self.mark_unbounded_loop();
        }
        self.invalidate_reg_tracking(rd);

        Ok(None)
    }

    /// Lower ExistsNext: check body result, short-circuit on TRUE, else advance.
    pub(super) fn lower_exists_next(
        &mut self,
        _pc: usize,
        block: usize,
        rd: u8,
        _r_binding: u8,
        r_body: u8,
    ) -> Result<Option<usize>, TmirError> {
        let loop_state = self.quantifier_loops.remove(&rd).ok_or_else(|| {
            TmirError::Emission(format!("ExistsNext for r{rd} without matching ExistsBegin"))
        })?;

        let body_val = self.load_reg(block, r_body)?;
        let zero = self.emit_i64_const(block, 0);
        let is_true = self.emit_with_result(
            block,
            Inst::ICmp { op: ICmpOp::Ne, ty: Ty::I64, lhs: body_val, rhs: zero },
        );

        let short_circuit_block = self.new_aux_block("exists_true");
        let advance_block = self.new_aux_block("exists_advance");

        let short_id = self.block_id_of(short_circuit_block);
        let advance_id = self.block_id_of(advance_block);
        let header_id = self.block_id_of(loop_state.header_block);
        let exit_id = self.block_id_of(loop_state.exit_block);

        self.emit(
            block,
            InstrNode::new(Inst::CondBr {
                cond: is_true,
                then_target: short_id,
                then_args: vec![],
                else_target: advance_id,
                else_args: vec![],
            }),
        );

        // Short-circuit: rd = TRUE, branch to exit.
        self.store_reg_imm(short_circuit_block, rd, 1)?;
        self.emit(
            short_circuit_block,
            InstrNode::new(Inst::Br { target: exit_id, args: vec![] }),
        );

        // Advance: increment index, branch to header.
        self.emit_advance_loop(advance_block, loop_state.idx_alloca, header_id);

        Ok(None)
    }

    /// Lower ChooseBegin: initialize iterator, branch to header.
    ///
    /// CHOOSE does not have a default value — if no element satisfies the
    /// predicate, it is a TLA+ runtime error (Halt). If the domain is empty,
    /// the header CondBr's `else_target` reaches a dedicated "exhausted"
    /// block (runtime error) instead of the natural exit block.
    pub(super) fn lower_choose_begin(
        &mut self,
        pc: usize,
        block: usize,
        rd: u8,
        r_binding: u8,
        r_domain: u8,
        loop_end: i32,
    ) -> Result<Option<usize>, TmirError> {
        // CHOOSE needs a custom exit target (exhausted / runtime error)
        // so it cannot reuse `emit_binding_frame_prelude` verbatim. We
        // still construct a `BindingFrame`-shaped result so the `*_next`
        // side can share the same state type as Forall/Exists.
        let exit_pc = self.resolve_forward_target(pc, loop_end, "ChooseBegin")?;
        let body_pc = pc + 1;
        let exit_block = self.block_index_for_pc(exit_pc)?;
        let body_block = self.block_index_for_pc(body_pc)?;

        let domain_ptr = self.load_reg_as_ptr(block, r_domain)?;
        let domain_len = self.load_at_offset(block, domain_ptr, 0);

        let idx_alloca = self.emit_with_result(
            block,
            Inst::Alloca { ty: Ty::I64, count: None, align: None },
        );
        let zero = self.emit_i64_const(block, 0);
        self.emit(
            block,
            InstrNode::new(Inst::Store { ty: Ty::I64, ptr: idx_alloca, value: zero, align: None, volatile: false }),
        );

        let header_block = self.new_aux_block("choose_header");
        let header_id = self.block_id_of(header_block);
        let body_id = self.block_id_of(body_block);

        // If domain is empty, it's a runtime error — branch to exhausted block.
        let exhausted_block = self.new_aux_block("choose_exhausted");
        let exhausted_id = self.block_id_of(exhausted_block);

        self.emit(block, InstrNode::new(Inst::Br { target: header_id, args: vec![] }));

        // Header: check i < len.
        let cur_idx = self.emit_with_result(
            header_block,
            Inst::Load { ty: Ty::I64, ptr: idx_alloca, align: None, volatile: false },
        );
        let in_bounds = self.emit_with_result(
            header_block,
            Inst::ICmp { op: ICmpOp::Slt, ty: Ty::I64, lhs: cur_idx, rhs: domain_len },
        );

        let load_block = self.new_aux_block("choose_load");
        let load_id = self.block_id_of(load_block);

        self.emit(
            header_block,
            InstrNode::new(Inst::CondBr {
                cond: in_bounds,
                then_target: load_id,
                then_args: vec![],
                else_target: exhausted_id,
                else_args: vec![],
            }),
        );

        // Exhausted: no element found — runtime error.
        self.emit_runtime_error_and_return(exhausted_block, JitRuntimeErrorKind::TypeMismatch);

        // Load element.
        let cur_idx2 = self.emit_with_result(
            load_block,
            Inst::Load { ty: Ty::I64, ptr: idx_alloca, align: None, volatile: false },
        );
        let one = self.emit_i64_const(load_block, 1);
        let slot_idx = self.emit_with_result(
            load_block,
            Inst::BinOp { op: BinOp::Add, ty: Ty::I64, lhs: cur_idx2, rhs: one },
        );
        let elem = self.load_at_dynamic_offset(load_block, domain_ptr, slot_idx);
        self.store_reg_value(load_block, r_binding, elem)?;

        self.emit(
            load_block,
            InstrNode::new(Inst::Br { target: body_id, args: vec![] }),
        );

        self.quantifier_loops.insert(rd, QuantifierLoopState {
            idx_alloca,
            header_block,
            exit_block,
        });

        if !self.annotate_loop_bound(header_block, r_domain) {
            self.mark_unbounded_loop();
        }
        // CHOOSE's result is the first-matching binding — value, not boolean.
        // We can't track its cardinality (it's a scalar), so clobber.
        self.invalidate_reg_tracking(rd);

        Ok(None)
    }

    /// Lower ChooseNext: if r_body is TRUE, store r_binding to rd and exit.
    /// Otherwise, advance iterator. If domain exhausted, runtime error.
    pub(super) fn lower_choose_next(
        &mut self,
        _pc: usize,
        block: usize,
        rd: u8,
        r_binding: u8,
        r_body: u8,
    ) -> Result<Option<usize>, TmirError> {
        let loop_state = self.quantifier_loops.remove(&rd).ok_or_else(|| {
            TmirError::Emission(format!("ChooseNext for r{rd} without matching ChooseBegin"))
        })?;

        let body_val = self.load_reg(block, r_body)?;
        let zero = self.emit_i64_const(block, 0);
        let is_true = self.emit_with_result(
            block,
            Inst::ICmp { op: ICmpOp::Ne, ty: Ty::I64, lhs: body_val, rhs: zero },
        );

        let found_block = self.new_aux_block("choose_found");
        let advance_block = self.new_aux_block("choose_advance");

        let found_id = self.block_id_of(found_block);
        let advance_id = self.block_id_of(advance_block);
        let header_id = self.block_id_of(loop_state.header_block);
        let exit_id = self.block_id_of(loop_state.exit_block);

        self.emit(
            block,
            InstrNode::new(Inst::CondBr {
                cond: is_true,
                then_target: found_id,
                then_args: vec![],
                else_target: advance_id,
                else_args: vec![],
            }),
        );

        // Found: rd = r_binding, branch to exit.
        let binding_val = self.load_reg(found_block, r_binding)?;
        self.store_reg_value(found_block, rd, binding_val)?;
        self.emit(
            found_block,
            InstrNode::new(Inst::Br { target: exit_id, args: vec![] }),
        );

        // Advance: increment index, branch to header.
        self.emit_advance_loop(advance_block, loop_state.idx_alloca, header_id);

        Ok(None)
    }

    /// Emit the standard "advance the loop index and branch to header"
    /// sequence used by every quantifier's `*Next` advance path.
    ///
    /// This is the dual of the prelude's load block: it's the only
    /// CFG transition that can re-enter the header outside the prelude
    /// itself. All three quantifiers share exactly the same shape
    /// (load idx, add 1, store, branch to header_id), so they all
    /// call through here.
    pub(super) fn emit_advance_loop(
        &mut self,
        advance_block: usize,
        idx_alloca: tmir::value::ValueId,
        header_id: tmir::value::BlockId,
    ) {
        let cur_idx = self.emit_with_result(
            advance_block,
            Inst::Load { ty: Ty::I64, ptr: idx_alloca, align: None, volatile: false },
        );
        let one = self.emit_i64_const(advance_block, 1);
        let next_idx = self.emit_with_result(
            advance_block,
            Inst::BinOp { op: BinOp::Add, ty: Ty::I64, lhs: cur_idx, rhs: one },
        );
        self.emit(
            advance_block,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: idx_alloca,
                value: next_idx,
                align: None,
                volatile: false,
            }),
        );
        self.emit(
            advance_block,
            InstrNode::new(Inst::Br { target: header_id, args: vec![] }),
        );
    }

    // =====================================================================
    // Jump target resolution
    // =====================================================================

    pub(super) fn resolve_forward_target(
        &self,
        pc: usize,
        offset: i32,
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
        if target >= self.instruction_len {
            return Err(TmirError::NotEligible {
                reason: format!(
                    "{opcode_name} at pc {pc} targets {target}, outside body len {}",
                    self.instruction_len
                ),
            });
        }
        Ok(target)
    }
}
