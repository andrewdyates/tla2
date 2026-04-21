// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Comparison and boolean operation lowering: Eq, Neq, Lt, Le, Gt, Ge,
//! And, Or, Not, Implies, Equiv, CondMove.

use crate::TmirError;
use tmir::inst::*;
use tmir::ty::Ty;
use tmir::Constant;

use super::Ctx;

impl<'cp> Ctx<'cp> {
    pub(super) fn lower_comparison(
        &mut self,
        block_idx: usize,
        rd: u8,
        r1: u8,
        r2: u8,
        predicate: ICmpOp,
    ) -> Result<(), TmirError> {
        let lhs = self.load_reg(block_idx, r1)?;
        let rhs = self.load_reg(block_idx, r2)?;
        let cmp = self.emit_with_result(
            block_idx,
            Inst::ICmp {
                op: predicate,
                ty: Ty::I64,
                lhs,
                rhs,
            },
        );
        // Zero-extend bool to i64 (0 or 1).
        let result = self.emit_with_result(
            block_idx,
            Inst::Cast {
                op: CastOp::ZExt,
                src_ty: Ty::Bool,
                dst_ty: Ty::I64,
                operand: cmp,
            },
        );
        self.store_reg_value(block_idx, rd, result)
    }

    pub(super) fn lower_boolean_binary(
        &mut self,
        block_idx: usize,
        rd: u8,
        r1: u8,
        r2: u8,
        op: BinOp,
    ) -> Result<(), TmirError> {
        let lhs = self.load_reg(block_idx, r1)?;
        let rhs = self.load_reg(block_idx, r2)?;
        let result = self.emit_with_result(
            block_idx,
            Inst::BinOp {
                op,
                ty: Ty::I64,
                lhs,
                rhs,
            },
        );
        self.store_reg_value(block_idx, rd, result)
    }

    pub(super) fn lower_not(&mut self, block_idx: usize, rd: u8, rs: u8) -> Result<(), TmirError> {
        let value = self.load_reg(block_idx, rs)?;
        let zero = self.emit_with_result(
            block_idx,
            Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(0),
            },
        );
        // NOT: value == 0
        let cmp = self.emit_with_result(
            block_idx,
            Inst::ICmp {
                op: ICmpOp::Eq,
                ty: Ty::I64,
                lhs: value,
                rhs: zero,
            },
        );
        let result = self.emit_with_result(
            block_idx,
            Inst::Cast {
                op: CastOp::ZExt,
                src_ty: Ty::Bool,
                dst_ty: Ty::I64,
                operand: cmp,
            },
        );
        self.store_reg_value(block_idx, rd, result)
    }

    pub(super) fn lower_implies(
        &mut self,
        block_idx: usize,
        rd: u8,
        r1: u8,
        r2: u8,
    ) -> Result<(), TmirError> {
        let lhs = self.load_reg(block_idx, r1)?;
        let rhs = self.load_reg(block_idx, r2)?;
        let zero = self.emit_with_result(
            block_idx,
            Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(0),
            },
        );
        // !lhs: lhs == 0
        let not_lhs = self.emit_with_result(
            block_idx,
            Inst::ICmp {
                op: ICmpOp::Eq,
                ty: Ty::I64,
                lhs,
                rhs: zero,
            },
        );
        // rhs != 0
        let rhs_bool = self.emit_with_result(
            block_idx,
            Inst::ICmp {
                op: ICmpOp::Ne,
                ty: Ty::I64,
                lhs: rhs,
                rhs: zero,
            },
        );
        // implies = !lhs || rhs
        let or_result = self.emit_with_result(
            block_idx,
            Inst::BinOp {
                op: BinOp::Or,
                ty: Ty::Bool,
                lhs: not_lhs,
                rhs: rhs_bool,
            },
        );
        let result = self.emit_with_result(
            block_idx,
            Inst::Cast {
                op: CastOp::ZExt,
                src_ty: Ty::Bool,
                dst_ty: Ty::I64,
                operand: or_result,
            },
        );
        self.store_reg_value(block_idx, rd, result)
    }

    pub(super) fn lower_equiv(
        &mut self,
        block_idx: usize,
        rd: u8,
        r1: u8,
        r2: u8,
    ) -> Result<(), TmirError> {
        let lhs = self.load_reg(block_idx, r1)?;
        let rhs = self.load_reg(block_idx, r2)?;
        // Equivalence on i64 booleans: lhs == rhs
        let cmp = self.emit_with_result(
            block_idx,
            Inst::ICmp {
                op: ICmpOp::Eq,
                ty: Ty::I64,
                lhs,
                rhs,
            },
        );
        let result = self.emit_with_result(
            block_idx,
            Inst::Cast {
                op: CastOp::ZExt,
                src_ty: Ty::Bool,
                dst_ty: Ty::I64,
                operand: cmp,
            },
        );
        self.store_reg_value(block_idx, rd, result)
    }

    pub(super) fn lower_cond_move(
        &mut self,
        block_idx: usize,
        rd: u8,
        cond: u8,
        rs: u8,
    ) -> Result<(), TmirError> {
        let cond_value = self.load_reg(block_idx, cond)?;
        let current = self.load_reg(block_idx, rd)?;
        let source = self.load_reg(block_idx, rs)?;
        let zero = self.emit_with_result(
            block_idx,
            Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(0),
            },
        );
        let cond_bool = self.emit_with_result(
            block_idx,
            Inst::ICmp {
                op: ICmpOp::Ne,
                ty: Ty::I64,
                lhs: cond_value,
                rhs: zero,
            },
        );
        let result = self.emit_with_result(
            block_idx,
            Inst::Select {
                ty: Ty::I64,
                cond: cond_bool,
                then_val: source,
                else_val: current,
            },
        );
        self.store_reg_value(block_idx, rd, result)
    }
}
