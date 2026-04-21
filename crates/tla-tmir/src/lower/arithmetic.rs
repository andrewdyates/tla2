// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Arithmetic lowering: overflow-checked Add, Sub, Mul, Neg, Div, Mod, real division.

use crate::TmirError;
use tla_jit::abi::JitRuntimeErrorKind;
use tmir::inst::*;
use tmir::ty::Ty;
use tmir::{Constant, InstrNode};

use super::Ctx;

impl<'cp> Ctx<'cp> {
    pub(super) fn lower_checked_binary_overflow(
        &mut self,
        block_idx: usize,
        rd: u8,
        r1: u8,
        r2: u8,
        overflow_op: OverflowOp,
    ) -> Result<Option<usize>, TmirError> {
        let lhs = self.load_reg(block_idx, r1)?;
        let rhs = self.load_reg(block_idx, r2)?;

        // Emit overflow-checked operation: returns (result, overflow_flag).
        let result = self.alloc_value();
        let overflow_flag = self.alloc_value();
        self.emit(
            block_idx,
            InstrNode::new(Inst::Overflow {
                op: overflow_op,
                ty: Ty::I64,
                lhs,
                rhs,
            })
            .with_result(result)
            .with_result(overflow_flag),
        );

        let overflow_block = self.new_aux_block("overflow");
        let continue_block = self.new_aux_block("continue");

        let overflow_id = self.block_id_of(overflow_block);
        let continue_id = self.block_id_of(continue_block);

        self.emit(
            block_idx,
            InstrNode::new(Inst::CondBr {
                cond: overflow_flag,
                then_target: overflow_id,
                then_args: vec![],
                else_target: continue_id,
                else_args: vec![],
            }),
        );

        self.emit_runtime_error_and_return(overflow_block, JitRuntimeErrorKind::ArithmeticOverflow);
        self.store_reg_value(continue_block, rd, result)?;

        Ok(Some(continue_block))
    }

    pub(super) fn lower_checked_negation(
        &mut self,
        block_idx: usize,
        rd: u8,
        rs: u8,
    ) -> Result<Option<usize>, TmirError> {
        let value = self.load_reg(block_idx, rs)?;

        // Negate via 0 - value with overflow check.
        let zero = self.emit_with_result(
            block_idx,
            Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(0),
            },
        );

        let result = self.alloc_value();
        let overflow_flag = self.alloc_value();
        self.emit(
            block_idx,
            InstrNode::new(Inst::Overflow {
                op: OverflowOp::SubOverflow,
                ty: Ty::I64,
                lhs: zero,
                rhs: value,
            })
            .with_result(result)
            .with_result(overflow_flag),
        );

        let overflow_block = self.new_aux_block("overflow");
        let continue_block = self.new_aux_block("continue");

        let overflow_id = self.block_id_of(overflow_block);
        let continue_id = self.block_id_of(continue_block);

        self.emit(
            block_idx,
            InstrNode::new(Inst::CondBr {
                cond: overflow_flag,
                then_target: overflow_id,
                then_args: vec![],
                else_target: continue_id,
                else_args: vec![],
            }),
        );

        self.emit_runtime_error_and_return(overflow_block, JitRuntimeErrorKind::ArithmeticOverflow);
        self.store_reg_value(continue_block, rd, result)?;

        Ok(Some(continue_block))
    }

    pub(super) fn lower_checked_division(
        &mut self,
        block_idx: usize,
        rd: u8,
        r1: u8,
        r2: u8,
        use_sdiv: bool, // true = sdiv, false = srem
    ) -> Result<Option<usize>, TmirError> {
        let lhs = self.load_reg(block_idx, r1)?;
        let rhs = self.load_reg(block_idx, r2)?;

        // Check for division by zero: rhs == 0
        let zero = self.emit_with_result(
            block_idx,
            Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(0),
            },
        );
        let is_zero = self.emit_with_result(
            block_idx,
            Inst::ICmp {
                op: ICmpOp::Eq,
                ty: Ty::I64,
                lhs: rhs,
                rhs: zero,
            },
        );

        let div_zero_block = self.new_aux_block("div_zero");
        let continue_block = self.new_aux_block("div_continue");

        let div_zero_id = self.block_id_of(div_zero_block);
        let continue_id = self.block_id_of(continue_block);

        self.emit(
            block_idx,
            InstrNode::new(Inst::CondBr {
                cond: is_zero,
                then_target: div_zero_id,
                then_args: vec![],
                else_target: continue_id,
                else_args: vec![],
            }),
        );

        self.emit_runtime_error_and_return(div_zero_block, JitRuntimeErrorKind::DivisionByZero);

        let op = if use_sdiv { BinOp::SDiv } else { BinOp::SRem };
        let result = self.emit_with_result(
            continue_block,
            Inst::BinOp {
                op,
                ty: Ty::I64,
                lhs,
                rhs,
            },
        );
        self.store_reg_value(continue_block, rd, result)?;

        Ok(Some(continue_block))
    }

    /// Lower TLA+ real division (a/b).
    ///
    /// TLA+ `/` on integers requires exact division. If `a % b != 0`, it is
    /// a runtime error. We emit: check zero, check exact, then sdiv.
    pub(super) fn lower_real_division(
        &mut self,
        block_idx: usize,
        rd: u8,
        r1: u8,
        r2: u8,
    ) -> Result<Option<usize>, TmirError> {
        let lhs = self.load_reg(block_idx, r1)?;
        let rhs = self.load_reg(block_idx, r2)?;

        // Check division by zero
        let zero = self.emit_with_result(
            block_idx,
            Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(0),
            },
        );
        let is_zero = self.emit_with_result(
            block_idx,
            Inst::ICmp {
                op: ICmpOp::Eq,
                ty: Ty::I64,
                lhs: rhs,
                rhs: zero,
            },
        );

        let div_zero_block = self.new_aux_block("realdiv_zero");
        let check_exact_block = self.new_aux_block("realdiv_check");

        let div_zero_id = self.block_id_of(div_zero_block);
        let check_exact_id = self.block_id_of(check_exact_block);

        self.emit(
            block_idx,
            InstrNode::new(Inst::CondBr {
                cond: is_zero,
                then_target: div_zero_id,
                then_args: vec![],
                else_target: check_exact_id,
                else_args: vec![],
            }),
        );
        self.emit_runtime_error_and_return(div_zero_block, JitRuntimeErrorKind::DivisionByZero);

        // Check exactness: a % b must be 0
        let remainder = self.emit_with_result(
            check_exact_block,
            Inst::BinOp {
                op: BinOp::SRem,
                ty: Ty::I64,
                lhs,
                rhs,
            },
        );
        let zero2 = self.emit_with_result(
            check_exact_block,
            Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(0),
            },
        );
        let is_inexact = self.emit_with_result(
            check_exact_block,
            Inst::ICmp {
                op: ICmpOp::Ne,
                ty: Ty::I64,
                lhs: remainder,
                rhs: zero2,
            },
        );

        let inexact_block = self.new_aux_block("realdiv_inexact");
        let continue_block = self.new_aux_block("realdiv_continue");

        let inexact_id = self.block_id_of(inexact_block);
        let continue_id = self.block_id_of(continue_block);

        self.emit(
            check_exact_block,
            InstrNode::new(Inst::CondBr {
                cond: is_inexact,
                then_target: inexact_id,
                then_args: vec![],
                else_target: continue_id,
                else_args: vec![],
            }),
        );
        self.emit_runtime_error_and_return(inexact_block, JitRuntimeErrorKind::TypeMismatch);

        let result = self.emit_with_result(
            continue_block,
            Inst::BinOp {
                op: BinOp::SDiv,
                ty: Ty::I64,
                lhs,
                rhs,
            },
        );
        self.store_reg_value(continue_block, rd, result)?;

        Ok(Some(continue_block))
    }
}
