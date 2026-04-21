// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Inter-function call lowering.

use crate::TmirError;
use tmir::inst::*;
use tmir::ty::Ty;
use tmir::Constant;

use super::Ctx;

impl<'cp> Ctx<'cp> {
    // =====================================================================
    // Inter-function Call
    // =====================================================================

    /// Lower `Opcode::Call { rd, op_idx, args_start, argc }`.
    ///
    /// Loads `argc` arguments from consecutive registers starting at
    /// `args_start`, emits a tMIR `Inst::Call` to the callee's FuncId,
    /// and stores the i64 result into register `rd`.
    pub(super) fn lower_call(
        &mut self,
        block_idx: usize,
        rd: u8,
        op_idx: u16,
        args_start: u8,
        argc: u8,
    ) -> Result<(), TmirError> {
        // Register the call target and get its tMIR FuncId.
        let callee_func_id = self.register_call_target(op_idx);

        // Build the call arguments: context pointers first, then user args.
        // Callee signature matches the entrypoint context (out_ptr, state_in,
        // [state_out,] state_len) plus its own i64 arguments.
        let mut call_args = vec![self.out_ptr, self.state_in_ptr];
        if let Some(sop) = self.state_out_ptr {
            call_args.push(sop);
        }
        // state_len: we don't track a ValueId for it in the callee case,
        // so emit a dummy constant 0 for state_len (unused by callee ops,
        // but must be present to match the signature).
        let state_len_val = self.emit_with_result(
            block_idx,
            Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(0),
            },
        );
        call_args.push(state_len_val);

        // Load user arguments from the register file.
        for i in 0..argc {
            let reg = args_start.checked_add(i).ok_or_else(|| {
                TmirError::Emission(format!(
                    "Call argument register overflow: args_start={args_start} + i={i}"
                ))
            })?;
            let val = self.load_reg(block_idx, reg)?;
            call_args.push(val);
        }

        // Emit the tMIR Call instruction.
        let result = self.emit_with_result(
            block_idx,
            Inst::Call {
                callee: callee_func_id,
                args: call_args,
            },
        );

        // Store the result into the destination register.
        self.store_reg_value(block_idx, rd, result)?;

        Ok(())
    }
}
