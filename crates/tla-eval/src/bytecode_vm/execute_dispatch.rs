// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Bytecode VM dispatch loop.
//!
//! Owns `execute_with_regs` and the exhaustive opcode `match` that routes
//! into family-specific modules. Extracted from `execute.rs` per #3611.

use tla_tir::bytecode::{BytecodeFunction, ConstantPool, Opcode};
use tla_value::Value;

use super::execute::{BytecodeVm, VmError};
use super::execute_loops::{
    choose_begin, choose_next, exists_begin, exists_next, forall_begin, forall_next,
    func_def_begin, loop_next, set_builder_begin, set_filter_begin, LoopAction, LoopState,
};

/// Outcome of dispatching a single opcode.
pub(super) enum DispatchOutcome {
    /// Advance PC by 1.
    Continue,
    /// Jump to the given PC.
    Jump(usize),
    /// Return a value from the current function.
    Return(Value),
}

impl<'a> BytecodeVm<'a> {
    /// Execute a bytecode function with a pre-initialized register file.
    ///
    /// Used by `Call` to pass arguments in callee registers 0..argc.
    pub(super) fn execute_with_regs(
        &mut self,
        func: &BytecodeFunction,
        constants: &ConstantPool,
        regs: &mut Vec<Value>,
    ) -> Result<Value, VmError> {
        let mut iter_stack: Vec<LoopState> = Vec::new();
        /// Dispatch a loop helper that returns `LoopAction`, applying jump or fall-through.
        macro_rules! dispatch_loop {
            ($pc:ident, $handler:path $(, $arg:expr )* $(,)?) => {{
                let action = $handler(regs, &mut iter_stack, $pc, $($arg),*)?;
                match action {
                    LoopAction::Continue => {}
                    LoopAction::Jump(target) => {
                        $pc = target;
                        continue;
                    }
                }
            }};
        }
        let instructions = &func.instructions;
        let mut pc: usize = 0;

        while pc < instructions.len() {
            match &instructions[pc] {
                // === Scalar/control family ===
                Opcode::LoadImm { .. }
                | Opcode::LoadBool { .. }
                | Opcode::LoadConst { .. }
                | Opcode::LoadVar { .. }
                | Opcode::LoadPrime { .. }
                | Opcode::StoreVar { .. }
                | Opcode::Move { .. }
                | Opcode::AddInt { .. }
                | Opcode::SubInt { .. }
                | Opcode::MulInt { .. }
                | Opcode::DivInt { .. }
                | Opcode::IntDiv { .. }
                | Opcode::ModInt { .. }
                | Opcode::NegInt { .. }
                | Opcode::PowInt { .. }
                | Opcode::Eq { .. }
                | Opcode::Neq { .. }
                | Opcode::LtInt { .. }
                | Opcode::LeInt { .. }
                | Opcode::GtInt { .. }
                | Opcode::GeInt { .. }
                | Opcode::And { .. }
                | Opcode::Or { .. }
                | Opcode::Not { .. }
                | Opcode::Implies { .. }
                | Opcode::Equiv { .. }
                | Opcode::Jump { .. }
                | Opcode::JumpTrue { .. }
                | Opcode::JumpFalse { .. }
                | Opcode::Call { .. }
                | Opcode::ValueApply { .. }
                | Opcode::CallExternal { .. }
                | Opcode::Ret { .. }
                | Opcode::CondMove { .. }
                | Opcode::Unchanged { .. } => {
                    match self.execute_scalar_opcode(&instructions[pc], constants, regs, pc)? {
                        DispatchOutcome::Continue => {}
                        DispatchOutcome::Jump(target) => {
                            pc = target;
                            continue;
                        }
                        DispatchOutcome::Return(val) => return Ok(val),
                    }
                }

                // === Compound-value family ===
                Opcode::SetEnum { .. }
                | Opcode::SetIn { .. }
                | Opcode::SetUnion { .. }
                | Opcode::SetIntersect { .. }
                | Opcode::SetDiff { .. }
                | Opcode::Subseteq { .. }
                | Opcode::Powerset { .. }
                | Opcode::BigUnion { .. }
                | Opcode::KSubset { .. }
                | Opcode::Range { .. }
                | Opcode::RecordNew { .. }
                | Opcode::RecordGet { .. }
                | Opcode::FuncApply { .. }
                | Opcode::Domain { .. }
                | Opcode::FuncExcept { .. }
                | Opcode::TupleNew { .. }
                | Opcode::TupleGet { .. }
                | Opcode::SeqNew { .. }
                | Opcode::StrConcat { .. }
                | Opcode::FuncDef { .. }
                | Opcode::FuncSet { .. }
                | Opcode::RecordSet { .. }
                | Opcode::Times { .. }
                | Opcode::MakeClosure { .. }
                | Opcode::Concat { .. }
                | Opcode::CallBuiltin { .. } => {
                    self.execute_compound_opcode(&instructions[pc], constants, regs)?;
                }

                // === Quantifier/loop family (delegated to execute_loops.rs) ===
                Opcode::ForallBegin {
                    rd,
                    r_binding,
                    r_domain,
                    loop_end,
                } => dispatch_loop!(pc, forall_begin, *rd, *r_binding, *r_domain, *loop_end),
                Opcode::ForallNext {
                    rd,
                    r_binding,
                    r_body,
                    loop_begin,
                } => dispatch_loop!(pc, forall_next, *rd, *r_binding, *r_body, *loop_begin),
                Opcode::ExistsBegin {
                    rd,
                    r_binding,
                    r_domain,
                    loop_end,
                } => dispatch_loop!(pc, exists_begin, *rd, *r_binding, *r_domain, *loop_end),
                Opcode::ExistsNext {
                    rd,
                    r_binding,
                    r_body,
                    loop_begin,
                } => dispatch_loop!(pc, exists_next, *rd, *r_binding, *r_body, *loop_begin),
                Opcode::SetFilterBegin {
                    rd,
                    r_binding,
                    r_domain,
                    loop_end,
                } => dispatch_loop!(pc, set_filter_begin, *rd, *r_binding, *r_domain, *loop_end),
                Opcode::SetBuilderBegin {
                    rd,
                    r_binding,
                    r_domain,
                    loop_end,
                } => dispatch_loop!(pc, set_builder_begin, *rd, *r_binding, *r_domain, *loop_end),
                Opcode::FuncDefBegin {
                    rd,
                    r_binding,
                    r_domain,
                    loop_end,
                } => dispatch_loop!(pc, func_def_begin, *rd, *r_binding, *r_domain, *loop_end),
                Opcode::LoopNext {
                    r_binding,
                    r_body,
                    loop_begin,
                } => dispatch_loop!(pc, loop_next, *r_binding, *r_body, *loop_begin),
                Opcode::ChooseBegin {
                    rd,
                    r_binding,
                    r_domain,
                    loop_end: _,
                } => dispatch_loop!(pc, choose_begin, *rd, *r_binding, *r_domain),
                Opcode::ChooseNext {
                    rd,
                    r_binding,
                    r_body,
                    loop_begin,
                } => dispatch_loop!(pc, choose_next, *rd, *r_binding, *r_body, *loop_begin),

                // === Trivial / Control ===
                Opcode::SetPrimeMode { enable } => {
                    self.prime_mode = *enable;
                }
                Opcode::Nop => {}
                Opcode::Halt => return Err(VmError::Halted),
            }

            pc += 1;
        }

        Ok(regs[0].clone())
    }
}
