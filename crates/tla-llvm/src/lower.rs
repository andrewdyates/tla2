// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bytecode-to-LLVM IR lowering.

use crate::error::LlvmError;
use crate::ir::{LlvmFunction, LlvmModule, LlvmType, LlvmValue};
use std::collections::{BTreeSet, HashMap};
use tla_jit::abi::{JitCallOut, JitRuntimeErrorKind, JitStatus};
use tla_tir::bytecode::{BytecodeFunction, Opcode};

const STATUS_OFFSET: usize = std::mem::offset_of!(JitCallOut, status);
const VALUE_OFFSET: usize = std::mem::offset_of!(JitCallOut, value);
const ERR_KIND_OFFSET: usize = std::mem::offset_of!(JitCallOut, err_kind);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum LoweringMode {
    Invariant,
    NextState,
}

/// Result of lowering a bytecode function to LLVM IR.
#[derive(Debug)]
pub(crate) struct LoweringResult {
    pub(crate) function: LlvmFunction,
    /// Intrinsic declarations required by the lowered function.
    pub(crate) required_declarations: Vec<String>,
}

pub(crate) fn lower_invariant(
    func: &BytecodeFunction,
    func_name: &str,
) -> Result<LoweringResult, LlvmError> {
    lower_function(func, func_name, LoweringMode::Invariant)
}

pub(crate) fn lower_next_state(
    func: &BytecodeFunction,
    func_name: &str,
) -> Result<LoweringResult, LlvmError> {
    lower_function(func, func_name, LoweringMode::NextState)
}

/// Lower a bytecode invariant function and register on the module (with declarations).
pub(crate) fn lower_invariant_into(
    func: &BytecodeFunction,
    func_name: &str,
    module: &mut LlvmModule,
) -> Result<(), LlvmError> {
    let result = lower_invariant(func, func_name)?;
    for decl in result.required_declarations {
        module.add_declaration(decl);
    }
    module.add_function(result.function);
    Ok(())
}

/// Lower a next-state bytecode function and register on the module (with declarations).
pub(crate) fn lower_next_state_into(
    func: &BytecodeFunction,
    func_name: &str,
    module: &mut LlvmModule,
) -> Result<(), LlvmError> {
    let result = lower_next_state(func, func_name)?;
    for decl in result.required_declarations {
        module.add_declaration(decl);
    }
    module.add_function(result.function);
    Ok(())
}

fn lower_function(
    func: &BytecodeFunction,
    func_name: &str,
    mode: LoweringMode,
) -> Result<LoweringResult, LlvmError> {
    let mut context = LoweringContext::new(func, func_name, mode)?;
    context.lower_body(func)?;
    Ok(context.finish())
}

struct LoweringContext {
    llvm_func: LlvmFunction,
    instruction_len: usize,
    mode: LoweringMode,
    register_file: Vec<LlvmValue>,
    block_map: HashMap<usize, usize>,
    out_ptr: LlvmValue,
    state_in_ptr: LlvmValue,
    state_out_ptr: Option<LlvmValue>,
    next_aux_block: u32,
    /// Track which LLVM intrinsics are used so we can emit declarations.
    used_intrinsics: BTreeSet<&'static str>,
}

impl LoweringContext {
    fn new(
        bytecode_func: &BytecodeFunction,
        func_name: &str,
        mode: LoweringMode,
    ) -> Result<Self, LlvmError> {
        if bytecode_func.instructions.is_empty() {
            return Err(LlvmError::NotEligible {
                reason: "empty bytecode function".to_owned(),
            });
        }

        if bytecode_func.arity != 0 {
            return Err(LlvmError::NotEligible {
                reason: format!(
                    "LLVM lowering requires arity 0 entrypoints, got arity {}",
                    bytecode_func.arity
                ),
            });
        }

        let block_targets = collect_block_targets(&bytecode_func.instructions)?;

        let out_ptr = LlvmValue("%out".to_owned());
        let state_in_ptr = match mode {
            LoweringMode::Invariant => LlvmValue("%state".to_owned()),
            LoweringMode::NextState => LlvmValue("%state_in".to_owned()),
        };
        let state_out_ptr = match mode {
            LoweringMode::Invariant => None,
            LoweringMode::NextState => Some(LlvmValue("%state_out".to_owned())),
        };

        let params = match mode {
            LoweringMode::Invariant => vec![
                (out_ptr.clone(), LlvmType::Ptr),
                (state_in_ptr.clone(), LlvmType::Ptr),
                (LlvmValue("%state_len".to_owned()), LlvmType::I32),
            ],
            LoweringMode::NextState => vec![
                (out_ptr.clone(), LlvmType::Ptr),
                (state_in_ptr.clone(), LlvmType::Ptr),
                (
                    state_out_ptr.clone().ok_or_else(|| {
                        LlvmError::IrEmission(
                            "missing state_out parameter for next-state lowering".to_owned(),
                        )
                    })?,
                    LlvmType::Ptr,
                ),
                (LlvmValue("%state_len".to_owned()), LlvmType::I32),
            ],
        };

        let mut llvm_func = LlvmFunction {
            name: func_name.to_owned(),
            params,
            return_type: LlvmType::Void,
            blocks: Vec::new(),
            next_reg: 0,
        };

        let entry_block = llvm_func.new_block("bb_0");
        let mut block_map = HashMap::new();
        block_map.insert(0, entry_block);

        for target_pc in block_targets.into_iter().filter(|pc| *pc != 0) {
            let block_index = llvm_func.new_block(&block_name(target_pc));
            block_map.insert(target_pc, block_index);
        }

        let register_file =
            create_register_file(&mut llvm_func, entry_block, bytecode_func.max_register);

        Ok(Self {
            llvm_func,
            instruction_len: bytecode_func.instructions.len(),
            mode,
            register_file,
            block_map,
            out_ptr,
            state_in_ptr,
            state_out_ptr,
            next_aux_block: 0,
            used_intrinsics: BTreeSet::new(),
        })
    }

    fn finish(self) -> LoweringResult {
        let declarations = self
            .used_intrinsics
            .iter()
            .map(|name| intrinsic_declaration(name))
            .collect();
        LoweringResult {
            function: self.llvm_func,
            required_declarations: declarations,
        }
    }

    fn lower_body(&mut self, bytecode_func: &BytecodeFunction) -> Result<(), LlvmError> {
        let mut current_block = Some(self.block_index_for_pc(0)?);

        for (pc, opcode) in bytecode_func.instructions.iter().enumerate() {
            if let Some(&target_block) = self.block_map.get(&pc) {
                match current_block {
                    Some(block) if block != target_block => {
                        if !self.block_is_terminated(block)? {
                            let target_ref = self.block_ref(target_block)?;
                            self.llvm_func
                                .terminate(block, format!("br label {target_ref}"));
                        }
                        current_block = Some(target_block);
                    }
                    None => {
                        current_block = Some(target_block);
                    }
                    _ => {}
                }
            }

            let Some(block) = current_block else {
                continue;
            };

            current_block = self.lower_opcode(pc, opcode, block)?;

            if let Some(block) = current_block {
                if let Some(&next_block) = self.block_map.get(&(pc + 1)) {
                    if next_block != block && !self.block_is_terminated(block)? {
                        let next_ref = self.block_ref(next_block)?;
                        self.llvm_func
                            .terminate(block, format!("br label {next_ref}"));
                        current_block = Some(next_block);
                    }
                }
            }
        }

        if let Some(block) = current_block {
            if !self.block_is_terminated(block)? {
                return Err(LlvmError::IrEmission(format!(
                    "function {} reaches end of body without a terminator",
                    self.llvm_func.name
                )));
            }
        }

        Ok(())
    }

    fn lower_opcode(
        &mut self,
        pc: usize,
        opcode: &Opcode,
        block: usize,
    ) -> Result<Option<usize>, LlvmError> {
        match *opcode {
            Opcode::LoadImm { rd, value } => {
                self.store_reg_imm(block, rd, value)?;
                Ok(Some(block))
            }
            Opcode::LoadBool { rd, value } => {
                self.store_reg_imm(block, rd, i64::from(value))?;
                Ok(Some(block))
            }
            Opcode::LoadVar { rd, var_idx } => {
                self.lower_load_var(block, rd, var_idx)?;
                Ok(Some(block))
            }
            Opcode::LoadPrime { rd, var_idx } => match self.mode {
                LoweringMode::Invariant => Err(LlvmError::NotEligible {
                    reason: "LoadPrime requires next-state lowering".to_owned(),
                }),
                LoweringMode::NextState => {
                    let state_out_ptr = self.state_out_ptr()?.clone();
                    self.lower_load_from_state_ptr(block, &state_out_ptr, rd, var_idx)?;
                    Ok(Some(block))
                }
            },
            Opcode::StoreVar { var_idx, rs } => match self.mode {
                LoweringMode::Invariant => Err(LlvmError::NotEligible {
                    reason: "StoreVar requires next-state lowering".to_owned(),
                }),
                LoweringMode::NextState => {
                    self.lower_store_var(block, var_idx, rs)?;
                    Ok(Some(block))
                }
            },
            Opcode::Move { rd, rs } => {
                let value = self.load_reg(block, rs)?;
                self.store_reg_value(block, rd, &value)?;
                Ok(Some(block))
            }
            Opcode::AddInt { rd, r1, r2 } => {
                self.lower_checked_binary_overflow(block, rd, r1, r2, "llvm.sadd.with.overflow.i64")
            }
            Opcode::SubInt { rd, r1, r2 } => {
                self.lower_checked_binary_overflow(block, rd, r1, r2, "llvm.ssub.with.overflow.i64")
            }
            Opcode::MulInt { rd, r1, r2 } => {
                self.lower_checked_binary_overflow(block, rd, r1, r2, "llvm.smul.with.overflow.i64")
            }
            Opcode::IntDiv { rd, r1, r2 } => self.lower_checked_division(block, rd, r1, r2, "sdiv"),
            Opcode::ModInt { rd, r1, r2 } => self.lower_checked_division(block, rd, r1, r2, "srem"),
            Opcode::DivInt { rd, r1, r2 } => self.lower_real_division(block, rd, r1, r2),
            Opcode::NegInt { rd, rs } => self.lower_checked_negation(block, rd, rs),
            Opcode::Eq { rd, r1, r2 } => {
                self.lower_comparison(block, rd, r1, r2, "eq")?;
                Ok(Some(block))
            }
            Opcode::Neq { rd, r1, r2 } => {
                self.lower_comparison(block, rd, r1, r2, "ne")?;
                Ok(Some(block))
            }
            Opcode::LtInt { rd, r1, r2 } => {
                self.lower_comparison(block, rd, r1, r2, "slt")?;
                Ok(Some(block))
            }
            Opcode::LeInt { rd, r1, r2 } => {
                self.lower_comparison(block, rd, r1, r2, "sle")?;
                Ok(Some(block))
            }
            Opcode::GtInt { rd, r1, r2 } => {
                self.lower_comparison(block, rd, r1, r2, "sgt")?;
                Ok(Some(block))
            }
            Opcode::GeInt { rd, r1, r2 } => {
                self.lower_comparison(block, rd, r1, r2, "sge")?;
                Ok(Some(block))
            }
            Opcode::And { rd, r1, r2 } => {
                self.lower_boolean_binary(block, rd, r1, r2, "and")?;
                Ok(Some(block))
            }
            Opcode::Or { rd, r1, r2 } => {
                self.lower_boolean_binary(block, rd, r1, r2, "or")?;
                Ok(Some(block))
            }
            Opcode::Not { rd, rs } => {
                self.lower_not(block, rd, rs)?;
                Ok(Some(block))
            }
            Opcode::Implies { rd, r1, r2 } => {
                self.lower_implies(block, rd, r1, r2)?;
                Ok(Some(block))
            }
            Opcode::Equiv { rd, r1, r2 } => {
                self.lower_equiv(block, rd, r1, r2)?;
                Ok(Some(block))
            }
            Opcode::Jump { offset } => {
                let target_pc = self.resolve_forward_target(pc, offset, "Jump")?;
                let target_ref = self.block_ref_for_pc(target_pc)?;
                self.llvm_func
                    .terminate(block, format!("br label {target_ref}"));
                Ok(None)
            }
            Opcode::JumpTrue { rs, offset } => {
                let target_pc = self.resolve_forward_target(pc, offset, "JumpTrue")?;
                let fallthrough_pc = pc + 1;
                let cond = self.load_reg(block, rs)?;
                let cond_i1 = self
                    .llvm_func
                    .emit_with_result(block, &format!("icmp ne i64 {cond}, 0"));
                let target_ref = self.block_ref_for_pc(target_pc)?;
                let fallthrough_ref = self.block_ref_for_pc(fallthrough_pc)?;
                self.llvm_func.terminate(
                    block,
                    format!("br i1 {cond_i1}, label {target_ref}, label {fallthrough_ref}"),
                );
                Ok(None)
            }
            Opcode::JumpFalse { rs, offset } => {
                let target_pc = self.resolve_forward_target(pc, offset, "JumpFalse")?;
                let fallthrough_pc = pc + 1;
                let cond = self.load_reg(block, rs)?;
                let cond_i1 = self
                    .llvm_func
                    .emit_with_result(block, &format!("icmp ne i64 {cond}, 0"));
                let target_ref = self.block_ref_for_pc(target_pc)?;
                let fallthrough_ref = self.block_ref_for_pc(fallthrough_pc)?;
                self.llvm_func.terminate(
                    block,
                    format!("br i1 {cond_i1}, label {fallthrough_ref}, label {target_ref}"),
                );
                Ok(None)
            }
            Opcode::CondMove { rd, cond, rs } => {
                self.lower_cond_move(block, rd, cond, rs)?;
                Ok(Some(block))
            }
            Opcode::Ret { rs } => {
                self.emit_success_return(block, rs)?;
                Ok(None)
            }
            Opcode::Halt => {
                self.emit_runtime_error_and_return(
                    block,
                    JitRuntimeErrorKind::TypeMismatch,
                );
                Ok(None)
            }
            Opcode::Nop => Ok(Some(block)),
            other => Err(LlvmError::UnsupportedOpcode(format!("{other:?}"))),
        }
    }

    // =====================================================================
    // State variable access
    // =====================================================================

    fn lower_load_var(&mut self, block: usize, rd: u8, var_idx: u16) -> Result<(), LlvmError> {
        self.lower_load_from_state_ptr(block, &self.state_in_ptr.clone(), rd, var_idx)
    }

    fn lower_load_from_state_ptr(
        &mut self,
        block: usize,
        state_ptr: &LlvmValue,
        rd: u8,
        var_idx: u16,
    ) -> Result<(), LlvmError> {
        let ptr = self.emit_state_slot_ptr(block, state_ptr, var_idx);
        let value = self
            .llvm_func
            .emit_with_result(block, &format!("load i64, ptr {ptr}"));
        self.store_reg_value(block, rd, &value)
    }

    fn lower_store_var(&mut self, block: usize, var_idx: u16, rs: u8) -> Result<(), LlvmError> {
        let value = self.load_reg(block, rs)?;
        let state_out_ptr = self.state_out_ptr()?.clone();
        let ptr = self.emit_state_slot_ptr(block, &state_out_ptr, var_idx);
        self.llvm_func
            .emit(block, format!("store i64 {value}, ptr {ptr}"));
        Ok(())
    }

    // =====================================================================
    // Arithmetic with overflow/error checking
    // =====================================================================

    fn lower_checked_binary_overflow(
        &mut self,
        block: usize,
        rd: u8,
        r1: u8,
        r2: u8,
        intrinsic_name: &str,
    ) -> Result<Option<usize>, LlvmError> {
        self.use_intrinsic(intrinsic_name);
        let lhs = self.load_reg(block, r1)?;
        let rhs = self.load_reg(block, r2)?;
        let pair_type = overflow_pair_type();
        let result_pair = self.llvm_func.emit_with_result(
            block,
            &format!("call {pair_type} @{intrinsic_name}(i64 {lhs}, i64 {rhs})"),
        );
        let result = self
            .llvm_func
            .emit_with_result(block, &format!("extractvalue {pair_type} {result_pair}, 0"));
        let overflow = self
            .llvm_func
            .emit_with_result(block, &format!("extractvalue {pair_type} {result_pair}, 1"));

        let overflow_block = self.new_aux_block("overflow");
        let continue_block = self.new_aux_block("continue");
        let overflow_ref = self.block_ref(overflow_block)?;
        let continue_ref = self.block_ref(continue_block)?;

        self.llvm_func.terminate(
            block,
            format!("br i1 {overflow}, label {overflow_ref}, label {continue_ref}"),
        );
        self.emit_runtime_error_and_return(overflow_block, JitRuntimeErrorKind::ArithmeticOverflow);
        self.store_reg_value(continue_block, rd, &result)?;

        Ok(Some(continue_block))
    }

    fn lower_checked_negation(
        &mut self,
        block: usize,
        rd: u8,
        rs: u8,
    ) -> Result<Option<usize>, LlvmError> {
        self.use_intrinsic("llvm.ssub.with.overflow.i64");
        let value = self.load_reg(block, rs)?;
        let pair_type = overflow_pair_type();
        let result_pair = self.llvm_func.emit_with_result(
            block,
            &format!("call {pair_type} @llvm.ssub.with.overflow.i64(i64 0, i64 {value})"),
        );
        let result = self
            .llvm_func
            .emit_with_result(block, &format!("extractvalue {pair_type} {result_pair}, 0"));
        let overflow = self
            .llvm_func
            .emit_with_result(block, &format!("extractvalue {pair_type} {result_pair}, 1"));

        let overflow_block = self.new_aux_block("overflow");
        let continue_block = self.new_aux_block("continue");
        let overflow_ref = self.block_ref(overflow_block)?;
        let continue_ref = self.block_ref(continue_block)?;

        self.llvm_func.terminate(
            block,
            format!("br i1 {overflow}, label {overflow_ref}, label {continue_ref}"),
        );
        self.emit_runtime_error_and_return(overflow_block, JitRuntimeErrorKind::ArithmeticOverflow);
        self.store_reg_value(continue_block, rd, &result)?;

        Ok(Some(continue_block))
    }

    fn lower_checked_division(
        &mut self,
        block: usize,
        rd: u8,
        r1: u8,
        r2: u8,
        opcode: &str,
    ) -> Result<Option<usize>, LlvmError> {
        let lhs = self.load_reg(block, r1)?;
        let rhs = self.load_reg(block, r2)?;
        let is_zero = self
            .llvm_func
            .emit_with_result(block, &format!("icmp eq i64 {rhs}, 0"));

        let division_by_zero_block = self.new_aux_block("div_zero");
        let continue_block = self.new_aux_block("div_continue");
        let division_by_zero_ref = self.block_ref(division_by_zero_block)?;
        let continue_ref = self.block_ref(continue_block)?;

        self.llvm_func.terminate(
            block,
            format!("br i1 {is_zero}, label {division_by_zero_ref}, label {continue_ref}"),
        );
        self.emit_runtime_error_and_return(
            division_by_zero_block,
            JitRuntimeErrorKind::DivisionByZero,
        );

        let result = self
            .llvm_func
            .emit_with_result(continue_block, &format!("{opcode} i64 {lhs}, {rhs}"));
        self.store_reg_value(continue_block, rd, &result)?;

        Ok(Some(continue_block))
    }

    /// Lower TLA+ real division (a/b).
    ///
    /// TLA+ `/` on integers requires exact division. If `a % b != 0`, it is
    /// a runtime error. We emit: check zero, check exact, then sdiv.
    fn lower_real_division(
        &mut self,
        block: usize,
        rd: u8,
        r1: u8,
        r2: u8,
    ) -> Result<Option<usize>, LlvmError> {
        let lhs = self.load_reg(block, r1)?;
        let rhs = self.load_reg(block, r2)?;

        // Check division by zero
        let is_zero = self
            .llvm_func
            .emit_with_result(block, &format!("icmp eq i64 {rhs}, 0"));

        let div_zero_block = self.new_aux_block("realdiv_zero");
        let check_exact_block = self.new_aux_block("realdiv_check");
        let div_zero_ref = self.block_ref(div_zero_block)?;
        let check_exact_ref = self.block_ref(check_exact_block)?;

        self.llvm_func.terminate(
            block,
            format!("br i1 {is_zero}, label {div_zero_ref}, label {check_exact_ref}"),
        );
        self.emit_runtime_error_and_return(div_zero_block, JitRuntimeErrorKind::DivisionByZero);

        // Check exactness: a % b must be 0
        let remainder = self
            .llvm_func
            .emit_with_result(check_exact_block, &format!("srem i64 {lhs}, {rhs}"));
        let is_inexact = self
            .llvm_func
            .emit_with_result(check_exact_block, &format!("icmp ne i64 {remainder}, 0"));

        let inexact_block = self.new_aux_block("realdiv_inexact");
        let continue_block = self.new_aux_block("realdiv_continue");
        let inexact_ref = self.block_ref(inexact_block)?;
        let continue_ref = self.block_ref(continue_block)?;

        self.llvm_func.terminate(
            check_exact_block,
            format!("br i1 {is_inexact}, label {inexact_ref}, label {continue_ref}"),
        );
        // Inexact real division is a type mismatch (non-integer result)
        self.emit_runtime_error_and_return(inexact_block, JitRuntimeErrorKind::TypeMismatch);

        let result = self
            .llvm_func
            .emit_with_result(continue_block, &format!("sdiv i64 {lhs}, {rhs}"));
        self.store_reg_value(continue_block, rd, &result)?;

        Ok(Some(continue_block))
    }

    // =====================================================================
    // Comparison and boolean operations
    // =====================================================================

    fn lower_comparison(
        &mut self,
        block: usize,
        rd: u8,
        r1: u8,
        r2: u8,
        predicate: &str,
    ) -> Result<(), LlvmError> {
        let lhs = self.load_reg(block, r1)?;
        let rhs = self.load_reg(block, r2)?;
        let cmp = self
            .llvm_func
            .emit_with_result(block, &format!("icmp {predicate} i64 {lhs}, {rhs}"));
        let result = self
            .llvm_func
            .emit_with_result(block, &format!("zext i1 {cmp} to i64"));
        self.store_reg_value(block, rd, &result)
    }

    fn lower_boolean_binary(
        &mut self,
        block: usize,
        rd: u8,
        r1: u8,
        r2: u8,
        opcode: &str,
    ) -> Result<(), LlvmError> {
        let lhs = self.load_reg(block, r1)?;
        let rhs = self.load_reg(block, r2)?;
        let result = self
            .llvm_func
            .emit_with_result(block, &format!("{opcode} i64 {lhs}, {rhs}"));
        self.store_reg_value(block, rd, &result)
    }

    fn lower_not(&mut self, block: usize, rd: u8, rs: u8) -> Result<(), LlvmError> {
        let value = self.load_reg(block, rs)?;
        let cmp = self
            .llvm_func
            .emit_with_result(block, &format!("icmp eq i64 {value}, 0"));
        let result = self
            .llvm_func
            .emit_with_result(block, &format!("zext i1 {cmp} to i64"));
        self.store_reg_value(block, rd, &result)
    }

    fn lower_implies(&mut self, block: usize, rd: u8, r1: u8, r2: u8) -> Result<(), LlvmError> {
        let lhs = self.load_reg(block, r1)?;
        let rhs = self.load_reg(block, r2)?;
        let not_lhs = self
            .llvm_func
            .emit_with_result(block, &format!("icmp eq i64 {lhs}, 0"));
        let rhs_i1 = self
            .llvm_func
            .emit_with_result(block, &format!("icmp ne i64 {rhs}, 0"));
        let or_result = self
            .llvm_func
            .emit_with_result(block, &format!("or i1 {not_lhs}, {rhs_i1}"));
        let result = self
            .llvm_func
            .emit_with_result(block, &format!("zext i1 {or_result} to i64"));
        self.store_reg_value(block, rd, &result)
    }

    fn lower_equiv(&mut self, block: usize, rd: u8, r1: u8, r2: u8) -> Result<(), LlvmError> {
        let lhs = self.load_reg(block, r1)?;
        let rhs = self.load_reg(block, r2)?;
        let cmp = self
            .llvm_func
            .emit_with_result(block, &format!("icmp eq i64 {lhs}, {rhs}"));
        let result = self
            .llvm_func
            .emit_with_result(block, &format!("zext i1 {cmp} to i64"));
        self.store_reg_value(block, rd, &result)
    }

    fn lower_cond_move(&mut self, block: usize, rd: u8, cond: u8, rs: u8) -> Result<(), LlvmError> {
        let cond_value = self.load_reg(block, cond)?;
        let current = self.load_reg(block, rd)?;
        let source = self.load_reg(block, rs)?;
        let cond_i1 = self
            .llvm_func
            .emit_with_result(block, &format!("icmp ne i64 {cond_value}, 0"));
        let result = self.llvm_func.emit_with_result(
            block,
            &format!("select i1 {cond_i1}, i64 {source}, i64 {current}"),
        );
        self.store_reg_value(block, rd, &result)
    }

    // =====================================================================
    // Return/error emission
    // =====================================================================

    fn emit_success_return(&mut self, block: usize, rs: u8) -> Result<(), LlvmError> {
        let result = self.load_reg(block, rs)?;
        let status_ptr = self.emit_out_field_ptr(block, STATUS_OFFSET);
        self.llvm_func.emit(
            block,
            format!("store i8 {}, ptr {status_ptr}", JitStatus::Ok as u8),
        );
        let value_ptr = self.emit_out_field_ptr(block, VALUE_OFFSET);
        self.llvm_func
            .emit(block, format!("store i64 {result}, ptr {value_ptr}"));
        self.llvm_func.terminate(block, "ret void".to_owned());
        Ok(())
    }

    fn emit_runtime_error_and_return(&mut self, block: usize, kind: JitRuntimeErrorKind) {
        let status_ptr = self.emit_out_field_ptr(block, STATUS_OFFSET);
        self.llvm_func.emit(
            block,
            format!(
                "store i8 {}, ptr {status_ptr}",
                JitStatus::RuntimeError as u8
            ),
        );
        let err_kind_ptr = self.emit_out_field_ptr(block, ERR_KIND_OFFSET);
        self.llvm_func.emit(
            block,
            format!("store i8 {}, ptr {err_kind_ptr}", kind as u8),
        );
        self.llvm_func.terminate(block, "ret void".to_owned());
    }

    // =====================================================================
    // Address computation helpers
    // =====================================================================

    fn emit_state_slot_ptr(
        &mut self,
        block: usize,
        state_ptr: &LlvmValue,
        var_idx: u16,
    ) -> LlvmValue {
        self.llvm_func.emit_with_result(
            block,
            &format!("getelementptr i64, ptr {state_ptr}, i32 {var_idx}"),
        )
    }

    fn emit_out_field_ptr(&mut self, block: usize, offset: usize) -> LlvmValue {
        self.llvm_func.emit_with_result(
            block,
            &format!("getelementptr i8, ptr {}, i64 {offset}", self.out_ptr),
        )
    }

    // =====================================================================
    // Register file access
    // =====================================================================

    fn load_reg(&mut self, block: usize, reg: u8) -> Result<LlvmValue, LlvmError> {
        let reg_ptr = self.reg_ptr(reg)?.clone();
        Ok(self
            .llvm_func
            .emit_with_result(block, &format!("load i64, ptr {reg_ptr}")))
    }

    fn store_reg_imm(&mut self, block: usize, reg: u8, value: i64) -> Result<(), LlvmError> {
        let reg_ptr = self.reg_ptr(reg)?.clone();
        self.llvm_func
            .emit(block, format!("store i64 {value}, ptr {reg_ptr}"));
        Ok(())
    }

    fn store_reg_value(
        &mut self,
        block: usize,
        reg: u8,
        value: &LlvmValue,
    ) -> Result<(), LlvmError> {
        let reg_ptr = self.reg_ptr(reg)?.clone();
        self.llvm_func
            .emit(block, format!("store i64 {value}, ptr {reg_ptr}"));
        Ok(())
    }

    fn reg_ptr(&self, reg: u8) -> Result<&LlvmValue, LlvmError> {
        self.register_file.get(usize::from(reg)).ok_or_else(|| {
            LlvmError::IrEmission(format!(
                "register r{reg} is outside allocated register file (size={})",
                self.register_file.len()
            ))
        })
    }

    // =====================================================================
    // Block/PC resolution
    // =====================================================================

    fn resolve_forward_target(
        &self,
        pc: usize,
        offset: i32,
        opcode_name: &str,
    ) -> Result<usize, LlvmError> {
        let target = resolve_target(pc, offset)?;
        if target <= pc {
            return Err(LlvmError::NotEligible {
                reason: format!(
                    "{opcode_name} at pc {pc} must target a later instruction (offset {offset})"
                ),
            });
        }
        if target >= self.instruction_len {
            return Err(LlvmError::NotEligible {
                reason: format!(
                    "{opcode_name} at pc {pc} targets {target}, outside body len {}",
                    self.instruction_len
                ),
            });
        }
        Ok(target)
    }

    fn block_index_for_pc(&self, pc: usize) -> Result<usize, LlvmError> {
        self.block_map.get(&pc).copied().ok_or_else(|| {
            LlvmError::IrEmission(format!("missing basic block for bytecode pc {pc}"))
        })
    }

    fn block_ref_for_pc(&self, pc: usize) -> Result<String, LlvmError> {
        let block = self.block_index_for_pc(pc)?;
        self.block_ref(block)
    }

    fn block_ref(&self, block: usize) -> Result<String, LlvmError> {
        let name = &self
            .llvm_func
            .blocks
            .get(block)
            .ok_or_else(|| LlvmError::IrEmission(format!("missing LLVM block index {block}")))?
            .name;
        Ok(format!("%{name}"))
    }

    fn block_is_terminated(&self, block: usize) -> Result<bool, LlvmError> {
        Ok(self
            .llvm_func
            .blocks
            .get(block)
            .ok_or_else(|| LlvmError::IrEmission(format!("missing LLVM block index {block}")))?
            .is_terminated())
    }

    fn new_aux_block(&mut self, prefix: &str) -> usize {
        let name = format!("{prefix}_{}", self.next_aux_block);
        self.next_aux_block += 1;
        self.llvm_func.new_block(&name)
    }

    fn state_out_ptr(&self) -> Result<&LlvmValue, LlvmError> {
        self.state_out_ptr.as_ref().ok_or_else(|| {
            LlvmError::IrEmission(
                "state_out pointer requested outside next-state lowering".to_owned(),
            )
        })
    }

    fn use_intrinsic(&mut self, name: &str) {
        // Map to static strings for the intrinsics we support
        let static_name = match name {
            "llvm.sadd.with.overflow.i64" => "llvm.sadd.with.overflow.i64",
            "llvm.ssub.with.overflow.i64" => "llvm.ssub.with.overflow.i64",
            "llvm.smul.with.overflow.i64" => "llvm.smul.with.overflow.i64",
            _ => return,
        };
        self.used_intrinsics.insert(static_name);
    }
}

// =========================================================================
// Free functions
// =========================================================================

fn create_register_file(
    llvm_func: &mut LlvmFunction,
    entry_block: usize,
    max_register: u8,
) -> Vec<LlvmValue> {
    (0..=max_register)
        .map(|reg| {
            let reg_ptr = LlvmValue(format!("%reg_{reg}"));
            llvm_func.emit(entry_block, format!("{reg_ptr} = alloca i64"));
            reg_ptr
        })
        .collect()
}

fn collect_block_targets(instructions: &[Opcode]) -> Result<BTreeSet<usize>, LlvmError> {
    let mut targets = BTreeSet::new();
    targets.insert(0);

    for (pc, opcode) in instructions.iter().enumerate() {
        match *opcode {
            Opcode::Jump { offset } => {
                let target = validate_forward_target(pc, offset, instructions.len(), "Jump")?;
                targets.insert(target);
            }
            Opcode::JumpTrue { offset, .. } => {
                let target = validate_forward_target(pc, offset, instructions.len(), "JumpTrue")?;
                let fallthrough = pc + 1;
                if fallthrough >= instructions.len() {
                    return Err(LlvmError::NotEligible {
                        reason: format!("JumpTrue at pc {pc} has no fallthrough instruction"),
                    });
                }
                targets.insert(target);
                targets.insert(fallthrough);
            }
            Opcode::JumpFalse { offset, .. } => {
                let target = validate_forward_target(pc, offset, instructions.len(), "JumpFalse")?;
                let fallthrough = pc + 1;
                if fallthrough >= instructions.len() {
                    return Err(LlvmError::NotEligible {
                        reason: format!("JumpFalse at pc {pc} has no fallthrough instruction"),
                    });
                }
                targets.insert(target);
                targets.insert(fallthrough);
            }
            _ => {}
        }
    }

    Ok(targets)
}

fn validate_forward_target(
    pc: usize,
    offset: i32,
    len: usize,
    opcode_name: &str,
) -> Result<usize, LlvmError> {
    let target = resolve_target(pc, offset)?;
    if target <= pc {
        return Err(LlvmError::NotEligible {
            reason: format!(
                "{opcode_name} at pc {pc} must target a later instruction (offset {offset})"
            ),
        });
    }
    if target >= len {
        return Err(LlvmError::NotEligible {
            reason: format!("{opcode_name} at pc {pc} targets {target}, outside body len {len}"),
        });
    }
    Ok(target)
}

fn resolve_target(pc: usize, offset: i32) -> Result<usize, LlvmError> {
    let target = (pc as i64) + i64::from(offset);
    usize::try_from(target).map_err(|_| LlvmError::NotEligible {
        reason: format!("jump target before start of function: pc {pc}, offset {offset}"),
    })
}

fn block_name(pc: usize) -> String {
    format!("bb_{pc}")
}

fn overflow_pair_type() -> String {
    LlvmType::Struct(vec![LlvmType::I64, LlvmType::I1]).to_string()
}

/// Generate the LLVM IR declaration for a known intrinsic.
fn intrinsic_declaration(name: &str) -> String {
    let pair_type = overflow_pair_type();
    match name {
        "llvm.sadd.with.overflow.i64" | "llvm.ssub.with.overflow.i64"
        | "llvm.smul.with.overflow.i64" => {
            format!("declare {pair_type} @{name}(i64, i64)")
        }
        other => format!("; unknown intrinsic: {other}"),
    }
}
