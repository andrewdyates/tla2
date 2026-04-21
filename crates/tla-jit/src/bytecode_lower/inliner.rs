// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bytecode inliner for JIT compilation.
//!
//! Inlines callee bytecode into the caller at `Call` sites so that the
//! resulting function no longer contains `Call` opcodes and can pass the
//! JIT eligibility gate.
//!
//! # Strategy
//!
//! For each `Call { rd, op_idx, args_start, argc }`:
//! 1. Look up the callee `BytecodeFunction` by `op_idx`
//! 2. Offset all callee registers by `caller_max_reg + 1` to avoid collisions
//! 3. Copy arguments: `Move { rd: remapped_param_i, rs: args_start + i }`
//! 4. Inline callee instructions with remapped registers and jump offsets
//! 5. Replace each `Ret { rs }` with `Move { rd: call_rd, rs: remapped_rs }`
//!    followed by `Jump` to the continuation point after the inlined block
//!
//! # Nested inlining
//!
//! After a first inlining pass, the result may still contain `Call` opcodes
//! (from callees that themselves call other operators). We repeat up to
//! `max_depth` passes.

use std::collections::HashMap;
use tla_tir::bytecode::{BytecodeFunction, Opcode};

/// Errors that can occur during bytecode inlining.
#[derive(Debug)]
pub(crate) enum InlineError {
    /// Register overflow: the inlined function would require more than
    /// 256 registers.
    RegisterOverflow {
        caller: String,
        callee: String,
        required: usize,
    },
}

impl std::fmt::Display for InlineError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::RegisterOverflow {
                caller,
                callee,
                required,
            } => write!(
                f,
                "register overflow inlining {callee} into {caller}: need {required} registers (max 256)"
            ),
        }
    }
}

/// Bytecode inliner: transforms a `BytecodeFunction` by replacing `Call`
/// opcodes with the inlined callee instructions.
pub(crate) struct BytecodeInliner;

impl BytecodeInliner {
    /// Inline callee bytecode into the caller at `Call` sites.
    ///
    /// - `caller`: the function to inline into
    /// - `callees`: map from `op_idx` to the callee `BytecodeFunction`
    /// - `max_depth`: maximum nesting depth for recursive inlining passes
    ///
    /// Returns the inlined function, or the original function unchanged if
    /// no `Call` opcodes were found.
    pub(crate) fn inline(
        caller: &BytecodeFunction,
        callees: &HashMap<u16, BytecodeFunction>,
        max_depth: usize,
    ) -> Result<BytecodeFunction, InlineError> {
        let mut current = caller.clone();

        for _depth in 0..max_depth {
            if !Self::has_inlineable_calls(&current, callees) {
                break;
            }
            current = Self::inline_one_pass(&current, callees)?;
        }

        Ok(current)
    }

    /// Check whether the function contains any `Call` opcodes whose callee
    /// is available in the map.
    fn has_inlineable_calls(
        func: &BytecodeFunction,
        callees: &HashMap<u16, BytecodeFunction>,
    ) -> bool {
        func.instructions
            .iter()
            .any(|op| matches!(op, Opcode::Call { op_idx, .. } if callees.contains_key(op_idx)))
    }

    /// Perform a single inlining pass, replacing all resolvable `Call` opcodes.
    fn inline_one_pass(
        caller: &BytecodeFunction,
        callees: &HashMap<u16, BytecodeFunction>,
    ) -> Result<BytecodeFunction, InlineError> {
        // First pass: compute the expanded instruction stream size and
        // validate register counts.
        let mut new_instructions: Vec<Opcode> = Vec::new();
        let mut new_max_register = caller.max_register;

        for op in &caller.instructions {
            match op {
                Opcode::Call {
                    rd,
                    op_idx,
                    args_start,
                    argc,
                } => {
                    if let Some(callee) = callees.get(op_idx) {
                        // Compute register offset: callee registers are remapped
                        // starting after the caller's current max.
                        let reg_offset = (new_max_register as u16) + 1;
                        let callee_max_remapped = reg_offset + (callee.max_register as u16);

                        if callee_max_remapped > 255 {
                            return Err(InlineError::RegisterOverflow {
                                caller: caller.name.clone(),
                                callee: callee.name.clone(),
                                required: callee_max_remapped as usize + 1,
                            });
                        }

                        let reg_offset_u8 = reg_offset as u8;

                        // Update the overall max register
                        new_max_register = new_max_register.max(callee_max_remapped as u8);

                        // 1. Emit argument copies: Move caller arg regs into
                        //    remapped callee parameter registers
                        for i in 0..*argc {
                            new_instructions.push(Opcode::Move {
                                rd: reg_offset_u8 + i, // remapped callee param register
                                rs: args_start + i,    // caller argument register
                            });
                        }

                        // 2. Inline callee instructions with remapped registers
                        //    and remapped jumps.
                        //
                        //    We need to handle Ret specially: replace with
                        //    Move { rd: call_rd, rs: remapped_ret_rs } + Jump to continuation.
                        //
                        //    The continuation point is right after all inlined
                        //    instructions. We'll emit a placeholder and patch later.
                        let inline_start = new_instructions.len();
                        let callee_len = callee.instructions.len();

                        // We need to know where the continuation point will be.
                        // Each Ret becomes 2 instructions (Move + Jump), all other
                        // instructions stay at 1. Count Ret instructions first.
                        let ret_count = callee
                            .instructions
                            .iter()
                            .filter(|op| matches!(op, Opcode::Ret { .. }))
                            .count();

                        // Total inlined instructions: (callee_len - ret_count) original
                        // + ret_count * 2 (Move+Jump for each Ret)
                        let inlined_len = callee_len + ret_count;

                        // Continuation PC (in the new_instructions stream) is
                        // inline_start + inlined_len.
                        let continuation_pc = inline_start + inlined_len;

                        // Build a PC mapping: old callee PC -> new instruction PC
                        // This is needed to remap jump offsets correctly.
                        // Each Ret instruction expands to 2 instructions, so PCs
                        // after a Ret are shifted by 1 for each prior Ret.
                        let mut pc_map = Vec::with_capacity(callee_len + 1);
                        let mut extra = 0usize;
                        for (i, callee_op) in callee.instructions.iter().enumerate() {
                            pc_map.push(inline_start + i + extra);
                            if matches!(callee_op, Opcode::Ret { .. }) {
                                extra += 1; // Ret expands to 2 instructions
                            }
                        }
                        // Map the "one past end" PC as well (for jump targets)
                        pc_map.push(inline_start + callee_len + extra);

                        // Now emit the remapped instructions
                        for (callee_pc, callee_op) in callee.instructions.iter().enumerate() {
                            match callee_op {
                                Opcode::Ret { rs } => {
                                    // Replace Ret with: Move { rd: call_rd, rs: remapped_rs }
                                    new_instructions.push(Opcode::Move {
                                        rd: *rd,
                                        rs: rs + reg_offset_u8,
                                    });
                                    // + Jump to continuation
                                    let current_pc = pc_map[callee_pc] + 1; // +1 because Move was just emitted
                                    let jump_offset = continuation_pc as i32 - current_pc as i32;
                                    new_instructions.push(Opcode::Jump {
                                        offset: jump_offset,
                                    });
                                }
                                _ => {
                                    let new_pc = pc_map[callee_pc];
                                    let remapped = remap_opcode(
                                        callee_op,
                                        reg_offset_u8,
                                        callee_pc,
                                        &pc_map,
                                        new_pc,
                                    );
                                    new_instructions.push(remapped);
                                }
                            }
                        }
                    } else {
                        // Callee not in map — leave Call in place
                        new_instructions.push(*op);
                    }
                }
                _ => {
                    new_instructions.push(*op);
                }
            }
        }

        // Now we need to remap jump offsets in the *caller's* original
        // instructions, since instruction indices have shifted due to inlining.
        // Actually, we need to rebuild the entire instruction stream with
        // correct jump targets.
        //
        // The approach above handles callee jumps correctly via pc_map, but
        // caller jumps that span across inlined blocks need adjustment too.
        //
        // Better approach: build a mapping from old caller PCs to new PCs,
        // then do a fixup pass on caller-originated jumps.

        // Let's redo this more carefully with a two-pass approach.
        let result = Self::inline_two_pass(caller, callees, new_max_register)?;
        Ok(result)
    }

    /// Two-pass inlining: first compute PC mapping, then emit with correct jumps.
    fn inline_two_pass(
        caller: &BytecodeFunction,
        callees: &HashMap<u16, BytecodeFunction>,
        new_max_register: u8,
    ) -> Result<BytecodeFunction, InlineError> {
        // Pass 1: compute the mapping from old caller PC to new PC.
        // For each caller instruction, compute how many new instructions it
        // will expand to.
        let mut caller_pc_to_new_pc: Vec<usize> = Vec::with_capacity(caller.instructions.len() + 1);
        let mut new_pc = 0usize;

        for op in &caller.instructions {
            caller_pc_to_new_pc.push(new_pc);
            match op {
                Opcode::Call { op_idx, argc, .. } => {
                    if let Some(callee) = callees.get(op_idx) {
                        // argc Move instructions for argument copying
                        let arg_copies = *argc as usize;

                        // Callee instructions with Ret expansion
                        let ret_count = callee
                            .instructions
                            .iter()
                            .filter(|op| matches!(op, Opcode::Ret { .. }))
                            .count();
                        let inlined_body = callee.instructions.len() + ret_count;

                        new_pc += arg_copies + inlined_body;
                    } else {
                        new_pc += 1;
                    }
                }
                _ => {
                    new_pc += 1;
                }
            }
        }
        // Map "one past end" for jump targets that point to the end
        caller_pc_to_new_pc.push(new_pc);

        // Pass 2: emit instructions with correct mappings.
        let mut new_instructions: Vec<Opcode> = Vec::with_capacity(new_pc);

        // Track register offset per inlined callee — we stack them up
        // to avoid collisions between different inline sites.
        let mut current_reg_ceiling = caller.max_register;

        for (caller_pc, op) in caller.instructions.iter().enumerate() {
            match op {
                Opcode::Call {
                    rd,
                    op_idx,
                    args_start,
                    argc,
                } => {
                    if let Some(callee) = callees.get(op_idx) {
                        let reg_offset = (current_reg_ceiling as u16) + 1;
                        let reg_offset_u8 = reg_offset as u8;
                        let callee_top = reg_offset + (callee.max_register as u16);
                        current_reg_ceiling = current_reg_ceiling.max(callee_top as u8);

                        // Emit argument copies
                        for i in 0..*argc {
                            new_instructions.push(Opcode::Move {
                                rd: reg_offset_u8 + i,
                                rs: args_start + i,
                            });
                        }

                        // Build callee PC map (callee_pc -> new_pc)
                        let inline_body_start = new_instructions.len();
                        let callee_len = callee.instructions.len();
                        let ret_count = callee
                            .instructions
                            .iter()
                            .filter(|op| matches!(op, Opcode::Ret { .. }))
                            .count();
                        let inlined_body_len = callee_len + ret_count;
                        let continuation_new_pc = inline_body_start + inlined_body_len;

                        let mut callee_pc_map: Vec<usize> = Vec::with_capacity(callee_len + 1);
                        {
                            let mut extra = 0usize;
                            for (i, callee_op) in callee.instructions.iter().enumerate() {
                                callee_pc_map.push(inline_body_start + i + extra);
                                if matches!(callee_op, Opcode::Ret { .. }) {
                                    extra += 1;
                                }
                            }
                            callee_pc_map.push(inline_body_start + callee_len + extra);
                        }

                        // Emit callee instructions
                        for (callee_pc, callee_op) in callee.instructions.iter().enumerate() {
                            match callee_op {
                                Opcode::Ret { rs } => {
                                    new_instructions.push(Opcode::Move {
                                        rd: *rd,
                                        rs: rs + reg_offset_u8,
                                    });
                                    let move_pc = callee_pc_map[callee_pc];
                                    let jump_pc = move_pc + 1;
                                    let jump_offset = continuation_new_pc as i32 - jump_pc as i32;
                                    new_instructions.push(Opcode::Jump {
                                        offset: jump_offset,
                                    });
                                }
                                _ => {
                                    let this_new_pc = callee_pc_map[callee_pc];
                                    let remapped = remap_opcode(
                                        callee_op,
                                        reg_offset_u8,
                                        callee_pc,
                                        &callee_pc_map,
                                        this_new_pc,
                                    );
                                    new_instructions.push(remapped);
                                }
                            }
                        }
                    } else {
                        // Leave Call in place
                        new_instructions.push(*op);
                    }
                }
                _ => {
                    // Remap jump offsets in caller instructions that reference
                    // shifted PCs.
                    let remapped = remap_caller_jump(op, caller_pc, &caller_pc_to_new_pc);
                    new_instructions.push(remapped);
                }
            }
        }

        let mut result = BytecodeFunction::new(caller.name.clone(), caller.arity);
        result.max_register = current_reg_ceiling.max(new_max_register);
        result.instructions = new_instructions;

        Ok(result)
    }
}

/// Remap a caller jump instruction whose targets may have shifted due to
/// inlining expanding instruction counts.
fn remap_caller_jump(op: &Opcode, caller_pc: usize, pc_map: &[usize]) -> Opcode {
    let new_pc = pc_map[caller_pc];
    match *op {
        Opcode::Jump { offset } => {
            let old_target = (caller_pc as i64 + offset as i64) as usize;
            let new_target = pc_map[old_target];
            Opcode::Jump {
                offset: new_target as i32 - new_pc as i32,
            }
        }
        Opcode::JumpTrue { rs, offset } => {
            let old_target = (caller_pc as i64 + offset as i64) as usize;
            let new_target = pc_map[old_target];
            Opcode::JumpTrue {
                rs,
                offset: new_target as i32 - new_pc as i32,
            }
        }
        Opcode::JumpFalse { rs, offset } => {
            let old_target = (caller_pc as i64 + offset as i64) as usize;
            let new_target = pc_map[old_target];
            Opcode::JumpFalse {
                rs,
                offset: new_target as i32 - new_pc as i32,
            }
        }
        Opcode::ForallBegin {
            rd,
            r_binding,
            r_domain,
            loop_end,
        } => {
            let old_target = (caller_pc as i64 + loop_end as i64) as usize;
            let new_target = pc_map[old_target];
            Opcode::ForallBegin {
                rd,
                r_binding,
                r_domain,
                loop_end: new_target as i32 - new_pc as i32,
            }
        }
        Opcode::ForallNext {
            rd,
            r_binding,
            r_body,
            loop_begin,
        } => {
            let old_target = (caller_pc as i64 + loop_begin as i64) as usize;
            let new_target = pc_map[old_target];
            Opcode::ForallNext {
                rd,
                r_binding,
                r_body,
                loop_begin: new_target as i32 - new_pc as i32,
            }
        }
        Opcode::ExistsBegin {
            rd,
            r_binding,
            r_domain,
            loop_end,
        } => {
            let old_target = (caller_pc as i64 + loop_end as i64) as usize;
            let new_target = pc_map[old_target];
            Opcode::ExistsBegin {
                rd,
                r_binding,
                r_domain,
                loop_end: new_target as i32 - new_pc as i32,
            }
        }
        Opcode::ExistsNext {
            rd,
            r_binding,
            r_body,
            loop_begin,
        } => {
            let old_target = (caller_pc as i64 + loop_begin as i64) as usize;
            let new_target = pc_map[old_target];
            Opcode::ExistsNext {
                rd,
                r_binding,
                r_body,
                loop_begin: new_target as i32 - new_pc as i32,
            }
        }
        Opcode::ChooseBegin {
            rd,
            r_binding,
            r_domain,
            loop_end,
        } => {
            let old_target = (caller_pc as i64 + loop_end as i64) as usize;
            let new_target = pc_map[old_target];
            Opcode::ChooseBegin {
                rd,
                r_binding,
                r_domain,
                loop_end: new_target as i32 - new_pc as i32,
            }
        }
        Opcode::ChooseNext {
            rd,
            r_binding,
            r_body,
            loop_begin,
        } => {
            let old_target = (caller_pc as i64 + loop_begin as i64) as usize;
            let new_target = pc_map[old_target];
            Opcode::ChooseNext {
                rd,
                r_binding,
                r_body,
                loop_begin: new_target as i32 - new_pc as i32,
            }
        }
        Opcode::SetBuilderBegin {
            rd,
            r_binding,
            r_domain,
            loop_end,
        } => {
            let old_target = (caller_pc as i64 + loop_end as i64) as usize;
            let new_target = pc_map[old_target];
            Opcode::SetBuilderBegin {
                rd,
                r_binding,
                r_domain,
                loop_end: new_target as i32 - new_pc as i32,
            }
        }
        Opcode::SetFilterBegin {
            rd,
            r_binding,
            r_domain,
            loop_end,
        } => {
            let old_target = (caller_pc as i64 + loop_end as i64) as usize;
            let new_target = pc_map[old_target];
            Opcode::SetFilterBegin {
                rd,
                r_binding,
                r_domain,
                loop_end: new_target as i32 - new_pc as i32,
            }
        }
        Opcode::FuncDefBegin {
            rd,
            r_binding,
            r_domain,
            loop_end,
        } => {
            let old_target = (caller_pc as i64 + loop_end as i64) as usize;
            let new_target = pc_map[old_target];
            Opcode::FuncDefBegin {
                rd,
                r_binding,
                r_domain,
                loop_end: new_target as i32 - new_pc as i32,
            }
        }
        Opcode::LoopNext {
            r_binding,
            r_body,
            loop_begin,
        } => {
            let old_target = (caller_pc as i64 + loop_begin as i64) as usize;
            let new_target = pc_map[old_target];
            Opcode::LoopNext {
                r_binding,
                r_body,
                loop_begin: new_target as i32 - new_pc as i32,
            }
        }
        // Non-jump opcodes pass through unchanged
        other => other,
    }
}

/// Remap all registers in a callee opcode by adding `offset`, and remap
/// jump targets using the provided PC map.
///
/// `callee_pc` is the original PC in the callee, `callee_pc_map` maps
/// callee PCs to new (absolute) PCs, and `new_pc` is the absolute PC of
/// this instruction in the output stream.
fn remap_opcode(
    op: &Opcode,
    offset: u8,
    callee_pc: usize,
    callee_pc_map: &[usize],
    new_pc: usize,
) -> Opcode {
    // Helper: remap a register
    let r = |reg: u8| -> u8 { reg + offset };

    // Helper: remap a jump offset
    let remap_jump = |old_offset: i32| -> i32 {
        let old_target = (callee_pc as i64 + old_offset as i64) as usize;
        let new_target = callee_pc_map[old_target];
        new_target as i32 - new_pc as i32
    };

    match *op {
        // Value loading
        Opcode::LoadImm { rd, value } => Opcode::LoadImm { rd: r(rd), value },
        Opcode::LoadBool { rd, value } => Opcode::LoadBool { rd: r(rd), value },
        Opcode::LoadConst { rd, idx } => Opcode::LoadConst { rd: r(rd), idx },
        Opcode::LoadVar { rd, var_idx } => Opcode::LoadVar { rd: r(rd), var_idx },
        Opcode::LoadPrime { rd, var_idx } => Opcode::LoadPrime { rd: r(rd), var_idx },
        Opcode::StoreVar { var_idx, rs } => Opcode::StoreVar { var_idx, rs: r(rs) },
        Opcode::Move { rd, rs } => Opcode::Move {
            rd: r(rd),
            rs: r(rs),
        },

        // Arithmetic
        Opcode::AddInt { rd, r1, r2 } => Opcode::AddInt {
            rd: r(rd),
            r1: r(r1),
            r2: r(r2),
        },
        Opcode::SubInt { rd, r1, r2 } => Opcode::SubInt {
            rd: r(rd),
            r1: r(r1),
            r2: r(r2),
        },
        Opcode::MulInt { rd, r1, r2 } => Opcode::MulInt {
            rd: r(rd),
            r1: r(r1),
            r2: r(r2),
        },
        Opcode::DivInt { rd, r1, r2 } => Opcode::DivInt {
            rd: r(rd),
            r1: r(r1),
            r2: r(r2),
        },
        Opcode::IntDiv { rd, r1, r2 } => Opcode::IntDiv {
            rd: r(rd),
            r1: r(r1),
            r2: r(r2),
        },
        Opcode::ModInt { rd, r1, r2 } => Opcode::ModInt {
            rd: r(rd),
            r1: r(r1),
            r2: r(r2),
        },
        Opcode::NegInt { rd, rs } => Opcode::NegInt {
            rd: r(rd),
            rs: r(rs),
        },
        Opcode::PowInt { rd, r1, r2 } => Opcode::PowInt {
            rd: r(rd),
            r1: r(r1),
            r2: r(r2),
        },

        // Comparison
        Opcode::Eq { rd, r1, r2 } => Opcode::Eq {
            rd: r(rd),
            r1: r(r1),
            r2: r(r2),
        },
        Opcode::Neq { rd, r1, r2 } => Opcode::Neq {
            rd: r(rd),
            r1: r(r1),
            r2: r(r2),
        },
        Opcode::LtInt { rd, r1, r2 } => Opcode::LtInt {
            rd: r(rd),
            r1: r(r1),
            r2: r(r2),
        },
        Opcode::LeInt { rd, r1, r2 } => Opcode::LeInt {
            rd: r(rd),
            r1: r(r1),
            r2: r(r2),
        },
        Opcode::GtInt { rd, r1, r2 } => Opcode::GtInt {
            rd: r(rd),
            r1: r(r1),
            r2: r(r2),
        },
        Opcode::GeInt { rd, r1, r2 } => Opcode::GeInt {
            rd: r(rd),
            r1: r(r1),
            r2: r(r2),
        },

        // Boolean
        Opcode::And { rd, r1, r2 } => Opcode::And {
            rd: r(rd),
            r1: r(r1),
            r2: r(r2),
        },
        Opcode::Or { rd, r1, r2 } => Opcode::Or {
            rd: r(rd),
            r1: r(r1),
            r2: r(r2),
        },
        Opcode::Not { rd, rs } => Opcode::Not {
            rd: r(rd),
            rs: r(rs),
        },
        Opcode::Implies { rd, r1, r2 } => Opcode::Implies {
            rd: r(rd),
            r1: r(r1),
            r2: r(r2),
        },
        Opcode::Equiv { rd, r1, r2 } => Opcode::Equiv {
            rd: r(rd),
            r1: r(r1),
            r2: r(r2),
        },

        // Control flow
        Opcode::Jump { offset } => Opcode::Jump {
            offset: remap_jump(offset),
        },
        Opcode::JumpTrue { rs, offset } => Opcode::JumpTrue {
            rs: r(rs),
            offset: remap_jump(offset),
        },
        Opcode::JumpFalse { rs, offset } => Opcode::JumpFalse {
            rs: r(rs),
            offset: remap_jump(offset),
        },
        Opcode::CondMove { rd, cond, rs } => Opcode::CondMove {
            rd: r(rd),
            cond: r(cond),
            rs: r(rs),
        },

        // Call — nested call, leave in place but remap registers
        Opcode::Call {
            rd,
            op_idx,
            args_start,
            argc,
        } => Opcode::Call {
            rd: r(rd),
            op_idx,
            args_start: r(args_start),
            argc,
        },

        // ValueApply — remap registers
        Opcode::ValueApply {
            rd,
            func,
            args_start,
            argc,
        } => Opcode::ValueApply {
            rd: r(rd),
            func: r(func),
            args_start: r(args_start),
            argc,
        },

        // Ret is handled separately (should not reach here)
        Opcode::Ret { rs } => Opcode::Ret { rs: r(rs) },

        // Set operations
        Opcode::SetEnum { rd, start, count } => Opcode::SetEnum {
            rd: r(rd),
            start: r(start),
            count,
        },
        Opcode::SetIn { rd, elem, set } => Opcode::SetIn {
            rd: r(rd),
            elem: r(elem),
            set: r(set),
        },
        Opcode::SetUnion { rd, r1, r2 } => Opcode::SetUnion {
            rd: r(rd),
            r1: r(r1),
            r2: r(r2),
        },
        Opcode::SetIntersect { rd, r1, r2 } => Opcode::SetIntersect {
            rd: r(rd),
            r1: r(r1),
            r2: r(r2),
        },
        Opcode::SetDiff { rd, r1, r2 } => Opcode::SetDiff {
            rd: r(rd),
            r1: r(r1),
            r2: r(r2),
        },
        Opcode::Subseteq { rd, r1, r2 } => Opcode::Subseteq {
            rd: r(rd),
            r1: r(r1),
            r2: r(r2),
        },
        Opcode::Powerset { rd, rs } => Opcode::Powerset {
            rd: r(rd),
            rs: r(rs),
        },
        Opcode::BigUnion { rd, rs } => Opcode::BigUnion {
            rd: r(rd),
            rs: r(rs),
        },
        Opcode::KSubset { rd, base, k } => Opcode::KSubset {
            rd: r(rd),
            base: r(base),
            k: r(k),
        },
        Opcode::Range { rd, lo, hi } => Opcode::Range {
            rd: r(rd),
            lo: r(lo),
            hi: r(hi),
        },

        // Quantifiers
        Opcode::ForallBegin {
            rd,
            r_binding,
            r_domain,
            loop_end,
        } => Opcode::ForallBegin {
            rd: r(rd),
            r_binding: r(r_binding),
            r_domain: r(r_domain),
            loop_end: remap_jump(loop_end),
        },
        Opcode::ForallNext {
            rd,
            r_binding,
            r_body,
            loop_begin,
        } => Opcode::ForallNext {
            rd: r(rd),
            r_binding: r(r_binding),
            r_body: r(r_body),
            loop_begin: remap_jump(loop_begin),
        },
        Opcode::ExistsBegin {
            rd,
            r_binding,
            r_domain,
            loop_end,
        } => Opcode::ExistsBegin {
            rd: r(rd),
            r_binding: r(r_binding),
            r_domain: r(r_domain),
            loop_end: remap_jump(loop_end),
        },
        Opcode::ExistsNext {
            rd,
            r_binding,
            r_body,
            loop_begin,
        } => Opcode::ExistsNext {
            rd: r(rd),
            r_binding: r(r_binding),
            r_body: r(r_body),
            loop_begin: remap_jump(loop_begin),
        },

        // Records / Functions / Tuples
        Opcode::RecordNew {
            rd,
            fields_start,
            values_start,
            count,
        } => Opcode::RecordNew {
            rd: r(rd),
            fields_start,
            values_start: r(values_start),
            count,
        },
        Opcode::RecordGet { rd, rs, field_idx } => Opcode::RecordGet {
            rd: r(rd),
            rs: r(rs),
            field_idx,
        },
        Opcode::FuncApply { rd, func, arg } => Opcode::FuncApply {
            rd: r(rd),
            func: r(func),
            arg: r(arg),
        },
        Opcode::Domain { rd, rs } => Opcode::Domain {
            rd: r(rd),
            rs: r(rs),
        },
        Opcode::FuncExcept {
            rd,
            func,
            path,
            val,
        } => Opcode::FuncExcept {
            rd: r(rd),
            func: r(func),
            path: r(path),
            val: r(val),
        },
        Opcode::TupleNew { rd, start, count } => Opcode::TupleNew {
            rd: r(rd),
            start: r(start),
            count,
        },
        Opcode::TupleGet { rd, rs, idx } => Opcode::TupleGet {
            rd: r(rd),
            rs: r(rs),
            idx,
        },
        Opcode::FuncDef {
            rd,
            r_domain,
            r_binding,
        } => Opcode::FuncDef {
            rd: r(rd),
            r_domain: r(r_domain),
            r_binding: r(r_binding),
        },
        Opcode::FuncSet { rd, domain, range } => Opcode::FuncSet {
            rd: r(rd),
            domain: r(domain),
            range: r(range),
        },
        Opcode::RecordSet {
            rd,
            fields_start,
            values_start,
            count,
        } => Opcode::RecordSet {
            rd: r(rd),
            fields_start,
            values_start: r(values_start),
            count,
        },
        Opcode::Times { rd, start, count } => Opcode::Times {
            rd: r(rd),
            start: r(start),
            count,
        },
        Opcode::SeqNew { rd, start, count } => Opcode::SeqNew {
            rd: r(rd),
            start: r(start),
            count,
        },
        Opcode::StrConcat { rd, r1, r2 } => Opcode::StrConcat {
            rd: r(rd),
            r1: r(r1),
            r2: r(r2),
        },
        Opcode::Concat { rd, r1, r2 } => Opcode::Concat {
            rd: r(rd),
            r1: r(r1),
            r2: r(r2),
        },

        // Special
        Opcode::Unchanged { rd, start, count } => Opcode::Unchanged {
            rd: r(rd),
            start,
            count,
        },
        Opcode::ChooseBegin {
            rd,
            r_binding,
            r_domain,
            loop_end,
        } => Opcode::ChooseBegin {
            rd: r(rd),
            r_binding: r(r_binding),
            r_domain: r(r_domain),
            loop_end: remap_jump(loop_end),
        },
        Opcode::ChooseNext {
            rd,
            r_binding,
            r_body,
            loop_begin,
        } => Opcode::ChooseNext {
            rd: r(rd),
            r_binding: r(r_binding),
            r_body: r(r_body),
            loop_begin: remap_jump(loop_begin),
        },
        Opcode::SetBuilderBegin {
            rd,
            r_binding,
            r_domain,
            loop_end,
        } => Opcode::SetBuilderBegin {
            rd: r(rd),
            r_binding: r(r_binding),
            r_domain: r(r_domain),
            loop_end: remap_jump(loop_end),
        },
        Opcode::SetFilterBegin {
            rd,
            r_binding,
            r_domain,
            loop_end,
        } => Opcode::SetFilterBegin {
            rd: r(rd),
            r_binding: r(r_binding),
            r_domain: r(r_domain),
            loop_end: remap_jump(loop_end),
        },
        Opcode::FuncDefBegin {
            rd,
            r_binding,
            r_domain,
            loop_end,
        } => Opcode::FuncDefBegin {
            rd: r(rd),
            r_binding: r(r_binding),
            r_domain: r(r_domain),
            loop_end: remap_jump(loop_end),
        },
        Opcode::LoopNext {
            r_binding,
            r_body,
            loop_begin,
        } => Opcode::LoopNext {
            r_binding: r(r_binding),
            r_body: r(r_body),
            loop_begin: remap_jump(loop_begin),
        },

        Opcode::SetPrimeMode { enable } => Opcode::SetPrimeMode { enable },
        Opcode::MakeClosure {
            rd,
            template_idx,
            captures_start,
            capture_count,
        } => Opcode::MakeClosure {
            rd: r(rd),
            template_idx,
            captures_start: r(captures_start),
            capture_count,
        },
        Opcode::CallExternal {
            rd,
            name_idx,
            args_start,
            argc,
        } => Opcode::CallExternal {
            rd: r(rd),
            name_idx,
            args_start: r(args_start),
            argc,
        },
        Opcode::CallBuiltin {
            rd,
            builtin,
            args_start,
            argc,
        } => Opcode::CallBuiltin {
            rd: r(rd),
            builtin,
            args_start: r(args_start),
            argc,
        },

        Opcode::Nop => Opcode::Nop,
        Opcode::Halt => Opcode::Halt,
    }
}

/// Check whether a function contains any `Call` opcodes.
pub(crate) fn has_call_opcodes(func: &BytecodeFunction) -> bool {
    func.instructions
        .iter()
        .any(|op| matches!(op, Opcode::Call { .. }))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Test basic inlining: caller calls a simple callee that adds two constants.
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_inline_simple_callee() {
        // Callee: fn add_one(x) -> x + 1
        //   r0 = param x
        //   r1 = 1
        //   r2 = r0 + r1
        //   ret r2
        let mut callee = BytecodeFunction::new("add_one".to_string(), 1);
        callee.emit(Opcode::LoadImm { rd: 1, value: 1 });
        callee.emit(Opcode::AddInt {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        callee.emit(Opcode::Ret { rs: 2 });

        // Caller: fn main()
        //   r0 = 10
        //   r1 = call add_one(r0)  // Call { rd: 1, op_idx: 0, args_start: 0, argc: 1 }
        //   ret r1
        let mut caller = BytecodeFunction::new("main".to_string(), 0);
        caller.emit(Opcode::LoadImm { rd: 0, value: 10 });
        caller.emit(Opcode::Call {
            rd: 1,
            op_idx: 0,
            args_start: 0,
            argc: 1,
        });
        caller.emit(Opcode::Ret { rs: 1 });

        let mut callees = HashMap::new();
        callees.insert(0u16, callee);

        let inlined = BytecodeInliner::inline(&caller, &callees, 3).unwrap();

        // Verify no Call opcodes remain
        assert!(
            !has_call_opcodes(&inlined),
            "inlined function should have no Call opcodes, got: {:#?}",
            inlined.instructions
        );

        // Verify the function still ends with Ret
        assert!(
            matches!(inlined.instructions.last(), Some(Opcode::Ret { .. })),
            "inlined function should end with Ret"
        );
    }

    /// Test inlining with no callees available leaves Call in place.
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_inline_no_callees() {
        let mut caller = BytecodeFunction::new("main".to_string(), 0);
        caller.emit(Opcode::Call {
            rd: 0,
            op_idx: 99,
            args_start: 1,
            argc: 0,
        });
        caller.emit(Opcode::Ret { rs: 0 });

        let callees = HashMap::new();
        let inlined = BytecodeInliner::inline(&caller, &callees, 3).unwrap();

        // Call should still be present
        assert!(
            has_call_opcodes(&inlined),
            "unresolvable Call should remain in place"
        );
    }

    /// Test inlining a zero-argument callee.
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_inline_zero_arg_callee() {
        // Callee: fn get_true() -> TRUE
        let mut callee = BytecodeFunction::new("get_true".to_string(), 0);
        callee.emit(Opcode::LoadBool { rd: 0, value: true });
        callee.emit(Opcode::Ret { rs: 0 });

        // Caller:
        //   r0 = call get_true()
        //   ret r0
        let mut caller = BytecodeFunction::new("main".to_string(), 0);
        caller.emit(Opcode::Call {
            rd: 0,
            op_idx: 0,
            args_start: 0,
            argc: 0,
        });
        caller.emit(Opcode::Ret { rs: 0 });

        let mut callees = HashMap::new();
        callees.insert(0u16, callee);

        let inlined = BytecodeInliner::inline(&caller, &callees, 3).unwrap();
        assert!(!has_call_opcodes(&inlined));
    }

    /// Test nested inlining: A calls B, B calls C.
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_inline_nested() {
        // C: fn const_5() -> 5
        let mut callee_c = BytecodeFunction::new("const_5".to_string(), 0);
        callee_c.emit(Opcode::LoadImm { rd: 0, value: 5 });
        callee_c.emit(Opcode::Ret { rs: 0 });

        // B: fn get_5() -> call const_5()
        let mut callee_b = BytecodeFunction::new("get_5".to_string(), 0);
        callee_b.emit(Opcode::Call {
            rd: 0,
            op_idx: 1, // const_5
            args_start: 0,
            argc: 0,
        });
        callee_b.emit(Opcode::Ret { rs: 0 });

        // A: fn main() -> call get_5()
        let mut caller = BytecodeFunction::new("main".to_string(), 0);
        caller.emit(Opcode::Call {
            rd: 0,
            op_idx: 0, // get_5
            args_start: 0,
            argc: 0,
        });
        caller.emit(Opcode::Ret { rs: 0 });

        let mut callees = HashMap::new();
        callees.insert(0u16, callee_b);
        callees.insert(1u16, callee_c);

        // With max_depth=1, the inner Call should remain
        let inlined_shallow = BytecodeInliner::inline(&caller, &callees, 1).unwrap();
        assert!(
            has_call_opcodes(&inlined_shallow),
            "depth=1 should not resolve nested call"
        );

        // With max_depth=3, all Calls should be resolved
        let inlined_deep = BytecodeInliner::inline(&caller, &callees, 3).unwrap();
        assert!(
            !has_call_opcodes(&inlined_deep),
            "depth=3 should resolve all nested calls"
        );
    }

    /// Test inlining preserves caller jump targets.
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_inline_preserves_caller_jumps() {
        // Callee: fn id(x) -> x
        let mut callee = BytecodeFunction::new("id".to_string(), 1);
        callee.emit(Opcode::Ret { rs: 0 });

        // Caller:
        //   r0 = TRUE
        //   JumpFalse r0, +3   -> target is PC 4 (past the Call)
        //   r1 = 42
        //   r2 = call id(r1)   -> PC 3, expands
        //   ret r2              -> PC 4
        let mut caller = BytecodeFunction::new("main".to_string(), 0);
        caller.emit(Opcode::LoadBool { rd: 0, value: true }); // PC 0
        caller.emit(Opcode::JumpFalse { rs: 0, offset: 3 }); // PC 1, target = PC 4
        caller.emit(Opcode::LoadImm { rd: 1, value: 42 }); // PC 2
        caller.emit(Opcode::Call {
            // PC 3
            rd: 2,
            op_idx: 0,
            args_start: 1,
            argc: 1,
        });
        caller.emit(Opcode::Ret { rs: 2 }); // PC 4

        let mut callees = HashMap::new();
        callees.insert(0u16, callee);

        let inlined = BytecodeInliner::inline(&caller, &callees, 3).unwrap();

        // Verify no Call opcodes
        assert!(!has_call_opcodes(&inlined));

        // Verify the JumpFalse still has a valid forward offset
        let jump_op = &inlined.instructions[1];
        if let Opcode::JumpFalse { offset, .. } = jump_op {
            assert!(
                *offset > 0,
                "JumpFalse should be a forward jump, got {offset}"
            );
        } else {
            panic!("expected JumpFalse at position 1, got {jump_op:?}");
        }
    }

    /// Test that callee with internal jumps are handled correctly.
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_inline_callee_with_internal_jumps() {
        // Callee: fn abs(x) -> IF x >= 0 THEN x ELSE -x
        //   r0 = param x
        //   r1 = 0
        //   r2 = (r0 >= r1)
        //   JumpFalse r2, +2  // skip to negation
        //   ret r0             // return x
        //   r3 = -r0
        //   ret r3             // return -x
        let mut callee = BytecodeFunction::new("abs".to_string(), 1);
        callee.emit(Opcode::LoadImm { rd: 1, value: 0 }); // PC 0
        callee.emit(Opcode::GeInt {
            rd: 2,
            r1: 0,
            r2: 1,
        }); // PC 1
        callee.emit(Opcode::JumpFalse { rs: 2, offset: 2 }); // PC 2, target = PC 4
        callee.emit(Opcode::Ret { rs: 0 }); // PC 3
        callee.emit(Opcode::NegInt { rd: 3, rs: 0 }); // PC 4
        callee.emit(Opcode::Ret { rs: 3 }); // PC 5

        // Caller:
        //   r0 = -7
        //   r1 = call abs(r0)
        //   ret r1
        let mut caller = BytecodeFunction::new("main".to_string(), 0);
        caller.emit(Opcode::LoadImm { rd: 0, value: -7 });
        caller.emit(Opcode::Call {
            rd: 1,
            op_idx: 0,
            args_start: 0,
            argc: 1,
        });
        caller.emit(Opcode::Ret { rs: 1 });

        let mut callees = HashMap::new();
        callees.insert(0u16, callee);

        let inlined = BytecodeInliner::inline(&caller, &callees, 3).unwrap();
        assert!(!has_call_opcodes(&inlined));

        // Verify the result has reasonable structure
        assert!(
            inlined.instructions.len() > 3,
            "inlined function should have more instructions than the original"
        );
    }

    /// Test register remapping doesn't collide.
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_inline_register_remapping() {
        // Callee uses r0..r2
        let mut callee = BytecodeFunction::new("callee".to_string(), 1);
        callee.emit(Opcode::LoadImm { rd: 1, value: 100 });
        callee.emit(Opcode::AddInt {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        callee.emit(Opcode::Ret { rs: 2 });

        // Caller uses r0..r3
        let mut caller = BytecodeFunction::new("caller".to_string(), 0);
        caller.emit(Opcode::LoadImm { rd: 0, value: 1 });
        caller.emit(Opcode::LoadImm { rd: 1, value: 2 });
        caller.emit(Opcode::LoadImm { rd: 2, value: 3 });
        caller.emit(Opcode::AddInt {
            rd: 3,
            r1: 0,
            r2: 1,
        }); // r3 = 3
        caller.emit(Opcode::Call {
            rd: 0,
            op_idx: 0,
            args_start: 3,
            argc: 1,
        });
        caller.emit(Opcode::Ret { rs: 0 });

        let mut callees = HashMap::new();
        callees.insert(0u16, callee);

        let inlined = BytecodeInliner::inline(&caller, &callees, 3).unwrap();
        assert!(!has_call_opcodes(&inlined));

        // Callee registers should be remapped to r4+ (caller max_register=3)
        // Check that the callee's LoadImm uses a register >= 4
        let has_high_reg = inlined
            .instructions
            .iter()
            .any(|op| matches!(op, Opcode::LoadImm { rd, value: 100 } if *rd >= 4));
        assert!(
            has_high_reg,
            "callee registers should be remapped above caller's max_register"
        );
    }

    /// Test multiple Call sites in the same function.
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_inline_multiple_calls() {
        // Callee: fn inc(x) -> x + 1
        let mut callee = BytecodeFunction::new("inc".to_string(), 1);
        callee.emit(Opcode::LoadImm { rd: 1, value: 1 });
        callee.emit(Opcode::AddInt {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        callee.emit(Opcode::Ret { rs: 2 });

        // Caller:
        //   r0 = 10
        //   r1 = call inc(r0)
        //   r2 = call inc(r1)
        //   ret r2
        let mut caller = BytecodeFunction::new("main".to_string(), 0);
        caller.emit(Opcode::LoadImm { rd: 0, value: 10 });
        caller.emit(Opcode::Call {
            rd: 1,
            op_idx: 0,
            args_start: 0,
            argc: 1,
        });
        caller.emit(Opcode::Call {
            rd: 2,
            op_idx: 0,
            args_start: 1,
            argc: 1,
        });
        caller.emit(Opcode::Ret { rs: 2 });

        let mut callees = HashMap::new();
        callees.insert(0u16, callee);

        let inlined = BytecodeInliner::inline(&caller, &callees, 3).unwrap();
        assert!(
            !has_call_opcodes(&inlined),
            "both Call sites should be inlined"
        );
    }
}
