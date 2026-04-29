// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Action predicate -> next-state function transformation.
//!
//! TLA+ actions are boolean predicates (`x' = expr /\ UNCHANGED y`).
//! The JIT next-state cache requires bytecode functions that produce
//! successor states using `StoreVar` opcodes.
//!
//! This module rewrites simple prime-equality patterns:
//!
//! ```text
//! LoadPrime { rd: rp, var_idx: x }   -.
//! Eq { rd: req, r1: rp, r2: rexpr }  -+-> LoadBool { rd: req, value: true }
//!                                        StoreVar { var_idx: x, rs: rexpr }
//! ```
//!
//! The rewrite preserves instruction count and jump targets by emitting the
//! action-enabled flag (`LoadBool(true)`) at the original `LoadPrime` PC and
//! delaying the `StoreVar` until the original `Eq` PC, after the RHS register
//! has definitely been computed.
//!
//! `Unchanged` opcodes are kept as-is. They rely on the caller seeding the
//! successor buffer from the predecessor state before execution.

use std::collections::BTreeSet;

use super::opcode::{Opcode, Register, VarIdx};

/// Result of attempting to rewrite an action predicate into next-state bytecode.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ActionTransformOutcome {
    /// The action was safely rewritten for next-state execution.
    Transformed(Vec<Opcode>),
    /// No next-state rewrite pattern was found.
    NoRewrite,
    /// The action used primed values in a way the next-state ABI cannot
    /// represent soundly.
    Unsafe(String),
}

/// Transform an action predicate's bytecode into next-state function bytecode.
///
/// The transform is intentionally conservative. It rejects actions whose RHS
/// depends on primed values (`x' = y'`), actions that would write the same
/// primed variable multiple times, and any function that would still contain an
/// unmatched `LoadPrime` after rewriting.
pub fn transform_action_to_next_state(instructions: &[Opcode]) -> ActionTransformOutcome {
    if instructions.is_empty() {
        return ActionTransformOutcome::NoRewrite;
    }

    let mut prime_defs: Vec<Option<(VarIdx, usize)>> = vec![None; 256];
    let mut tainted = [false; 256];
    let mut rewrites: Vec<(usize, usize, VarIdx, Register, Register)> = Vec::new();
    let mut total_prime_loads = 0usize;
    let mut has_unchanged = false;
    let mut stored_vars = BTreeSet::new();

    for (pc, op) in instructions.iter().enumerate() {
        match *op {
            Opcode::LoadPrime { rd, var_idx } => {
                prime_defs[rd as usize] = Some((var_idx, pc));
                tainted[rd as usize] = true;
                total_prime_loads += 1;
            }
            Opcode::Eq { rd, r1, r2 } => {
                if let Some((var_idx, prime_pc)) = prime_defs[r1 as usize] {
                    if tainted[r2 as usize] {
                        return ActionTransformOutcome::Unsafe(format!(
                            "prime-tainted RHS for primed var {var_idx}"
                        ));
                    }
                    if eq_result_interferes_before_rewrite(instructions, rd, r2, prime_pc, pc) {
                        return ActionTransformOutcome::Unsafe(format!(
                            "Eq destination r{rd} conflicts with live RHS before rewrite"
                        ));
                    }
                    if !stored_vars.insert(var_idx) {
                        return ActionTransformOutcome::Unsafe(format!(
                            "duplicate writes to primed var {var_idx}"
                        ));
                    }
                    rewrites.push((prime_pc, pc, var_idx, r2, rd));
                    prime_defs[r1 as usize] = None;
                    tainted[rd as usize] = false;
                } else if let Some((var_idx, prime_pc)) = prime_defs[r2 as usize] {
                    if tainted[r1 as usize] {
                        return ActionTransformOutcome::Unsafe(format!(
                            "prime-tainted RHS for primed var {var_idx}"
                        ));
                    }
                    if eq_result_interferes_before_rewrite(instructions, rd, r1, prime_pc, pc) {
                        return ActionTransformOutcome::Unsafe(format!(
                            "Eq destination r{rd} conflicts with live RHS before rewrite"
                        ));
                    }
                    if !stored_vars.insert(var_idx) {
                        return ActionTransformOutcome::Unsafe(format!(
                            "duplicate writes to primed var {var_idx}"
                        ));
                    }
                    rewrites.push((prime_pc, pc, var_idx, r1, rd));
                    prime_defs[r2 as usize] = None;
                    tainted[rd as usize] = false;
                } else {
                    tainted[rd as usize] = opcode_reads_tainted(op, &tainted);
                }
            }
            Opcode::Unchanged { .. } => {
                has_unchanged = true;
                if let Some(rd) = dest_register(op) {
                    prime_defs[rd as usize] = None;
                    tainted[rd as usize] = false;
                }
            }
            _ => {
                let reads_tainted = opcode_reads_tainted(op, &tainted);
                if reads_tainted && dest_register(op).is_none() {
                    return ActionTransformOutcome::Unsafe(format!(
                        "primed value escapes into non-rewrite opcode at pc {pc}"
                    ));
                }
                if let Some(rd) = dest_register(op) {
                    prime_defs[rd as usize] = None;
                    tainted[rd as usize] = reads_tainted;
                }
            }
        }
    }

    if rewrites.is_empty() {
        // UNCHANGED-only actions are still executable next-state actions. The
        // caller seeds state_out from state_in before native execution, so the
        // unchanged successor is represented without StoreVar opcodes.
        if has_unchanged && total_prime_loads == 0 {
            return ActionTransformOutcome::Transformed(instructions.to_vec());
        }
        return ActionTransformOutcome::NoRewrite;
    }

    if rewrites.len() != total_prime_loads {
        return ActionTransformOutcome::Unsafe(
            "residual LoadPrime remains after action rewrite".to_string(),
        );
    }

    let mut result = instructions.to_vec();
    for &(prime_pc, eq_pc, var_idx, expr_reg, eq_rd) in &rewrites {
        result[prime_pc] = Opcode::LoadBool {
            rd: eq_rd,
            value: true,
        };
        result[eq_pc] = Opcode::StoreVar {
            var_idx,
            rs: expr_reg,
        };
    }

    ActionTransformOutcome::Transformed(result)
}

fn dest_register(op: &Opcode) -> Option<Register> {
    op.dest_register()
}

fn eq_result_interferes_before_rewrite(
    instructions: &[Opcode],
    eq_rd: Register,
    expr_reg: Register,
    prime_pc: usize,
    eq_pc: usize,
) -> bool {
    if eq_rd == expr_reg {
        return true;
    }

    instructions[prime_pc + 1..eq_pc]
        .iter()
        .any(|op| opcode_reads_register(op, eq_rd) || opcode_writes_register(op, eq_rd))
}

fn opcode_reads_register(op: &Opcode, reg: Register) -> bool {
    let mut tainted = [false; 256];
    tainted[reg as usize] = true;
    opcode_reads_tainted(op, &tainted)
}

fn opcode_writes_register(op: &Opcode, reg: Register) -> bool {
    op.dest_register() == Some(reg) || op.binding_register() == Some(reg)
}

fn range_reads_tainted(tainted: &[bool; 256], start: Register, count: u8) -> bool {
    (0..count).any(|offset| tainted[start.saturating_add(offset) as usize])
}

fn opcode_reads_tainted(op: &Opcode, tainted: &[bool; 256]) -> bool {
    match op {
        Opcode::LoadImm { .. }
        | Opcode::LoadBool { .. }
        | Opcode::LoadConst { .. }
        | Opcode::LoadVar { .. }
        | Opcode::LoadPrime { .. }
        | Opcode::Jump { .. }
        | Opcode::SetPrimeMode { .. }
        | Opcode::Nop
        | Opcode::Halt
        | Opcode::Unchanged { .. } => false,
        Opcode::StoreVar { rs, .. }
        | Opcode::Move { rs, .. }
        | Opcode::NegInt { rs, .. }
        | Opcode::Not { rs, .. }
        | Opcode::Powerset { rs, .. }
        | Opcode::BigUnion { rs, .. }
        | Opcode::Domain { rs, .. }
        | Opcode::RecordGet { rs, .. }
        | Opcode::TupleGet { rs, .. }
        | Opcode::Ret { rs }
        | Opcode::JumpTrue { rs, .. }
        | Opcode::JumpFalse { rs, .. } => tainted[*rs as usize],
        Opcode::AddInt { r1, r2, .. }
        | Opcode::SubInt { r1, r2, .. }
        | Opcode::MulInt { r1, r2, .. }
        | Opcode::DivInt { r1, r2, .. }
        | Opcode::IntDiv { r1, r2, .. }
        | Opcode::ModInt { r1, r2, .. }
        | Opcode::PowInt { r1, r2, .. }
        | Opcode::Eq { r1, r2, .. }
        | Opcode::Neq { r1, r2, .. }
        | Opcode::LtInt { r1, r2, .. }
        | Opcode::LeInt { r1, r2, .. }
        | Opcode::GtInt { r1, r2, .. }
        | Opcode::GeInt { r1, r2, .. }
        | Opcode::And { r1, r2, .. }
        | Opcode::Or { r1, r2, .. }
        | Opcode::Implies { r1, r2, .. }
        | Opcode::Equiv { r1, r2, .. }
        | Opcode::SetUnion { r1, r2, .. }
        | Opcode::SetIntersect { r1, r2, .. }
        | Opcode::SetDiff { r1, r2, .. }
        | Opcode::Subseteq { r1, r2, .. }
        | Opcode::StrConcat { r1, r2, .. }
        | Opcode::Concat { r1, r2, .. } => tainted[*r1 as usize] || tainted[*r2 as usize],
        Opcode::Range { lo, hi, .. } => tainted[*lo as usize] || tainted[*hi as usize],
        Opcode::KSubset { base, k, .. } => tainted[*base as usize] || tainted[*k as usize],
        Opcode::SetIn { elem, set, .. } => tainted[*elem as usize] || tainted[*set as usize],
        Opcode::FuncApply { func, arg, .. } => tainted[*func as usize] || tainted[*arg as usize],
        Opcode::FuncSet { domain, range, .. } => {
            tainted[*domain as usize] || tainted[*range as usize]
        }
        Opcode::FuncExcept {
            func, path, val, ..
        } => tainted[*func as usize] || tainted[*path as usize] || tainted[*val as usize],
        Opcode::CondMove { cond, rs, .. } => tainted[*cond as usize] || tainted[*rs as usize],
        Opcode::SetEnum { start, count, .. }
        | Opcode::TupleNew { start, count, .. }
        | Opcode::SeqNew { start, count, .. }
        | Opcode::Times { start, count, .. } => range_reads_tainted(tainted, *start, *count),
        Opcode::RecordNew {
            values_start,
            count,
            ..
        }
        | Opcode::RecordSet {
            values_start,
            count,
            ..
        } => range_reads_tainted(tainted, *values_start, *count),
        Opcode::FuncDef {
            r_domain,
            r_binding,
            ..
        } => tainted[*r_domain as usize] || tainted[*r_binding as usize],
        Opcode::Call {
            args_start, argc, ..
        }
        | Opcode::CallExternal {
            args_start, argc, ..
        }
        | Opcode::CallBuiltin {
            args_start, argc, ..
        } => range_reads_tainted(tainted, *args_start, *argc),
        Opcode::ValueApply {
            func,
            args_start,
            argc,
            ..
        } => tainted[*func as usize] || range_reads_tainted(tainted, *args_start, *argc),
        Opcode::MakeClosure {
            captures_start,
            capture_count,
            ..
        } => range_reads_tainted(tainted, *captures_start, *capture_count),
        Opcode::ForallBegin {
            r_binding,
            r_domain,
            ..
        }
        | Opcode::ExistsBegin {
            r_binding,
            r_domain,
            ..
        }
        | Opcode::ChooseBegin {
            r_binding,
            r_domain,
            ..
        }
        | Opcode::SetFilterBegin {
            r_binding,
            r_domain,
            ..
        }
        | Opcode::SetBuilderBegin {
            r_binding,
            r_domain,
            ..
        }
        | Opcode::FuncDefBegin {
            r_binding,
            r_domain,
            ..
        } => tainted[*r_binding as usize] || tainted[*r_domain as usize],
        Opcode::ForallNext {
            r_binding, r_body, ..
        }
        | Opcode::ExistsNext {
            r_binding, r_body, ..
        }
        | Opcode::ChooseNext {
            r_binding, r_body, ..
        }
        | Opcode::LoopNext {
            r_binding, r_body, ..
        } => tainted[*r_binding as usize] || tainted[*r_body as usize],
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_assignment_rewrite() {
        let instructions = vec![
            Opcode::LoadVar { rd: 0, var_idx: 0 },
            Opcode::LoadImm { rd: 1, value: 1 },
            Opcode::AddInt {
                rd: 2,
                r1: 0,
                r2: 1,
            },
            Opcode::LoadPrime { rd: 3, var_idx: 0 },
            Opcode::Eq {
                rd: 4,
                r1: 3,
                r2: 2,
            },
            Opcode::Ret { rs: 4 },
        ];

        let ActionTransformOutcome::Transformed(transformed) =
            transform_action_to_next_state(&instructions)
        else {
            panic!("should rewrite simple assignment");
        };

        assert_eq!(transformed[3], Opcode::LoadBool { rd: 4, value: true });
        assert_eq!(transformed[4], Opcode::StoreVar { var_idx: 0, rs: 2 });
    }

    #[test]
    fn test_reversed_eq_operands() {
        let instructions = vec![
            Opcode::LoadImm { rd: 0, value: 42 },
            Opcode::LoadPrime { rd: 1, var_idx: 0 },
            Opcode::Eq {
                rd: 2,
                r1: 0,
                r2: 1,
            },
            Opcode::Ret { rs: 2 },
        ];

        let ActionTransformOutcome::Transformed(transformed) =
            transform_action_to_next_state(&instructions)
        else {
            panic!("should rewrite reversed assignment");
        };

        assert_eq!(transformed[1], Opcode::LoadBool { rd: 2, value: true });
        assert_eq!(transformed[2], Opcode::StoreVar { var_idx: 0, rs: 0 });
    }

    #[test]
    fn test_no_prime_returns_no_rewrite() {
        let instructions = vec![
            Opcode::LoadVar { rd: 0, var_idx: 0 },
            Opcode::LoadImm { rd: 1, value: 5 },
            Opcode::LtInt {
                rd: 2,
                r1: 0,
                r2: 1,
            },
            Opcode::Ret { rs: 2 },
        ];

        assert_eq!(
            transform_action_to_next_state(&instructions),
            ActionTransformOutcome::NoRewrite
        );
    }

    #[test]
    fn test_unchanged_only_action_is_executable_next_state() {
        let instructions = vec![
            Opcode::LoadVar { rd: 0, var_idx: 0 },
            Opcode::LoadImm { rd: 1, value: 1 },
            Opcode::Eq {
                rd: 2,
                r1: 0,
                r2: 1,
            },
            Opcode::Unchanged {
                rd: 3,
                start: 0,
                count: 1,
            },
            Opcode::And {
                rd: 4,
                r1: 2,
                r2: 3,
            },
            Opcode::Ret { rs: 4 },
        ];

        let ActionTransformOutcome::Transformed(transformed) =
            transform_action_to_next_state(&instructions)
        else {
            panic!("UNCHANGED-only action should stay executable");
        };

        assert_eq!(
            transformed, instructions,
            "UNCHANGED-only actions rely on caller-seeded state_out"
        );
    }

    #[test]
    fn test_unchanged_preserved() {
        let instructions = vec![
            Opcode::LoadVar { rd: 0, var_idx: 0 },
            Opcode::LoadImm { rd: 1, value: 1 },
            Opcode::AddInt {
                rd: 2,
                r1: 0,
                r2: 1,
            },
            Opcode::LoadPrime { rd: 3, var_idx: 0 },
            Opcode::Eq {
                rd: 4,
                r1: 3,
                r2: 2,
            },
            Opcode::Unchanged {
                rd: 5,
                start: 0,
                count: 1,
            },
            Opcode::Ret { rs: 5 },
        ];

        let ActionTransformOutcome::Transformed(transformed) =
            transform_action_to_next_state(&instructions)
        else {
            panic!("should rewrite assignment with unchanged");
        };

        assert_eq!(transformed[3], Opcode::LoadBool { rd: 4, value: true });
        assert_eq!(transformed[4], Opcode::StoreVar { var_idx: 0, rs: 2 });
        assert!(matches!(
            transformed[5],
            Opcode::Unchanged {
                rd: 5,
                start: 0,
                count: 1
            }
        ));
    }

    #[test]
    fn test_prime_first_self_copy_rewrite() {
        let instructions = vec![
            Opcode::LoadPrime { rd: 0, var_idx: 0 },
            Opcode::LoadVar { rd: 1, var_idx: 0 },
            Opcode::Eq {
                rd: 2,
                r1: 0,
                r2: 1,
            },
            Opcode::Ret { rs: 2 },
        ];

        let ActionTransformOutcome::Transformed(transformed) =
            transform_action_to_next_state(&instructions)
        else {
            panic!("should rewrite prime-first self-copy");
        };

        assert_eq!(transformed[0], Opcode::LoadBool { rd: 2, value: true });
        assert_eq!(transformed[2], Opcode::StoreVar { var_idx: 0, rs: 1 });
    }

    #[test]
    fn test_prime_first_rhs_computation_rewrite() {
        let instructions = vec![
            Opcode::LoadPrime { rd: 0, var_idx: 0 },
            Opcode::LoadVar { rd: 1, var_idx: 0 },
            Opcode::LoadImm { rd: 2, value: 1 },
            Opcode::AddInt {
                rd: 3,
                r1: 1,
                r2: 2,
            },
            Opcode::Eq {
                rd: 4,
                r1: 0,
                r2: 3,
            },
            Opcode::Ret { rs: 4 },
        ];

        let ActionTransformOutcome::Transformed(transformed) =
            transform_action_to_next_state(&instructions)
        else {
            panic!("should rewrite prime-first rhs computation");
        };

        assert_eq!(transformed[0], Opcode::LoadBool { rd: 4, value: true });
        assert_eq!(transformed[4], Opcode::StoreVar { var_idx: 0, rs: 3 });
    }

    #[test]
    fn test_prime_tainted_rhs_is_rejected() {
        let instructions = vec![
            Opcode::LoadPrime { rd: 0, var_idx: 1 },
            Opcode::LoadPrime { rd: 1, var_idx: 0 },
            Opcode::Eq {
                rd: 2,
                r1: 1,
                r2: 0,
            },
            Opcode::Ret { rs: 2 },
        ];

        let ActionTransformOutcome::Unsafe(reason) = transform_action_to_next_state(&instructions)
        else {
            panic!("cross-prime assignment must be rejected");
        };
        assert!(reason.contains("prime-tainted RHS"));
    }

    #[test]
    fn test_duplicate_store_is_rejected() {
        let instructions = vec![
            Opcode::LoadImm { rd: 0, value: 1 },
            Opcode::LoadPrime { rd: 1, var_idx: 0 },
            Opcode::Eq {
                rd: 2,
                r1: 1,
                r2: 0,
            },
            Opcode::LoadImm { rd: 3, value: 2 },
            Opcode::LoadPrime { rd: 4, var_idx: 0 },
            Opcode::Eq {
                rd: 5,
                r1: 4,
                r2: 3,
            },
            Opcode::Ret { rs: 5 },
        ];

        let ActionTransformOutcome::Unsafe(reason) = transform_action_to_next_state(&instructions)
        else {
            panic!("duplicate stores must be rejected");
        };
        assert!(reason.contains("duplicate writes"));
    }

    #[test]
    fn test_eq_result_register_live_before_rewrite_is_rejected() {
        let instructions = vec![
            Opcode::LoadImm { rd: 1, value: 42 },
            Opcode::LoadPrime { rd: 0, var_idx: 0 },
            // r1 is still live between LoadPrime and Eq, so moving the
            // Eq result write to pc=1 would clobber it before this Move.
            Opcode::Move { rd: 2, rs: 1 },
            Opcode::Eq {
                rd: 1,
                r1: 0,
                r2: 2,
            },
            Opcode::Ret { rs: 1 },
        ];

        let ActionTransformOutcome::Unsafe(reason) = transform_action_to_next_state(&instructions)
        else {
            panic!("live Eq destination must be rejected");
        };
        assert!(reason.contains("conflicts with live RHS"));
    }
}
