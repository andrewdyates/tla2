// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Action predicate → next-state function transformation.
//!
//! TLA+ actions are boolean predicates (`x' = expr /\ UNCHANGED y`).
//! The JIT next-state cache requires bytecode functions that **produce**
//! successor states using `StoreVar` opcodes.
//!
//! This module transforms compiled action predicate bytecode into
//! next-state function bytecode by rewriting patterns:
//!
//! ```text
//! LoadPrime { rd: rp, var_idx: x }   ─┐
//! Eq { rd: req, r1: rp, r2: rexpr }  ─┘ → StoreVar { var_idx: x, rs: rexpr }
//!                                          LoadBool { rd: req, value: true }
//! ```
//!
//! `Unchanged` opcodes are kept as-is — the JIT lowerer handles them
//! by comparing `state_in[x] == state_out[x]` and the caller
//! pre-fills `state_out` from `state_in`.
//!
//! Part of #3910: Enable JIT next-state dispatch for action operators.

use super::opcode::{Opcode, Register, VarIdx};

/// Transform an action predicate's bytecode into next-state function bytecode.
///
/// Scans for `LoadPrime(x) → Eq(prime_reg, expr_reg)` patterns and rewrites
/// them to `StoreVar(x, expr_reg) → LoadBool(true)`. Also handles the
/// reversed case `Eq(expr_reg, prime_reg)`.
///
/// Returns `Some(transformed_instructions)` if at least one `StoreVar` was
/// emitted, or `None` if no suitable patterns were found (the action is too
/// complex for this simple rewriting).
pub fn transform_action_to_next_state(instructions: &[Opcode]) -> Option<Vec<Opcode>> {
    if instructions.is_empty() {
        return None;
    }

    // Phase 1: Identify LoadPrime instructions and their consuming Eq.
    // Build a map: register → (var_idx, pc) for LoadPrime outputs.
    let mut prime_defs: Vec<Option<(VarIdx, usize)>> = vec![None; 256];
    let mut rewrites: Vec<(usize, usize, VarIdx, Register)> = Vec::new(); // (prime_pc, eq_pc, var_idx, expr_reg)

    for (pc, op) in instructions.iter().enumerate() {
        match *op {
            Opcode::LoadPrime { rd, var_idx } => {
                prime_defs[rd as usize] = Some((var_idx, pc));
            }
            Opcode::Eq { rd: _, r1, r2 } => {
                // Check if r1 is a LoadPrime result
                if let Some((var_idx, prime_pc)) = prime_defs[r1 as usize] {
                    rewrites.push((prime_pc, pc, var_idx, r2));
                    prime_defs[r1 as usize] = None; // consumed
                }
                // Check if r2 is a LoadPrime result (reversed operands)
                else if let Some((var_idx, prime_pc)) = prime_defs[r2 as usize] {
                    rewrites.push((prime_pc, pc, var_idx, r1));
                    prime_defs[r2 as usize] = None; // consumed
                }
            }
            // Any write to a register kills the prime_def
            _ => {
                if let Some(rd) = dest_register(op) {
                    prime_defs[rd as usize] = None;
                }
            }
        }
    }

    if rewrites.is_empty() {
        return None;
    }

    // Phase 2: Apply rewrites.
    let mut result = instructions.to_vec();
    for &(prime_pc, eq_pc, var_idx, expr_reg) in &rewrites {
        // Replace LoadPrime with StoreVar
        result[prime_pc] = Opcode::StoreVar {
            var_idx,
            rs: expr_reg,
        };
        // Replace Eq with LoadBool(true) — the assignment always "succeeds"
        let eq_rd = match result[eq_pc] {
            Opcode::Eq { rd, .. } => rd,
            _ => unreachable!(),
        };
        result[eq_pc] = Opcode::LoadBool {
            rd: eq_rd,
            value: true,
        };
    }

    Some(result)
}

/// Extract the destination register of an opcode, if any.
///
/// Uses the `dest_register()` method from `opcode_support` which is
/// authoritative for all opcode variants.
fn dest_register(op: &Opcode) -> Option<Register> {
    op.dest_register()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_assignment_rewrite() {
        // x' = x + 1: LoadVar(x) → AddInt → LoadPrime(x) → Eq
        let instructions = vec![
            Opcode::LoadVar {
                rd: 0,
                var_idx: 0,
            },
            Opcode::LoadImm { rd: 1, value: 1 },
            Opcode::AddInt {
                rd: 2,
                r1: 0,
                r2: 1,
            },
            Opcode::LoadPrime {
                rd: 3,
                var_idx: 0,
            },
            Opcode::Eq {
                rd: 4,
                r1: 3,
                r2: 2,
            },
            Opcode::Ret { rs: 4 },
        ];

        let result = transform_action_to_next_state(&instructions);
        assert!(result.is_some(), "should rewrite simple assignment");
        let transformed = result.unwrap();

        // LoadPrime(rd=3) → StoreVar(var_idx=0, rs=2)
        assert_eq!(
            transformed[3],
            Opcode::StoreVar {
                var_idx: 0,
                rs: 2
            }
        );
        // Eq(rd=4) → LoadBool(rd=4, true)
        assert_eq!(
            transformed[4],
            Opcode::LoadBool {
                rd: 4,
                value: true
            }
        );
    }

    #[test]
    fn test_reversed_eq_operands() {
        // x' = 42 with Eq(r1=expr, r2=prime)
        let instructions = vec![
            Opcode::LoadImm { rd: 0, value: 42 },
            Opcode::LoadPrime {
                rd: 1,
                var_idx: 0,
            },
            Opcode::Eq {
                rd: 2,
                r1: 0,
                r2: 1,
            },
            Opcode::Ret { rs: 2 },
        ];

        let result = transform_action_to_next_state(&instructions);
        assert!(result.is_some());
        let transformed = result.unwrap();

        assert_eq!(
            transformed[1],
            Opcode::StoreVar {
                var_idx: 0,
                rs: 0
            }
        );
        assert_eq!(
            transformed[2],
            Opcode::LoadBool {
                rd: 2,
                value: true
            }
        );
    }

    #[test]
    fn test_no_prime_returns_none() {
        // Pure boolean predicate — no LoadPrime
        let instructions = vec![
            Opcode::LoadVar {
                rd: 0,
                var_idx: 0,
            },
            Opcode::LoadImm { rd: 1, value: 5 },
            Opcode::LtInt {
                rd: 2,
                r1: 0,
                r2: 1,
            },
            Opcode::Ret { rs: 2 },
        ];

        assert!(transform_action_to_next_state(&instructions).is_none());
    }

    #[test]
    fn test_unchanged_preserved() {
        // x' = x + 1 /\ UNCHANGED y
        let instructions = vec![
            Opcode::LoadVar {
                rd: 0,
                var_idx: 0,
            },
            Opcode::LoadImm { rd: 1, value: 1 },
            Opcode::AddInt {
                rd: 2,
                r1: 0,
                r2: 1,
            },
            Opcode::LoadPrime {
                rd: 3,
                var_idx: 0,
            },
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

        let result = transform_action_to_next_state(&instructions);
        assert!(result.is_some());
        let transformed = result.unwrap();

        // StoreVar replaces LoadPrime
        assert_eq!(
            transformed[3],
            Opcode::StoreVar {
                var_idx: 0,
                rs: 2
            }
        );
        // Unchanged is preserved
        assert!(matches!(
            transformed[5],
            Opcode::Unchanged {
                rd: 5,
                start: 0,
                count: 1
            }
        ));
    }
}
