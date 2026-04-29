// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Validation for next-state action bytecode eligibility.
//!
//! The action transform rewrites entry actions from predicate form into
//! next-state functions, but LLVM2 and the JIT may still traverse `Call`
//! edges through the shared bytecode chunk. To keep the next-state ABI
//! sound, retained entry actions must not reach helper functions that still
//! depend on primed-state evaluation machinery.

use rustc_hash::FxHashSet;
use tla_tir::bytecode::{BytecodeChunk, BytecodeFunction, Opcode};

/// Validate a transformed next-state action entry and every reachable callee.
///
/// Entry actions may write successor state via `StoreVar` and `Unchanged`,
/// but reachable helper functions must stay pure current-state computations.
/// Any primed-state opcode that survives in the closure is rejected before
/// LLVM2/JIT can compile it.
pub(crate) fn validate_next_state_action_chunk(
    entry_func_idx: u16,
    entry_instructions: &[Opcode],
    chunk: &BytecodeChunk,
    state_var_count: usize,
) -> Result<(), String> {
    validate_entry_shape(entry_instructions, &chunk.constants, state_var_count)?;
    validate_reachable_callees(entry_func_idx, entry_instructions, chunk)
}

fn validate_entry_shape(
    instructions: &[Opcode],
    constants: &tla_tir::bytecode::ConstantPool,
    state_var_count: usize,
) -> Result<(), String> {
    let mut stored_vars = std::collections::BTreeSet::new();
    let mut unchanged_vars = std::collections::BTreeSet::new();

    for op in instructions {
        match *op {
            Opcode::LoadPrime { .. } => {
                return Err("residual LoadPrime remains after action rewrite".to_string());
            }
            Opcode::SetPrimeMode { .. } => {
                return Err("SetPrimeMode remains after action rewrite".to_string());
            }
            Opcode::StoreVar { var_idx, .. } => {
                if !stored_vars.insert(var_idx) {
                    return Err(format!("duplicate writes to primed var {var_idx}"));
                }
            }
            Opcode::Unchanged { start, count, .. } => {
                for offset in 0..count as u16 {
                    let value = constants.get_value(start + offset);
                    let tla_value::Value::SmallInt(var_idx) = value else {
                        return Err("Unchanged metadata does not decode to SmallInt var indices"
                            .to_string());
                    };
                    unchanged_vars.insert(*var_idx as u16);
                }
            }
            _ => {}
        }
    }

    if let Some(var_idx) = stored_vars.intersection(&unchanged_vars).next() {
        return Err(format!(
            "primed var {var_idx} is both written and UNCHANGED"
        ));
    }

    if stored_vars.is_empty()
        && !unchanged_vars.is_empty()
        && unchanged_vars.len() != state_var_count
    {
        return Err(format!(
            "UNCHANGED-only action covers {} of {state_var_count} state variables",
            unchanged_vars.len()
        ));
    }

    Ok(())
}

fn validate_reachable_callees(
    entry_func_idx: u16,
    entry_instructions: &[Opcode],
    chunk: &BytecodeChunk,
) -> Result<(), String> {
    let mut visited = FxHashSet::default();
    let mut pending = collect_direct_callees(entry_instructions);

    while let Some(func_idx) = pending.pop() {
        if !visited.insert(func_idx) {
            continue;
        }

        let callee = chunk.functions.get(func_idx as usize).ok_or_else(|| {
            format!("entry action {entry_func_idx} references missing callee {func_idx}")
        })?;

        validate_helper_shape(func_idx, callee)?;
        pending.extend(collect_direct_callees(&callee.instructions));
    }

    Ok(())
}

fn collect_direct_callees(instructions: &[Opcode]) -> Vec<u16> {
    instructions
        .iter()
        .filter_map(|op| match *op {
            Opcode::Call { op_idx, .. } => Some(op_idx),
            _ => None,
        })
        .collect()
}

fn validate_helper_shape(func_idx: u16, func: &BytecodeFunction) -> Result<(), String> {
    for op in &func.instructions {
        match *op {
            Opcode::LoadPrime { .. } => {
                return Err(format!("reachable callee {func_idx} contains LoadPrime"));
            }
            Opcode::SetPrimeMode { .. } => {
                return Err(format!("reachable callee {func_idx} contains SetPrimeMode"));
            }
            Opcode::StoreVar { .. } => {
                return Err(format!(
                    "reachable callee {func_idx} writes successor state"
                ));
            }
            Opcode::Unchanged { .. } => {
                return Err(format!(
                    "reachable callee {func_idx} contains Unchanged next-state check"
                ));
            }
            _ => {}
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use tla_tir::bytecode::BytecodeFunction;

    fn make_entry_with_call(op_idx: u16) -> Vec<Opcode> {
        vec![
            Opcode::LoadImm { rd: 0, value: 1 },
            Opcode::Call {
                rd: 1,
                op_idx,
                args_start: 0,
                argc: 0,
            },
            Opcode::StoreVar { var_idx: 0, rs: 0 },
            Opcode::Ret { rs: 1 },
        ]
    }

    #[test]
    fn test_rejects_reachable_callee_with_load_prime() {
        let entry = make_entry_with_call(1);
        let mut helper = BytecodeFunction::new("BadPrimeHelper".to_string(), 0);
        helper.emit(Opcode::LoadPrime { rd: 0, var_idx: 1 });
        helper.emit(Opcode::Ret { rs: 0 });

        let mut chunk = BytecodeChunk::new();
        chunk.add_function(BytecodeFunction::new("Entry".to_string(), 0));
        chunk.add_function(helper);

        let reason =
            validate_next_state_action_chunk(0, &entry, &chunk, 2).expect_err("helper must reject");
        assert!(reason.contains("reachable callee 1 contains LoadPrime"));
    }

    #[test]
    fn test_rejects_reachable_callee_with_set_prime_mode() {
        let entry = make_entry_with_call(1);
        let mut helper = BytecodeFunction::new("BadPrimeModeHelper".to_string(), 0);
        helper.emit(Opcode::SetPrimeMode { enable: true });
        helper.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        helper.emit(Opcode::SetPrimeMode { enable: false });
        helper.emit(Opcode::Ret { rs: 0 });

        let mut chunk = BytecodeChunk::new();
        chunk.add_function(BytecodeFunction::new("Entry".to_string(), 0));
        chunk.add_function(helper);

        let reason =
            validate_next_state_action_chunk(0, &entry, &chunk, 1).expect_err("helper must reject");
        assert!(reason.contains("reachable callee 1 contains SetPrimeMode"));
    }

    #[test]
    fn test_accepts_pure_reachable_callee() {
        let entry = make_entry_with_call(1);
        let mut helper = BytecodeFunction::new("PureHelper".to_string(), 0);
        helper.emit(Opcode::LoadVar { rd: 0, var_idx: 1 });
        helper.emit(Opcode::LoadImm { rd: 1, value: 1 });
        helper.emit(Opcode::AddInt {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        helper.emit(Opcode::Ret { rs: 2 });

        let mut chunk = BytecodeChunk::new();
        chunk.add_function(BytecodeFunction::new("Entry".to_string(), 0));
        chunk.add_function(helper);

        validate_next_state_action_chunk(0, &entry, &chunk, 2)
            .expect("pure helper should remain eligible");
    }

    #[test]
    fn test_accepts_unchanged_only_full_state_action() {
        let mut chunk = BytecodeChunk::new();
        let start = chunk.constants.add_value(tla_value::Value::SmallInt(0));
        chunk.constants.add_value(tla_value::Value::SmallInt(1));
        chunk.add_function(BytecodeFunction::new("Entry".to_string(), 0));
        let entry = vec![
            Opcode::Unchanged {
                rd: 0,
                start,
                count: 2,
            },
            Opcode::Ret { rs: 0 },
        ];

        validate_next_state_action_chunk(0, &entry, &chunk, 2)
            .expect("full-state UNCHANGED action should be executable");
    }

    #[test]
    fn test_rejects_unchanged_only_partial_state_action() {
        let mut chunk = BytecodeChunk::new();
        let start = chunk.constants.add_value(tla_value::Value::SmallInt(0));
        chunk.add_function(BytecodeFunction::new("Entry".to_string(), 0));
        let entry = vec![
            Opcode::Unchanged {
                rd: 0,
                start,
                count: 1,
            },
            Opcode::Ret { rs: 0 },
        ];

        let reason = validate_next_state_action_chunk(0, &entry, &chunk, 2)
            .expect_err("partial-frame UNCHANGED-only action must stay uncompiled");
        assert!(reason.contains("UNCHANGED-only action covers 1 of 2 state variables"));
    }
}
