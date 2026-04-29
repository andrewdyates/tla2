// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for the bytecode VM executor.

mod builtins;
mod call;
mod compound_values;
mod lambda_closure;
mod scalar_ops;
mod state_and_loops;

use super::execute::{BytecodeVm, VmError};
use std::sync::Arc;
use tla_core::intern_name;
use tla_tir::bytecode::{BytecodeChunk, BytecodeFunction, ConstantPool, Opcode};
use tla_value::{SortedSet, Value};

/// Helper: execute a single function with given state.
pub(super) fn exec(func: BytecodeFunction, constants: ConstantPool, state: &[Value]) -> Value {
    exec_with_next(func, constants, state, None)
}

/// Helper: execute a single function with given state and optional next state.
pub(super) fn exec_with_next(
    func: BytecodeFunction,
    constants: ConstantPool,
    state: &[Value],
    next_state: Option<&[Value]>,
) -> Value {
    let mut chunk = BytecodeChunk::new();
    chunk.constants = constants;
    chunk.add_function(func);
    let mut vm = BytecodeVm::new(&chunk, state, next_state);
    vm.execute_function(0).expect("VM execution failed")
}

/// Helper: construct a BytecodeFunction with instructions.
pub(super) fn make_func(
    name: String,
    arity: u8,
    instructions: Vec<Opcode>,
    max_register: u8,
) -> BytecodeFunction {
    BytecodeFunction {
        name,
        arity,
        max_register,
        instructions,
    }
}

/// Helper: build and execute a simple function.
pub(super) fn exec_simple(instructions: Vec<Opcode>, max_reg: u8) -> Value {
    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.max_register = max_reg;
    func.instructions = instructions;
    exec(func, ConstantPool::new(), &[])
}
