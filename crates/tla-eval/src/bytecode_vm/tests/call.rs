// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Call opcode test suite: parameter passing, zero-arg calls, transitive calls,
//! caller-register preservation, and recursion-depth guard.

use super::{make_func, BytecodeChunk, BytecodeVm, ConstantPool, Opcode, Value, VmError};
use std::sync::Arc;
use tla_value::FuncValue;

/// Test Call opcode: callee is a separate function in the chunk.
/// Add(x, y) == x + y, Main calls Add(3, 4) → 7
#[test]
fn test_vm_call_parameterized() {
    let constants = ConstantPool::new();
    let mut chunk = BytecodeChunk::new();

    // Function 0: Add(x, y) == x + y
    let add_func = make_func(
        "Add".to_string(),
        2,
        vec![
            Opcode::AddInt {
                rd: 2,
                r1: 0,
                r2: 1,
            },
            Opcode::Ret { rs: 2 },
        ],
        2,
    );
    chunk.add_function(add_func);

    // Function 1: Main == Add(3, 4)
    let main_func = make_func(
        "Main".to_string(),
        0,
        vec![
            Opcode::LoadImm { rd: 0, value: 3 },
            Opcode::LoadImm { rd: 1, value: 4 },
            Opcode::Call {
                rd: 2,
                op_idx: 0,
                args_start: 0,
                argc: 2,
            },
            Opcode::Ret { rs: 2 },
        ],
        2,
    );
    chunk.add_function(main_func);

    chunk.constants = constants;
    let state: Vec<Value> = vec![];
    let mut vm = BytecodeVm::new(&chunk, &state, None);
    let result = vm.execute_function(1).expect("VM execution failed");
    assert_eq!(result, Value::SmallInt(7));
}

/// Test Call opcode: zero-arg callee.
/// N == 42, Main == N + 1 → 43
#[test]
fn test_vm_call_zero_arg() {
    let constants = ConstantPool::new();
    let mut chunk = BytecodeChunk::new();

    // Function 0: N == 42
    let n_func = make_func(
        "N".to_string(),
        0,
        vec![Opcode::LoadImm { rd: 0, value: 42 }, Opcode::Ret { rs: 0 }],
        0,
    );
    chunk.add_function(n_func);

    // Function 1: Main == N + 1
    let main_func = make_func(
        "Main".to_string(),
        0,
        vec![
            Opcode::Call {
                rd: 0,
                op_idx: 0,
                args_start: 0,
                argc: 0,
            },
            Opcode::LoadImm { rd: 1, value: 1 },
            Opcode::AddInt {
                rd: 2,
                r1: 0,
                r2: 1,
            },
            Opcode::Ret { rs: 2 },
        ],
        2,
    );
    chunk.add_function(main_func);

    chunk.constants = constants;
    let state: Vec<Value> = vec![];
    let mut vm = BytecodeVm::new(&chunk, &state, None);
    let result = vm.execute_function(1).expect("VM execution failed");
    assert_eq!(result, Value::SmallInt(43));
}

/// Test Call opcode: transitive calls (A calls B calls C).
/// C == 10, B == C + 5, A == B + 1 → 16
#[test]
fn test_vm_call_transitive() {
    let constants = ConstantPool::new();
    let mut chunk = BytecodeChunk::new();

    // Function 0: C == 10
    let c_func = make_func(
        "C".to_string(),
        0,
        vec![Opcode::LoadImm { rd: 0, value: 10 }, Opcode::Ret { rs: 0 }],
        0,
    );
    chunk.add_function(c_func);

    // Function 1: B == C + 5
    let b_func = make_func(
        "B".to_string(),
        0,
        vec![
            Opcode::Call {
                rd: 0,
                op_idx: 0,
                args_start: 0,
                argc: 0,
            },
            Opcode::LoadImm { rd: 1, value: 5 },
            Opcode::AddInt {
                rd: 2,
                r1: 0,
                r2: 1,
            },
            Opcode::Ret { rs: 2 },
        ],
        2,
    );
    chunk.add_function(b_func);

    // Function 2: A == B + 1
    let a_func = make_func(
        "A".to_string(),
        0,
        vec![
            Opcode::Call {
                rd: 0,
                op_idx: 1,
                args_start: 0,
                argc: 0,
            },
            Opcode::LoadImm { rd: 1, value: 1 },
            Opcode::AddInt {
                rd: 2,
                r1: 0,
                r2: 1,
            },
            Opcode::Ret { rs: 2 },
        ],
        2,
    );
    chunk.add_function(a_func);

    chunk.constants = constants;
    let state: Vec<Value> = vec![];
    let mut vm = BytecodeVm::new(&chunk, &state, None);
    let result = vm.execute_function(2).expect("VM execution failed");
    assert_eq!(result, Value::SmallInt(16));
}

/// Test Call opcode: callee register writes must not clobber caller registers.
#[test]
fn test_vm_call_preserves_caller_registers() {
    let constants = ConstantPool::new();
    let mut chunk = BytecodeChunk::new();

    // Function 0: Inc(x) == x + 1
    let inc_func = make_func(
        "Inc".to_string(),
        1,
        vec![
            Opcode::LoadImm { rd: 1, value: 1 },
            Opcode::AddInt {
                rd: 2,
                r1: 0,
                r2: 1,
            },
            Opcode::Ret { rs: 2 },
        ],
        2,
    );
    chunk.add_function(inc_func);

    // Function 1:
    //   caller r0 = 40, caller r1 = 2
    //   r2 = Inc(r1)
    //   return r0 + r1 + r2 = 45
    let main_func = make_func(
        "Main".to_string(),
        0,
        vec![
            Opcode::LoadImm { rd: 0, value: 40 },
            Opcode::LoadImm { rd: 1, value: 2 },
            Opcode::Call {
                rd: 2,
                op_idx: 0,
                args_start: 1,
                argc: 1,
            },
            Opcode::AddInt {
                rd: 3,
                r1: 0,
                r2: 2,
            },
            Opcode::AddInt {
                rd: 4,
                r1: 1,
                r2: 3,
            },
            Opcode::Ret { rs: 4 },
        ],
        4,
    );
    chunk.add_function(main_func);

    chunk.constants = constants;
    let state: Vec<Value> = vec![];
    let mut vm = BytecodeVm::new(&chunk, &state, None);
    let result = vm.execute_function(1).expect("VM execution failed");
    assert_eq!(result, Value::SmallInt(45));
}

/// Test Call opcode: recursion must fail closed at the VM depth guard and
/// leave the VM reusable afterward.
#[test]
fn test_vm_call_depth_guard_and_reset() {
    let constants = ConstantPool::new();
    let mut chunk = BytecodeChunk::new();

    let recursive = make_func(
        "Loop".to_string(),
        0,
        vec![
            Opcode::Call {
                rd: 0,
                op_idx: 0,
                args_start: 0,
                argc: 0,
            },
            Opcode::Ret { rs: 0 },
        ],
        0,
    );
    chunk.add_function(recursive);

    let ok_func = make_func(
        "Ok".to_string(),
        0,
        vec![Opcode::LoadImm { rd: 0, value: 7 }, Opcode::Ret { rs: 0 }],
        0,
    );
    chunk.add_function(ok_func);

    chunk.constants = constants;
    let state: Vec<Value> = vec![];
    let mut vm = BytecodeVm::new(&chunk, &state, None);

    let err = vm
        .execute_function(0)
        .expect_err("recursive call should hit depth guard");
    assert!(
        matches!(err, VmError::Unsupported(ref msg) if msg.contains("call depth exceeded")),
        "expected depth guard error, got {err:?}"
    );

    let ok = vm
        .execute_function(1)
        .expect("depth counter should reset after guarded failure");
    assert_eq!(ok, Value::SmallInt(7));
}

/// Test ValueApply opcode: apply a function value to a single argument.
/// f = {1 |-> 10, 2 |-> 20}, ValueApply(f, 2) → 20
#[test]
fn test_vm_value_apply_func_single_arg() {
    let mut constants = ConstantPool::new();
    let func_val = Value::Func(Arc::new(FuncValue::from_sorted_entries(vec![
        (Value::SmallInt(1), Value::SmallInt(10)),
        (Value::SmallInt(2), Value::SmallInt(20)),
    ])));
    let const_idx = constants.add_value(func_val);

    let main_func = make_func(
        "Main".to_string(),
        0,
        vec![
            Opcode::LoadConst {
                rd: 0,
                idx: const_idx,
            },
            Opcode::LoadImm { rd: 1, value: 2 },
            Opcode::ValueApply {
                rd: 2,
                func: 0,
                args_start: 1,
                argc: 1,
            },
            Opcode::Ret { rs: 2 },
        ],
        2,
    );

    let mut chunk = BytecodeChunk::new();
    chunk.constants = constants;
    chunk.add_function(main_func);
    let state: Vec<Value> = vec![];
    let mut vm = BytecodeVm::new(&chunk, &state, None);
    let result = vm.execute_function(0).expect("VM execution failed");
    assert_eq!(result, Value::SmallInt(20));
}

/// Test ValueApply opcode: apply a tuple as a function (TLA+ tuples are 1-indexed functions).
/// t = <<100, 200, 300>>, ValueApply(t, 2) → 200
#[test]
fn test_vm_value_apply_tuple_as_func() {
    let mut constants = ConstantPool::new();
    let tuple_val = Value::Tuple(
        vec![
            Value::SmallInt(100),
            Value::SmallInt(200),
            Value::SmallInt(300),
        ]
        .into(),
    );
    let const_idx = constants.add_value(tuple_val);

    let main_func = make_func(
        "Main".to_string(),
        0,
        vec![
            Opcode::LoadConst {
                rd: 0,
                idx: const_idx,
            },
            Opcode::LoadImm { rd: 1, value: 2 },
            Opcode::ValueApply {
                rd: 2,
                func: 0,
                args_start: 1,
                argc: 1,
            },
            Opcode::Ret { rs: 2 },
        ],
        2,
    );

    let mut chunk = BytecodeChunk::new();
    chunk.constants = constants;
    chunk.add_function(main_func);
    let state: Vec<Value> = vec![];
    let mut vm = BytecodeVm::new(&chunk, &state, None);
    let result = vm.execute_function(0).expect("VM execution failed");
    assert_eq!(result, Value::SmallInt(200));
}

/// Test ValueApply opcode: applying a non-callable multi-arg value fails
/// gracefully (closures would need EvalCtx, non-closure multi-arg is unsupported).
#[test]
fn test_vm_value_apply_multi_arg_non_closure_errors() {
    let mut constants = ConstantPool::new();
    let func_val = Value::Func(Arc::new(FuncValue::from_sorted_entries(vec![(
        Value::SmallInt(1),
        Value::SmallInt(10),
    )])));
    let const_idx = constants.add_value(func_val);

    let main_func = make_func(
        "Main".to_string(),
        0,
        vec![
            Opcode::LoadConst {
                rd: 0,
                idx: const_idx,
            },
            Opcode::LoadImm { rd: 1, value: 1 },
            Opcode::LoadImm { rd: 2, value: 2 },
            Opcode::ValueApply {
                rd: 3,
                func: 0,
                args_start: 1,
                argc: 2,
            },
            Opcode::Ret { rs: 3 },
        ],
        3,
    );

    let mut chunk = BytecodeChunk::new();
    chunk.constants = constants;
    chunk.add_function(main_func);
    let state: Vec<Value> = vec![];
    let mut vm = BytecodeVm::new(&chunk, &state, None);
    let err = vm
        .execute_function(0)
        .expect_err("multi-arg ValueApply on non-closure should error");
    assert!(
        matches!(err, VmError::Unsupported(ref msg) if msg.contains("value apply")),
        "expected unsupported error for multi-arg non-closure, got {err:?}"
    );
}
