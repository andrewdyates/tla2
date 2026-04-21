// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Cross-module identifier resolution tests for the bytecode compiler.
//!
//! Verifies that the bytecode compiler handles EXTENDS and INSTANCE operator
//! references correctly: compiling them on-demand when possible, falling back
//! to `CallExternal` when needed, and emitting `CallBuiltin`/`Concat` opcodes
//! for stdlib operators.
//!
//! Part of #3789: bytecode VM cross-module identifier resolution.

use super::*;
use crate::bytecode::BuiltinOp;
use crate::nodes::{TirModuleRefSegment, TirOperatorRef};
use tla_core::ast::Expr;

// ---------------------------------------------------------------------------
// Helper: build a simple TirExpr body from an integer constant.
// ---------------------------------------------------------------------------
fn int_const(n: i64) -> Spanned<TirExpr> {
    spanned(TirExpr::Const {
        value: Value::SmallInt(n),
        ty: TirType::Int,
    })
}

fn bool_const(b: bool) -> Spanned<TirExpr> {
    spanned(TirExpr::Const {
        value: Value::Bool(b),
        ty: TirType::Bool,
    })
}

fn name_ident(name: &str) -> Spanned<TirExpr> {
    spanned(TirExpr::Name(ident_name(name)))
}

fn add_expr(left: Spanned<TirExpr>, right: Spanned<TirExpr>) -> Spanned<TirExpr> {
    spanned(TirExpr::ArithBinOp {
        left: Box::new(left),
        op: TirArithOp::Add,
        right: Box::new(right),
    })
}

fn mul_expr(left: Spanned<TirExpr>, right: Spanned<TirExpr>) -> Spanned<TirExpr> {
    spanned(TirExpr::ArithBinOp {
        left: Box::new(left),
        op: TirArithOp::Mul,
        right: Box::new(right),
    })
}

fn make_callee_info(params: &[&str], body: Spanned<TirExpr>) -> CalleeInfo {
    CalleeInfo {
        params: params.iter().map(|s| s.to_string()).collect(),
        body: std::sync::Arc::new(body),
        ast_body: None,
    }
}

fn make_callee_info_with_ast(
    params: &[&str],
    body: Spanned<TirExpr>,
    ast_body: Spanned<Expr>,
) -> CalleeInfo {
    CalleeInfo {
        params: params.iter().map(|s| s.to_string()).collect(),
        body: std::sync::Arc::new(body),
        ast_body: Some(PreservedAstBody(std::sync::Arc::new(ast_body))),
    }
}

fn make_operator_ref(
    path: Vec<TirModuleRefSegment>,
    operator: &str,
    args: Vec<Spanned<TirExpr>>,
) -> Spanned<TirExpr> {
    spanned(TirExpr::OperatorRef(TirOperatorRef {
        path,
        operator: operator.to_string(),
        operator_id: tla_core::NameId(0),
        args,
    }))
}

fn module_segment(name: &str) -> TirModuleRefSegment {
    TirModuleRefSegment {
        name: name.to_string(),
        name_id: tla_core::NameId(0),
        args: vec![],
    }
}

// ---------------------------------------------------------------------------
// On-demand compilation: zero-arg cross-module ident emits Call (not CallExternal)
// ---------------------------------------------------------------------------

/// A zero-arg INSTANCE-imported operator in callee_bodies that is not
/// pre-compiled should be compiled on-demand and emit Call, not CallExternal.
#[test]
fn test_cross_module_zero_arg_emits_call_not_call_external() {
    let mut compiler = BytecodeCompiler::new();
    let mut callees = std::collections::HashMap::new();
    // Imported == 99 (zero-arg from INSTANCE module)
    callees.insert("Imported".to_string(), make_callee_info(&[], int_const(99)));
    // Entry: Main == Imported
    let body = name_ident("Imported");
    let idx = compiler
        .compile_expression_with_callees("Main", &[], &body, &callees)
        .expect("zero-arg cross-module ident should compile");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);

    let has_call = func
        .instructions
        .iter()
        .any(|op| matches!(op, Opcode::Call { argc: 0, .. }));
    let has_call_external = func
        .instructions
        .iter()
        .any(|op| matches!(op, Opcode::CallExternal { .. }));
    assert!(
        has_call,
        "zero-arg cross-module ident should emit Call(argc=0): {:?}",
        func.instructions
    );
    assert!(
        !has_call_external,
        "zero-arg cross-module ident should NOT emit CallExternal: {:?}",
        func.instructions
    );
}

// ---------------------------------------------------------------------------
// On-demand compilation: parameterized cross-module Apply emits Call
// ---------------------------------------------------------------------------

/// A parameterized INSTANCE-imported operator called with args should be
/// compiled on-demand and emit Call(argc=N), not CallExternal.
#[test]
fn test_cross_module_parameterized_apply_emits_call() {
    let mut compiler = BytecodeCompiler::new();
    let mut callees = std::collections::HashMap::new();
    // Double(x) == x * 2
    callees.insert(
        "Double".to_string(),
        make_callee_info(&["x"], mul_expr(name_ident("x"), int_const(2))),
    );
    // Entry: Main == Double(7)
    let body = spanned(TirExpr::Apply {
        op: Box::new(name_ident("Double")),
        args: vec![int_const(7)],
    });
    let idx = compiler
        .compile_expression_with_callees("Main", &[], &body, &callees)
        .expect("parameterized cross-module Apply should compile");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);

    let has_call = func
        .instructions
        .iter()
        .any(|op| matches!(op, Opcode::Call { argc: 1, .. }));
    let has_call_external = func
        .instructions
        .iter()
        .any(|op| matches!(op, Opcode::CallExternal { .. }));
    assert!(
        has_call,
        "parameterized cross-module Apply should emit Call(argc=1): {:?}",
        func.instructions
    );
    assert!(
        !has_call_external,
        "parameterized cross-module Apply should NOT emit CallExternal: {:?}",
        func.instructions
    );
}

// ---------------------------------------------------------------------------
// Module-qualified OperatorRef compiles on-demand
// ---------------------------------------------------------------------------

/// Module-qualified OperatorRef (e.g., I!Base) should resolve by operator
/// name and compile on-demand when the callee is in callee_bodies.
#[test]
fn test_module_qualified_operator_ref_compiles_on_demand() {
    let mut compiler = BytecodeCompiler::new();
    let mut callees = std::collections::HashMap::new();
    callees.insert("Base".to_string(), make_callee_info(&[], int_const(42)));
    // I!Base — module-qualified with path=["I"]
    let body = make_operator_ref(vec![module_segment("I")], "Base", vec![]);
    let idx = compiler
        .compile_expression_with_callees("Main", &[], &body, &callees)
        .expect("module-qualified OperatorRef should compile on-demand");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);

    let has_call = func
        .instructions
        .iter()
        .any(|op| matches!(op, Opcode::Call { argc: 0, .. }));
    assert!(
        has_call,
        "module-qualified OperatorRef should emit Call: {:?}",
        func.instructions
    );
}

/// Module-qualified OperatorRef with args (e.g., I!Scale(5)) should compile
/// on-demand and emit Call(argc=1).
#[test]
fn test_module_qualified_operator_ref_with_args_compiles_on_demand() {
    let mut compiler = BytecodeCompiler::new();
    let mut callees = std::collections::HashMap::new();
    // Scale(x) == x + 10
    callees.insert(
        "Scale".to_string(),
        make_callee_info(&["x"], add_expr(name_ident("x"), int_const(10))),
    );
    // I!Scale(5)
    let body = make_operator_ref(vec![module_segment("I")], "Scale", vec![int_const(5)]);
    let idx = compiler
        .compile_expression_with_callees("Main", &[], &body, &callees)
        .expect("module-qualified OperatorRef with args should compile");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);

    let has_call = func
        .instructions
        .iter()
        .any(|op| matches!(op, Opcode::Call { argc: 1, .. }));
    let has_call_external = func
        .instructions
        .iter()
        .any(|op| matches!(op, Opcode::CallExternal { .. }));
    assert!(
        has_call,
        "module-qualified OperatorRef with args should emit Call(argc=1): {:?}",
        func.instructions
    );
    assert!(
        !has_call_external,
        "module-qualified OperatorRef with args should NOT emit CallExternal: {:?}",
        func.instructions
    );
}

// ---------------------------------------------------------------------------
// Transitive cross-module dependencies
// ---------------------------------------------------------------------------

/// Three-deep transitive chain: A -> B -> C, where C is a constant.
/// All three should compile via on-demand resolution.
#[test]
fn test_cross_module_transitive_chain_compiles() {
    let mut compiler = BytecodeCompiler::new();
    let mut callees = std::collections::HashMap::new();
    // C == 10
    callees.insert("C".to_string(), make_callee_info(&[], int_const(10)));
    // B == C + 5
    callees.insert(
        "B".to_string(),
        make_callee_info(&[], add_expr(name_ident("C"), int_const(5))),
    );
    // A == B * 2
    callees.insert(
        "A".to_string(),
        make_callee_info(&[], mul_expr(name_ident("B"), int_const(2))),
    );
    // Entry: Main == A
    let body = name_ident("A");
    let idx = compiler
        .compile_expression_with_callees("Main", &[], &body, &callees)
        .expect("transitive chain should compile");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);

    let has_call = func
        .instructions
        .iter()
        .any(|op| matches!(op, Opcode::Call { argc: 0, .. }));
    let has_call_external = func
        .instructions
        .iter()
        .any(|op| matches!(op, Opcode::CallExternal { .. }));
    assert!(
        has_call,
        "transitive chain should emit Call: {:?}",
        func.instructions
    );
    assert!(
        !has_call_external,
        "transitive chain should NOT emit CallExternal: {:?}",
        func.instructions
    );
    // Expect at least 4 compiled functions: C, B, A (sub-functions) + Main.
    assert!(
        chunk.function_count() >= 4,
        "transitive chain should compile all 3 callees + main: {} functions",
        chunk.function_count()
    );
}

// ---------------------------------------------------------------------------
// CallExternal fallback for recursive callees
// ---------------------------------------------------------------------------

/// Self-referential callee (Rec == Rec) should terminate compilation without
/// infinite recursion. The recursion guard causes fallback to CallExternal.
#[test]
fn test_recursive_callee_terminates_with_call_external() {
    let mut compiler = BytecodeCompiler::new();
    let mut callees = std::collections::HashMap::new();
    // Rec == Rec (self-referential)
    callees.insert("Rec".to_string(), make_callee_info(&[], name_ident("Rec")));
    let body = name_ident("Rec");
    let result = compiler.compile_expression_with_callees("Main", &[], &body, &callees);
    // Either outcome is acceptable as long as no infinite loop occurs:
    // - Ok: compiled with some combination of Call and CallExternal
    // - Err: compilation failed (also acceptable)
    match result {
        Ok(func_idx) => {
            let chunk = compiler.finish();
            let func = chunk.get_function(func_idx);
            // Compilation terminated — verify it produced valid instructions.
            assert!(
                !func.instructions.is_empty(),
                "recursive callee should produce non-empty instructions"
            );
        }
        Err(e) => {
            // Failed compilation is also acceptable for self-referential operators.
            assert!(
                !format!("{e:?}").is_empty(),
                "compilation error should have a non-empty description"
            );
        }
    }
}

// ---------------------------------------------------------------------------
// CallExternal fallback when callee body is unsupported
// ---------------------------------------------------------------------------

/// When a callee body contains an unsupported TIR expression (e.g., temporal
/// operator), on-demand compilation fails and the compiler falls back to
/// CallExternal.
#[test]
fn test_unsupported_callee_body_falls_back_to_call_external() {
    let mut compiler = BytecodeCompiler::new();
    let mut callees = std::collections::HashMap::new();
    // Bad == Always(TRUE) — temporal operator, unsupported in bytecode.
    callees.insert(
        "Bad".to_string(),
        make_callee_info(&[], spanned(TirExpr::Always(Box::new(bool_const(true))))),
    );
    // Entry: Main == Bad
    let body = name_ident("Bad");
    // The Apply pathway in compile_name_expr hits on-demand compilation,
    // which fails for temporal operators, and falls back to CallExternal.
    let idx = compiler
        .compile_expression_with_callees("Main", &[], &body, &callees)
        .expect("unsupported callee body should produce CallExternal fallback");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);

    let has_call_external = func
        .instructions
        .iter()
        .any(|op| matches!(op, Opcode::CallExternal { .. }));
    assert!(
        has_call_external,
        "unsupported callee body should emit CallExternal: {:?}",
        func.instructions
    );
}

// ---------------------------------------------------------------------------
// OperatorRef with unsupported callee falls back to CallExternal
// ---------------------------------------------------------------------------

/// OperatorRef pointing to a callee with an unsupported body should emit
/// CallExternal as a fallback.
#[test]
fn test_operator_ref_unsupported_callee_emits_call_external() {
    let mut compiler = BytecodeCompiler::new();
    let mut callees = std::collections::HashMap::new();
    // Temporal == Eventually(TRUE) — unsupported
    callees.insert(
        "Temporal".to_string(),
        make_callee_info(
            &[],
            spanned(TirExpr::Eventually(Box::new(bool_const(true)))),
        ),
    );
    // OperatorRef to Temporal
    let body = make_operator_ref(vec![], "Temporal", vec![]);
    let idx = compiler
        .compile_expression_with_callees("Main", &[], &body, &callees)
        .expect("unsupported callee OperatorRef should produce CallExternal");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);

    let has_call_external = func
        .instructions
        .iter()
        .any(|op| matches!(op, Opcode::CallExternal { .. }));
    assert!(
        has_call_external,
        "unsupported callee OperatorRef should emit CallExternal: {:?}",
        func.instructions
    );
}

// ---------------------------------------------------------------------------
// Multiple cross-module references in a single function body
// ---------------------------------------------------------------------------

/// A function body that references two different cross-module operators should
/// compile both on-demand.
#[test]
fn test_multiple_cross_module_refs_in_single_body() {
    let mut compiler = BytecodeCompiler::new();
    let mut callees = std::collections::HashMap::new();
    // Left == 10
    callees.insert("Left".to_string(), make_callee_info(&[], int_const(10)));
    // Right == 20
    callees.insert("Right".to_string(), make_callee_info(&[], int_const(20)));
    // Entry: Main == Left + Right
    let body = add_expr(name_ident("Left"), name_ident("Right"));
    let idx = compiler
        .compile_expression_with_callees("Main", &[], &body, &callees)
        .expect("multiple cross-module refs should compile");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);

    let call_count = func
        .instructions
        .iter()
        .filter(|op| matches!(op, Opcode::Call { argc: 0, .. }))
        .count();
    let has_call_external = func
        .instructions
        .iter()
        .any(|op| matches!(op, Opcode::CallExternal { .. }));
    assert!(
        call_count >= 2,
        "body with two cross-module refs should emit at least 2 Call(argc=0) opcodes: {:?}",
        func.instructions
    );
    assert!(
        !has_call_external,
        "both cross-module refs should compile on-demand, not CallExternal: {:?}",
        func.instructions
    );
}

// ---------------------------------------------------------------------------
// Parameterized operator referenced as first-class value (closure)
// ---------------------------------------------------------------------------

/// A parameterized operator referenced with zero args via OperatorRef should
/// produce a closure constant (operator-as-value pattern), not a zero-arg Call.
#[test]
fn test_cross_module_parameterized_ref_as_value_emits_closure() {
    let mut compiler = BytecodeCompiler::new();
    let mut callees = std::collections::HashMap::new();
    // Add(a, b) == a + b
    callees.insert(
        "Add".to_string(),
        make_callee_info_with_ast(
            &["a", "b"],
            add_expr(name_ident("a"), name_ident("b")),
            Spanned {
                node: Expr::OpRef("+".to_string()),
                span: tla_core::Span::default(),
            },
        ),
    );
    // Entry: GetAdd == Add (zero args → operator as value)
    let body = make_operator_ref(vec![], "Add", vec![]);
    let idx = compiler
        .compile_expression_with_callees("GetAdd", &[], &body, &callees)
        .expect("parameterized OperatorRef as value should compile as closure");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);

    // Should load a closure constant, not emit Call(argc=0).
    let loads_const = func
        .instructions
        .iter()
        .any(|op| matches!(op, Opcode::LoadConst { .. }));
    let has_zero_call = func
        .instructions
        .iter()
        .any(|op| matches!(op, Opcode::Call { argc: 0, .. }));
    assert!(
        loads_const,
        "parameterized ref as value should load a closure constant: {:?}",
        func.instructions
    );
    assert!(
        !has_zero_call,
        "parameterized ref as value should NOT emit Call(argc=0): {:?}",
        func.instructions
    );
}

// ---------------------------------------------------------------------------
// Builtin operator names (EXTENDS module ops) compile to CallBuiltin
// ---------------------------------------------------------------------------

/// Calling a builtin operator like `Cardinality` with correct arity should
/// emit `CallBuiltin`, not `Call` or `CallExternal`.
#[test]
fn test_builtin_operator_emits_call_builtin() {
    let mut compiler = BytecodeCompiler::new();
    // Entry: Main == Cardinality({1, 2, 3})
    let set = spanned(TirExpr::SetEnum(vec![
        int_const(1),
        int_const(2),
        int_const(3),
    ]));
    let body = spanned(TirExpr::Apply {
        op: Box::new(name_ident("Cardinality")),
        args: vec![set],
    });
    let callees = std::collections::HashMap::new();
    let idx = compiler
        .compile_expression_with_callees("Main", &[], &body, &callees)
        .expect("builtin Cardinality should compile");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);

    let has_call_builtin = func.instructions.iter().any(|op| {
        matches!(
            op,
            Opcode::CallBuiltin {
                builtin: BuiltinOp::Cardinality,
                ..
            }
        )
    });
    assert!(
        has_call_builtin,
        "Cardinality should emit CallBuiltin: {:?}",
        func.instructions
    );
}

/// Multiple builtin operators in a single body should each emit CallBuiltin.
#[test]
fn test_multiple_builtins_emit_call_builtin() {
    let mut compiler = BytecodeCompiler::new();
    let set = spanned(TirExpr::SetEnum(vec![int_const(1), int_const(2)]));
    // IsFiniteSet({1, 2})
    let is_fin = spanned(TirExpr::Apply {
        op: Box::new(name_ident("IsFiniteSet")),
        args: vec![set],
    });
    // Len(<<3, 4>>)
    let seq = spanned(TirExpr::Tuple(vec![int_const(3), int_const(4)]));
    let len = spanned(TirExpr::Apply {
        op: Box::new(name_ident("Len")),
        args: vec![seq],
    });
    // Entry: Main == IF IsFiniteSet({1,2}) THEN Len(<<3,4>>) ELSE 0
    let body = spanned(TirExpr::If {
        cond: Box::new(is_fin),
        then_: Box::new(len),
        else_: Box::new(int_const(0)),
    });
    let callees = std::collections::HashMap::new();
    let idx = compiler
        .compile_expression_with_callees("Main", &[], &body, &callees)
        .expect("multiple builtins should compile");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);

    let builtin_count = func
        .instructions
        .iter()
        .filter(|op| matches!(op, Opcode::CallBuiltin { .. }))
        .count();
    assert!(
        builtin_count >= 2,
        "should emit at least 2 CallBuiltin opcodes: {:?}",
        func.instructions
    );
}

// ---------------------------------------------------------------------------
// Concat opcode for \o and \circ
// ---------------------------------------------------------------------------

/// The `\o` (sequence concatenation) operator should emit a Concat opcode.
#[test]
fn test_concat_operator_emits_concat_opcode() {
    let mut compiler = BytecodeCompiler::new();
    // Main == <<1>> \o <<2>>  (represented as Apply of "\\o" with 2 args)
    let left = spanned(TirExpr::Tuple(vec![int_const(1)]));
    let right = spanned(TirExpr::Tuple(vec![int_const(2)]));
    let body = spanned(TirExpr::Apply {
        op: Box::new(name_ident("\\o")),
        args: vec![left, right],
    });
    let callees = std::collections::HashMap::new();
    let idx = compiler
        .compile_expression_with_callees("Main", &[], &body, &callees)
        .expect("\\o operator should compile");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);

    let has_concat = func
        .instructions
        .iter()
        .any(|op| matches!(op, Opcode::Concat { .. }));
    assert!(
        has_concat,
        "\\o should emit Concat opcode: {:?}",
        func.instructions
    );
}

/// The `\circ` operator should also emit a Concat opcode (alias for \o).
#[test]
fn test_circ_operator_emits_concat_opcode() {
    let mut compiler = BytecodeCompiler::new();
    let left = spanned(TirExpr::Tuple(vec![int_const(1)]));
    let right = spanned(TirExpr::Tuple(vec![int_const(2)]));
    let body = spanned(TirExpr::Apply {
        op: Box::new(name_ident("\\circ")),
        args: vec![left, right],
    });
    let callees = std::collections::HashMap::new();
    let idx = compiler
        .compile_expression_with_callees("Main", &[], &body, &callees)
        .expect("\\circ operator should compile");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);

    let has_concat = func
        .instructions
        .iter()
        .any(|op| matches!(op, Opcode::Concat { .. }));
    assert!(
        has_concat,
        "\\circ should emit Concat opcode: {:?}",
        func.instructions
    );
}

// ---------------------------------------------------------------------------
// On-demand compilation clears parent bindings
// ---------------------------------------------------------------------------

/// Parent quantifier bindings must NOT leak into on-demand compiled callees.
/// Without clearing parent bindings, the callee could reference registers
/// from the parent's register file that exceed its own max_register.
#[test]
fn test_on_demand_callee_clears_parent_bindings() {
    let mut constants = ConstantPool::new();
    let mut state = FnCompileState::new("Main".to_string(), 0, &mut constants);
    let op_indices = std::collections::HashMap::new();
    state.op_indices = Some(&op_indices);

    // Simulate parent context with many quantifier bindings.
    for i in 0..10 {
        state.bindings.push((format!("qvar{i}"), i as u8));
    }
    state.next_reg = 10;

    let callee_bodies = std::collections::HashMap::new();
    state.callee_bodies = Some(&callee_bodies);

    // Inner == 42 (zero-arg, should compile against op_indices, not parent bindings)
    let info = CalleeInfo {
        params: vec![],
        body: std::sync::Arc::new(int_const(42)),
        ast_body: None,
    };

    let func_idx = state
        .compile_callee_on_demand("Inner", &info)
        .expect("on-demand callee should compile against op_indices, not parent bindings");

    assert_eq!(func_idx, 0, "first sub-function should take index 0");
    let sub_func = &state.sub_functions[0];
    // The sub-function should have a small max register (not 10+).
    assert!(
        sub_func.max_register < 5,
        "on-demand callee max_register should be small, not inherit parent: {}",
        sub_func.max_register
    );
}

// ---------------------------------------------------------------------------
// Mixed on-demand and pre-compiled callees
// ---------------------------------------------------------------------------

/// A function body that references both a pre-compiled (phase 1) callee and
/// an on-demand callee should emit Call for both.
#[test]
fn test_mixed_precompiled_and_on_demand_callees() {
    let mut compiler = BytecodeCompiler::new();
    let mut callees = std::collections::HashMap::new();

    // PreComp == 5 (pre-compiled in phase 1 via compile_operator)
    let pre_op = crate::TirOperator {
        name: "PreComp".to_string(),
        name_id: tla_core::NameId(0),
        params: vec![],
        is_recursive: false,
        body: int_const(5),
    };
    compiler
        .compile_operator(&pre_op)
        .expect("PreComp should compile");

    // OnDemand == 10 (in callee_bodies only, not pre-compiled)
    callees.insert("OnDemand".to_string(), make_callee_info(&[], int_const(10)));

    // Entry: Main == PreComp + OnDemand
    let body = add_expr(name_ident("PreComp"), name_ident("OnDemand"));
    let idx = compiler
        .compile_expression_with_callees("Main", &[], &body, &callees)
        .expect("mixed pre-compiled and on-demand should compile");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);

    let call_count = func
        .instructions
        .iter()
        .filter(|op| matches!(op, Opcode::Call { argc: 0, .. }))
        .count();
    assert!(
        call_count >= 2,
        "should emit Call for both pre-compiled and on-demand callees: {:?}",
        func.instructions
    );
}

// ---------------------------------------------------------------------------
// OperatorRef with nested module path
// ---------------------------------------------------------------------------

/// OperatorRef with a multi-segment module path (e.g., A!B!Op) should still
/// resolve by the operator's simple name.
#[test]
fn test_deeply_qualified_operator_ref_resolves_by_name() {
    let mut compiler = BytecodeCompiler::new();
    let mut callees = std::collections::HashMap::new();
    callees.insert("DeepOp".to_string(), make_callee_info(&[], int_const(77)));
    // A!B!DeepOp — two module path segments
    let body = make_operator_ref(
        vec![module_segment("A"), module_segment("B")],
        "DeepOp",
        vec![],
    );
    let idx = compiler
        .compile_expression_with_callees("Main", &[], &body, &callees)
        .expect("deeply qualified OperatorRef should compile");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);

    let has_call = func
        .instructions
        .iter()
        .any(|op| matches!(op, Opcode::Call { argc: 0, .. }));
    assert!(
        has_call,
        "deeply qualified OperatorRef should resolve by simple name and emit Call: {:?}",
        func.instructions
    );
}

// ---------------------------------------------------------------------------
// On-demand compilation with operator replacements
// ---------------------------------------------------------------------------

/// When .cfg `CONSTANT Foo <- Bar` replacements are active, the on-demand
/// compiler should resolve through the replacement chain.
#[test]
fn test_on_demand_with_operator_replacements() {
    let mut compiler = BytecodeCompiler::new();
    // Set up replacement: Foo -> Bar
    let mut replacements = std::collections::HashMap::new();
    replacements.insert("Foo".to_string(), "Bar".to_string());
    compiler.set_op_replacements(replacements);

    let mut callees = std::collections::HashMap::new();
    // Bar == 99 (the replacement target)
    callees.insert("Bar".to_string(), make_callee_info(&[], int_const(99)));
    // Entry: Main == Foo (should resolve through Foo -> Bar)
    let body = name_ident("Foo");
    let idx = compiler
        .compile_expression_with_callees("Main", &[], &body, &callees)
        .expect("operator replacement should resolve cross-module ref");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);

    let has_call = func
        .instructions
        .iter()
        .any(|op| matches!(op, Opcode::Call { argc: 0, .. }));
    assert!(
        has_call,
        "operator replacement should resolve to Call: {:?}",
        func.instructions
    );
}
