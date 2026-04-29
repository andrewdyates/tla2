// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Function definition, LET, CASE, apply/EXCEPT, and binding-form capture parity.

use super::*;
use tla_value::error::EvalError;

const FUNCDEF_MODULE: &str = "\
---- MODULE TirFuncDef ----
FuncSingle == [x \\in {1, 2, 3} |-> x * 2]
FuncInterval == [x \\in 1..5 |-> x + 10]
FuncSeq == [x \\in 1..3 |-> x * 10]
====";

#[test]
fn test_tir_parity_func_def() {
    let module = parse_module(FUNCDEF_MODULE);
    for name in &["FuncSingle", "FuncInterval", "FuncSeq"] {
        assert_parity(&module, name);
    }
}

// Part of #3363: multi-variable func def must produce tuple keys matching S \X T domain.
// Regression test for 03b93d03d — before the fix, multi-var func defs used bare
// innermost-variable keys instead of <<x, y>> tuples, causing silent data loss.
const FUNCDEF_MULTI_MODULE: &str = "\
---- MODULE TirFuncDefMulti ----
EXTENDS Integers
FuncMulti2 == [x \\in {1, 2}, y \\in {3, 4} |-> x + y]
FuncMulti2Domain == DOMAIN [x \\in {1, 2}, y \\in {3, 4} |-> x + y]
FuncMulti2Apply == LET f == [x \\in {1, 2}, y \\in {3, 4} |-> x + y] IN f[<<1, 3>>]
FuncMulti2Size == LET f == [x \\in {1, 2}, y \\in {3, 4} |-> x + y] IN Cardinality(DOMAIN f)
FuncMultiSameDomain == [i, j \\in {1, 2} |-> i * 10 + j]
====";

#[test]
fn test_tir_parity_func_def_multi() {
    let module = parse_module(FUNCDEF_MULTI_MODULE);
    for name in &[
        "FuncMulti2",
        "FuncMulti2Domain",
        "FuncMulti2Apply",
        "FuncMulti2Size",
        "FuncMultiSameDomain",
    ] {
        assert_parity(&module, name);
    }
}

const LET_MODULE: &str = "\
---- MODULE TirLet ----
LetSimple == LET a == 10 IN a + 5
LetChained == LET a == 3 b == a + 7 IN a + b
LetNested == LET outer == LET inner == 42 IN inner IN outer + 1
====";

#[test]
fn test_tir_parity_let() {
    let module = parse_module(LET_MODULE);
    for name in &["LetSimple", "LetChained", "LetNested"] {
        assert_parity(&module, name);
    }
}

// Part of #3262: parameterized LET defs lowered to LAMBDA + binding.
const LET_PARAMETERIZED_MODULE: &str = "\
---- MODULE TirLetParam ----
LetParam == LET Inc(x) == x + 1 IN Inc(4)
LetParamMulti == LET Add(a, b) == a + b IN Add(3, 7)
LetParamChained == LET Double(x) == x * 2 Inc(x) == x + 1 IN Double(Inc(3))
LetMixed == LET c == 100 Inc(x) == x + c IN Inc(5)
====";

#[test]
fn test_tir_parity_let_parameterized() {
    let module = parse_module(LET_PARAMETERIZED_MODULE);
    for name in &["LetParam", "LetParamMulti", "LetParamChained", "LetMixed"] {
        assert_parity(&module, name);
    }
}

const CASE_MODULE: &str = "\
---- MODULE TirCase ----
CaseFirst == CASE TRUE -> 1 [] FALSE -> 2
CaseSecond == CASE FALSE -> 1 [] TRUE -> 2
CaseOther == CASE FALSE -> 1 [] FALSE -> 2 [] OTHER -> 99
====";

#[test]
fn test_tir_parity_case() {
    let module = parse_module(CASE_MODULE);
    for name in &["CaseFirst", "CaseSecond", "CaseOther"] {
        assert_parity(&module, name);
    }
}

const STEP4_MODULE: &str = "\
---- MODULE TirStep4 ----
Inc(x) == x + 1
ApplyUnary(P(_), y) == P(y)
ApplyBinary(P(_,_), a, b) == P(a, b)
ApplyInc == Inc(4)
ApplyViaParam == ApplyUnary(Inc, 4)
ApplyBuiltinPlus == ApplyBinary(+, 1, 2)
FuncApplyOp == [x \\in 1..3 |-> x * 10][2]
DomainOp == DOMAIN [x \\in 1..3 |-> x * 10]
FuncSetOp == [1..2 -> {TRUE, FALSE}]
ExceptRecordOp == [ [a |-> 1, b |-> 2] EXCEPT !.a = 3 ]
ExceptAtOp == [ [a |-> 1] EXCEPT !.a = @ + 2 ]
ExceptSeqOp == [ <<10, 20, 30>> EXCEPT ![2] = 99 ]
====";

const STEP4_ERROR_MODULE: &str = "\
---- MODULE TirStep4Errors ----
TupleApplyOutOfBoundsOp == <<10>>[2]
ExceptIntFuncFieldOp == [ [i \\in 2..3 |-> i] EXCEPT !.bad = 0 ]
====";

#[test]
fn test_tir_parity_step4_apply_and_function_ops() {
    let module = parse_module(STEP4_MODULE);
    for name in &[
        "ApplyInc",
        "ApplyViaParam",
        "ApplyBuiltinPlus",
        "FuncApplyOp",
        "DomainOp",
        "FuncSetOp",
        "ExceptRecordOp",
        "ExceptAtOp",
        "ExceptSeqOp",
    ] {
        assert_parity(&module, name);
    }
}

#[test]
fn test_tir_parity_tuple_apply_out_of_bounds_error() {
    let module = parse_module(STEP4_ERROR_MODULE);
    let (ast_err, tir_err) = assert_error_parity(&module, "TupleApplyOutOfBoundsOp");

    match (ast_err, tir_err) {
        (
            EvalError::IndexOutOfBounds {
                index: ast_index,
                len: ast_len,
                ..
            },
            EvalError::IndexOutOfBounds {
                index: tir_index,
                len: tir_len,
                ..
            },
        ) => {
            assert_eq!((ast_index, ast_len), (2, 1));
            assert_eq!(
                (tir_index, tir_len),
                (ast_index, ast_len),
                "TIR tuple apply should preserve AST IndexOutOfBounds details"
            );
        }
        (ast, tir) => panic!("tuple apply error parity mismatch: AST={ast:?}, TIR={tir:?}"),
    }
}

#[test]
fn test_tir_parity_except_intfunc_field_error() {
    let module = parse_module(STEP4_ERROR_MODULE);
    let (ast_err, tir_err) = assert_error_parity(&module, "ExceptIntFuncFieldOp");

    match (ast_err, tir_err) {
        (
            EvalError::Internal {
                message: ast_message,
                ..
            },
            EvalError::Internal {
                message: tir_message,
                ..
            },
        ) => {
            assert_eq!(ast_message, "Field access on function not supported");
            assert_eq!(
                tir_message, ast_message,
                "TIR IntFunc field EXCEPT should preserve AST internal error message"
            );
        }
        (ast, tir) => {
            panic!("IntFunc field EXCEPT error parity mismatch: AST={ast:?}, TIR={tir:?}")
        }
    }
}

const BINDING_FORM_CAPTURE_MODULE: &str = "\
---- MODULE TirBindingFormCapture ----
FuncCapture == [node \\in {1, 2} |-> [p \\in {1, 2} |-> IF p = node THEN 1 ELSE 0]][2]
NestedFilter == [nbrs \\in {{{1, 2}}} |->
  [n \\in 1..2 |-> {m \\in 1..2 : {m, n} \\in nbrs /\\ m < n}]][{{1, 2}}]
====";

#[test]
fn test_tir_parity_func_def_captures_outer_bound_value() {
    let module = parse_module(BINDING_FORM_CAPTURE_MODULE);
    assert_parity(&module, "FuncCapture");
}

#[test]
fn test_tir_parity_nested_filter_inside_function_def() {
    let module = parse_module(BINDING_FORM_CAPTURE_MODULE);
    assert_parity(&module, "NestedFilter");
}
