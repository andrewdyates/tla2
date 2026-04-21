// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for Quint JSON IR import.

use super::*;
use crate::ast::{Expr, Unit};

/// Minimal Quint IR with a single module containing a variable and a val def.
const MINIMAL_IR: &str = r#"
{
    "modules": [
        {
            "name": "Counter",
            "id": 1,
            "declarations": [
                {
                    "kind": "var",
                    "name": "count",
                    "id": 2
                },
                {
                    "kind": "const",
                    "name": "N",
                    "id": 3
                },
                {
                    "kind": "def",
                    "name": "Init",
                    "qualifier": "action",
                    "id": 4,
                    "params": [],
                    "expr": {
                        "kind": "app",
                        "opcode": "assign",
                        "id": 5,
                        "args": [
                            { "kind": "name", "name": "count", "id": 6 },
                            { "kind": "int", "value": 0, "id": 7 }
                        ]
                    }
                }
            ]
        }
    ]
}
"#;

#[test]
fn test_parse_quint_json_minimal() {
    let modules = parse_quint_json(MINIMAL_IR).expect("should parse minimal IR");
    assert_eq!(modules.len(), 1);
    let m = &modules[0];
    assert_eq!(m.name.node, "Counter");
    assert_eq!(m.units.len(), 3);

    // First unit: variable declaration
    match &m.units[0].node {
        Unit::Variable(vars) => {
            assert_eq!(vars.len(), 1);
            assert_eq!(vars[0].node, "count");
        }
        other => panic!("expected Variable, got {other:?}"),
    }

    // Second unit: constant declaration
    match &m.units[1].node {
        Unit::Constant(consts) => {
            assert_eq!(consts.len(), 1);
            assert_eq!(consts[0].name.node, "N");
        }
        other => panic!("expected Constant, got {other:?}"),
    }

    // Third unit: Init operator (assign desugars to x' = val)
    match &m.units[2].node {
        Unit::Operator(op) => {
            assert_eq!(op.name.node, "Init");
            assert!(op.params.is_empty());
            // Body should be: count' = 0  -> Eq(Prime(Ident("count")), Int(0))
            match &op.body.node {
                Expr::Eq(left, right) => {
                    match &left.node {
                        Expr::Prime(inner) => match &inner.node {
                            Expr::Ident(name, _) => assert_eq!(name, "count"),
                            other => panic!("expected Ident inside Prime, got {other:?}"),
                        },
                        other => panic!("expected Prime, got {other:?}"),
                    }
                    match &right.node {
                        Expr::Int(n) => assert_eq!(*n, 0.into()),
                        other => panic!("expected Int(0), got {other:?}"),
                    }
                }
                other => panic!("expected Eq, got {other:?}"),
            }
        }
        other => panic!("expected Operator, got {other:?}"),
    }
}

/// Test boolean operators.
#[test]
fn test_parse_quint_json_boolean_ops() {
    let json = r#"
    {
        "modules": [{
            "name": "BoolSpec",
            "id": 1,
            "declarations": [{
                "kind": "def",
                "name": "BoolOp",
                "qualifier": "val",
                "id": 2,
                "params": [],
                "expr": {
                    "kind": "app",
                    "opcode": "and",
                    "id": 3,
                    "args": [
                        { "kind": "bool", "value": true, "id": 4 },
                        {
                            "kind": "app",
                            "opcode": "not",
                            "id": 5,
                            "args": [
                                { "kind": "bool", "value": false, "id": 6 }
                            ]
                        }
                    ]
                }
            }]
        }]
    }
    "#;
    let modules = parse_quint_json(json).expect("should parse boolean ops");
    let m = &modules[0];
    match &m.units[0].node {
        Unit::Operator(op) => {
            assert_eq!(op.name.node, "BoolOp");
            match &op.body.node {
                Expr::And(left, right) => {
                    assert!(matches!(left.node, Expr::Bool(true)));
                    match &right.node {
                        Expr::Not(inner) => {
                            assert!(matches!(inner.node, Expr::Bool(false)));
                        }
                        other => panic!("expected Not, got {other:?}"),
                    }
                }
                other => panic!("expected And, got {other:?}"),
            }
        }
        other => panic!("expected Operator, got {other:?}"),
    }
}

/// Test set operations with quantifiers.
#[test]
fn test_parse_quint_json_set_forall() {
    let json = r#"
    {
        "modules": [{
            "name": "SetSpec",
            "id": 1,
            "declarations": [{
                "kind": "def",
                "name": "AllPositive",
                "qualifier": "val",
                "id": 2,
                "params": [],
                "expr": {
                    "kind": "app",
                    "opcode": "forall",
                    "id": 3,
                    "args": [
                        {
                            "kind": "app",
                            "opcode": "Set",
                            "id": 4,
                            "args": [
                                { "kind": "int", "value": 1, "id": 5 },
                                { "kind": "int", "value": 2, "id": 6 },
                                { "kind": "int", "value": 3, "id": 7 }
                            ]
                        },
                        {
                            "kind": "lambda",
                            "id": 8,
                            "qualifier": "puredef",
                            "params": [{ "name": "x", "id": 9 }],
                            "expr": {
                                "kind": "app",
                                "opcode": "gt",
                                "id": 10,
                                "args": [
                                    { "kind": "name", "name": "x", "id": 11 },
                                    { "kind": "int", "value": 0, "id": 12 }
                                ]
                            }
                        }
                    ]
                }
            }]
        }]
    }
    "#;
    let modules = parse_quint_json(json).expect("should parse set forall");
    let m = &modules[0];
    match &m.units[0].node {
        Unit::Operator(op) => {
            assert_eq!(op.name.node, "AllPositive");
            match &op.body.node {
                Expr::Forall(bounds, _body) => {
                    assert_eq!(bounds.len(), 1);
                    assert_eq!(bounds[0].name.node, "x");
                    assert!(bounds[0].domain.is_some());
                    // Domain should be SetEnum({1, 2, 3})
                    match &bounds[0].domain.as_ref().expect("domain").node {
                        Expr::SetEnum(elems) => assert_eq!(elems.len(), 3),
                        other => panic!("expected SetEnum, got {other:?}"),
                    }
                }
                other => panic!("expected Forall, got {other:?}"),
            }
        }
        other => panic!("expected Operator, got {other:?}"),
    }
}

/// Test operator definitions with parameters.
#[test]
fn test_parse_quint_json_operator_with_params() {
    let json = r#"
    {
        "modules": [{
            "name": "ParamSpec",
            "id": 1,
            "declarations": [{
                "kind": "def",
                "name": "Add",
                "qualifier": "def",
                "id": 2,
                "params": [
                    { "name": "a", "id": 3 },
                    { "name": "b", "id": 4 }
                ],
                "expr": {
                    "kind": "app",
                    "opcode": "iadd",
                    "id": 5,
                    "args": [
                        { "kind": "name", "name": "a", "id": 6 },
                        { "kind": "name", "name": "b", "id": 7 }
                    ]
                }
            }]
        }]
    }
    "#;
    let modules = parse_quint_json(json).expect("should parse parameterized operator");
    let m = &modules[0];
    match &m.units[0].node {
        Unit::Operator(op) => {
            assert_eq!(op.name.node, "Add");
            assert_eq!(op.params.len(), 2);
            assert_eq!(op.params[0].name.node, "a");
            assert_eq!(op.params[1].name.node, "b");
            match &op.body.node {
                Expr::Add(_, _) => {} // correct
                other => panic!("expected Add, got {other:?}"),
            }
        }
        other => panic!("expected Operator, got {other:?}"),
    }
}

/// Test record construction and field access.
#[test]
fn test_parse_quint_json_record() {
    let json = r#"
    {
        "modules": [{
            "name": "RecSpec",
            "id": 1,
            "declarations": [{
                "kind": "def",
                "name": "MyRec",
                "qualifier": "val",
                "id": 2,
                "params": [],
                "expr": {
                    "kind": "app",
                    "opcode": "Rec",
                    "id": 3,
                    "args": [
                        { "kind": "str", "value": "x", "id": 4 },
                        { "kind": "int", "value": 1, "id": 5 },
                        { "kind": "str", "value": "y", "id": 6 },
                        { "kind": "int", "value": 2, "id": 7 }
                    ]
                }
            }]
        }]
    }
    "#;
    let modules = parse_quint_json(json).expect("should parse record");
    let m = &modules[0];
    match &m.units[0].node {
        Unit::Operator(op) => match &op.body.node {
            Expr::Record(fields) => {
                assert_eq!(fields.len(), 2);
                assert_eq!(fields[0].0.node, "x");
                assert_eq!(fields[1].0.node, "y");
            }
            other => panic!("expected Record, got {other:?}"),
        },
        other => panic!("expected Operator, got {other:?}"),
    }
}

/// Test if-then-else translation.
#[test]
fn test_parse_quint_json_ite() {
    let json = r#"
    {
        "modules": [{
            "name": "IteSpec",
            "id": 1,
            "declarations": [{
                "kind": "def",
                "name": "MaxVal",
                "qualifier": "def",
                "id": 2,
                "params": [
                    { "name": "a", "id": 3 },
                    { "name": "b", "id": 4 }
                ],
                "expr": {
                    "kind": "app",
                    "opcode": "ite",
                    "id": 5,
                    "args": [
                        {
                            "kind": "app",
                            "opcode": "gt",
                            "id": 6,
                            "args": [
                                { "kind": "name", "name": "a", "id": 7 },
                                { "kind": "name", "name": "b", "id": 8 }
                            ]
                        },
                        { "kind": "name", "name": "a", "id": 9 },
                        { "kind": "name", "name": "b", "id": 10 }
                    ]
                }
            }]
        }]
    }
    "#;
    let modules = parse_quint_json(json).expect("should parse ite");
    let m = &modules[0];
    match &m.units[0].node {
        Unit::Operator(op) => match &op.body.node {
            Expr::If(cond, then_br, else_br) => {
                assert!(matches!(cond.node, Expr::Gt(_, _)));
                assert!(matches!(then_br.node, Expr::Ident(_, _)));
                assert!(matches!(else_br.node, Expr::Ident(_, _)));
            }
            other => panic!("expected If, got {other:?}"),
        },
        other => panic!("expected Operator, got {other:?}"),
    }
}

/// Test let-in expression.
#[test]
fn test_parse_quint_json_let() {
    let json = r#"
    {
        "modules": [{
            "name": "LetSpec",
            "id": 1,
            "declarations": [{
                "kind": "def",
                "name": "Result",
                "qualifier": "val",
                "id": 2,
                "params": [],
                "expr": {
                    "kind": "let",
                    "id": 3,
                    "opdef": {
                        "kind": "def",
                        "name": "tmp",
                        "qualifier": "val",
                        "id": 4,
                        "params": [],
                        "expr": { "kind": "int", "value": 42, "id": 5 }
                    },
                    "expr": {
                        "kind": "app",
                        "opcode": "iadd",
                        "id": 6,
                        "args": [
                            { "kind": "name", "name": "tmp", "id": 7 },
                            { "kind": "int", "value": 1, "id": 8 }
                        ]
                    }
                }
            }]
        }]
    }
    "#;
    let modules = parse_quint_json(json).expect("should parse let-in");
    let m = &modules[0];
    match &m.units[0].node {
        Unit::Operator(op) => match &op.body.node {
            Expr::Let(defs, body) => {
                assert_eq!(defs.len(), 1);
                assert_eq!(defs[0].name.node, "tmp");
                assert!(matches!(body.node, Expr::Add(_, _)));
            }
            other => panic!("expected Let, got {other:?}"),
        },
        other => panic!("expected Operator, got {other:?}"),
    }
}

/// Test label translation strips `__label_` prefix.
#[test]
fn test_parse_quint_json_label_stripping() {
    let json = r#"
    {
        "modules": [{
            "name": "LabelSpec",
            "id": 1,
            "declarations": [{
                "kind": "def",
                "name": "__label_MyStep",
                "qualifier": "action",
                "id": 2,
                "params": [],
                "expr": { "kind": "bool", "value": true, "id": 3 }
            }]
        }]
    }
    "#;
    let modules = parse_quint_json(json).expect("should parse label");
    let m = &modules[0];
    match &m.units[0].node {
        Unit::Operator(op) => {
            // Should strip __label_ prefix
            assert_eq!(op.name.node, "MyStep");
        }
        other => panic!("expected Operator, got {other:?}"),
    }
}

/// Test is_quint_json_path detection.
#[test]
fn test_is_quint_json_path() {
    use std::path::Path;
    assert!(is_quint_json_path(Path::new("foo.qnt.json")));
    assert!(is_quint_json_path(Path::new("/path/to/Counter.qnt.json")));
    assert!(!is_quint_json_path(Path::new("foo.tla")));
    assert!(!is_quint_json_path(Path::new("foo.json")));
    assert!(!is_quint_json_path(Path::new("foo.qnt")));
}

/// Test that integer values encoded as strings are correctly parsed.
/// Quint BigInt may emit very large integers as strings in JSON.
#[test]
fn test_parse_quint_json_string_encoded_int() {
    // Note: Quint normally emits integers as JSON numbers, but the spec allows
    // string encoding for BigInt values that exceed JSON number precision.
    // Our custom deserializer handles both forms.
    let json = r#"
    {
        "modules": [{
            "name": "BigIntSpec",
            "id": 1,
            "declarations": [{
                "kind": "def",
                "name": "BigVal",
                "qualifier": "val",
                "id": 2,
                "expr": { "kind": "int", "value": "999999999999", "id": 3 }
            }]
        }]
    }
    "#;
    let modules = parse_quint_json(json).expect("should parse string-encoded int");
    match &modules[0].units[0].node {
        Unit::Operator(op) => match &op.body.node {
            Expr::Int(n) => assert_eq!(*n, 999_999_999_999i64.into()),
            other => panic!("expected Int, got {other:?}"),
        },
        other => panic!("expected Operator, got {other:?}"),
    }
}

/// Test invalid JSON produces a clear error.
#[test]
fn test_parse_quint_json_invalid_json() {
    let result = parse_quint_json("not valid json");
    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(matches!(err, QuintError::Json(_)));
}

/// Test empty modules array.
#[test]
fn test_parse_quint_json_empty_modules() {
    let json = r#"{ "modules": [] }"#;
    let modules = parse_quint_json(json).expect("should parse empty modules");
    assert!(modules.is_empty());
}

/// Test multiple modules.
#[test]
fn test_parse_quint_json_multiple_modules() {
    let json = r#"
    {
        "modules": [
            {
                "name": "ModA",
                "id": 1,
                "declarations": [{
                    "kind": "var",
                    "name": "x",
                    "id": 2
                }]
            },
            {
                "name": "ModB",
                "id": 3,
                "declarations": [{
                    "kind": "var",
                    "name": "y",
                    "id": 4
                }]
            }
        ]
    }
    "#;
    let modules = parse_quint_json(json).expect("should parse multiple modules");
    assert_eq!(modules.len(), 2);
    assert_eq!(modules[0].name.node, "ModA");
    assert_eq!(modules[1].name.node, "ModB");
}

/// Test that translated modules auto-extend Integers (always needed for Quint).
#[test]
fn test_parse_quint_json_auto_extends_integers() {
    let modules = parse_quint_json(MINIMAL_IR).expect("should parse");
    let m = &modules[0];
    let extends: Vec<&str> = m.extends.iter().map(|e| e.node.as_str()).collect();
    assert!(
        extends.contains(&"Integers"),
        "should auto-extend Integers, got: {extends:?}"
    );
}

/// Test sequence operations: Append maps to stdlib Apply("Append", ...).
#[test]
fn test_parse_quint_json_sequence_append() {
    let json = r#"
    {
        "modules": [{
            "name": "SeqSpec",
            "id": 1,
            "declarations": [{
                "kind": "def",
                "name": "Result",
                "qualifier": "val",
                "id": 2,
                "params": [],
                "expr": {
                    "kind": "app",
                    "opcode": "append",
                    "id": 3,
                    "args": [
                        {
                            "kind": "app",
                            "opcode": "Tup",
                            "id": 4,
                            "args": [
                                { "kind": "int", "value": 1, "id": 5 },
                                { "kind": "int", "value": 2, "id": 6 }
                            ]
                        },
                        { "kind": "int", "value": 3, "id": 7 }
                    ]
                }
            }]
        }]
    }
    "#;
    let modules = parse_quint_json(json).expect("should parse sequence append");
    let m = &modules[0];
    // Should auto-extend Sequences.
    let extends: Vec<&str> = m.extends.iter().map(|e| e.node.as_str()).collect();
    assert!(extends.contains(&"Sequences"), "should extend Sequences");
    // Body should be Apply(Ident("Append"), [Tuple(1,2), 3]).
    match &m.units[0].node {
        Unit::Operator(op) => match &op.body.node {
            Expr::Apply(func, args) => {
                match &func.node {
                    Expr::Ident(name, _) => assert_eq!(name, "Append"),
                    other => panic!("expected Ident(Append), got {other:?}"),
                }
                assert_eq!(args.len(), 2);
            }
            other => panic!("expected Apply, got {other:?}"),
        },
        other => panic!("expected Operator, got {other:?}"),
    }
}

/// Test set cardinality (size opcode -> Cardinality).
#[test]
fn test_parse_quint_json_set_cardinality() {
    let json = r#"
    {
        "modules": [{
            "name": "CardSpec",
            "id": 1,
            "declarations": [{
                "kind": "def",
                "name": "Count",
                "qualifier": "val",
                "id": 2,
                "params": [],
                "expr": {
                    "kind": "app",
                    "opcode": "size",
                    "id": 3,
                    "args": [
                        {
                            "kind": "app",
                            "opcode": "Set",
                            "id": 4,
                            "args": [
                                { "kind": "int", "value": 1, "id": 5 },
                                { "kind": "int", "value": 2, "id": 6 }
                            ]
                        }
                    ]
                }
            }]
        }]
    }
    "#;
    let modules = parse_quint_json(json).expect("should parse cardinality");
    let m = &modules[0];
    let extends: Vec<&str> = m.extends.iter().map(|e| e.node.as_str()).collect();
    assert!(extends.contains(&"FiniteSets"), "should extend FiniteSets");
    match &m.units[0].node {
        Unit::Operator(op) => match &op.body.node {
            Expr::Apply(func, _) => match &func.node {
                Expr::Ident(name, _) => assert_eq!(name, "Cardinality"),
                other => panic!("expected Ident(Cardinality), got {other:?}"),
            },
            other => panic!("expected Apply, got {other:?}"),
        },
        other => panic!("expected Operator, got {other:?}"),
    }
}

/// Test oneOf maps to CHOOSE.
#[test]
fn test_parse_quint_json_one_of() {
    let json = r#"
    {
        "modules": [{
            "name": "NondetSpec",
            "id": 1,
            "declarations": [{
                "kind": "def",
                "name": "Pick",
                "qualifier": "nondet",
                "id": 2,
                "params": [],
                "expr": {
                    "kind": "app",
                    "opcode": "oneOf",
                    "id": 3,
                    "args": [
                        {
                            "kind": "app",
                            "opcode": "Set",
                            "id": 4,
                            "args": [
                                { "kind": "int", "value": 1, "id": 5 },
                                { "kind": "int", "value": 2, "id": 6 }
                            ]
                        }
                    ]
                }
            }]
        }]
    }
    "#;
    let modules = parse_quint_json(json).expect("should parse oneOf");
    let m = &modules[0];
    match &m.units[0].node {
        Unit::Operator(op) => match &op.body.node {
            Expr::Choose(bv, body) => {
                assert_eq!(bv.name.node, "__chosen");
                assert!(bv.domain.is_some());
                assert!(matches!(body.node, Expr::Bool(true)));
            }
            other => panic!("expected Choose, got {other:?}"),
        },
        other => panic!("expected Operator, got {other:?}"),
    }
}

/// Test type constant translations (Bool -> BOOLEAN, Nat, Int, String -> STRING).
#[test]
fn test_parse_quint_json_type_constants() {
    let json = r#"
    {
        "modules": [{
            "name": "TypeSpec",
            "id": 1,
            "declarations": [{
                "kind": "def",
                "name": "BoolSet",
                "qualifier": "val",
                "id": 2,
                "params": [],
                "expr": {
                    "kind": "app",
                    "opcode": "Bool",
                    "id": 3,
                    "args": []
                }
            }]
        }]
    }
    "#;
    let modules = parse_quint_json(json).expect("should parse type constant");
    let m = &modules[0];
    match &m.units[0].node {
        Unit::Operator(op) => match &op.body.node {
            Expr::Ident(name, _) => assert_eq!(name, "BOOLEAN"),
            other => panic!("expected Ident(BOOLEAN), got {other:?}"),
        },
        other => panic!("expected Operator, got {other:?}"),
    }
}

/// Test record set translation (setOfRecs -> RecordSet).
#[test]
fn test_parse_quint_json_record_set() {
    let json = r#"
    {
        "modules": [{
            "name": "RecSetSpec",
            "id": 1,
            "declarations": [{
                "kind": "def",
                "name": "RS",
                "qualifier": "val",
                "id": 2,
                "params": [],
                "expr": {
                    "kind": "app",
                    "opcode": "RecordSet",
                    "id": 3,
                    "args": [
                        { "kind": "str", "value": "x", "id": 4 },
                        {
                            "kind": "app",
                            "opcode": "Set",
                            "id": 5,
                            "args": [
                                { "kind": "int", "value": 1, "id": 6 },
                                { "kind": "int", "value": 2, "id": 7 }
                            ]
                        },
                        { "kind": "str", "value": "y", "id": 8 },
                        {
                            "kind": "app",
                            "opcode": "Bool",
                            "id": 9,
                            "args": []
                        }
                    ]
                }
            }]
        }]
    }
    "#;
    let modules = parse_quint_json(json).expect("should parse record set");
    let m = &modules[0];
    match &m.units[0].node {
        Unit::Operator(op) => match &op.body.node {
            Expr::RecordSet(fields) => {
                assert_eq!(fields.len(), 2);
                assert_eq!(fields[0].0.node, "x");
                assert_eq!(fields[1].0.node, "y");
            }
            other => panic!("expected RecordSet, got {other:?}"),
        },
        other => panic!("expected Operator, got {other:?}"),
    }
}

/// Test nth (0-based to 1-based index adjustment).
#[test]
fn test_parse_quint_json_nth() {
    let json = r#"
    {
        "modules": [{
            "name": "NthSpec",
            "id": 1,
            "declarations": [{
                "kind": "def",
                "name": "First",
                "qualifier": "val",
                "id": 2,
                "params": [],
                "expr": {
                    "kind": "app",
                    "opcode": "nth",
                    "id": 3,
                    "args": [
                        { "kind": "name", "name": "seq", "id": 4 },
                        { "kind": "int", "value": 0, "id": 5 }
                    ]
                }
            }]
        }]
    }
    "#;
    let modules = parse_quint_json(json).expect("should parse nth");
    let m = &modules[0];
    match &m.units[0].node {
        Unit::Operator(op) => match &op.body.node {
            // nth(seq, 0) -> FuncApply(seq, 0 + 1)
            Expr::FuncApply(func, arg) => {
                assert!(matches!(func.node, Expr::Ident(_, _)));
                // arg should be Add(Int(0), Int(1))
                match &arg.node {
                    Expr::Add(left, right) => {
                        assert!(matches!(left.node, Expr::Int(_)));
                        match &right.node {
                            Expr::Int(n) => assert_eq!(*n, 1.into()),
                            other => panic!("expected Int(1), got {other:?}"),
                        }
                    }
                    other => panic!("expected Add, got {other:?}"),
                }
            }
            other => panic!("expected FuncApply, got {other:?}"),
        },
        other => panic!("expected Operator, got {other:?}"),
    }
}

/// Test put/setBy maps to EXCEPT.
#[test]
fn test_parse_quint_json_put() {
    let json = r#"
    {
        "modules": [{
            "name": "PutSpec",
            "id": 1,
            "declarations": [{
                "kind": "def",
                "name": "Updated",
                "qualifier": "val",
                "id": 2,
                "params": [],
                "expr": {
                    "kind": "app",
                    "opcode": "put",
                    "id": 3,
                    "args": [
                        { "kind": "name", "name": "m", "id": 4 },
                        { "kind": "str", "value": "key", "id": 5 },
                        { "kind": "int", "value": 42, "id": 6 }
                    ]
                }
            }]
        }]
    }
    "#;
    let modules = parse_quint_json(json).expect("should parse put");
    let m = &modules[0];
    match &m.units[0].node {
        Unit::Operator(op) => match &op.body.node {
            Expr::Except(base, specs) => {
                assert!(matches!(base.node, Expr::Ident(_, _)));
                assert_eq!(specs.len(), 1);
                assert_eq!(specs[0].path.len(), 1);
            }
            other => panic!("expected Except, got {other:?}"),
        },
        other => panic!("expected Operator, got {other:?}"),
    }
}

/// Test parsing real Apalache booleans.qnt.json file.
/// This validates compatibility with actual Quint compiler output, which includes
/// extra top-level fields (stage, warnings, table, types, effects, errors) and
/// declaration-level fields (typeAnnotation, depth) that we ignore.
#[test]
fn test_parse_real_booleans_qnt_json() {
    let path = std::path::Path::new(env!("HOME")).join("apalache-ref/test/tla/booleans.qnt.json");
    if !path.exists() {
        // Skip gracefully if apalache-ref is not available.
        eprintln!("Skipping: {} not found", path.display());
        return;
    }
    let json = std::fs::read_to_string(&path).expect("should read booleans.qnt.json");
    let modules = parse_quint_json(&json).expect("should parse real booleans.qnt.json");
    assert_eq!(modules.len(), 1, "expected 1 module");
    let m = &modules[0];
    assert_eq!(m.name.node, "booleans");

    // Should have: var b, def step, def init
    assert_eq!(m.units.len(), 3, "expected 3 units (var + 2 defs)");

    // First unit: variable b
    match &m.units[0].node {
        Unit::Variable(vars) => {
            assert_eq!(vars.len(), 1);
            assert_eq!(vars[0].node, "b");
        }
        other => panic!("expected Variable, got {other:?}"),
    }

    // Second and third: operator defs (step, init)
    let mut op_names: Vec<&str> = Vec::new();
    for unit in &m.units[1..] {
        match &unit.node {
            Unit::Operator(op) => op_names.push(&op.name.node),
            other => panic!("expected Operator, got {other:?}"),
        }
    }
    assert!(op_names.contains(&"step"), "should have 'step' operator");
    assert!(op_names.contains(&"init"), "should have 'init' operator");

    // The step operator body should contain assign (b' = ...) via actionAll
    // which translates to a conjunction of operations.
    let step_unit = m.units.iter().find(|u| {
        matches!(&u.node, Unit::Operator(op) if op.name.node == "step")
    });
    assert!(step_unit.is_some(), "step operator must exist");
}

/// Test parsing real Apalache bigint.qnt.json file.
#[test]
fn test_parse_real_bigint_qnt_json() {
    let path = std::path::Path::new(env!("HOME")).join("apalache-ref/test/tla/bigint.qnt.json");
    if !path.exists() {
        eprintln!("Skipping: {} not found", path.display());
        return;
    }
    let json = std::fs::read_to_string(&path).expect("should read bigint.qnt.json");
    let modules = parse_quint_json(&json).expect("should parse real bigint.qnt.json");
    assert_eq!(modules.len(), 1, "expected 1 module");
    let m = &modules[0];
    assert_eq!(m.name.node, "t");

    // Should have: var balance, def step, def inv, def init
    assert_eq!(m.units.len(), 4, "expected 4 units (var + 3 defs)");

    // First: variable balance
    match &m.units[0].node {
        Unit::Variable(vars) => {
            assert_eq!(vars[0].node, "balance");
        }
        other => panic!("expected Variable(balance), got {other:?}"),
    }

    // Check that the init operator contains assignment with big integer (100000000000)
    let init_unit = m.units.iter().find(|u| {
        matches!(&u.node, Unit::Operator(op) if op.name.node == "init")
    });
    assert!(init_unit.is_some(), "init operator must exist");
    match &init_unit.unwrap().node {
        Unit::Operator(op) => {
            // init body: balance' = 100000000000
            // Translated as: Eq(Prime(Ident("balance")), Int(100000000000))
            match &op.body.node {
                Expr::Eq(left, right) => {
                    match &left.node {
                        Expr::Prime(inner) => match &inner.node {
                            Expr::Ident(name, _) => assert_eq!(name, "balance"),
                            other => panic!("expected Ident(balance) inside Prime, got {other:?}"),
                        },
                        other => panic!("expected Prime, got {other:?}"),
                    }
                    match &right.node {
                        Expr::Int(n) => {
                            assert_eq!(*n, 100_000_000_000i64.into());
                        }
                        other => panic!("expected Int(100000000000), got {other:?}"),
                    }
                }
                other => panic!("expected Eq for init body, got {other:?}"),
            }
        }
        _ => unreachable!(),
    }

    // Check that inv operator uses ilt (less-than)
    let inv_unit = m.units.iter().find(|u| {
        matches!(&u.node, Unit::Operator(op) if op.name.node == "inv")
    });
    assert!(inv_unit.is_some(), "inv operator must exist");
    match &inv_unit.unwrap().node {
        Unit::Operator(op) => match &op.body.node {
            Expr::Lt(_, _) => {} // correct: ilt -> Lt
            other => panic!("expected Lt for inv body, got {other:?}"),
        },
        _ => unreachable!(),
    }
}

/// Test that extra top-level fields in Quint output (stage, warnings, table, types,
/// effects, errors) are gracefully ignored by our deserializer.
#[test]
fn test_parse_quint_json_ignores_extra_fields() {
    let json = r#"
    {
        "stage": "compiling",
        "warnings": [],
        "modules": [{
            "name": "M",
            "id": 1,
            "declarations": [{
                "kind": "var",
                "name": "x",
                "typeAnnotation": {"id": 1, "kind": "int"},
                "id": 2,
                "depth": 0
            }]
        }],
        "table": {},
        "types": {},
        "effects": {},
        "errors": []
    }
    "#;
    let modules = parse_quint_json(json).expect("should ignore extra fields");
    assert_eq!(modules.len(), 1);
    assert_eq!(modules[0].name.node, "M");
    match &modules[0].units[0].node {
        Unit::Variable(vars) => assert_eq!(vars[0].node, "x"),
        other => panic!("expected Variable, got {other:?}"),
    }
}

/// Test lambda expression translation (used in filter, map, etc.).
#[test]
fn test_parse_quint_json_lambda() {
    let json = r#"
    {
        "modules": [{
            "name": "LamSpec",
            "id": 1,
            "declarations": [{
                "kind": "def",
                "name": "doubled",
                "qualifier": "val",
                "id": 2,
                "expr": {
                    "kind": "app",
                    "opcode": "map",
                    "id": 3,
                    "args": [
                        {
                            "kind": "app",
                            "opcode": "Set",
                            "id": 4,
                            "args": [
                                { "kind": "int", "value": 1, "id": 5 },
                                { "kind": "int", "value": 2, "id": 6 }
                            ]
                        },
                        {
                            "kind": "lambda",
                            "id": 7,
                            "qualifier": "puredef",
                            "params": [{ "name": "x", "id": 8 }],
                            "expr": {
                                "kind": "app",
                                "opcode": "imul",
                                "id": 9,
                                "args": [
                                    { "kind": "name", "name": "x", "id": 10 },
                                    { "kind": "int", "value": 2, "id": 11 }
                                ]
                            }
                        }
                    ]
                }
            }]
        }]
    }
    "#;
    let modules = parse_quint_json(json).expect("should parse map with lambda");
    let m = &modules[0];
    match &m.units[0].node {
        Unit::Operator(op) => {
            assert_eq!(op.name.node, "doubled");
            // map(Set, lambda) -> SetBuilder(body, [x \in Set])
            match &op.body.node {
                Expr::SetBuilder(body, bounds) => {
                    assert_eq!(bounds.len(), 1);
                    assert_eq!(bounds[0].name.node, "x");
                    // body should be Mul(x, 2)
                    assert!(matches!(body.node, Expr::Mul(_, _)));
                }
                other => panic!("expected SetBuilder, got {other:?}"),
            }
        }
        other => panic!("expected Operator, got {other:?}"),
    }
}

/// Test temporal operator translations.
#[test]
fn test_parse_quint_json_temporal_ops() {
    let json = r#"
    {
        "modules": [{
            "name": "TemporalSpec",
            "id": 1,
            "declarations": [
                {
                    "kind": "def",
                    "name": "AlwaysSafe",
                    "qualifier": "temporal",
                    "id": 2,
                    "expr": {
                        "kind": "app",
                        "opcode": "always",
                        "id": 3,
                        "args": [
                            { "kind": "name", "name": "Safe", "id": 4 }
                        ]
                    }
                },
                {
                    "kind": "def",
                    "name": "EventuallyDone",
                    "qualifier": "temporal",
                    "id": 5,
                    "expr": {
                        "kind": "app",
                        "opcode": "eventually",
                        "id": 6,
                        "args": [
                            { "kind": "name", "name": "Done", "id": 7 }
                        ]
                    }
                }
            ]
        }]
    }
    "#;
    let modules = parse_quint_json(json).expect("should parse temporal ops");
    let m = &modules[0];
    assert_eq!(m.units.len(), 2);

    match &m.units[0].node {
        Unit::Operator(op) => {
            assert_eq!(op.name.node, "AlwaysSafe");
            assert!(matches!(op.body.node, Expr::Always(_)));
        }
        other => panic!("expected Operator with Always, got {other:?}"),
    }

    match &m.units[1].node {
        Unit::Operator(op) => {
            assert_eq!(op.name.node, "EventuallyDone");
            assert!(matches!(op.body.node, Expr::Eventually(_)));
        }
        other => panic!("expected Operator with Eventually, got {other:?}"),
    }
}

/// Test keys maps to DOMAIN.
#[test]
fn test_parse_quint_json_keys() {
    let json = r#"
    {
        "modules": [{
            "name": "KeysSpec",
            "id": 1,
            "declarations": [{
                "kind": "def",
                "name": "K",
                "qualifier": "val",
                "id": 2,
                "params": [],
                "expr": {
                    "kind": "app",
                    "opcode": "keys",
                    "id": 3,
                    "args": [
                        { "kind": "name", "name": "m", "id": 4 }
                    ]
                }
            }]
        }]
    }
    "#;
    let modules = parse_quint_json(json).expect("should parse keys");
    let m = &modules[0];
    match &m.units[0].node {
        Unit::Operator(op) => match &op.body.node {
            Expr::Domain(_) => {} // correct
            other => panic!("expected Domain, got {other:?}"),
        },
        other => panic!("expected Operator, got {other:?}"),
    }
}
