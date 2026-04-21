// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::value::{FuncSetValue, IntIntervalFunc};
use std::sync::Arc;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_func_set_membership_with_nat_range() {
    assert_eq!(
        eval_str(r#"([x \in {1, 2} |-> x] \in [{1, 2} -> Nat])"#).unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        eval_str(r#"([x \in {1} |-> -1] \in [{1} -> Nat])"#).unwrap(),
        Value::Bool(false)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_func_in_func_set() {
    // Function set membership test: [x \in S |-> e] \in [S -> T]

    // Create function: [x \in {1,2} |-> "b0"]
    let func = eval_str(r#"[x \in {1,2} |-> "b0"]"#).unwrap();
    println!("func = {:?}", func);

    // Create function set: [{1,2} -> {"b0", "b1"}]
    let func_set = eval_str(r#"[{1,2} -> {"b0", "b1"}]"#).unwrap();
    println!("func_set = {:?}", func_set);

    // The function should be in the function set
    let result = eval_str(r#"[x \in {1,2} |-> "b0"] \in [{1,2} -> {"b0", "b1"}]"#).unwrap();
    println!("result = {:?}", result);

    assert_eq!(result, Value::Bool(true));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_func_set_membership_tuple_seq_and_intfunc_use_interval_domain_helper() {
    assert_eq!(
        eval_str(r#"<< "a", "b" >> \in [1..2 -> {"a", "b"}]"#).unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        eval_str(r#"<< "a", "c" >> \in [1..2 -> {"a", "b"}]"#).unwrap(),
        Value::Bool(false)
    );
    assert_eq!(
        eval_str(r#"[i \in 2..3 |-> "a"] \in [2..3 -> {"a", "b"}]"#).unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        eval_str(r#"[i \in 2..3 |-> "a"] \in [1..2 -> {"a", "b"}]"#).unwrap(),
        Value::Bool(false)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lazy_powerset_membership() {
    // Lazy powerset membership: x \in SUBSET S <==> x \subseteq S
    // This tests that we don't enumerate the full powerset

    // {1} is a subset of {1, 2, 3}
    assert_eq!(
        eval_str(r#"{1} \in SUBSET {1, 2, 3}"#).unwrap(),
        Value::Bool(true)
    );

    // {1, 2} is a subset of {1, 2, 3}
    assert_eq!(
        eval_str(r#"{1, 2} \in SUBSET {1, 2, 3}"#).unwrap(),
        Value::Bool(true)
    );

    // {} is a subset of any set
    assert_eq!(
        eval_str(r#"{} \in SUBSET {1, 2, 3}"#).unwrap(),
        Value::Bool(true)
    );

    // {4} is NOT a subset of {1, 2, 3}
    assert_eq!(
        eval_str(r#"{4} \in SUBSET {1, 2, 3}"#).unwrap(),
        Value::Bool(false)
    );

    // Non-set values are not in SUBSET
    assert_eq!(
        eval_str(r#"1 \in SUBSET {1, 2, 3}"#).unwrap(),
        Value::Bool(false)
    );

    // Test \notin SUBSET
    assert_eq!(
        eval_str(r#"{4} \notin SUBSET {1, 2, 3}"#).unwrap(),
        Value::Bool(true)
    );

    assert_eq!(
        eval_str(r#"{1} \notin SUBSET {1, 2, 3}"#).unwrap(),
        Value::Bool(false)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lazy_nested_powerset_membership() {
    // Test nested powersets like SlidingPuzzles: board \in SUBSET (SUBSET Pos)
    // This checks that lazy evaluation works recursively

    // {{1}, {2}} is a set of subsets of {1, 2, 3}
    // So {{1}, {2}} \in SUBSET SUBSET {1, 2, 3} should be TRUE
    assert_eq!(
        eval_str(r#"{{1}, {2}} \in SUBSET SUBSET {1, 2, 3}"#).unwrap(),
        Value::Bool(true)
    );

    // {{1}, {4}} should be FALSE because {4} is not a subset of {1, 2, 3}
    assert_eq!(
        eval_str(r#"{{1}, {4}} \in SUBSET SUBSET {1, 2, 3}"#).unwrap(),
        Value::Bool(false)
    );

    // Empty set of sets is valid
    assert_eq!(
        eval_str(r#"{} \in SUBSET SUBSET {1, 2, 3}"#).unwrap(),
        Value::Bool(true)
    );

    // {1} (not a set of sets) should be FALSE
    assert_eq!(
        eval_str(r#"{{1, 2}, 3} \in SUBSET SUBSET {1, 2, 3}"#).unwrap(),
        Value::Bool(false)
    );

    // Test \notin for nested powerset
    assert_eq!(
        eval_str(r#"{{1}, {4}} \notin SUBSET SUBSET {1, 2, 3}"#).unwrap(),
        Value::Bool(true)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lazy_seq_membership() {
    // Lazy Seq membership: x \in Seq(S) <==> x is a sequence AND all elements are in S
    // This tests that we don't enumerate the infinite set Seq(S)

    // Empty sequence is in Seq(S) for any S
    assert_eq!(
        eval_str(r#"<<>> \in Seq({1, 2, 3})"#).unwrap(),
        Value::Bool(true)
    );

    // <<1, 2>> is in Seq({1, 2, 3})
    assert_eq!(
        eval_str(r#"<<1, 2>> \in Seq({1, 2, 3})"#).unwrap(),
        Value::Bool(true)
    );

    // <<1, 4>> is NOT in Seq({1, 2, 3}) because 4 is not in {1, 2, 3}
    assert_eq!(
        eval_str(r#"<<1, 4>> \in Seq({1, 2, 3})"#).unwrap(),
        Value::Bool(false)
    );

    // Non-sequence values are not in Seq(S)
    assert_eq!(
        eval_str(r#"1 \in Seq({1, 2, 3})"#).unwrap(),
        Value::Bool(false)
    );

    // A set is not a sequence
    assert_eq!(
        eval_str(r#"{1, 2} \in Seq({1, 2, 3})"#).unwrap(),
        Value::Bool(false)
    );

    // Test \notin Seq
    assert_eq!(
        eval_str(r#"<<1, 4>> \notin Seq({1, 2, 3})"#).unwrap(),
        Value::Bool(true)
    );

    assert_eq!(
        eval_str(r#"<<1, 2>> \notin Seq({1, 2, 3})"#).unwrap(),
        Value::Bool(false)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lazy_seq_membership_manual_func_uses_domain_helper() {
    let module_src = r#"
---- MODULE Test ----
Op == Seq({"a", "b"})
====
"#;
    let tree = parse_to_syntax_tree(module_src);
    let lower_result = lower(FileId(0), &tree);
    assert!(
        lower_result.errors.is_empty(),
        "Lower errors: {:?}",
        lower_result.errors
    );
    let module = lower_result.module.expect("module should lower");
    let seq_expr = module
        .units
        .iter()
        .find_map(|unit| match &unit.node {
            tla_core::ast::Unit::Operator(def) if def.name.node == "Op" => Some(&def.body),
            _ => None,
        })
        .expect("Op definition should exist");

    let ctx = EvalCtx::new();

    let func = Value::Func(Arc::new(FuncValue::from_sorted_entries(vec![
        (Value::int(1), Value::string("a")),
        (Value::int(2), Value::string("b")),
    ])));
    assert!(
        crate::eval_membership::eval_membership_lazy(&ctx, &func, seq_expr).unwrap(),
        "manual Func with domain 1..n should satisfy Seq(S)"
    );

    let gap_domain = Value::Func(Arc::new(FuncValue::from_sorted_entries(vec![
        (Value::int(1), Value::string("a")),
        (Value::int(3), Value::string("b")),
    ])));
    assert!(
        !crate::eval_membership::eval_membership_lazy(&ctx, &gap_domain, seq_expr).unwrap(),
        "manual Func with non-consecutive domain should not satisfy Seq(S)"
    );

    let wrong_range = Value::Func(Arc::new(FuncValue::from_sorted_entries(vec![
        (Value::int(1), Value::string("a")),
        (Value::int(2), Value::string("c")),
    ])));
    assert!(
        !crate::eval_membership::eval_membership_lazy(&ctx, &wrong_range, seq_expr).unwrap(),
        "manual Func with values outside S should not satisfy Seq(S)"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lazy_nested_seq_membership() {
    // Test nested sequences: Seq(S \times T) pattern from ReadersWriters
    // waiting \in Seq({"read", "write"} \times Actors)

    // Empty sequence is valid
    assert_eq!(
        eval_str(r#"<<>> \in Seq({"a", "b"} \times {1, 2})"#).unwrap(),
        Value::Bool(true)
    );

    // <<<<"a", 1>>, <<"b", 2>>>> is a valid sequence of pairs
    assert_eq!(
        eval_str(r#"<< <<"a", 1>>, <<"b", 2>> >> \in Seq({"a", "b"} \times {1, 2})"#).unwrap(),
        Value::Bool(true)
    );

    // <<<<"c", 1>>>> is NOT valid because "c" is not in {"a", "b"}
    assert_eq!(
        eval_str(r#"<< <<"c", 1>> >> \in Seq({"a", "b"} \times {1, 2})"#).unwrap(),
        Value::Bool(false)
    );

    // <<<<"a", 3>>>> is NOT valid because 3 is not in {1, 2}
    assert_eq!(
        eval_str(r#"<< <<"a", 3>> >> \in Seq({"a", "b"} \times {1, 2})"#).unwrap(),
        Value::Bool(false)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lazy_recordset_membership_with_int() {
    // Test RecordSet membership with infinite sets (Int/Nat)
    // This is the pattern used in EWD998: Token == [pos : Node, q : Int, color : Color]
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    let src = r#"
---- MODULE Test ----
EXTENDS Integers
Node == 0..3
Color == {"white", "black"}
Token == [pos : Node, q : Int, color : Color]

ValidToken == [color |-> "black", pos |-> 1, q |-> 0]
InvalidPos == [color |-> "white", pos |-> 5, q |-> 0]
InvalidColor == [color |-> "green", pos |-> 1, q |-> 0]
MissingField == [color |-> "black", pos |-> 1]

TestValid == ValidToken \in Token
TestInvalidPos == InvalidPos \in Token
TestInvalidColor == InvalidColor \in Token
TestMissingField == MissingField \in Token
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    assert!(
        lower_result.errors.is_empty(),
        "Lower errors: {:?}",
        lower_result.errors
    );
    let module = lower_result.module.unwrap();

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);

    // Valid record should be in Token
    let result = ctx.eval_op("TestValid").expect("TestValid");
    assert_eq!(result, Value::Bool(true), "Valid token should be in Token");

    // Invalid pos (5 not in 0..3) should NOT be in Token
    let result = ctx.eval_op("TestInvalidPos").expect("TestInvalidPos");
    assert_eq!(
        result,
        Value::Bool(false),
        "Invalid pos should not be in Token"
    );

    // Invalid color should NOT be in Token
    let result = ctx.eval_op("TestInvalidColor").expect("TestInvalidColor");
    assert_eq!(
        result,
        Value::Bool(false),
        "Invalid color should not be in Token"
    );

    // Missing field should NOT be in Token
    let result = ctx.eval_op("TestMissingField").expect("TestMissingField");
    assert_eq!(
        result,
        Value::Bool(false),
        "Missing field should not be in Token"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_func_in_func_set_with_context() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Test with context: operator definitions like Barrier's TypeOK
    let src = r#"
---- MODULE Test ----
CONSTANT N
ProcSet == 1..N
pc == [p \in ProcSet |-> "b0"]
TypeOK == pc \in [ProcSet -> {"b0", "b1"}]
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    // Debug: print the TypeOK operator definition AST
    for unit in &module.units {
        if let tla_core::ast::Unit::Operator(op_def) = &unit.node {
            if op_def.name.node == "TypeOK" {
                println!("TypeOK body AST: {:?}", op_def.body.node);
            }
        }
    }

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);
    ctx.bind_mut("N", Value::int(3));

    // First evaluate pc
    let pc_val = ctx.eval_op("pc").expect("pc should evaluate");
    println!("pc = {:?}", pc_val);

    // Then evaluate ProcSet
    let procset = ctx.eval_op("ProcSet").expect("ProcSet should evaluate");
    println!("ProcSet = {:?}", procset);

    // Then evaluate TypeOK
    let type_ok = ctx.eval_op("TypeOK").expect("TypeOK should evaluate");
    println!("TypeOK = {:?}", type_ok);

    assert_eq!(type_ok, Value::Bool(true));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_contains_with_ctx_manual_funcset_uses_domain_helper() {
    let ctx = EvalCtx::new();
    let func = Value::Func(Arc::new(FuncValue::from_sorted_entries(vec![
        (Value::int(1), Value::string("a")),
        (Value::int(3), Value::string("b")),
    ])));
    let func_set = Value::FuncSet(FuncSetValue::new(
        Value::set([Value::int(1), Value::int(3)]),
        Value::set([Value::string("a"), Value::string("b")]),
    ));

    assert!(
        crate::set_contains_with_ctx(&ctx, &func, &func_set, None).unwrap(),
        "context-aware FuncSet membership should accept matching manual Func values"
    );

    let wrong_domain = Value::Func(Arc::new(FuncValue::from_sorted_entries(vec![
        (Value::int(1), Value::string("a")),
        (Value::int(2), Value::string("b")),
    ])));
    assert!(
        !crate::set_contains_with_ctx(&ctx, &wrong_domain, &func_set, None).unwrap(),
        "context-aware FuncSet membership should reject domain mismatches"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_contains_with_ctx_tuple_seq_and_intfunc_use_interval_domain_helper() {
    let ctx = EvalCtx::new();
    let func_set = Value::FuncSet(FuncSetValue::new(
        Value::Interval(Arc::new(IntervalValue::new(1.into(), 2.into()))),
        Value::set([Value::string("a"), Value::string("b")]),
    ));

    let tuple = Value::tuple([Value::string("a"), Value::string("b")]);
    assert!(
        crate::set_contains_with_ctx(&ctx, &tuple, &func_set, None).unwrap(),
        "tuple should match [1..2 -> {{\"a\",\"b\"}}] without OrdSet materialization"
    );

    let seq = Value::seq([Value::string("a"), Value::string("b")]);
    assert!(
        crate::set_contains_with_ctx(&ctx, &seq, &func_set, None).unwrap(),
        "sequence should match [1..2 -> {{\"a\",\"b\"}}] without OrdSet materialization"
    );

    let intfunc = Value::IntFunc(Arc::new(IntIntervalFunc::new(
        1,
        2,
        vec![Value::string("a"), Value::string("b")],
    )));
    assert!(
        crate::set_contains_with_ctx(&ctx, &intfunc, &func_set, None).unwrap(),
        "IntFunc with domain 1..2 should match [1..2 -> {{\"a\",\"b\"}}]"
    );

    let shifted_intfunc = Value::IntFunc(Arc::new(IntIntervalFunc::new(
        2,
        3,
        vec![Value::string("a"), Value::string("b")],
    )));
    assert!(
        !crate::set_contains_with_ctx(&ctx, &shifted_intfunc, &func_set, None).unwrap(),
        "IntFunc with shifted domain should be rejected"
    );
}

/// Regression test for #1500: SeqSet and BigUnion with SetPred operands.
/// SeqSetValue::contains and UnionValue::contains return None when base/inner
/// membership is indeterminate (SetPred). set_contains_with_ctx must handle
/// these cases instead of falling through to TypeError.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_seqset_and_union_with_set_pred_membership_1500() {
    // SeqSet: <<2, 3>> \in Seq({n \in {1,2,3} : n > 0}) should be TRUE
    let src = r#"
---- MODULE Test ----
EXTENDS Integers, Sequences

\* Seq(SetPred) membership: <<2, 3>> is a sequence with all elements in {n \in {1,2,3} : n > 0}
SeqPredMember == <<2, 3>> \in Seq({n \in {1, 2, 3} : n > 0})

\* Seq(SetPred) non-membership via predicate failure: <<1>> has 1 which IS in base {1,2,3}
\* but 1 does NOT satisfy n > 2. This forces the indeterminate SetPred path (not a
\* base-set shortcut).
SeqPredNonMember == ~(<<1>> \in Seq({n \in {1, 2, 3} : n > 2}))

\* UNION with SetPred inner sets: 2 \in UNION {{n \in {1,2,3} : n > 1}, {10}}
UnionPredMember == 2 \in UNION {{n \in {1, 2, 3} : n > 1}, {10}}

\* UNION with SetPred non-membership via predicate failure: 1 IS in base {1,2,3}
\* but 1 does NOT satisfy n > 1, and 1 /= 10. Forces indeterminate path.
UnionPredNonMember == ~(1 \in UNION {{n \in {1, 2, 3} : n > 1}, {10}})

====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    assert!(
        lower_result.errors.is_empty(),
        "Errors: {:?}",
        lower_result.errors
    );
    let module = lower_result.module.unwrap();
    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);

    assert_eq!(
        ctx.eval_op("SeqPredMember").unwrap(),
        Value::Bool(true),
        "#1500: <<2, 3>> should be in Seq({{n \\in {{1,2,3}} : n > 0}})"
    );
    assert_eq!(
        ctx.eval_op("SeqPredNonMember").unwrap(),
        Value::Bool(true),
        "#1500: <<1>> should NOT be in Seq({{n \\in {{1,2,3}} : n > 2}}) — predicate failure path"
    );
    assert_eq!(
        ctx.eval_op("UnionPredMember").unwrap(),
        Value::Bool(true),
        "#1500: 2 should be in UNION {{{{n \\in {{1,2,3}} : n > 1}}, {{10}}}}"
    );
    assert_eq!(
        ctx.eval_op("UnionPredNonMember").unwrap(),
        Value::Bool(true),
        "#1500: 1 should NOT be in UNION {{{{n \\in {{1,2,3}} : n > 1}}, {{10}}}} — predicate failure path"
    );
}
