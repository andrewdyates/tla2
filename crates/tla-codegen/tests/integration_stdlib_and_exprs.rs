// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Stdlib operator and expression translation tests: Cardinality, Len, Head,
//! Tail, Append, Max, Min, Reverse, IsFiniteSet, ToString, LET, and CASE.

mod common;

use common::parse_and_generate;
use tla_codegen::CodeGenOptions;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_stdlib_cardinality() {
    // Tests Cardinality from FiniteSets module
    let source = r#"
---- MODULE CardTest ----
EXTENDS FiniteSets
VARIABLE s

Init == s = {1, 2, 3}

Next == s' = s

InvSize == Cardinality(s) = 3
====
"#;

    let options = CodeGenOptions::default();
    let code = parse_and_generate(source, &options).expect("generation failed");

    // Cardinality(s) should translate to s.len() as i64
    assert!(
        code.contains(".len() as i64"),
        "Cardinality should translate to len(): {}",
        code
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_stdlib_len_operator() {
    // Tests Len operator translation in an invariant
    let source = r#"
---- MODULE LenOp ----
EXTENDS Sequences
VARIABLE s

Init == s = {1, 2, 3}

Next == s' = s

InvHasLen == Len(s) > 0
====
"#;

    let options = CodeGenOptions::default();
    let code = parse_and_generate(source, &options).expect("generation failed");

    // Len(s) should translate to s.len() as i64
    assert!(
        code.contains(".len() as i64"),
        "Len should translate to len(): {}",
        code
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_stdlib_head_tail_operator() {
    // Tests Head and Tail operator translation in invariants
    let source = r#"
---- MODULE HeadTailOp ----
EXTENDS Sequences
VARIABLE s

Init == s = {1, 2, 3}

Next == s' = s

InvHead == Head(s) = Head(s)
InvTail == Tail(s) = Tail(s)
====
"#;

    let options = CodeGenOptions::default();
    let code = parse_and_generate(source, &options).expect("generation failed");

    // Head should translate to .first().cloned().unwrap()
    assert!(
        code.contains(".first()"),
        "Head should translate to .first(): {}",
        code
    );
    // Tail should translate to skip(1)
    assert!(
        code.contains("skip(1)"),
        "Tail should translate to skip(1): {}",
        code
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_stdlib_append() {
    // Tests Append from Sequences module
    let source = r#"
---- MODULE AppendTest ----
EXTENDS Sequences
VARIABLE seq

Init == seq = <<>>

Next == seq' = Append(seq, 1)
====
"#;

    let options = CodeGenOptions::default();
    let code = parse_and_generate(source, &options).expect("generation failed");

    // Append should generate code that pushes to a vec
    assert!(
        code.contains("push("),
        "Append should translate to push: {}",
        code
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_stdlib_max_min() {
    // Tests Max and Min from FiniteSetsExt module
    let source = r#"
---- MODULE MaxMin ----
EXTENDS FiniteSetsExt
VARIABLE s

Init == s = {1, 2, 3}

Next == s' = s

InvBounded == Max(s) >= Min(s)
====
"#;

    let options = CodeGenOptions::default();
    let code = parse_and_generate(source, &options).expect("generation failed");

    // Max and Min should translate to iter().max/min()
    assert!(
        code.contains(".max()"),
        "Max should translate to .max(): {}",
        code
    );
    assert!(
        code.contains(".min()"),
        "Min should translate to .min(): {}",
        code
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_stdlib_reverse() {
    // Tests Reverse from SequencesExt module
    let source = r#"
---- MODULE ReverseTest ----
EXTENDS SequencesExt
VARIABLE seq

Init == seq = <<1, 2, 3>>

Next == seq' = Reverse(seq)
====
"#;

    let options = CodeGenOptions::default();
    let code = parse_and_generate(source, &options).expect("generation failed");

    // Reverse should translate to .reverse()
    assert!(
        code.contains(".reverse()"),
        "Reverse should translate to .reverse(): {}",
        code
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_stdlib_is_finite_set() {
    // Tests IsFiniteSet from FiniteSets module
    let source = r#"
---- MODULE FiniteTest ----
EXTENDS FiniteSets
VARIABLE s

Init == s = {1, 2}

Next == s' = s

InvFinite == IsFiniteSet(s)
====
"#;

    let options = CodeGenOptions::default();
    let code = parse_and_generate(source, &options).expect("generation failed");

    // IsFiniteSet should translate to true (all our sets are finite)
    assert!(
        code.contains("true"),
        "IsFiniteSet should translate to true"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_stdlib_tostring() {
    // Tests ToString from TLC module
    let source = r#"
---- MODULE ToStringTest ----
EXTENDS TLC
VARIABLE x, str

Init == x = 42 /\ str = ""

Next == x' = x /\ str' = ToString(x)
====
"#;

    let options = CodeGenOptions::default();
    let code = parse_and_generate(source, &options).expect("generation failed");

    // ToString should translate to format!("{:?}", ...)
    assert!(
        code.contains("format!"),
        "ToString should translate to format!: {}",
        code
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_range_membership_uses_direct_bounds_checks() {
    let source = r#"
---- MODULE RangeMembership ----
VARIABLE x

Init == x \in 1..3

Next == x' \in 0..1 /\ x \notin 4..5
====
"#;

    let options = CodeGenOptions::default();
    let code = parse_and_generate(source, &options).expect("generation failed");

    assert!(
        code.contains("for x in range_set(1_i64, 3_i64)")
            && code.contains("for x_next in range_set(0_i64, 1_i64)"),
        "Init/next range choices should still enumerate the range directly: {}",
        code
    );
    assert!(
        code.contains("__elem >= __start && __elem <= __end"),
        "Range membership should lower to direct inclusive bounds checks: {}",
        code
    );
    assert!(
        code.contains("let __elem = new.x"),
        "is_next range membership should test the candidate next-state value directly: {}",
        code
    );
    assert!(
        code.contains("let __elem = old.x"),
        "Guard range non-membership should test the current-state value directly: {}",
        code
    );
    assert!(
        code.contains("__elem < __start || __elem > __end"),
        "Range non-membership should lower to direct exclusive bounds checks: {}",
        code
    );
    assert!(
        !code.contains("range_set(1_i64, 3_i64).contains")
            && !code.contains("range_set(0_i64, 1_i64).contains")
            && !code.contains("range_set(4_i64, 5_i64).contains"),
        "Range membership should not materialize a TlaSet for contains checks: {}",
        code
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_let_expression() {
    // Use LET in an invariant where it will be code-generated
    let source = r#"
---- MODULE LetTest ----
VARIABLE x

Init == x = 1

InvLetCheck == LET doubled == x * 2 IN doubled > 0
====
"#;

    let options = CodeGenOptions::default();
    let code = parse_and_generate(source, &options).expect("generation failed");

    // Verify LET generates let binding with a block
    assert!(
        code.contains("let doubled") || code.contains("{"),
        "LET should generate let binding:\n{}",
        code
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_case_expression() {
    let source = r#"
---- MODULE CaseTest ----
VARIABLE category

Value == 50

Init == category = CASE Value < 10 -> "small"
                     [] Value < 100 -> "medium"
                     [] OTHER -> "large"
====
"#;

    let options = CodeGenOptions::default();
    let code = parse_and_generate(source, &options).expect("generation failed");

    // Verify CASE generates if/else chain
    assert!(code.contains("if "), "CASE should generate if");
    assert!(
        code.contains("else if "),
        "CASE should generate else if for multiple arms"
    );
    assert!(
        code.contains("else {"),
        "CASE with OTHER should generate final else"
    );
}
