// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Apalache feature parity regression tests at the model checker API level.
//!
//! These tests exercise key Apalache-specific features through the `ModelChecker`
//! API directly, complementing the CLI-level tests in `crates/tla-cli/tests/apalache_parity.rs`.
//!
//! Features tested (mapped to Apalache parity gaps):
//! - Gap 12: `:=` primed assignment operator (`x' := e` equiv to `x' = e`)
//! - Gap 13: `EXCEPT ==` syntax (`[f EXCEPT ![k] == v]`)
//! - Gap 13: `<:` type annotation operator (identity in BFS mode)
//! - Gap 13: LET-without-IN (nested LET, Apalache extension)
//! - Gap 6/12: FunAsSeq (function-to-sequence conversion)
//! - Gap 6: Variants module (Variant, VariantTag, VariantGetUnsafe, VariantGetOrElse)
//! - Apalache operators: ApaFoldSet, ApaFoldSeqLeft, MkSeq, Guess, Repeat, SetAsFun
//! - Annotation operators: Skolem, Expand, ConstCardinality
//! - LAMBDA expressions in higher-order contexts
//! - Option module pattern (built on Variants)
//!
//! Tests that use `EXTENDS Apalache` or `EXTENDS Variants` require loading
//! the TLA+ library source files via `ModuleLoader`. Tests that only use
//! standard modules (Naturals, Sequences, FiniteSets) work with the simple
//! `ModelChecker::new` API.
//!
//! Part of #3828.

mod common;

use std::path::PathBuf;
use tla_check::{CheckResult, Config, ModelChecker};
use tla_core::ModuleLoader;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn config_with_invariants(invariants: &[&str]) -> Config {
    Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: invariants.iter().map(|s| s.to_string()).collect(),
        ..Default::default()
    }
}

/// Load extended modules (Apalache.tla, Variants.tla, etc.).
/// Returns the loaded module references needed for `ModelChecker::new_with_extends`.
fn load_extends(module: &tla_core::ast::Module) -> (ModuleLoader, Vec<String>) {
    let mut loader = ModuleLoader::with_base_dir(PathBuf::from("."));
    loader.add_search_path(PathBuf::from("tests/tla_library"));
    loader.add_search_path(PathBuf::from("../../test_specs/tla_library"));
    loader.add_search_path(PathBuf::from("../../test_specs"));
    let names = loader
        .load_extends(module)
        .expect("Failed to load extended modules");
    (loader, names)
}

fn assert_success(result: &CheckResult, test_name: &str) {
    match result {
        CheckResult::Success(_) => {}
        other => panic!("{test_name}: Expected Success, got: {other:?}"),
    }
}

fn assert_success_with_min_states(result: &CheckResult, test_name: &str, min_states: usize) {
    match result {
        CheckResult::Success(stats) => {
            assert!(
                stats.states_found >= min_states,
                "{test_name}: Expected at least {min_states} states, got {}",
                stats.states_found
            );
        }
        other => panic!("{test_name}: Expected Success, got: {other:?}"),
    }
}

fn assert_success_with_states(result: &CheckResult, test_name: &str, expected_states: usize) {
    match result {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, expected_states,
                "{test_name}: Expected {expected_states} states, got {}",
                stats.states_found
            );
        }
        other => panic!("{test_name}: Expected Success, got: {other:?}"),
    }
}

// ===========================================================================
// Gap 12: := primed assignment operator
// ===========================================================================

/// := operator: basic assignment in Init and Next (x := 0, x' := x + 1).
/// In BFS mode, := is semantically equivalent to =.
/// Requires loading Apalache.tla for the := operator definition.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_apalache_assign_op_basic() {
    let src = r#"
---- MODULE ApalacheAssignOp ----
EXTENDS Apalache, Naturals
VARIABLE x
Init == x := 0
Next == IF x < 3 THEN x' := x + 1 ELSE UNCHANGED x
Bounded == x \in 0..3
====
"#;
    let module = common::parse_module(src);
    let config = config_with_invariants(&["Bounded"]);

    let (loader, names) = load_extends(&module);
    let extended_modules: Vec<_> = names
        .iter()
        .filter_map(|name| loader.get(name).map(|l| &l.module))
        .collect();

    let mut checker = ModelChecker::new_with_extends(&module, &extended_modules, &config);
    checker.set_deadlock_check(false);
    let result = checker.check();

    assert_success_with_states(&result, "assign_op_basic", 4);
}

/// := operator in nested IF/THEN/ELSE and conjunctive lists with multiple variables.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_apalache_assign_op_nested() {
    let src = r#"
---- MODULE ApalacheAssignOpNested ----
EXTENDS Apalache, Naturals
VARIABLES x, y
Init ==
    /\ x := 0
    /\ y := 10
Next ==
    /\ IF x < 3
       THEN x' := x + 1
       ELSE x' := x
    /\ IF y > 7
       THEN y' := y - 1
       ELSE y' := y
XBounded == x \in 0..3
YBounded == y \in 7..10
====
"#;
    let module = common::parse_module(src);
    let config = config_with_invariants(&["XBounded", "YBounded"]);

    let (loader, names) = load_extends(&module);
    let extended_modules: Vec<_> = names
        .iter()
        .filter_map(|name| loader.get(name).map(|l| &l.module))
        .collect();

    let mut checker = ModelChecker::new_with_extends(&module, &extended_modules, &config);
    checker.set_deadlock_check(false);
    let result = checker.check();

    assert_success(&result, "assign_op_nested");
}

// ===========================================================================
// Gap 13: EXCEPT == syntax
// ===========================================================================

/// EXCEPT with == (Apalache extension): [f EXCEPT ![k] == v].
/// The == form is syntactically distinct from = but semantically identical.
/// No EXTENDS Apalache needed -- this is a parser-level extension.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_apalache_except_double_eq() {
    let src = r#"
---- MODULE ApalacheExceptDoubleEq ----
EXTENDS Naturals
VARIABLE counters
Init == counters = [i \in {1, 2, 3} |-> 0]
Next ==
    \/ /\ counters[1] < 2
       /\ counters' = [counters EXCEPT ![1] == counters[1] + 1]
    \/ /\ counters[2] < 2 /\ counters[3] < 2
       /\ counters' = [counters EXCEPT ![2] == counters[2] + 1,
                                       ![3] == counters[3] + 1]
    \/ UNCHANGED counters
DomainOK == DOMAIN counters = {1, 2, 3}
NonNeg == \A i \in {1, 2, 3} : counters[i] >= 0
Bounded == \A i \in {1, 2, 3} : counters[i] <= 2
====
"#;
    let module = common::parse_module(src);
    let config = config_with_invariants(&["DomainOK", "NonNeg", "Bounded"]);

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    let result = checker.check();

    assert_success(&result, "except_double_eq");
}

// ===========================================================================
// Gap 13: <: type annotation operator
// ===========================================================================

/// <: type annotation: user-defined operator `a <: b == a` acting as identity.
/// Apalache uses <: for type annotations; in BFS mode it's pure identity.
/// No EXTENDS Apalache needed -- the <: operator is user-defined in the spec.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_apalache_type_annotation() {
    let src = r#"
---- MODULE ApalacheTypeAnnotation ----
EXTENDS Naturals, FiniteSets
a <: b == a
VARIABLE state
Init ==
    state = [
        nums |-> {} <: {"set_of_int"},
        flag |-> FALSE,
        count |-> 0
    ]
Next ==
    \/ /\ state.count < 3
       /\ state' = [state EXCEPT
            !.nums = state.nums \union {state.count},
            !.count = state.count + 1]
    \/ UNCHANGED state
EmptyAnnotated == ({} <: {"type_hint"}) = {}
SetAnnotated == ({1, 2} <: {"type_hint"}) = {1, 2}
IntAnnotated == (42 <: "type_hint") = 42
BoolAnnotated == (TRUE <: "type_hint") = TRUE
SeqAnnotated == (<<1, 2>> <: "type_hint") = <<1, 2>>
CountOK == state.count \in 0..3
====
"#;
    let module = common::parse_module(src);
    let config = config_with_invariants(&[
        "EmptyAnnotated",
        "SetAnnotated",
        "IntAnnotated",
        "BoolAnnotated",
        "SeqAnnotated",
        "CountOK",
    ]);

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    let result = checker.check();

    // POR may reduce state count, so just assert success with at least 1 state.
    assert_success_with_min_states(&result, "type_annotation", 1);
}

// ===========================================================================
// Gap 13: LET-without-IN
// ===========================================================================

/// LET-without-IN: Apalache extension allowing nested LET blocks.
/// Tests that `LET ... IN LET ... IN expr` parses and evaluates correctly.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_apalache_let_without_in() {
    let src = r#"
---- MODULE ApalacheLetWithoutIn ----
EXTENDS Naturals, FiniteSets
VARIABLE items

Range(seq) ==
    LET helper(S, e) == S \union {e}
    IN LET result == helper(helper({}, 1), 2)
    IN result

Init == items = {1, 2}

Next == IF Cardinality(items) < 4
        THEN \E x \in 1..5 : items' = items \union {x}
        ELSE UNCHANGED items

RangeOK == Range(<<1, 2>>) = {1, 2}
ItemsSubset == items \subseteq 1..5
ItemsBounded == Cardinality(items) <= 5
====
"#;
    let module = common::parse_module(src);
    let config = config_with_invariants(&["RangeOK", "ItemsSubset", "ItemsBounded"]);

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    let result = checker.check();

    assert_success(&result, "let_without_in");
}

// ===========================================================================
// Gap 6/12: FunAsSeq (function-to-sequence conversion)
// ===========================================================================

/// FunAsSeq: convert a function with domain 1..n to a sequence, then use
/// standard sequence operators (Len, Head, SubSeq).
/// Requires loading Apalache.tla for FunAsSeq operator.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_apalache_fun_as_seq() {
    let src = r#"
---- MODULE ApalacheFunAsSeq ----
EXTENDS Apalache, Naturals, Sequences
VARIABLE seq
f == [i \in {1, 2, 3} |-> i * 10]
asSeq == FunAsSeq(f, 3, 3)
Init == seq = asSeq
Next ==
    \/ /\ Len(seq) < 5
       /\ seq' = Append(seq, 40)
    \/ /\ Len(seq) > 1
       /\ seq' = Tail(seq)
    \/ UNCHANGED seq
AsSeqLenOK == Len(asSeq) = 3
AsSeqElem1 == asSeq[1] = 10
AsSeqElem2 == asSeq[2] = 20
AsSeqElem3 == asSeq[3] = 30
HeadOK == Head(asSeq) = 10
SubSeqOK == SubSeq(asSeq, 1, 2) = <<10, 20>>
====
"#;
    let module = common::parse_module(src);
    let config = config_with_invariants(&[
        "AsSeqLenOK",
        "AsSeqElem1",
        "AsSeqElem2",
        "AsSeqElem3",
        "HeadOK",
        "SubSeqOK",
    ]);

    let (loader, names) = load_extends(&module);
    let extended_modules: Vec<_> = names
        .iter()
        .filter_map(|name| loader.get(name).map(|l| &l.module))
        .collect();

    let mut checker = ModelChecker::new_with_extends(&module, &extended_modules, &config);
    checker.set_deadlock_check(false);
    let result = checker.check();

    assert_success(&result, "fun_as_seq");
}

// ===========================================================================
// Gap 6: Variants module
// ===========================================================================

/// Variants module: Variant construction, VariantTag, VariantGetUnsafe,
/// VariantGetOrElse in a message-passing state machine pattern.
/// Requires loading Variants.tla from test_specs/tla_library.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_apalache_variants() {
    let src = r#"
---- MODULE ApalacheVariants ----
EXTENDS Variants, Naturals
VARIABLE msg
MkRequest(id) == Variant("Request", id)
MkResponse(val) == Variant("Response", val)
MkError(code) == Variant("Error", code)
Init == msg = MkRequest(1)
Next ==
    \/ /\ VariantTag(msg) = "Request"
       /\ msg' = MkResponse(VariantGetUnsafe("Request", msg) * 10)
    \/ /\ VariantTag(msg) = "Response"
       /\ LET val == VariantGetUnsafe("Response", msg)
          IN IF val > 50
             THEN msg' = MkError(500)
             ELSE msg' = MkRequest(val + 1)
    \/ /\ VariantTag(msg) = "Error"
       /\ msg' = MkRequest(0)
ValidTag == VariantTag(msg) \in {"Request", "Response", "Error"}
FallbackOK == VariantGetOrElse("Missing", msg, -1) = -1
====
"#;
    let module = common::parse_module(src);
    let config = config_with_invariants(&["ValidTag", "FallbackOK"]);

    let (loader, names) = load_extends(&module);
    let extended_modules: Vec<_> = names
        .iter()
        .filter_map(|name| loader.get(name).map(|l| &l.module))
        .collect();

    let mut checker = ModelChecker::new_with_extends(&module, &extended_modules, &config);
    checker.set_deadlock_check(false);
    let result = checker.check();

    assert_success(&result, "variants");
}

// ===========================================================================
// Apalache operators: ApaFoldSet, ApaFoldSeqLeft, MkSeq
// ===========================================================================

/// ApaFoldSet: fold a binary operator over a finite set.
/// Tests sum, product, empty set, single-element set, and record accumulator.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_apalache_fold_set() {
    let src = r#"
---- MODULE ApalacheFoldSet ----
EXTENDS Apalache, Naturals, FiniteSets
VARIABLE x
Add(a, b) == a + b
Mul(a, b) == a * b
MergeCount(acc, elem) ==
    [sum |-> acc.sum + elem, count |-> acc.count + 1]
Init == x = 0
Next == IF x < 1 THEN x' = x + 1 ELSE UNCHANGED x
SumOK == ApaFoldSet(Add, 0, {1, 2, 3}) = 6
ProductOK == ApaFoldSet(Mul, 1, {2, 3, 4}) = 24
EmptyOK == ApaFoldSet(Add, 42, {}) = 42
SingleOK == ApaFoldSet(Add, 0, {7}) = 7
StatsOK == LET s == ApaFoldSet(MergeCount, [sum |-> 0, count |-> 0], {10, 20, 30})
           IN s.sum = 60 /\ s.count = 3
====
"#;
    let module = common::parse_module(src);
    let config = config_with_invariants(&["SumOK", "ProductOK", "EmptyOK", "SingleOK", "StatsOK"]);

    let (loader, names) = load_extends(&module);
    let extended_modules: Vec<_> = names
        .iter()
        .filter_map(|name| loader.get(name).map(|l| &l.module))
        .collect();

    let mut checker = ModelChecker::new_with_extends(&module, &extended_modules, &config);
    checker.set_deadlock_check(false);
    let result = checker.check();

    assert_success_with_states(&result, "fold_set", 2);
}

/// ApaFoldSeqLeft: fold a binary operator left-to-right over a sequence.
/// MkSeq: construct a sequence from an operator.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_apalache_fold_seq_and_mkseq() {
    let src = r#"
---- MODULE ApalacheFoldSeqMkSeq ----
EXTENDS Apalache, Naturals, Sequences
VARIABLE n
Add(a, b) == a + b
Double(i) == i * 2
Init == n = 0
Next == IF n < 1 THEN n' = n + 1 ELSE UNCHANGED n
SeqSumOK == ApaFoldSeqLeft(Add, 0, <<10, 20, 30>>) = 60
EmptySeqOK == ApaFoldSeqLeft(Add, 99, <<>>) = 99
MkSeqOK == MkSeq(4, Double) = <<2, 4, 6, 8>>
MkSeqLenOK == Len(MkSeq(4, Double)) = 4
PipeOK == ApaFoldSeqLeft(Add, 0, MkSeq(4, Double)) = 20
====
"#;
    let module = common::parse_module(src);
    let config =
        config_with_invariants(&["SeqSumOK", "EmptySeqOK", "MkSeqOK", "MkSeqLenOK", "PipeOK"]);

    let (loader, names) = load_extends(&module);
    let extended_modules: Vec<_> = names
        .iter()
        .filter_map(|name| loader.get(name).map(|l| &l.module))
        .collect();

    let mut checker = ModelChecker::new_with_extends(&module, &extended_modules, &config);
    checker.set_deadlock_check(false);
    let result = checker.check();

    assert_success_with_states(&result, "fold_seq_mkseq", 2);
}

// ===========================================================================
// LAMBDA expressions in higher-order contexts
// ===========================================================================

/// LAMBDA: anonymous operators passed to ApaFoldSet, ApaFoldSeqLeft, MkSeq.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_apalache_lambda() {
    let src = r#"
---- MODULE ApalacheLambda ----
EXTENDS Apalache, Naturals, Sequences
VARIABLE n
Init == n = 0
Next == IF n < 1 THEN n' = n + 1 ELSE UNCHANGED n
LambdaSumOK == ApaFoldSet(LAMBDA a, b: a + b, 0, {1, 2, 3, 4, 5}) = 15
LambdaProductOK == ApaFoldSeqLeft(LAMBDA acc, x: acc * x, 1, <<2, 3, 4>>) = 24
LambdaSquareOK == MkSeq(4, LAMBDA i: i * i) = <<1, 4, 9, 16>>
LambdaFilterOK == ApaFoldSet(
    LAMBDA a, b: IF b > 3 THEN a + b ELSE a,
    0,
    {1, 2, 3, 4, 5}
) = 9
====
"#;
    let module = common::parse_module(src);
    let config = config_with_invariants(&[
        "LambdaSumOK",
        "LambdaProductOK",
        "LambdaSquareOK",
        "LambdaFilterOK",
    ]);

    let (loader, names) = load_extends(&module);
    let extended_modules: Vec<_> = names
        .iter()
        .filter_map(|name| loader.get(name).map(|l| &l.module))
        .collect();

    let mut checker = ModelChecker::new_with_extends(&module, &extended_modules, &config);
    checker.set_deadlock_check(false);
    let result = checker.check();

    assert_success_with_states(&result, "lambda", 2);
}

// ===========================================================================
// Guess: nondeterministic choice from a set
// ===========================================================================

/// Guess: Apalache's nondeterministic CHOOSE-like operator.
/// In BFS mode, Guess(S) behaves like CHOOSE x \in S : TRUE (picks one value).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_apalache_guess() {
    let src = r#"
---- MODULE ApalacheGuess ----
EXTENDS Apalache, Naturals
VARIABLE chosen
Init == chosen = Guess({1, 2, 3})
Next == UNCHANGED chosen
InRange == chosen \in {1, 2, 3}
====
"#;
    let module = common::parse_module(src);
    let config = config_with_invariants(&["InRange"]);

    let (loader, names) = load_extends(&module);
    let extended_modules: Vec<_> = names
        .iter()
        .filter_map(|name| loader.get(name).map(|l| &l.module))
        .collect();

    let mut checker = ModelChecker::new_with_extends(&module, &extended_modules, &config);
    checker.set_deadlock_check(false);
    let result = checker.check();

    // Guess may produce 1 state (CHOOSE-like) or 3 states (nondeterministic).
    // The key assertion is that it succeeds and the invariant holds.
    assert_success_with_min_states(&result, "guess", 1);
}

// ===========================================================================
// SetAsFun: convert set of pairs to a function
// ===========================================================================

/// SetAsFun: Apalache operator converting {<<k,v>>, ...} to a function.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_apalache_set_as_fun() {
    let src = r#"
---- MODULE ApalacheSetAsFun ----
EXTENDS Apalache, Naturals
VARIABLE f
Init == f = SetAsFun({<<1, 10>>, <<2, 20>>, <<3, 30>>})
Next == UNCHANGED f
DomainOK == DOMAIN f = {1, 2, 3}
Val1OK == f[1] = 10
Val2OK == f[2] = 20
Val3OK == f[3] = 30
====
"#;
    let module = common::parse_module(src);
    let config = config_with_invariants(&["DomainOK", "Val1OK", "Val2OK", "Val3OK"]);

    let (loader, names) = load_extends(&module);
    let extended_modules: Vec<_> = names
        .iter()
        .filter_map(|name| loader.get(name).map(|l| &l.module))
        .collect();

    let mut checker = ModelChecker::new_with_extends(&module, &extended_modules, &config);
    checker.set_deadlock_check(false);
    let result = checker.check();

    assert_success_with_states(&result, "set_as_fun", 1);
}

// ===========================================================================
// Annotation operators: Skolem, Expand, ConstCardinality
// ===========================================================================

/// Skolem, Expand, ConstCardinality: Apalache annotation operators that act
/// as identity in BFS mode (they're hints for the symbolic engine).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_apalache_annotation_operators() {
    let src = r#"
---- MODULE ApalacheAnnotationOps ----
EXTENDS Apalache, Naturals, FiniteSets
VARIABLE x
Init == x \in {1, 2, 3}
Next == UNCHANGED x
SkolemOK == Skolem(\E y \in {1, 2, 3} : y = x)
ExpandOK == x \in Expand({1, 2, 3})
CardOK == ConstCardinality(Cardinality({1, 2, 3})) = 3
====
"#;
    let module = common::parse_module(src);
    let config = config_with_invariants(&["SkolemOK", "ExpandOK", "CardOK"]);

    let (loader, names) = load_extends(&module);
    let extended_modules: Vec<_> = names
        .iter()
        .filter_map(|name| loader.get(name).map(|l| &l.module))
        .collect();

    let mut checker = ModelChecker::new_with_extends(&module, &extended_modules, &config);
    checker.set_deadlock_check(false);
    let result = checker.check();

    assert_success_with_states(&result, "annotation_operators", 3);
}

// ===========================================================================
// Repeat operator
// ===========================================================================

/// Repeat: iterated application of a two-argument operator.
/// Repeat(F, n, init) applies F(F(...F(init, 1)..., n-1), n).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_apalache_repeat() {
    let src = r#"
---- MODULE ApalacheRepeat ----
EXTENDS Apalache, Naturals
VARIABLE val
F(x, i) == x + i
Init == val = Repeat(F, 3, 0)
Next == UNCHANGED val
\* Repeat(F, 3, 0) = F(F(F(0, 1), 2), 3) = ((0+1)+2)+3 = 6
Correct == val = 6
====
"#;
    let module = common::parse_module(src);
    let config = config_with_invariants(&["Correct"]);

    let (loader, names) = load_extends(&module);
    let extended_modules: Vec<_> = names
        .iter()
        .filter_map(|name| loader.get(name).map(|l| &l.module))
        .collect();

    let mut checker = ModelChecker::new_with_extends(&module, &extended_modules, &config);
    checker.set_deadlock_check(false);
    let result = checker.check();

    assert_success_with_states(&result, "repeat", 1);
}

// ===========================================================================
// Combined: multiple Apalache features in one spec
// ===========================================================================

/// Combined test: := operator + EXCEPT == + Variants + ApaFoldSet in one spec.
/// This exercises the interaction of multiple Apalache features together.
#[cfg_attr(test, ntest::timeout(15000))]
#[test]
fn test_apalache_combined_features() {
    let src = r#"
---- MODULE ApalacheCombined ----
EXTENDS Apalache, Variants, Naturals, FiniteSets
VARIABLE state
Init ==
    /\ state := [
        values |-> [i \in {1, 2, 3} |-> 0],
        status |-> Variant("Idle", 0),
        total  |-> 0
    ]
Next ==
    \/ /\ VariantTag(state.status) = "Idle"
       /\ state' := [state EXCEPT
            !.values == [state.values EXCEPT ![1] == 1],
            !.status == Variant("Running", 1),
            !.total  == ApaFoldSet(LAMBDA a, b: a + b, 0, {1, 0, 0})]
    \/ /\ VariantTag(state.status) = "Running"
       /\ state' := [state EXCEPT
            !.status == Variant("Done", 0)]
    \/ /\ VariantTag(state.status) = "Done"
       /\ UNCHANGED state
StatusOK == VariantTag(state.status) \in {"Idle", "Running", "Done"}
TotalOK == state.total \in {0, 1}
DomainOK == DOMAIN state.values = {1, 2, 3}
====
"#;
    let module = common::parse_module(src);
    let config = config_with_invariants(&["StatusOK", "TotalOK", "DomainOK"]);

    let (loader, names) = load_extends(&module);
    let extended_modules: Vec<_> = names
        .iter()
        .filter_map(|name| loader.get(name).map(|l| &l.module))
        .collect();

    let mut checker = ModelChecker::new_with_extends(&module, &extended_modules, &config);
    checker.set_deadlock_check(false);
    let result = checker.check();

    assert_success(&result, "combined_features");
}

// ===========================================================================
// Option module (built on Variants)
// ===========================================================================

/// Option module operators via Variants: Some, None, IsSome, IsNone,
/// OptionGetOrElse, OptionToSet.
/// Requires loading Variants.tla from test_specs/tla_library.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_apalache_option_module() {
    let src = r#"
---- MODULE ApalacheOption ----
EXTENDS Integers, Sequences, Variants, FiniteSets
UNIT_VAL == "U_OF_UNIT"
Some(val) == Variant("Some", val)
NoneVal == Variant("None", UNIT_VAL)
IsSome(opt) == VariantTag(opt) = "Some"
IsNone(opt) == VariantTag(opt) = "None"
OptionGetOrElse(opt, default) == VariantGetOrElse("Some", opt, default)
OptionToSet(opt) ==
    IF IsSome(opt) THEN {VariantGetUnsafe("Some", opt)} ELSE {}
VARIABLE result
Init == result = NoneVal
Next ==
    \/ /\ IsNone(result)
       /\ result' = Some(1)
    \/ /\ IsSome(result)
       /\ LET val == OptionGetOrElse(result, 0)
          IN IF val < 3
             THEN result' = Some(val + 1)
             ELSE result' = NoneVal
ValidOption == IsSome(result) \/ IsNone(result)
NoneExclusive == IsNone(result) => ~IsSome(result)
GetOrElseOK == IsNone(result) => OptionGetOrElse(result, -1) = -1
ToSetOK == IsNone(result) => OptionToSet(result) = {}
SomeToSetOK == IsSome(result) => Cardinality(OptionToSet(result)) = 1
ValueBound == IsSome(result) => OptionGetOrElse(result, 0) \in 1..3
====
"#;
    let module = common::parse_module(src);
    let config = config_with_invariants(&[
        "ValidOption",
        "NoneExclusive",
        "GetOrElseOK",
        "ToSetOK",
        "SomeToSetOK",
        "ValueBound",
    ]);

    let (loader, names) = load_extends(&module);
    let extended_modules: Vec<_> = names
        .iter()
        .filter_map(|name| loader.get(name).map(|l| &l.module))
        .collect();

    let mut checker = ModelChecker::new_with_extends(&module, &extended_modules, &config);
    checker.set_deadlock_check(false);
    let result = checker.check();

    // States: None, Some(1), Some(2), Some(3) = 4 distinct states
    assert_success_with_states(&result, "option_module", 4);
}
