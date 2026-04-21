// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::lower::lower;
use crate::span::FileId;
use crate::syntax::parse_to_syntax_tree;

fn lower_module(src: &str) -> crate::ast::Module {
    let tree = parse_to_syntax_tree(src);
    let result = lower(FileId(0), &tree);
    assert!(
        result.errors.is_empty(),
        "Lower errors: {:?}",
        result.errors
    );
    result.module.expect("Expected module")
}

fn resolve_source(src: &str) -> ResolveResult {
    let module = lower_module(src);
    resolve(&module)
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_basic_operator() {
    let result = resolve_source(
        r"
        ---- MODULE Test ----
        VARIABLE x
        Init == x = 0
        ====
        ",
    );
    assert!(result.is_ok(), "Errors: {:?}", result.errors);
    assert!(result
        .symbols
        .iter()
        .any(|s| s.name == "x" && s.kind == SymbolKind::Variable));
    assert!(result
        .symbols
        .iter()
        .any(|s| s.name == "Init" && s.kind == SymbolKind::Operator));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_undefined_reference() {
    let result = resolve_source(
        r"
        ---- MODULE Test ----
        Init == y = 0
        ====
        ",
    );
    assert!(!result.is_ok());
    assert!(matches!(
        &result.errors[0].kind,
        ResolveErrorKind::Undefined { name } if name == "y"
    ));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_duplicate_definition() {
    let result = resolve_source(
        r"
        ---- MODULE Test ----
        VARIABLE x
        VARIABLE x
        ====
        ",
    );
    assert!(!result.is_ok());
    assert!(matches!(
        &result.errors[0].kind,
        ResolveErrorKind::Duplicate { name, .. } if name == "x"
    ));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_quantifier_scope() {
    let result = resolve_source(
        r"
        ---- MODULE Test ----
        VARIABLE S
        AllPositive == \A x \in S : x > 0
        ====
        ",
    );
    assert!(result.is_ok(), "Errors: {:?}", result.errors);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tuple_pattern_binder_scope() {
    let result = resolve_source(
        r"
        ---- MODULE Test ----
        VARIABLE moved
        Foo == \A <<pc, m>> \in moved : pc = m
        Bar == \A <<x, y>> \in moved, z \in {x} : z = x
        ====
        ",
    );
    assert!(result.is_ok(), "Errors: {:?}", result.errors);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_let_scope() {
    let result = resolve_source(
        r"
        ---- MODULE Test ----
        Double(n) == LET twice == n * 2 IN twice
        ====
        ",
    );
    assert!(result.is_ok(), "Errors: {:?}", result.errors);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_builder_scope() {
    let result = resolve_source(
        r"
        ---- MODULE Test ----
        VARIABLE S
        Squares == {x * x : x \in S}
        ====
        ",
    );
    assert!(result.is_ok(), "Errors: {:?}", result.errors);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_builtin_infix_ops_are_resolvable() {
    let result = resolve_source(
        r"
        ---- MODULE Test ----
        Init == <<1>> \o <<2>>
        Single == 1 :> 2
        Merge == (1 :> 2) @@ (3 :> 4)
        ====
        ",
    );
    assert!(result.is_ok(), "Errors: {:?}", result.errors);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_function_def_scope() {
    let result = resolve_source(
        r"
        ---- MODULE Test ----
        VARIABLE S
        SquareFunc == [x \in S |-> x * x]
        ====
        ",
    );
    assert!(result.is_ok(), "Errors: {:?}", result.errors);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lambda_scope() {
    let result = resolve_source(
        r"
        ---- MODULE Test ----
        Twice == LAMBDA x : x + x
        ====
        ",
    );
    assert!(result.is_ok(), "Errors: {:?}", result.errors);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_operator_parameters() {
    let result = resolve_source(
        r"
        ---- MODULE Test ----
        Add(a, b) == a + b
        ====
        ",
    );
    assert!(result.is_ok(), "Errors: {:?}", result.errors);
    // Check that Add is an operator with arity 2
    let add_sym = result
        .symbols
        .iter()
        .find(|s| s.name == "Add")
        .expect("Add operator must be in symbol table");
    assert_eq!(add_sym.arity, 2);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_constant_declaration() {
    let result = resolve_source(
        r"
        ---- MODULE Test ----
        CONSTANT N
        Double == N * 2
        ====
        ",
    );
    assert!(result.is_ok(), "Errors: {:?}", result.errors);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_except_at_placeholder_is_resolvable_in_update_value() {
    let result = resolve_source(
        r"
        ---- MODULE Test ----
        EXTENDS TLC
        CONSTANTS Acceptor, Value
        VARIABLE votes

        Init == votes = [a \in Acceptor |-> {}]
        Next == \E a \in Acceptor, v \in Value :
                  votes' = [votes EXCEPT ![a] = @ \cup {<<0, v>>}]
        ====
        ",
    );
    assert!(result.is_ok(), "Errors: {:?}", result.errors);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_at_is_undefined_outside_except_update_value() {
    let result = resolve_source(
        r"
        ---- MODULE Test ----
        Init == @
        ====
        ",
    );
    assert!(!result.is_ok(), "Expected semantic errors");
    assert!(matches!(
        &result.errors[0].kind,
        ResolveErrorKind::Undefined { name } if name == "@"
    ));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_nested_scopes() {
    let result = resolve_source(
        r"
        ---- MODULE Test ----
        VARIABLE S
        Nested == \A x \in S : \E y \in S : x = y
        ====
        ",
    );
    assert!(result.is_ok(), "Errors: {:?}", result.errors);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_shadowing() {
    // Inner x should shadow outer x
    let result = resolve_source(
        r"
        ---- MODULE Test ----
        VARIABLE x
        Test == \A x \in {1,2,3} : x > 0
        ====
        ",
    );
    assert!(result.is_ok(), "Errors: {:?}", result.errors);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_out_of_scope_reference() {
    // y should not be visible outside the quantifier
    let result = resolve_source(
        r"
        ---- MODULE Test ----
        VARIABLE S
        Bad == (\A x \in S : x > 0) /\ y = 1
        ====
        ",
    );
    assert!(!result.is_ok());
    assert!(matches!(
        &result.errors[0].kind,
        ResolveErrorKind::Undefined { name } if name == "y"
    ));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_recursive_decl_followed_by_definition_not_duplicate() {
    let result = resolve_source(
        r"
        ---- MODULE Test ----
        EXTENDS Integers

        RECURSIVE F(_)
        F(n) == IF n = 0 THEN 0 ELSE n + F(n - 1)

        Init == F(3) = 6
        ====
        ",
    );
    assert!(result.is_ok(), "Errors: {:?}", result.errors);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_resolve_with_extends_does_not_duplicate_recursive_decl() {
    let bits = lower_module(
        r"
        ---- MODULE Bits ----
        EXTENDS Integers

        RECURSIVE And(_, _, _, _)
        And(x, y, n, m) == IF m = 0 THEN 0 ELSE And(x, y, n + 1, m \div 2)

        x & y == And(x, y, 0, x)
        ====
        ",
    );

    let main = lower_module(
        r"
        ---- MODULE Main ----
        EXTENDS Bits
        Init == (1 & 1) = 1
        ====
        ",
    );

    let result = resolve_with_extends(&main, &[&bits]);
    assert!(result.is_ok(), "Errors: {:?}", result.errors);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_resolve_with_extends_injects_transitive_stdlib() {
    // Main EXTENDS Echo, Echo EXTENDS TLC. Main should be able to reference PrintT.
    let echo = lower_module(
        r"
        ---- MODULE Echo ----
        EXTENDS TLC
        ====
        ",
    );

    let main = lower_module(
        r#"
        ---- MODULE Main ----
        EXTENDS Echo
        Init == PrintT("hi")
        ====
        "#,
    );

    let result = resolve_with_extends(&main, &[&echo]);
    assert!(result.is_ok(), "Errors: {:?}", result.errors);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_named_assume_defines_identifier() {
    let result = resolve_source(
        r"
        ---- MODULE Test ----
        ASSUME ValueNonempty == TRUE
        Init == ValueNonempty
        ====
        ",
    );
    assert!(result.is_ok(), "Errors: {:?}", result.errors);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tlaps_assume_prove_new_binds_names_for_resolution() {
    let result = resolve_source(
        r"
        ---- MODULE Test ----
        CONSTANT S
        P(x) == x \in S

        THEOREM T == TRUE
        <1>1. ASSUME NEW x \in S,
                     P(x)
              PROVE TRUE
            OBVIOUS
        <1>. QED BY <1>1
        ====
        ",
    );
    assert!(result.is_ok(), "Errors: {:?}", result.errors);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tlaps_assume_prove_new_without_domain_binds_names_for_resolution() {
    let result = resolve_source(
        r"
        ---- MODULE Test ----
        THEOREM T == TRUE
        <1>1. ASSUME NEW x,
                     x = x
              PROVE TRUE
            OBVIOUS
        <1>. QED BY <1>1
        ====
        ",
    );
    assert!(result.is_ok(), "Errors: {:?}", result.errors);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tlaps_theorem_assume_prove_new_binds_names_for_resolution() {
    let result = resolve_source(
        r"
        ---- MODULE Test ----
        THEOREM Thm ==
            ASSUME NEW x,
                   x = x
            PROVE x = x
        ====
        ",
    );
    assert!(result.is_ok(), "Errors: {:?}", result.errors);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_resolve_with_extends_skips_stdlib_stub_if_module_loaded() {
    // If a module named like a stdlib module is actually loaded from source,
    // do not inject our synthetic stub for the same name (avoid duplicates).
    let tlaps = lower_module(
        r"
        ---- MODULE TLAPS ----
        SMT == TRUE
        SetExtensionality == TRUE
        ====
        ",
    );

    let main = lower_module(
        r"
        ---- MODULE Main ----
        EXTENDS TLAPS
        Init == SMT /\ SetExtensionality
        ====
        ",
    );

    let result = resolve_with_extends(&main, &[&tlaps]);
    assert!(result.is_ok(), "Errors: {:?}", result.errors);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_same_arity_operators_from_multiple_stdlib_modules_allowed() {
    // Both Functions and SequencesExt define Range(1) - this should not error.
    // TLC treats same-arity duplicate operators from EXTENDS as a warning, not an error.
    let result = resolve_source(
        r"
        ---- MODULE Test ----
        EXTENDS Functions, SequencesExt
        Init == Range([x \in {1} |-> x]) = {1}
        ====
        ",
    );
    assert!(result.is_ok(), "Errors: {:?}", result.errors);
}
