// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Apalache parser integration tests.
//! Tests that Apalache-specific operators parse correctly as standard
//! function-call syntax (no special parser grammar needed). Part of #3760.

use super::*;

fn parse_tree(source: &str) -> SyntaxNode {
    let result = parse(source);
    assert!(
        result.errors.is_empty(),
        "Parse errors: {:?}",
        result.errors
    );
    let tree = SyntaxNode::new_root(result.green_node);
    assert_eq!(tree.kind(), SyntaxKind::Root);
    tree
}

fn count_nodes_of_kind(node: &SyntaxNode, kind: SyntaxKind) -> usize {
    let mut count = usize::from(node.kind() == kind);
    for child in node.children() {
        count += count_nodes_of_kind(&child, kind);
    }
    count
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_apa_fold_set() {
    let source = r"---- MODULE Test ----
EXTENDS Integers
Add(a, b) == a + b
Sum == ApaFoldSet(Add, 0, {1, 2, 3})
====";
    let tree = parse_tree(source);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::OperatorDef), 2);
    // ApaFoldSet(Add, 0, {1, 2, 3}) should parse as a function application
    assert!(count_nodes_of_kind(&tree, SyntaxKind::ApplyExpr) >= 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_apa_fold_seq_left() {
    let source = r"---- MODULE Test ----
EXTENDS Integers, Sequences
Cat(acc, x) == acc + x
Total == ApaFoldSeqLeft(Cat, 0, <<10, 20, 30>>)
====";
    let tree = parse_tree(source);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::OperatorDef), 2);
    assert!(count_nodes_of_kind(&tree, SyntaxKind::ApplyExpr) >= 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_variant_create() {
    let source = r#"---- MODULE Test ----
v == Variant("Some", 42)
===="#;
    let tree = parse_tree(source);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::OperatorDef), 1);
    assert!(count_nodes_of_kind(&tree, SyntaxKind::ApplyExpr) >= 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_variant_tag() {
    let source = r#"---- MODULE Test ----
tag == VariantTag([tag |-> "None", value |-> 0])
===="#;
    let tree = parse_tree(source);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::OperatorDef), 1);
    assert!(count_nodes_of_kind(&tree, SyntaxKind::ApplyExpr) >= 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_variant_get_or_else() {
    let source = r#"---- MODULE Test ----
val == VariantGetOrElse("Some", v, 0)
===="#;
    let tree = parse_tree(source);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::OperatorDef), 1);
    assert!(count_nodes_of_kind(&tree, SyntaxKind::ApplyExpr) >= 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_variant_filter() {
    let source = r#"---- MODULE Test ----
filtered == VariantFilter("Ok", S)
===="#;
    let tree = parse_tree(source);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::OperatorDef), 1);
    assert!(count_nodes_of_kind(&tree, SyntaxKind::ApplyExpr) >= 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_gen_and_guess() {
    let source = r"---- MODULE Test ----
g == Gen(3)
choice == Guess({1, 2, 3})
====";
    let tree = parse_tree(source);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::OperatorDef), 2);
    assert!(count_nodes_of_kind(&tree, SyntaxKind::ApplyExpr) >= 2);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_mkseq_and_repeat() {
    let source = r"---- MODULE Test ----
EXTENDS Integers
Double(i) == i * 2
F(x, i) == x + i
seq == MkSeq(3, Double)
rep == Repeat(F, 5, 0)
====";
    let tree = parse_tree(source);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::OperatorDef), 4);
    assert!(count_nodes_of_kind(&tree, SyntaxKind::ApplyExpr) >= 2);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_colon_eq_assignment() {
    // Apalache uses := for assignment annotations
    let source = r"---- MODULE Test ----
EXTENDS Integers
VARIABLE x
Next == x' := 1
====";
    let tree = parse_tree(source);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::OperatorDef), 1);
    // := should parse as a binary expression (x' := 1)
    assert!(count_nodes_of_kind(&tree, SyntaxKind::BinaryExpr) >= 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_skolem_expand_const_cardinality() {
    let source = r"---- MODULE Test ----
EXTENDS FiniteSets
a == Skolem(\E x \in {1, 2}: x > 0)
b == Expand(SUBSET {1, 2})
c == ConstCardinality(Cardinality({1, 2}) = 2)
====";
    let tree = parse_tree(source);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::OperatorDef), 3);
    assert!(count_nodes_of_kind(&tree, SyntaxKind::ApplyExpr) >= 3);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_set_as_fun() {
    let source = r#"---- MODULE Test ----
f == SetAsFun({<<1, "a">>, <<2, "b">>})
===="#;
    let tree = parse_tree(source);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::OperatorDef), 1);
    assert!(count_nodes_of_kind(&tree, SyntaxKind::ApplyExpr) >= 1);
}

// === Multi-module and EXTENDS edge cases ===

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_recursive_with_arity() {
    // RECURSIVE g(_) -- forward declaration with arity
    let source = r"---- MODULE Test ----
EXTENDS Naturals
RECURSIVE g(_)
f(a) == IF a = 0 THEN 1 ELSE a * g(a-1)
g(a) == f(a)
====";
    let tree = parse_tree(source);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::RecursiveDecl), 1);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::OperatorDef), 2);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_recursive_without_arity() {
    // RECURSIVE fact -- no arity marker (used for recursive functions)
    let source = r"---- MODULE Test ----
EXTENDS Naturals
RECURSIVE fact
fact[n \in Nat] == IF n = 0 THEN 1 ELSE n * fact[n-1]
====";
    let tree = parse_tree(source);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::RecursiveDecl), 1);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::OperatorDef), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_multiple_recursive_decls() {
    // Multiple RECURSIVE declarations in one module
    let source = r"---- MODULE Test ----
EXTENDS Naturals
RECURSIVE g(_)
RECURSIVE fact
g(a) == IF a = 0 THEN 1 ELSE a * g(a-1)
fact[n \in Nat] == IF n = 0 THEN 1 ELSE n * fact[n-1]
====";
    let tree = parse_tree(source);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::RecursiveDecl), 2);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::OperatorDef), 2);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_keyword_as_record_field() {
    // Keywords should be usable as record field names (per TLC test208)
    let source = r"---- MODULE Test ----
bar == 17
Foo == bar.RECURSIVE
====";
    let tree = parse_tree(source);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::OperatorDef), 2);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::RecordAccessExpr), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_keyword_fields_except() {
    // Keywords as field names in EXCEPT specs (per TLC test208)
    let source = r"---- MODULE Test ----
bar == 17
Foo == [bar EXCEPT !.RECURSIVE = 0]
====";
    let tree = parse_tree(source);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::OperatorDef), 2);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::ExceptExpr), 1);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::ExceptSpec), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_multiple_keyword_fields() {
    // Multiple keyword-named fields accessed and EXCEPT'd
    let source = r"---- MODULE Test ----
bar == 17
Foo ==
  /\ bar.NEW
  /\ bar.BY
  /\ bar.LAMBDA
  /\ bar.THEN
  /\ [bar EXCEPT !.NEW = 0]
  /\ [bar EXCEPT !.LAMBDA = 0]
====";
    let tree = parse_tree(source);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::OperatorDef), 2);
    assert!(
        count_nodes_of_kind(&tree, SyntaxKind::RecordAccessExpr) >= 4,
        "expected at least 4 record access nodes for keyword fields"
    );
    assert!(
        count_nodes_of_kind(&tree, SyntaxKind::ExceptExpr) >= 2,
        "expected at least 2 EXCEPT expressions"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_named_instance_with_params() {
    // Named INSTANCE with parameter substitution (test203 pattern)
    let source = r"---- MODULE Test ----
EXTENDS Naturals
RECURSIVE g(_)
foo(n) == INSTANCE TestHelper WITH A <- g, b <- n
g(n) == IF n = 0 THEN 1 ELSE n * foo(n-1)!h
====";
    let tree = parse_tree(source);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::RecursiveDecl), 1);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::OperatorDef), 2);
    assert!(
        count_nodes_of_kind(&tree, SyntaxKind::InstanceDecl) >= 1,
        "expected INSTANCE declaration in operator RHS"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_parameterized_instance() {
    // Parameterized INSTANCE: I(a) == INSTANCE Mod WITH y <- a (test212 pattern)
    let source = r"---- MODULE Test ----
VARIABLE x
I(a) == INSTANCE TestMod WITH y <- a
L == INSTANCE TestMod WITH y <- x
====";
    let tree = parse_tree(source);
    assert_eq!(
        count_nodes_of_kind(&tree, SyntaxKind::InstanceDecl),
        2,
        "expected 2 INSTANCE declarations"
    );
    assert_eq!(
        count_nodes_of_kind(&tree, SyntaxKind::OperatorDef),
        2,
        "expected 2 operator definitions wrapping INSTANCE"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_instance_with_lambda_substitution() {
    // INSTANCE with LAMBDA in substitution (test201 pattern)
    let source = r"---- MODULE Test ----
EXTENDS Naturals
foo == INSTANCE TestHelper WITH A <- LAMBDA y : y^3, b <- 4
====";
    let tree = parse_tree(source);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::InstanceDecl), 1);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::LambdaExpr), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_constant_with_operator_arity() {
    // CONSTANT with operator arity: CONSTANT Op(_), Op2(_,_)
    let source = r"---- MODULE Test ----
CONSTANT Op(_), Op2(_, _)
====";
    let tree = parse_tree(source);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::ConstantDecl), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_extends_multiple_modules() {
    // EXTENDS with many modules (common Apalache pattern)
    let source = r"---- MODULE Test ----
EXTENDS Naturals, Sequences, FiniteSets, TLC, Integers
VARIABLE x
Init == x = 0
====";
    let tree = parse_tree(source);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::ExtendsClause), 1);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::OperatorDef), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_multi_module_instance_pattern() {
    // Multi-module file where later module INSTANCE first module
    let source = r"---- MODULE Helper ----
CONSTANT A(_), b
def == A(b)
====

---- MODULE Main ----
EXTENDS Naturals
foo == INSTANCE Helper WITH A <- LAMBDA y : y + 1, b <- 4
====";
    let result = parse_multi_module(source);
    assert!(
        result.errors.is_empty(),
        "Parse errors: {:?}",
        result.errors
    );
    assert_eq!(result.modules.len(), 2);
    assert_eq!(result.modules[0].name, "Helper");
    assert_eq!(result.modules[1].name, "Main");
    assert_eq!(
        count_nodes_of_kind(&result.modules[0].syntax_node, SyntaxKind::ConstantDecl),
        1
    );
    assert!(count_nodes_of_kind(&result.modules[1].syntax_node, SyntaxKind::InstanceDecl) >= 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_recursive_comma_separated() {
    // RECURSIVE with comma-separated declarations
    let source = r"---- MODULE Test ----
EXTENDS Naturals
RECURSIVE f(_), g(_)
f(n) == IF n = 0 THEN 1 ELSE g(n-1)
g(n) == IF n = 0 THEN 1 ELSE n * f(n-1)
====";
    let tree = parse_tree(source);
    // Comma-separated RECURSIVE produces a single RecursiveDecl node
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::RecursiveDecl), 1);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::OperatorDef), 2);
}

// === RECURSIVE edge cases (Part of #3761) ===

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_recursive_higher_arity() {
    // RECURSIVE with 3-parameter operator
    let source = r"---- MODULE Test ----
EXTENDS Naturals
RECURSIVE Ack(_, _, _)
Ack(m, n, k) == IF m = 0 THEN n + k ELSE Ack(m - 1, n, k)
====";
    let tree = parse_tree(source);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::RecursiveDecl), 1);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::OperatorDef), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_recursive_in_let_in() {
    // RECURSIVE inside a LET/IN block
    let source = r"---- MODULE Test ----
EXTENDS Naturals
Result ==
  LET RECURSIVE fact(_)
      fact(n) == IF n = 0 THEN 1 ELSE n * fact(n - 1)
  IN fact(5)
====";
    let tree = parse_tree(source);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::LetExpr), 1);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::RecursiveDecl), 1);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::OperatorDef), 2);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_recursive_multiple_in_let() {
    // Multiple RECURSIVE declarations inside LET/IN
    let source = r"---- MODULE Test ----
EXTENDS Naturals
Result ==
  LET RECURSIVE even(_)
      RECURSIVE odd(_)
      even(n) == IF n = 0 THEN TRUE ELSE odd(n - 1)
      odd(n) == IF n = 0 THEN FALSE ELSE even(n - 1)
  IN even(4)
====";
    let tree = parse_tree(source);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::LetExpr), 1);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::RecursiveDecl), 2);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_recursive_no_blank_line_before_def() {
    // RECURSIVE followed immediately by definition (no blank line)
    let source = r"---- MODULE Test ----
EXTENDS Naturals
RECURSIVE f(_)
f(n) == IF n = 0 THEN 1 ELSE n * f(n - 1)
====";
    let tree = parse_tree(source);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::RecursiveDecl), 1);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::OperatorDef), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_recursive_mixed_arity_comma_separated() {
    // RECURSIVE with mixed arities: zero-arity and multi-arity
    let source = r"---- MODULE Test ----
EXTENDS Naturals
RECURSIVE val, f(_), g(_, _)
val == 0
f(n) == IF n = 0 THEN val ELSE g(n, f(n - 1))
g(a, b) == a + b
====";
    let tree = parse_tree(source);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::RecursiveDecl), 1);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::OperatorDef), 3);
}

// === Fold operator edge cases (Part of #3761) ===

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_apa_fold_set_with_lambda() {
    // ApaFoldSet with LAMBDA as the operator argument
    let source = r"---- MODULE Test ----
EXTENDS Integers
Sum == ApaFoldSet(LAMBDA a, b: a + b, 0, {1, 2, 3})
====";
    let tree = parse_tree(source);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::OperatorDef), 1);
    assert!(count_nodes_of_kind(&tree, SyntaxKind::ApplyExpr) >= 1);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::LambdaExpr), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_apa_fold_seq_left_with_lambda() {
    // ApaFoldSeqLeft with LAMBDA as the operator argument
    let source = r"---- MODULE Test ----
EXTENDS Integers, Sequences
Total == ApaFoldSeqLeft(LAMBDA acc, x: acc + x, 0, <<10, 20, 30>>)
====";
    let tree = parse_tree(source);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::OperatorDef), 1);
    assert!(count_nodes_of_kind(&tree, SyntaxKind::ApplyExpr) >= 1);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::LambdaExpr), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_nested_fold_calls() {
    // Nested fold calls: fold inside fold
    let source = r"---- MODULE Test ----
EXTENDS Integers
Add(a, b) == a + b
Mul(a, b) == a * b
Result == ApaFoldSet(Add, 0, {ApaFoldSet(Mul, 1, {2, 3}), 4, 5})
====";
    let tree = parse_tree(source);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::OperatorDef), 3);
    // At least 2 ApaFoldSet calls (outer + inner) plus Add and Mul calls
    assert!(
        count_nodes_of_kind(&tree, SyntaxKind::ApplyExpr) >= 2,
        "expected at least 2 function applications for nested folds"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_fold_set_community_module() {
    // FoldSet from FiniteSetsExt community module
    let source = r"---- MODULE Test ----
EXTENDS Integers, FiniteSets
Add(a, b) == a + b
Sum == FoldSet(Add, 0, {1, 2, 3})
====";
    let tree = parse_tree(source);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::OperatorDef), 2);
    assert!(count_nodes_of_kind(&tree, SyntaxKind::ApplyExpr) >= 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_fold_seq_community_module() {
    // FoldSeq from SequencesExt community module
    let source = r"---- MODULE Test ----
EXTENDS Integers, Sequences
Add(a, b) == a + b
Total == FoldSeq(Add, 0, <<1, 2, 3>>)
====";
    let tree = parse_tree(source);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::OperatorDef), 2);
    assert!(count_nodes_of_kind(&tree, SyntaxKind::ApplyExpr) >= 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_apa_fold_set_empty_set() {
    // ApaFoldSet with empty set should parse correctly
    let source = r"---- MODULE Test ----
EXTENDS Integers
Add(a, b) == a + b
Result == ApaFoldSet(Add, 42, {})
====";
    let tree = parse_tree(source);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::OperatorDef), 2);
    assert!(count_nodes_of_kind(&tree, SyntaxKind::ApplyExpr) >= 1);
    assert!(count_nodes_of_kind(&tree, SyntaxKind::SetEnumExpr) >= 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_apa_fold_seq_left_empty_seq() {
    // ApaFoldSeqLeft with empty sequence
    let source = r"---- MODULE Test ----
EXTENDS Integers, Sequences
Add(a, b) == a + b
Result == ApaFoldSeqLeft(Add, 99, <<>>)
====";
    let tree = parse_tree(source);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::OperatorDef), 2);
    assert!(count_nodes_of_kind(&tree, SyntaxKind::ApplyExpr) >= 1);
    assert!(count_nodes_of_kind(&tree, SyntaxKind::TupleExpr) >= 1);
}

// === Multi-module file edge cases (Part of #3761) ===

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_multi_module_text_before_first_module() {
    // Text/comments before the first module header (SANY ignores this)
    let source = r"This is some documentation text.
It appears before the module.

---- MODULE Test ----
VARIABLE x
Init == x = 0
====";
    let result = parse_multi_module(source);
    assert!(
        result.errors.is_empty(),
        "Parse errors: {:?}",
        result.errors
    );
    assert_eq!(result.modules.len(), 1);
    assert_eq!(result.modules[0].name, "Test");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_multi_module_text_after_last_module() {
    // Trailing text after the last module end (SANY ignores this)
    let source = r"---- MODULE Test ----
VARIABLE x
Init == x = 0
====

This is trailing text that should be ignored.
Maybe some shell commands or notes here.";
    let result = parse_multi_module(source);
    assert!(
        result.errors.is_empty(),
        "Parse errors: {:?}",
        result.errors
    );
    assert_eq!(result.modules.len(), 1);
    assert_eq!(result.modules[0].name, "Test");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_multi_module_text_between_modules() {
    // Text between two module blocks
    let source = r"---- MODULE A ----
ValA == 1
====

Some text between modules.

---- MODULE B ----
ValB == 2
====";
    let result = parse_multi_module(source);
    assert!(
        result.errors.is_empty(),
        "Parse errors: {:?}",
        result.errors
    );
    assert_eq!(result.modules.len(), 2);
    assert_eq!(result.modules[0].name, "A");
    assert_eq!(result.modules[1].name, "B");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_multi_module_empty_body() {
    // Module with no declarations (empty body)
    let source = r"---- MODULE Empty ----
====";
    let result = parse_multi_module(source);
    assert!(
        result.errors.is_empty(),
        "Parse errors: {:?}",
        result.errors
    );
    assert_eq!(result.modules.len(), 1);
    assert_eq!(result.modules[0].name, "Empty");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_multi_module_four_modules() {
    // Stress test: 4 modules in one file
    let source = r"---- MODULE Types ----
TypeOK == TRUE
====

---- MODULE Helpers ----
EXTENDS Naturals
Max(a, b) == IF a > b THEN a ELSE b
====

---- MODULE Spec ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = x + 1
====

---- MODULE Main ----
EXTENDS Naturals
VARIABLE y
Init == y = 0
Next == y' = y + 1
====";
    let result = parse_multi_module(source);
    assert!(
        result.errors.is_empty(),
        "Parse errors: {:?}",
        result.errors
    );
    assert_eq!(result.modules.len(), 4);
    assert_eq!(result.modules[0].name, "Types");
    assert_eq!(result.modules[1].name, "Helpers");
    assert_eq!(result.modules[2].name, "Spec");
    assert_eq!(result.modules[3].name, "Main");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_multi_module_with_recursive_in_inner() {
    // Multi-module file where an inner module uses RECURSIVE
    let source = r"---- MODULE MathHelpers ----
EXTENDS Naturals
RECURSIVE fact(_)
fact(n) == IF n = 0 THEN 1 ELSE n * fact(n - 1)
====

---- MODULE Main ----
EXTENDS Naturals
VARIABLE x
Init == x = 1
Next == x' = x + 1
====";
    let result = parse_multi_module(source);
    assert!(
        result.errors.is_empty(),
        "Parse errors: {:?}",
        result.errors
    );
    assert_eq!(result.modules.len(), 2);
    assert_eq!(result.modules[0].name, "MathHelpers");
    assert_eq!(result.modules[1].name, "Main");
    assert_eq!(
        count_nodes_of_kind(&result.modules[0].syntax_node, SyntaxKind::RecursiveDecl),
        1
    );
    assert_eq!(
        count_nodes_of_kind(&result.modules[0].syntax_node, SyntaxKind::OperatorDef),
        1
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_multi_module_extends_only_body() {
    // Module with only EXTENDS and no other declarations
    let source = r"---- MODULE Base ----
EXTENDS Naturals
====

---- MODULE Main ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
====";
    let result = parse_multi_module(source);
    assert!(
        result.errors.is_empty(),
        "Parse errors: {:?}",
        result.errors
    );
    assert_eq!(result.modules.len(), 2);
    assert_eq!(result.modules[0].name, "Base");
    assert_eq!(result.modules[1].name, "Main");
    assert_eq!(
        count_nodes_of_kind(&result.modules[0].syntax_node, SyntaxKind::ExtendsClause),
        1
    );
    assert_eq!(
        count_nodes_of_kind(&result.modules[0].syntax_node, SyntaxKind::OperatorDef),
        0
    );
}

// === Combined edge cases (Part of #3761) ===

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_recursive_with_fold_pattern() {
    // Common Apalache pattern: RECURSIVE + fold in same module
    let source = r"---- MODULE Test ----
EXTENDS Integers
RECURSIVE SumSet(_, _)
SumSet(acc, S) ==
  IF S = {} THEN acc
  ELSE LET x == CHOOSE x \in S : TRUE
       IN SumSet(acc + x, S \ {x})
Alt == ApaFoldSet(LAMBDA a, b: a + b, 0, {1, 2, 3})
====";
    let tree = parse_tree(source);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::RecursiveDecl), 1);
    // 3 OperatorDefs: SumSet, x (inside LET), Alt
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::OperatorDef), 3);
    assert!(count_nodes_of_kind(&tree, SyntaxKind::ApplyExpr) >= 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_multi_module_with_fold_and_recursive() {
    // Multi-module file with fold operators and RECURSIVE across modules
    let source = r"---- MODULE Helpers ----
EXTENDS Integers
RECURSIVE Sum(_, _)
Sum(acc, S) ==
  IF S = {} THEN acc
  ELSE LET x == CHOOSE x \in S : TRUE
       IN Sum(acc + x, S \ {x})
====

---- MODULE Main ----
EXTENDS Integers
Add(a, b) == a + b
Total == ApaFoldSet(Add, 0, {1, 2, 3})
====";
    let result = parse_multi_module(source);
    assert!(
        result.errors.is_empty(),
        "Parse errors: {:?}",
        result.errors
    );
    assert_eq!(result.modules.len(), 2);
    assert_eq!(result.modules[0].name, "Helpers");
    assert_eq!(result.modules[1].name, "Main");
    // Helpers has RECURSIVE
    assert_eq!(
        count_nodes_of_kind(&result.modules[0].syntax_node, SyntaxKind::RecursiveDecl),
        1
    );
    // Main has fold call
    assert!(count_nodes_of_kind(&result.modules[1].syntax_node, SyntaxKind::ApplyExpr) >= 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_recursive_function_with_set_arg() {
    // RECURSIVE function definition (f[x \in S]) with set domain
    let source = r"---- MODULE Test ----
EXTENDS Naturals
RECURSIVE size(_)
size[S \in SUBSET {1, 2, 3}] ==
  IF S = {} THEN 0 ELSE 1
====";
    let tree = parse_tree(source);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::RecursiveDecl), 1);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::OperatorDef), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_map_then_fold_set() {
    // MapThenFoldSet from community Folds module
    let source = r"---- MODULE Test ----
EXTENDS Integers
Add(a, b) == a + b
Double(x) == x * 2
ChooseF(S) == CHOOSE x \in S : TRUE
Result == MapThenFoldSet(Add, 0, Double, ChooseF, {1, 2, 3})
====";
    let tree = parse_tree(source);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::OperatorDef), 4);
    assert!(count_nodes_of_kind(&tree, SyntaxKind::ApplyExpr) >= 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_apa_fold_with_record_base() {
    // ApaFoldSet with a record as the base value
    let source = r#"---- MODULE Test ----
EXTENDS Integers
Merge(acc, x) == [acc EXCEPT !.sum = @ + x, !.count = @ + 1]
Result == ApaFoldSet(Merge, [sum |-> 0, count |-> 0], {10, 20, 30})
===="#;
    let tree = parse_tree(source);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::OperatorDef), 2);
    assert!(count_nodes_of_kind(&tree, SyntaxKind::ApplyExpr) >= 1);
}

// === Gap 13: Parser edge cases for Apalache compatibility (#3761) ===

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_except_double_eq() {
    // SANY rejects == in EXCEPT but Apalache accepts it.
    // TLA2 should accept both = and == in EXCEPT specs.
    let source = r#"---- MODULE Test ----
EXTENDS Integers
Update(counters, e) == [ counters EXCEPT ![e] == counters[e] + 1 ]
===="#;
    let tree = parse_tree(source);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::OperatorDef), 1);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::ExceptExpr), 1);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::ExceptSpec), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_except_mixed_eq_styles() {
    // Mix of = and == in EXCEPT specs within the same expression
    let source = r#"---- MODULE Test ----
EXTENDS Integers
Update(r) == [ r EXCEPT ![1] = 10, ![2] == 20 ]
===="#;
    let tree = parse_tree(source);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::ExceptSpec), 2);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_lt_colon_operator_def() {
    // Apalache <: type annotation operator definition
    let source = r"---- MODULE Test ----
a <: b == a
====";
    let tree = parse_tree(source);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::OperatorDef), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_lt_colon_infix_usage() {
    // Apalache <: type annotation operator used in expressions
    let source = r"---- MODULE Test ----
a <: b == a
Init == {} <: {Int}
====";
    let tree = parse_tree(source);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::OperatorDef), 2);
    // The <: should produce a BinaryExpr
    assert!(count_nodes_of_kind(&tree, SyntaxKind::BinaryExpr) >= 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_let_without_in() {
    // Apalache extension: LET without IN
    let source = r"---- MODULE Test ----
Range(seq) == LET AddToSet(S, e) == S \union {e}
              IN LET Range == AddToSet({}, seq)
====";
    let tree = parse_tree(source);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::OperatorDef), 3);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::LetExpr), 2);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_apalache_recursion_spec() {
    // Full Recursion.tla pattern: <: operator and standard TLA+
    let source = r"---- MODULE Test ----
EXTENDS Integers
VARIABLES Set, size
a <: b == a
Card(S) ==
  LET fun ==
    CHOOSE f \in [SUBSET S -> Int]:
      \A T \in SUBSET S:
        IF T = ({} <: {Int})
        THEN f[T] = 0
        ELSE \E t \in T:
              f[T] = 1 + f[T \ {t}]
  IN
  fun[S]
Init ==
    /\ Set = {} <: {Int}
    /\ size = 0
====";
    let tree = parse_tree(source);
    // a <: b, Card, Init = 3 operator defs + fun inside LET = 4
    assert!(count_nodes_of_kind(&tree, SyntaxKind::OperatorDef) >= 3);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_fold_defined_pattern() {
    // Pattern from FoldDefined.tla: EXCEPT with == and LET without IN
    let source = r#"---- MODULE Test ----
EXTENDS Integers
Mode(seq, elIfEmpty) ==
    LET ExtRange == {1, 2, 3}
    IN LET CountElem(countersAndCurrentMode, e) ==
         LET counters == countersAndCurrentMode
         IN LET newCounters == [ counters EXCEPT ![e] == counters + 1 ]
            IN newCounters
       IN CountElem(ExtRange, elIfEmpty)
===="#;
    let tree = parse_tree(source);
    assert!(count_nodes_of_kind(&tree, SyntaxKind::ExceptExpr) >= 1);
    assert!(count_nodes_of_kind(&tree, SyntaxKind::LetExpr) >= 2);
}
