// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for the TLA+ parser, extracted from parser.rs for #1261 gate compliance.

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
fn test_parse_simple_module() {
    let source = r"---- MODULE Test ----
VARIABLE x
Next == x' = x + 1
====";
    let tree = parse_tree(source);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::Module), 1);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::VariableDecl), 1);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::OperatorDef), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_extends() {
    let source = r"---- MODULE Test ----
EXTENDS Naturals, Sequences
====";
    let tree = parse_tree(source);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::Module), 1);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::ExtendsClause), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_operator_def() {
    let source = r"---- MODULE Test ----
Add(a, b) == a + b
====";
    let tree = parse_tree(source);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::OperatorDef), 1);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::OperatorParam), 2);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::BinaryExpr), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_quantifier() {
    let source = r"---- MODULE Test ----
AllPositive(S) == \A x \in S : x > 0
====";
    let tree = parse_tree(source);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::OperatorDef), 1);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::QuantExpr), 1);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::BoundVar), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_set_expressions() {
    let source = r"---- MODULE Test ----
S == {1, 2, 3}
T == {x \in S : x > 1}
U == {x + 1 : x \in S}
====";
    let tree = parse_tree(source);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::OperatorDef), 3);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::SetEnumExpr), 1);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::SetFilterExpr), 1);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::SetBuilderExpr), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_function_def() {
    let source = r"---- MODULE Test ----
f == [x \in Nat |-> x * 2]
====";
    let tree = parse_tree(source);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::OperatorDef), 1);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::FuncDefExpr), 1);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::BoundVar), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_record() {
    let source = r"---- MODULE Test ----
r == [a |-> 1, b |-> 2]
====";
    let tree = parse_tree(source);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::OperatorDef), 1);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::RecordExpr), 1);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::RecordField), 2);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_if_then_else() {
    let source = r"---- MODULE Test ----
Max(a, b) == IF a > b THEN a ELSE b
====";
    let tree = parse_tree(source);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::OperatorDef), 1);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::IfExpr), 1);
    assert!(count_nodes_of_kind(&tree, SyntaxKind::BinaryExpr) >= 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_prefix_operator_def() {
    // Test parsing prefix operator definition like -. a == 0 - a
    let source = r"---- MODULE Integers ----
EXTENDS Naturals
LOCAL R == INSTANCE ProtoReals
Int  ==  R!Int
-. a == 0 - a
====";
    let tree = parse_tree(source);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::Module), 1);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::ExtendsClause), 1);
    assert!(
        count_nodes_of_kind(&tree, SyntaxKind::OperatorDef) >= 2,
        "expected at least Int and prefix operator defs"
    );
    assert!(
        count_nodes_of_kind(&tree, SyntaxKind::InstanceDecl) >= 1,
        "expected a named instance declaration for LOCAL R == INSTANCE ProtoReals"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_parenthesized_op_ref() {
    // Test parsing parenthesized operator as a value/reference
    let source = r"---- MODULE Test ----
Op == (-)
====";
    let tree = parse_tree(source);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::OperatorDef), 1);
    assert!(
        count_nodes_of_kind(&tree, SyntaxKind::OperatorRef) >= 1,
        "expected parenthesized operator reference node"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_parenthesized_infix_op() {
    // Test parsing parenthesized infix operators like B (-) C.
    // Parser doesn't produce OperatorRef for parenthesized operators yet;
    // this test verifies parsing succeeds without errors.
    let source = r"---- MODULE Test ----
Result == B (-) C
====";
    let tree = parse_tree(source);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::OperatorDef), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_parenthesized_infix_op_in_func_call() {
    // Test parsing parenthesized infix operators inside function calls.
    // Parser doesn't produce OperatorRef for parenthesized operators yet;
    // this test verifies parsing succeeds without errors.
    let source = r"---- MODULE Test ----
Result == SumBag(B (-) SetToBag({e}))
====";
    let tree = parse_tree(source);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::OperatorDef), 1);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::SetEnumExpr), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_temporal_spec() {
    // Test parsing temporal operators and fairness conditions
    let src = r"---- MODULE Test ----
VARIABLES x
vars == <<x>>
Init == x = 0
Next == x' = x + 1
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
====";
    let tree = parse_tree(src);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::VariableDecl), 1);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::OperatorDef), 4);
    assert!(
        count_nodes_of_kind(&tree, SyntaxKind::SubscriptExpr) >= 1,
        "expected [] [Next]_vars to produce a subscript expression"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_theorem_with_proof() {
    // Test parsing theorem with structured proof
    let src = r"---- MODULE Test ----
THEOREM TypeCorrect == TRUE
<1>1. Init => TypeOK
  BY DEF Init, TypeOK
<1>. QED  BY <1>1
====";
    let tree = parse_tree(src);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::TheoremStmt), 1);
    // 3 Proof nodes: 1 structured proof + 2 leaf proofs (BY clauses)
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::Proof), 3);
    assert!(
        count_nodes_of_kind(&tree, SyntaxKind::ProofStep) >= 2,
        "expected labeled step and QED step"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_lemma_with_multiple_steps() {
    // Test parsing lemma with multiple proof steps
    let src = r"---- MODULE Test ----
LEMMA TypeCorrect == Spec => []TypeOK
<1>1. Init => TypeOK
  BY DEF Init, TypeOK
<1>2. TypeOK /\ [Next]_vars => TypeOK'
  BY DEF TypeOK, Next, vars
<1>. QED  BY <1>1, <1>2, PTL DEF Spec
====";
    let tree = parse_tree(src);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::TheoremStmt), 1);
    // 4 Proof nodes: 1 structured proof + 3 leaf proofs (BY clauses)
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::Proof), 4);
    assert!(
        count_nodes_of_kind(&tree, SyntaxKind::ProofStep) >= 3,
        "expected two numbered steps and a QED step"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_number_prefixed_operator() {
    // Test parsing operators with number-prefixed names like 1aMessage, 2avMessage
    // commonly used in consensus algorithm specs (Paxos, BFT, etc.)
    let source = r#"---- MODULE Test ----
1aMessage == [type : {"1a"}, bal : Ballot]
1bMessage == [type : {"1b"}, bal : Ballot, mbal : Ballot, mval : Value]
2avMessage == [type : {"2av"}, bal : Ballot, val : Value]
1bOr2bMsgs == {m \in bmsgs : m.type \in {"1b", "2b"}}
===="#;
    let tree = parse_tree(source);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::OperatorDef), 4);
    assert!(
        count_nodes_of_kind(&tree, SyntaxKind::RecordSetExpr) >= 3,
        "expected record-set constructors for the message type operators"
    );
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::SetFilterExpr), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_proof_followed_by_number_def() {
    // Test that number-prefixed operator definitions work after a proof
    let source = r#"---- MODULE Test ----
THEOREM Foo == TRUE
<1>1. Init => TypeOK
  BY DEF Init
<1>. QED  BY <1>1

1bOr2bMsgs == {m \in bmsgs : m.type = "1b"}
===="#;
    let tree = parse_tree(source);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::TheoremStmt), 1);
    // 3 Proof nodes: 1 structured proof + 2 leaf proofs (BY clauses)
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::Proof), 3);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::OperatorDef), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_set_filter_with_tuple_pattern() {
    // Test set filter with tuple pattern: {<<x, y>> \in S : P}
    let source = r"---- MODULE Test ----
free == {<<pc, m>> \in moved : m \cap board = {}}
====";
    let tree = parse_tree(source);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::OperatorDef), 1);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::SetFilterExpr), 1);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::TuplePattern), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_proof_local_definition() {
    // Test proof-local definitions without DEFINE keyword: <1> P(x) == expr
    let source = r"---- MODULE Test ----
LEMMA L == TRUE
<1> SUFFICES TRUE
  OBVIOUS
<1> P(b) == b > 0
<1>1. \A b : P(b)
  OBVIOUS
<1>. QED BY <1>1
====";
    let tree = parse_tree(source);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::TheoremStmt), 1);
    // 4 Proof nodes: 1 structured proof + 3 leaf proofs (OBVIOUS x2, BY x1)
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::Proof), 4);
    assert!(
        count_nodes_of_kind(&tree, SyntaxKind::ProofStep) >= 4,
        "expected SUFFICES/local-def/step/QED proof structure"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_submodule() {
    // Test submodule (inner module) parsing
    let source = r"------------------------- MODULE Outer --------------------------
VARIABLE now
-----------------------------------------------------------------------------

   -------------------------- MODULE Inner ----------------------------------
   VARIABLE t
   TNext == t' = 0
  ==========================================================================

Op == INSTANCE Inner
====";
    let tree = parse_tree(source);
    assert!(
        count_nodes_of_kind(&tree, SyntaxKind::Module) >= 2,
        "expected outer and inner module nodes"
    );
    assert!(
        count_nodes_of_kind(&tree, SyntaxKind::InstanceDecl) >= 1,
        "expected instance declaration for `Op == INSTANCE Inner`"
    );
    assert!(
        count_nodes_of_kind(&tree, SyntaxKind::OperatorDef) >= 1,
        "expected at least TNext operator definition inside submodule"
    );
}

/// Regression test for #150: bullet /\ before => was incorrectly parsed.
/// The expression `/\ IF ... ELSE x => y` should be parsed as
/// `(IF ... ELSE x) => y`, not `IF ... ELSE (x => y)`.
///
/// In TLA+, a single bullet /\ is cosmetic and shouldn't affect semantics.
/// When parsing inside a bullet list, infix operators at or left of the
/// bullet column should NOT be absorbed into nested expressions like
/// IF-THEN-ELSE branches.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bullet_if_then_else_implication() {
    // This pattern appears in Lamport's auxiliary variables paper
    let source = r"---- MODULE Test ----
Test1 ==
    /\ IF TRUE THEN TRUE ELSE FALSE
    => FALSE

Test2 == (IF TRUE THEN TRUE ELSE FALSE) => FALSE
====";
    let tree = parse_tree(source);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::OperatorDef), 2);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::IfExpr), 2);
    assert!(
        count_nodes_of_kind(&tree, SyntaxKind::BinaryExpr) >= 2,
        "expected implication binary expressions for both Test1 and Test2"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_named_instance_definition_ok() {
    let source = r"---- MODULE Main ----
VARIABLE x
I == INSTANCE A WITH K <- 1
Init == x = 0
Next == x' = x
====";
    let tree = parse_tree(source);
    assert_eq!(count_nodes_of_kind(&tree, SyntaxKind::VariableDecl), 1);
    assert!(
        count_nodes_of_kind(&tree, SyntaxKind::InstanceDecl) >= 1,
        "expected named instance declaration"
    );
    assert!(
        count_nodes_of_kind(&tree, SyntaxKind::OperatorDef) >= 2,
        "expected Init and Next operator definitions"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_reject_instance_in_substitution_rhs() {
    // TLC/SANY rejects INSTANCE in general expression positions, including within WITH
    // substitutions. This spec is syntactically rejected by TLC:
    //   I == INSTANCE A WITH K <- (INSTANCE Missing)
    let source = r"---- MODULE Main ----
VARIABLE x
I == INSTANCE A WITH K <- (INSTANCE Missing)
Init == x = 0
Next == x' = x
====";
    let result = parse(source);
    assert!(!result.errors.is_empty(), "expected parse errors, got none");
    assert!(
        result.errors.iter().any(|e| e
            .message
            .contains("INSTANCE is not a valid expression here")),
        "expected an INSTANCE-in-expression error, got: {:?}",
        result.errors
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_reject_instance_in_substitution_rhs_no_parens() {
    // TLC/SANY also rejects INSTANCE in expression positions without parentheses, e.g.:
    //   I == INSTANCE A WITH K <- INSTANCE Missing
    let source = r"---- MODULE Main ----
VARIABLE x
I == INSTANCE A WITH K <- INSTANCE Missing
Init == x = 0
Next == x' = x
====";
    let result = parse(source);
    assert!(!result.errors.is_empty(), "expected parse errors, got none");
    assert!(
        result.errors.iter().any(|e| e
            .message
            .contains("INSTANCE is not a valid expression here")),
        "expected an INSTANCE-in-expression error, got: {:?}",
        result.errors
    );
}

/// Regression test for #2900: nested ASSUME/PROVE in theorem body must not leak
/// LET-defined operators as module-level OperatorDef nodes.
///
/// NaturalsInduction.tla RecursiveFcnOfNat has:
///   THEOREM RecursiveFcnOfNat ==
///     ASSUME NEW Def(_,_),
///            ASSUME NEW n \in Nat, NEW g, NEW h, ...
///            PROVE  Def(g, n) = Def(h, n)
///     PROVE  LET f[n \in Nat] == Def(f, n)
///            IN  f = [n \in Nat |-> Def(f, n)]
///
/// Before the fix, the parser failed to handle the nested ASSUME...PROVE,
/// leaving the outer PROVE's LET expression unparsed, which then got
/// interpreted as a module-level `f == ...` operator definition.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_nested_assume_prove_no_operator_leak() {
    let source = r"---- MODULE Test ----
EXTENDS Integers
THEOREM RecursiveFcnOfNat ==
  ASSUME NEW Def(_,_),
         ASSUME NEW n \in Nat, NEW g, NEW h,
                \A i \in 0..(n-1) : g[i] = h[i]
         PROVE  Def(g, n) = Def(h, n)
  PROVE  LET f[n \in Nat] == Def(f, n)
         IN  f = [n \in Nat |-> Def(f, n)]

Op(x) == x + 1
====";
    let tree = parse_tree(source);
    // Count MODULE-LEVEL OperatorDef nodes only (direct children of Module).
    // The LET inside the theorem body creates a nested OperatorDef for 'f',
    // but it must NOT appear at the module level.
    let module = tree
        .children()
        .find(|n| n.kind() == SyntaxKind::Module)
        .expect("expected Module node");
    let module_level_opdefs: Vec<_> = module
        .children()
        .filter(|n| n.kind() == SyntaxKind::OperatorDef)
        .collect();
    assert_eq!(
        module_level_opdefs.len(),
        1,
        "expected exactly 1 module-level operator (Op), but got {} — \
         nested ASSUME/PROVE LET leaked: {:?}",
        module_level_opdefs.len(),
        module_level_opdefs
            .iter()
            .map(|n| n.text().to_string().chars().take(40).collect::<String>())
            .collect::<Vec<_>>()
    );
    assert_eq!(
        count_nodes_of_kind(&tree, SyntaxKind::TheoremStmt),
        1,
        "expected exactly 1 theorem"
    );
}

// === Multi-module parsing tests ===

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_multi_module_single_module_regression() {
    let source = r"---- MODULE Test ----
VARIABLE x
Next == x' = x + 1
====";
    let result = parse_multi_module(source);
    assert!(
        result.errors.is_empty(),
        "Parse errors: {:?}",
        result.errors
    );
    assert_eq!(result.modules.len(), 1);
    assert_eq!(result.modules[0].name, "Test");
    assert_eq!(result.modules[0].syntax_node.kind(), SyntaxKind::Module);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_multi_module_two_modules_extends() {
    let source = r"---- MODULE Helper ----
HelpOp == 42
====

---- MODULE Main ----
EXTENDS Helper
UseHelper == HelpOp + 1
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

    // The last module is the "main" module
    let main = &result.modules[1];
    assert_eq!(main.syntax_node.kind(), SyntaxKind::Module);
    assert_eq!(
        count_nodes_of_kind(&main.syntax_node, SyntaxKind::ExtendsClause),
        1
    );
    assert_eq!(
        count_nodes_of_kind(&main.syntax_node, SyntaxKind::OperatorDef),
        1
    );

    // Helper module has one operator, no extends
    let helper = &result.modules[0];
    assert_eq!(
        count_nodes_of_kind(&helper.syntax_node, SyntaxKind::ExtendsClause),
        0
    );
    assert_eq!(
        count_nodes_of_kind(&helper.syntax_node, SyntaxKind::OperatorDef),
        1
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_multi_module_three_modules() {
    let source = r"---- MODULE A ----
ValA == 1
====

---- MODULE B ----
ValB == 2
====

---- MODULE C ----
EXTENDS A, B
ValC == ValA + ValB
====";
    let result = parse_multi_module(source);
    assert!(
        result.errors.is_empty(),
        "Parse errors: {:?}",
        result.errors
    );
    assert_eq!(result.modules.len(), 3);
    assert_eq!(result.modules[0].name, "A");
    assert_eq!(result.modules[1].name, "B");
    assert_eq!(result.modules[2].name, "C");

    // C extends both A and B
    let c_module = &result.modules[2];
    assert_eq!(
        count_nodes_of_kind(&c_module.syntax_node, SyntaxKind::ExtendsClause),
        1
    );
    assert_eq!(
        count_nodes_of_kind(&c_module.syntax_node, SyntaxKind::OperatorDef),
        1
    );
}
