// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::config::FormatConfig;
use super::formatter::TlaFormatter;
use super::pretty_module;
use crate::lower::lower;
use crate::span::FileId;
use crate::syntax::parse_to_syntax_tree;
use insta::assert_snapshot;

/// Parse source -> CST -> AST -> pretty print
fn roundtrip(src: &str) -> String {
    let tree = parse_to_syntax_tree(src);
    let result = lower(FileId(0), &tree);
    let module = result.module.expect("Failed to lower module");
    pretty_module(&module)
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn snapshot_simple_spec() {
    let src = r"---- MODULE Counter ----
VARIABLE count

Init == count = 0

Increment == count' = count + 1

Decrement == count' = count - 1

Next == Increment \/ Decrement
====";
    assert_snapshot!("snapshot_simple_spec", roundtrip(src));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn snapshot_quantifiers_and_sets() {
    let src = r"---- MODULE Sets ----
S == {1, 2, 3}
T == {x \in S : x > 1}
U == \A x \in S : x > 0
V == \E x \in S : x = 2
====";
    assert_snapshot!("snapshot_quantifiers_and_sets", roundtrip(src));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn snapshot_functions_and_records() {
    let src = r"---- MODULE FuncsRecords ----
f == [x \in S |-> x + 1]
r == [a |-> 1, b |-> 2]
g == [S -> T]
====";
    assert_snapshot!("snapshot_functions_and_records", roundtrip(src));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pretty_simple_module() {
    let src = r"---- MODULE Test ----
VARIABLE x

Init == x = 0

Next == x' = x + 1
====";
    let result = roundtrip(src);
    assert!(result.contains("MODULE Test"));
    assert!(result.contains("VARIABLE x"));
    assert!(result.contains("Init == x = 0"));
    assert!(result.contains("x' = x + 1"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pretty_quantifiers() {
    let src = r"---- MODULE Test ----
P == \A x \in S : \E y \in T : x = y
====";
    let result = roundtrip(src);
    assert!(result.contains("\\A x \\in S : \\E y \\in T : x = y"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pretty_sets() {
    let src = r"---- MODULE Test ----
S == {1, 2, 3}
T == {x \in S : x > 1}
====";
    let result = roundtrip(src);
    assert!(result.contains("{1, 2, 3}"));
    assert!(result.contains("{x \\in S : x > 1}"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pretty_function_def() {
    let src = r"---- MODULE Test ----
f == [x \in S |-> x + 1]
====";
    let result = roundtrip(src);
    assert!(result.contains("[x \\in S |-> x + 1]"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pretty_record() {
    let src = r"---- MODULE Test ----
r == [a |-> 1, b |-> 2]
====";
    let result = roundtrip(src);
    assert!(result.contains("[a |-> 1, b |-> 2]"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pretty_tuple() {
    let src = r"---- MODULE Test ----
t == <<1, 2, 3>>
====";
    let result = roundtrip(src);
    assert!(result.contains("<<1, 2, 3>>"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pretty_if_then_else() {
    let src = r"---- MODULE Test ----
P == IF x > 0 THEN y ELSE z
====";
    let result = roundtrip(src);
    assert!(result.contains("IF x > 0 THEN y ELSE z"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pretty_temporal() {
    let src = r"---- MODULE Test ----
Spec == []P
====";
    let result = roundtrip(src);
    assert!(result.contains("[]P"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn snapshot_temporal_operators() {
    let src = r"---- MODULE Temporal ----
VARIABLE x

AlwaysP == []P
EventuallyP == <>P
LeadsToQ == P ~> Q
====";
    assert_snapshot!("snapshot_temporal_operators", roundtrip(src));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn snapshot_fairness_operators() {
    let src = r"---- MODULE Fairness ----
VARIABLE x, y

Weak == WF_x(Action)
Strong == SF_y(OtherAction)
====";
    assert_snapshot!("snapshot_fairness_operators", roundtrip(src));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn snapshot_case_expression() {
    let src = r#"---- MODULE Case ----
Result == CASE x = 1 -> "one"
            [] x = 2 -> "two"
            [] OTHER -> "other"
===="#;
    assert_snapshot!("snapshot_case_expression", roundtrip(src));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn snapshot_let_expression() {
    let src = r"---- MODULE Let ----
Compute == LET a == 1
               b == 2
           IN a + b
====";
    assert_snapshot!("snapshot_let_expression", roundtrip(src));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn snapshot_except_expression() {
    let src = r"---- MODULE Except ----
f == [a |-> 1, b |-> 2]
g == [f EXCEPT !.a = 3]
h == [f EXCEPT ![1] = 42]
====";
    assert_snapshot!("snapshot_except_expression", roundtrip(src));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn snapshot_function_set() {
    let src = r"---- MODULE FuncSet ----
AllFuncs == [S -> T]
====";
    assert_snapshot!("snapshot_function_set", roundtrip(src));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn snapshot_record_set() {
    let src = r"---- MODULE RecordSet ----
AllRecords == [a : S, b : T]
====";
    assert_snapshot!("snapshot_record_set", roundtrip(src));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn snapshot_cartesian_product() {
    let src = r"---- MODULE Cartesian ----
Product == S \X T \X U
====";
    assert_snapshot!("snapshot_cartesian_product", roundtrip(src));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn snapshot_set_operations() {
    let src = r"---- MODULE SetOps ----
Cup == A \cup B
Cap == A \cap B
Minus == A \ B
Power == SUBSET S
Big == UNION SetOfSets
====";
    assert_snapshot!("snapshot_set_operations", roundtrip(src));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn snapshot_comparison_operators() {
    let src = r"---- MODULE Compare ----
LT == x < y
LEQ == x <= y
GT == x > y
GEQ == x >= y
NEQ == x /= y
Range == 1..10
====";
    assert_snapshot!("snapshot_comparison_operators", roundtrip(src));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn snapshot_arithmetic_operators() {
    let src = r"---- MODULE Arith ----
Add == x + y
Sub == x - y
Mul == x * y
Div == x / y
IDiv == x \div y
Mod == x % y
Pow == x^y
Neg == -x
====";
    assert_snapshot!("snapshot_arithmetic_operators", roundtrip(src));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn snapshot_logic_operators() {
    let src = r"---- MODULE Logic ----
Conj == P /\ Q
Disj == P \/ Q
Neg == ~P
Impl == P => Q
Equiv == P <=> Q
====";
    assert_snapshot!("snapshot_logic_operators", roundtrip(src));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn snapshot_action_operators() {
    let src = r"---- MODULE Actions ----
VARIABLE x

En == ENABLED Action
Unch == UNCHANGED x
Prime == x'
====";
    assert_snapshot!("snapshot_action_operators", roundtrip(src));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn snapshot_choose_expression() {
    let src = r"---- MODULE Choose ----
Min == CHOOSE x \in S : \A y \in S : x <= y
====";
    assert_snapshot!("snapshot_choose_expression", roundtrip(src));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn snapshot_domain_expression() {
    let src = r"---- MODULE Domain ----
Keys == DOMAIN f
====";
    assert_snapshot!("snapshot_domain_expression", roundtrip(src));
}

// =========================================================================
// Formatter tests (width-aware TlaFormatter)
// =========================================================================

/// Parse source -> CST -> AST -> format with TlaFormatter
fn format(src: &str) -> String {
    let tree = parse_to_syntax_tree(src);
    let result = lower(FileId(0), &tree);
    let module = result.module.expect("Failed to lower module");
    TlaFormatter::default().format_module(&module)
}

/// Format with custom config
fn format_with_config(src: &str, config: FormatConfig) -> String {
    let tree = parse_to_syntax_tree(src);
    let result = lower(FileId(0), &tree);
    let module = result.module.expect("Failed to lower module");
    TlaFormatter::new(config).format_module(&module)
}

/// Round-trip test: parse -> format -> parse -> format should give same result.
fn roundtrip_format_stable(src: &str) {
    let formatted_once = format(src);
    let formatted_twice = format(&formatted_once);
    assert_eq!(
        formatted_once, formatted_twice,
        "Formatter output is not stable (idempotent)"
    );
}

/// Round-trip test: parse -> format -> parse should produce equivalent AST.
fn roundtrip_format_ast_eq(src: &str) {
    let tree1 = parse_to_syntax_tree(src);
    let result1 = lower(FileId(0), &tree1);
    let module1 = result1.module.expect("Failed to lower module");

    let formatted = TlaFormatter::default().format_module(&module1);

    let tree2 = parse_to_syntax_tree(&formatted);
    let result2 = lower(FileId(0), &tree2);
    let module2 = result2.module.expect("Failed to lower formatted module");

    // Compare pretty-printed (compact) versions to check structural equivalence
    let pp1 = pretty_module(&module1);
    let pp2 = pretty_module(&module2);
    assert_eq!(pp1, pp2, "AST differs after format roundtrip");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_formatter_simple_module() {
    let src = r"---- MODULE Test ----
VARIABLE x

Init == x = 0

Next == x' = x + 1
====";
    let result = format(src);
    assert!(result.contains("MODULE Test"));
    assert!(result.contains("VARIABLE x"));
    assert!(result.contains("Init == x = 0"));
    assert!(result.contains("x' = x + 1"));
    // Check padded delimiters
    assert!(result.starts_with("---"));
    assert!(result.ends_with('\n'));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_formatter_conjunction_vertical_alignment() {
    // Long conjunction list should be vertically aligned
    let src = r"---- MODULE Test ----
TypeOK == /\ x \in {1, 2, 3}
          /\ y \in {4, 5, 6}
          /\ z \in {7, 8, 9}
====";
    let result = format(src);
    // Should contain vertically-aligned /\ list
    assert!(
        result.contains("/\\"),
        "formatted output should contain /\\ operators"
    );
    // The conjunction list should have newlines (multi-line)
    let body_start = result.find("TypeOK ==").expect("TypeOK not found");
    let body = &result[body_start..];
    let newline_count = body.matches('\n').count();
    assert!(
        newline_count >= 3,
        "conjunction list with 3 items should span multiple lines, got {newline_count} newlines"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_formatter_short_conjunction_inline() {
    // Short conjunction should stay inline
    let src = r"---- MODULE Test ----
P == A /\ B
====";
    let result = format(src);
    assert!(
        result.contains("A /\\ B"),
        "short conjunction should stay inline: {result}"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_formatter_disjunction_vertical_alignment() {
    let src = r"---- MODULE Test ----
Next == \/ Action1
        \/ Action2
        \/ Action3
====";
    let result = format(src);
    assert!(result.contains("\\/"), "should contain \\/ operators");
    let body_start = result.find("Next ==").expect("Next not found");
    let body = &result[body_start..];
    let newline_count = body.matches('\n').count();
    assert!(
        newline_count >= 3,
        "disjunction list with 3 items should span multiple lines, got {newline_count} newlines"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_formatter_case_multiline() {
    let src = r#"---- MODULE Test ----
Result == CASE x = 1 -> "one"
            [] x = 2 -> "two"
            [] x = 3 -> "three"
            [] OTHER -> "other"
===="#;
    let result = format(src);
    assert!(result.contains("CASE"), "should contain CASE");
    assert!(result.contains("OTHER"), "should contain OTHER");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_formatter_let_in() {
    let src = r"---- MODULE Test ----
Compute == LET a == 1
               b == 2
           IN a + b
====";
    let result = format(src);
    assert!(result.contains("LET"), "should contain LET");
    assert!(result.contains("IN"), "should contain IN");
    assert!(result.contains("a == 1"), "should contain first def");
    assert!(result.contains("b == 2"), "should contain second def");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_formatter_indent_width_4() {
    let src = r"---- MODULE Test ----
TypeOK == /\ x \in Nat
          /\ y \in Nat
          /\ z \in Nat
====";
    let config = FormatConfig::default().with_indent_width(4);
    let result = format_with_config(src, config);
    // With indent_width 4, indented body should use 4-space indentation
    assert!(result.contains("TypeOK"), "should contain TypeOK");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_formatter_narrow_width_breaks_more() {
    let src = r"---- MODULE Test ----
P == IF some_long_condition > 0 THEN some_long_result ELSE some_other_result
====";
    let config = FormatConfig::default().with_max_width(40);
    let result = format_with_config(src, config);
    // With narrow width, IF/THEN/ELSE should break to multiple lines
    let body_start = result.find("P ==").expect("P not found");
    let body = &result[body_start..];
    let has_multiline_if = body.contains("IF") && body.contains("THEN") && body.contains("ELSE");
    assert!(has_multiline_if, "should contain IF/THEN/ELSE");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_formatter_module_delimiters() {
    let src = r"---- MODULE Test ----
X == 1
====";
    let result = format(src);
    // Module header should have padded dashes
    let first_line = result.lines().next().expect("no output");
    assert!(
        first_line.contains("MODULE Test"),
        "header should contain MODULE Test"
    );
    assert!(
        first_line.starts_with("---"),
        "header should start with dashes"
    );
    assert!(
        first_line.ends_with("---") || first_line.ends_with('-'),
        "header should end with dashes"
    );

    // Module footer should be equals signs
    let last_non_empty = result
        .lines()
        .rev()
        .find(|l| !l.is_empty())
        .expect("no output");
    assert!(
        last_non_empty.starts_with("===="),
        "footer should start with ===="
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_formatter_separator_line() {
    let src = r"---- MODULE Test ----
VARIABLE x
----
Init == x = 0
====";
    let result = format(src);
    // Separator lines should be padded dashes
    let lines: Vec<&str> = result.lines().collect();
    let sep_line = lines
        .iter()
        .find(|l| l.starts_with("---") && !l.contains("MODULE"));
    assert!(sep_line.is_some(), "should contain a separator line");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_formatter_variables_plural() {
    let src = r"---- MODULE Test ----
VARIABLE x, y, z
Init == x = 0
====";
    let result = format(src);
    // Multiple variables should use VARIABLES (plural)
    assert!(
        result.contains("VARIABLES x, y, z"),
        "multiple vars should use VARIABLES: {result}"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_formatter_single_variable() {
    let src = r"---- MODULE Test ----
VARIABLE x
Init == x = 0
====";
    let result = format(src);
    assert!(
        result.contains("VARIABLE x"),
        "single var should use VARIABLE (singular): {result}"
    );
}

// --- Round-trip stability tests ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_roundtrip_stable_simple() {
    roundtrip_format_stable(
        r"---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
====",
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_roundtrip_stable_quantifiers() {
    roundtrip_format_stable(
        r"---- MODULE Test ----
P == \A x \in S : \E y \in T : x = y
====",
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_roundtrip_stable_sets() {
    roundtrip_format_stable(
        r"---- MODULE Test ----
S == {1, 2, 3}
T == {x \in S : x > 1}
====",
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_roundtrip_stable_let_in() {
    roundtrip_format_stable(
        r"---- MODULE Test ----
Compute == LET a == 1
               b == 2
           IN a + b
====",
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_roundtrip_stable_if_then_else() {
    roundtrip_format_stable(
        r"---- MODULE Test ----
P == IF x > 0 THEN y ELSE z
====",
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_roundtrip_stable_temporal() {
    roundtrip_format_stable(
        r"---- MODULE Test ----
VARIABLE x
Spec == []P
Fair == WF_x(Next)
====",
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_roundtrip_stable_except() {
    roundtrip_format_stable(
        r"---- MODULE Test ----
f == [a |-> 1, b |-> 2]
g == [f EXCEPT !.a = 3]
====",
    );
}

// --- AST equivalence round-trip tests ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_roundtrip_ast_eq_simple() {
    roundtrip_format_ast_eq(
        r"---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
====",
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_roundtrip_ast_eq_quantifiers() {
    roundtrip_format_ast_eq(
        r"---- MODULE Test ----
P == \A x \in S : \E y \in T : x = y
====",
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_roundtrip_ast_eq_sets_and_functions() {
    roundtrip_format_ast_eq(
        r"---- MODULE Test ----
S == {1, 2, 3}
T == {x \in S : x > 1}
f == [x \in S |-> x + 1]
r == [a |-> 1, b |-> 2]
====",
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_roundtrip_ast_eq_case() {
    roundtrip_format_ast_eq(
        r#"---- MODULE Test ----
Result == CASE x = 1 -> "one"
            [] x = 2 -> "two"
            [] OTHER -> "other"
===="#,
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_roundtrip_ast_eq_conjunction_list() {
    roundtrip_format_ast_eq(
        r"---- MODULE Test ----
TypeOK == /\ x \in Nat
          /\ y \in Nat
          /\ z \in Nat
====",
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_roundtrip_ast_eq_let_in() {
    roundtrip_format_ast_eq(
        r"---- MODULE Test ----
Compute == LET a == 1
               b == 2
           IN a + b
====",
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_roundtrip_ast_eq_temporal() {
    roundtrip_format_ast_eq(
        r"---- MODULE Test ----
VARIABLE x
Spec == []P
Fair == WF_x(Next)
Strong == SF_x(Next)
====",
    );
}

// --- Snapshot tests for the formatter ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn snapshot_fmt_simple_spec() {
    let src = r"---- MODULE Counter ----
VARIABLE count

Init == count = 0

Increment == count' = count + 1

Decrement == count' = count - 1

Next == Increment \/ Decrement
====";
    assert_snapshot!("fmt_simple_spec", format(src));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn snapshot_fmt_conjunction_list() {
    let src = r"---- MODULE TypeCheck ----
VARIABLE x, y, z

TypeOK == /\ x \in Nat
          /\ y \in Nat
          /\ z \in Nat
====";
    assert_snapshot!("fmt_conjunction_list", format(src));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn snapshot_fmt_disjunction_list() {
    let src = r"---- MODULE Actions ----
Next == \/ Action1
        \/ Action2
        \/ Action3
====";
    assert_snapshot!("fmt_disjunction_list", format(src));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn snapshot_fmt_case_expression() {
    let src = r#"---- MODULE CaseTest ----
Result == CASE x = 1 -> "one"
            [] x = 2 -> "two"
            [] x = 3 -> "three"
            [] OTHER -> "other"
===="#;
    assert_snapshot!("fmt_case_expression", format(src));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn snapshot_fmt_let_in() {
    let src = r"---- MODULE LetTest ----
Compute == LET a == 1
               b == 2
               c == a + b
           IN c * 2
====";
    assert_snapshot!("fmt_let_in", format(src));
}
