// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Regression test for #465: the lexer tokenizes `_vars` as a single `Ident`.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_extract_subscript_single_ident() {
    let src = r#"
---- MODULE Test ----
VARIABLE x
vars == <<x>>
Init == x = 0
Next == x' = x + 1
Spec == Init /\ [][Next]_vars
===="#;
    let tree = parse_to_syntax_tree(src);

    let spec_body = find_op_body(&tree, "Spec").expect("Spec not found");
    let result =
        extract_spec_formula(&spec_body).expect("extract_spec_formula should handle _vars");

    assert_eq!(result.init, "Init");
    assert_eq!(result.next, "Next");
    assert_eq!(result.vars.as_deref(), Some("vars"));
    assert!(
        result.stuttering_allowed,
        "Square bracket form [A]_v should allow stuttering"
    );
}

/// Part of #2291: angle-bracket `<<A>>_v` forms forbid stuttering.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_extract_angle_bracket_form_forbids_stuttering() {
    let src = r#"
---- MODULE Test ----
VARIABLE x
vars == <<x>>
Init == x = 0
Next == x' = x + 1
Spec == Init /\ []<<Next>>_vars
===="#;
    let tree = parse_to_syntax_tree(src);

    let spec_body = find_op_body(&tree, "Spec").expect("Spec not found");
    let result = extract_spec_formula(&spec_body).expect("Failed to extract");

    assert_eq!(result.init, "Init");
    assert_eq!(result.next, "Next");
    assert_eq!(result.vars.as_deref(), Some("vars"));
    assert!(
        !result.stuttering_allowed,
        "Angle bracket form <<A>>_v should forbid stuttering"
    );
}

/// Part of #2291: angle-bracket stuttering settings propagate through config resolution.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_resolve_angle_bracket_stuttering_forbidden() {
    use crate::check::resolve_spec_from_config;
    use crate::config::Config;

    let src = r#"
---- MODULE Test ----
VARIABLE x
vars == <<x>>
Init == x = 0
Next == x' = x + 1
Spec == Init /\ []<<Next>>_vars
===="#;
    let tree = parse_to_syntax_tree(src);

    let config = Config {
        specification: Some("Spec".to_string()),
        ..Default::default()
    };
    let resolved = resolve_spec_from_config(&config, &tree).unwrap();

    assert_eq!(resolved.init, "Init");
    assert_eq!(resolved.next, "Next");
    assert!(
        !resolved.stuttering_allowed,
        "<<Next>>_vars should resolve to stuttering_allowed=false, but got true"
    );
}

/// Regression test for #1278: disjunctive actions in `[A]_v` must preserve the full action.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_extract_disjunction_in_action_subscript() {
    let src = r#"
---- MODULE Test ----
VARIABLE x
vars == <<x>>
TraceInit == x = 0
Next == x' = x + 1
TraceSpec == TraceInit /\ [][Next \/ UNCHANGED vars]_vars
===="#;
    let tree = parse_to_syntax_tree(src);

    let spec_body = find_op_body(&tree, "TraceSpec").expect("TraceSpec not found");
    let result = extract_spec_formula(&spec_body).expect("Failed to extract");

    assert_eq!(result.init, "TraceInit");
    assert!(
        result.next.contains("UNCHANGED") || result.next_node.is_some(),
        "Action should preserve the UNCHANGED disjunct or a lowered next_node, got next='{}'",
        result.next
    );
    assert_eq!(result.vars.as_deref(), Some("vars"));
    assert!(
        result.stuttering_allowed,
        "Square bracket form [A]_v should allow stuttering"
    );
}

#[test]
fn test_extract_apply_expr_in_action_subscript() {
    let src = r#"
---- MODULE Test ----
EXTENDS Integers
VARIABLE x
vars == <<x>>
Init == x = 0
Step(y) == x' = x + y
Spec == Init /\ [][Step(1)]_vars
===="#;
    let tree = parse_to_syntax_tree(src);

    let spec_body = find_op_body(&tree, "Spec").expect("Spec not found");
    let result = extract_spec_formula(&spec_body).expect("Failed to extract");

    assert_eq!(result.init, "Init");
    assert!(
        result.next_node.is_some(),
        "ApplyExpr Step(1) should produce next_node for inline lowering"
    );
    assert_eq!(result.vars.as_deref(), Some("vars"));
    assert!(
        result.stuttering_allowed,
        "Square bracket form [A]_v should allow stuttering"
    );
}

/// `UNCHANGED vars` is a unary expression and should stay on the inline-lowering path.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_extract_unary_expr_unchanged_in_action_subscript() {
    let src = r#"
---- MODULE Test ----
VARIABLE x
vars == <<x>>
Init == x = 0
Spec == Init /\ [][UNCHANGED vars]_vars
===="#;
    let tree = parse_to_syntax_tree(src);

    let spec_body = find_op_body(&tree, "Spec").expect("Spec not found");
    let result = extract_spec_formula(&spec_body).expect("Failed to extract");

    assert_eq!(result.init, "Init");
    assert!(
        result.next_node.is_some(),
        "UnaryExpr UNCHANGED vars should produce next_node for inline lowering"
    );
    assert!(
        result.next.contains("UNCHANGED"),
        "next text should contain UNCHANGED, got: '{}'",
        result.next
    );
    assert_eq!(result.vars.as_deref(), Some("vars"));
    assert!(
        result.stuttering_allowed,
        "Square bracket form [A]_v should allow stuttering"
    );
}
