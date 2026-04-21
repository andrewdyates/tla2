// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_extract_simple_spec() {
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
    let result = extract_spec_formula(&spec_body).expect("Failed to extract");

    assert_eq!(result.init, "Init");
    assert_eq!(result.next, "Next");
    assert_eq!(result.vars.as_deref(), Some("vars"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_extract_conjunction_style() {
    let src = r#"
---- MODULE Test ----
VARIABLE x
vars == <<x>>
Init == x = 0
Next == x' = x + 1
Spec == /\ Init /\ [][Next]_vars
===="#;
    let tree = parse_to_syntax_tree(src);

    let spec_body = find_op_body(&tree, "Spec").expect("Spec not found in conjunction-style test");
    let result =
        extract_spec_formula(&spec_body).expect("Failed to extract conjunction-style spec formula");

    assert_eq!(result.init, "Init");
    assert_eq!(result.next, "Next");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_extract_tuple_vars() {
    let src = r#"
---- MODULE Test ----
VARIABLE x, y
Init == x = 0 /\ y = 0
Next == x' = x + 1 /\ y' = y
Spec == Init /\ [][Next]_<<x, y>>
===="#;
    let tree = parse_to_syntax_tree(src);

    let spec_body = find_op_body(&tree, "Spec").expect("Spec not found in tuple-vars test");
    let result =
        extract_spec_formula(&spec_body).expect("Failed to extract tuple-vars spec formula");

    assert_eq!(result.init, "Init");
    assert_eq!(result.next, "Next");
    assert!(result.vars.is_some(), "Tuple vars should be extracted");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_extract_existential_in_next() {
    // Test: Spec == Init /\ [][\E n \in Node: Next(n)]_vars
    // The NEXT action is an existential quantifier, not just "n".
    let src = r#"
---- MODULE Test ----
CONSTANT Node
VARIABLE x
vars == x
Init == x = 0
Next(n) == x' = n
Spec == Init /\ [][\E n \in Node: Next(n)]_vars
===="#;
    let tree = parse_to_syntax_tree(src);

    let spec_body = find_op_body(&tree, "Spec").expect("Spec not found");
    let result = extract_spec_formula(&spec_body).expect("Failed to extract");

    assert_eq!(result.init, "Init");
    assert_eq!(result.vars.as_deref(), Some("vars"));
    assert_ne!(
        result.next, "n",
        "Next should not collapse to the quantified variable"
    );
}
