// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_extract_with_weak_fairness() {
    let src = r#"
---- MODULE Test ----
VARIABLE x
vars == <<x>>
Init == x = 0
Next == x' = x + 1
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
===="#;
    let tree = parse_to_syntax_tree(src);

    let spec_body = find_op_body(&tree, "Spec").expect("Spec not found");
    let result = extract_spec_formula(&spec_body).expect("Failed to extract");

    assert_eq!(result.init, "Init");
    assert_eq!(result.next, "Next");
    assert_eq!(result.vars.as_deref(), Some("vars"));
    assert_eq!(result.fairness.len(), 1);
    match &result.fairness[0] {
        FairnessConstraint::Weak { vars, action, .. } => {
            assert_eq!(vars, "vars");
            assert_eq!(action, "Next");
        }
        _ => panic!("Expected weak fairness"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_extract_with_strong_fairness() {
    let src = r#"
---- MODULE Test ----
VARIABLE x
vars == <<x>>
Init == x = 0
Next == x' = x + 1
Spec == Init /\ [][Next]_vars /\ SF_vars(Next)
===="#;
    let tree = parse_to_syntax_tree(src);

    let spec_body = find_op_body(&tree, "Spec").expect("Spec not found");
    let result = extract_spec_formula(&spec_body).expect("Failed to extract");

    assert_eq!(result.init, "Init");
    assert_eq!(result.next, "Next");
    assert_eq!(result.fairness.len(), 1);
    match &result.fairness[0] {
        FairnessConstraint::Strong { vars, action, .. } => {
            assert_eq!(vars, "vars");
            assert_eq!(action, "Next");
        }
        _ => panic!("Expected strong fairness"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_extract_with_multiple_fairness() {
    let src = r#"
---- MODULE Test ----
VARIABLE x
vars == <<x>>
Init == x = 0
Next == x' = x + 1
Action1 == x' = x + 1
Action2 == x' = x + 2
Spec == Init /\ [][Next]_vars /\ WF_vars(Action1) /\ SF_vars(Action2)
===="#;
    let tree = parse_to_syntax_tree(src);

    let spec_body = find_op_body(&tree, "Spec").expect("Spec not found");
    let result = extract_spec_formula(&spec_body).expect("Failed to extract");

    assert_eq!(result.init, "Init");
    assert_eq!(result.next, "Next");
    assert_eq!(result.fairness.len(), 2);

    let has_weak = result
        .fairness
        .iter()
        .any(|f| matches!(f, FairnessConstraint::Weak { .. }));
    let has_strong = result
        .fairness
        .iter()
        .any(|f| matches!(f, FairnessConstraint::Strong { .. }));
    assert!(has_weak, "Should have weak fairness");
    assert!(has_strong, "Should have strong fairness");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_extract_quantified_fairness() {
    let src = r#"
---- MODULE Test ----
EXTENDS Integers
CONSTANT Clients
VARIABLE x
vars == <<x>>
Init == x = 0
Next == x' = x + 1
Action(c) == x' = c
Spec == Init /\ [][Next]_vars /\ \A c \in Clients: WF_vars(Action(c))
===="#;
    let tree = parse_to_syntax_tree(src);

    let spec_body = find_op_body(&tree, "Spec").expect("Spec not found");
    let result = extract_spec_formula(&spec_body).expect("Failed to extract");

    assert_eq!(result.init, "Init");
    assert_eq!(result.next, "Next");
    assert_eq!(
        result.fairness.len(),
        1,
        "Should have one quantified fairness constraint"
    );
    match &result.fairness[0] {
        FairnessConstraint::QuantifiedTemporal { .. } => {}
        _ => panic!("Expected QuantifiedTemporal, got {:?}", &result.fairness[0]),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_extract_multiple_quantified_fairness() {
    let src = r#"
---- MODULE Test ----
EXTENDS Integers
CONSTANT Clients
VARIABLE x
vars == <<x>>
Init == x = 0
Next == x' = x + 1
Action1(c) == x' = c
Action2(c) == x' = c + 1
Spec ==
  /\ Init /\ [][Next]_vars
  /\ \A c \in Clients: WF_vars(Action1(c))
  /\ \A c \in Clients: SF_vars(Action2(c))
===="#;
    let tree = parse_to_syntax_tree(src);

    let spec_body = find_op_body(&tree, "Spec").expect("Spec not found");
    let result = extract_spec_formula(&spec_body).expect("Failed to extract");

    assert_eq!(result.init, "Init");
    assert_eq!(result.next, "Next");
    assert_eq!(
        result.fairness.len(),
        2,
        "Should have two quantified fairness constraints"
    );

    for fc in &result.fairness {
        assert!(
            matches!(fc, FairnessConstraint::QuantifiedTemporal { .. }),
            "Expected QuantifiedTemporal, got {:?}",
            fc
        );
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_extract_all_fairness_tuple_subscript_in_conjunction_list() {
    let src = r#"
---- MODULE Test ----
CONSTANT participants
VARIABLE coordinator, participant

vars == <<coordinator, participant>>

coordProgB == UNCHANGED vars
parProgNB(i, j) == UNCHANGED vars

fairnessNB ==
  /\ \A i \in participants: WF_<<coordinator, participant>>(\E j \in participants: parProgNB(i, j))
  /\ WF_<<coordinator, participant>>(coordProgB)
===="#;
    let tree = parse_to_syntax_tree(src);

    let fairness_body = find_op_body(&tree, "fairnessNB").expect("fairnessNB not found");
    let fairness = extract_all_fairness(&fairness_body);

    assert!(
        fairness
            .iter()
            .any(|f| matches!(f, FairnessConstraint::QuantifiedTemporal { .. })),
        "Expected QuantifiedTemporal in extracted fairness, got {:?}",
        fairness
    );

    assert!(
        fairness.iter().any(|f| matches!(
            f,
            FairnessConstraint::Weak { action, .. } if action == "coordProgB"
        )),
        "Expected WF for coordProgB in extracted fairness, got {:?}",
        fairness
    );
}
