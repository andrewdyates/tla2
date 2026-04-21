// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_split_named_instance_real_action_subscript_as_safety() {
    let inner = inner_named_instance_module();
    let outer = outer_named_instance_module();
    let config = named_instance_config("Refines");
    let checker = ModelChecker::new_with_extends(&outer, &[&inner], &config);

    let (safety_parts, liveness_expr) = checker
        .separate_safety_liveness_parts("Refines", operator_body(&outer, "Refines"))
        .expect("named-instance property should split successfully");

    assert_eq!(
        safety_parts.init_terms.len(),
        1,
        "named-instance Spec should keep one init predicate"
    );
    assert_eq!(
        safety_parts.always_terms.len(),
        1,
        "named-instance [][Next]_vars should stay on the safety action lane"
    );
    assert!(
        liveness_expr.is_none(),
        "named-instance [][Next]_vars must not leak to the liveness checker"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_split_named_instance_expanded_action_stays_liveness() {
    let inner = inner_named_instance_module();
    let outer = outer_named_instance_module();
    let config = named_instance_config("Expanded");
    let checker = ModelChecker::new_with_extends(&outer, &[&inner], &config);

    let (safety_parts, liveness_expr) = checker
        .separate_safety_liveness_parts("Expanded", operator_body(&outer, "Expanded"))
        .expect("expanded named-instance property should split successfully");

    assert!(
        safety_parts.init_terms.is_empty(),
        "expanded [](A \\/ UNCHANGED vars) should not extract init predicates"
    );
    assert!(
        safety_parts.always_terms.is_empty(),
        "expanded [](A \\/ UNCHANGED vars) must not be misclassified as safety"
    );
    assert!(
        liveness_expr.is_some(),
        "expanded [](A \\/ UNCHANGED vars) should remain on the liveness/rejection path"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_split_named_instance_raw_action_stays_liveness() {
    let inner = inner_named_instance_module();
    let outer = outer_named_instance_module();
    let config = named_instance_config("RawRefines");
    let checker = ModelChecker::new_with_extends(&outer, &[&inner], &config);

    let (safety_parts, liveness_expr) = checker
        .separate_safety_liveness_parts("RawRefines", operator_body(&outer, "RawRefines"))
        .expect("named-instance raw action property should split successfully");

    assert!(
        safety_parts.init_terms.is_empty(),
        "named-instance []Next should not extract init predicates"
    );
    assert!(
        safety_parts.always_terms.is_empty(),
        "named-instance []Next must not be misclassified as safety"
    );
    assert!(
        liveness_expr.is_some(),
        "named-instance []Next should remain on the liveness/rejection path"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_split_named_instance_init_substitution_keeps_structural_action_promotion() {
    let inner = inner_named_instance_module();
    let outer = outer_named_instance_init_split_module();
    let config = named_instance_config("Refines");
    let checker = ModelChecker::new_with_extends(&outer, &[&inner], &config);

    let (safety_parts, liveness_expr) = checker
        .separate_safety_liveness_parts("Refines", operator_body(&outer, "Refines"))
        .expect("named-instance property with substituted init split should still split");

    assert_eq!(
        safety_parts.init_terms.len(),
        2,
        "substituting Init <- (InitLeft /\\ InitRight) should preserve both init conjuncts"
    );
    assert_eq!(
        safety_parts.always_terms.len(),
        1,
        "substituting one source conjunct into two init conjuncts must not drop [][Next]_vars"
    );
    assert!(
        liveness_expr.is_none(),
        "named-instance structural [][Next]_vars should remain fully handled after init expansion"
    );
}
