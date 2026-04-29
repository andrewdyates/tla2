// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::scan::{contains_temporal_operators, find_op_body_in_tree};
use super::*;
use crate::config::Config;

#[test]
fn test_explicit_init_next_returns_resolved_spec() {
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Config::default()
    };
    let tree = tla_core::parse_to_syntax_tree("---- MODULE Test ---- ====");
    let result = resolve_spec_from_config(&config, &tree).unwrap();
    assert_eq!(result.init, "Init");
    assert_eq!(result.next, "Next");
    assert!(result.next_node.is_none());
    assert!(result.fairness.is_empty());
    assert!(result.stuttering_allowed);
}

#[test]
fn test_no_init_returns_missing_init_error() {
    let config = Config::default();
    let tree = tla_core::parse_to_syntax_tree("---- MODULE Test ---- ====");
    let result = resolve_spec_from_config(&config, &tree);
    assert!(matches!(
        result,
        Err(CheckError::Config(ConfigCheckError::MissingInit))
    ));
}

#[test]
fn test_init_without_next_returns_missing_next_error() {
    let config = Config {
        init: Some("Init".to_string()),
        next: None,
        ..Config::default()
    };
    let tree = tla_core::parse_to_syntax_tree("---- MODULE Test ---- ====");
    let result = resolve_spec_from_config(&config, &tree);
    assert!(matches!(
        result,
        Err(CheckError::Config(ConfigCheckError::MissingNext))
    ));
}

#[test]
fn test_specification_not_found_returns_error() {
    let config = Config {
        specification: Some("NonExistent".to_string()),
        ..Config::default()
    };
    let tree = tla_core::parse_to_syntax_tree("---- MODULE Test ---- ====");
    let result = resolve_spec_from_config(&config, &tree);
    assert!(matches!(
        result,
        Err(CheckError::Config(ConfigCheckError::Specification(_)))
    ));
    if let Err(CheckError::Config(ConfigCheckError::Specification(msg))) = result {
        assert!(
            msg.contains("NonExistent"),
            "Error should name the operator: {msg}"
        );
    }
}

#[test]
fn test_specification_with_simple_init_next() {
    let src = r#"---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
Spec == Init /\ [][Next]_x
===="#;
    let tree = tla_core::parse_to_syntax_tree(src);
    let config = Config {
        specification: Some("Spec".to_string()),
        ..Config::default()
    };
    let result = resolve_spec_from_config(&config, &tree).unwrap();
    assert_eq!(result.init, "Init");
    assert_eq!(result.next, "Next");
    assert!(result.stuttering_allowed);
}

#[test]
fn test_explicit_init_next_takes_precedence_over_specification() {
    // Even if SPECIFICATION is set, explicit INIT/NEXT should win
    let config = Config {
        init: Some("MyInit".to_string()),
        next: Some("MyNext".to_string()),
        specification: Some("Spec".to_string()),
        ..Config::default()
    };
    let tree = tla_core::parse_to_syntax_tree("---- MODULE Test ---- ====");
    let result = resolve_spec_from_config(&config, &tree).unwrap();
    assert_eq!(result.init, "MyInit");
    assert_eq!(result.next, "MyNext");
}

#[test]
fn test_contains_temporal_operators_detects_wf() {
    let src = r#"---- MODULE Test ----
VARIABLE x
Fairness == WF_x(TRUE)
===="#;
    let tree = tla_core::parse_to_syntax_tree(src);
    // Find the Fairness operator body
    let body = find_op_body_in_tree(&tree, "Fairness");
    assert!(body.is_some(), "Should find Fairness operator");
    assert!(contains_temporal_operators(&body.unwrap()));
}

#[test]
fn test_contains_temporal_operators_false_for_plain_expr() {
    let src = r#"---- MODULE Test ----
VARIABLE x
Plain == x = 0
===="#;
    let tree = tla_core::parse_to_syntax_tree(src);
    let body = find_op_body_in_tree(&tree, "Plain");
    assert!(body.is_some(), "Should find Plain operator");
    assert!(!contains_temporal_operators(&body.unwrap()));
}

#[test]
fn test_find_op_body_in_tree_returns_none_for_missing() {
    let src = "---- MODULE Test ---- ====";
    let tree = tla_core::parse_to_syntax_tree(src);
    assert!(find_op_body_in_tree(&tree, "NonExistent").is_none());
}

#[test]
fn test_find_op_body_in_tree_finds_operator() {
    let src = r#"---- MODULE Test ----
VARIABLE x
Init == x = 0
===="#;
    let tree = tla_core::parse_to_syntax_tree(src);
    let body = find_op_body_in_tree(&tree, "Init");
    assert!(body.is_some(), "Should find Init operator body");
}

// ── Regression tests for #2445 ──────────────────────────────────────

#[test]
fn test_recursive_spec_resolution_propagates_cyclic_candidate_error() {
    // Previously, the fallback loop at resolve.rs:307-312 silently dropped
    // cyclic reference errors and resolved the next candidate instead.
    let src = r#"---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
Bad == Bad
Good == Init /\ [][Next]_x
Spec == Bad /\ Good
===="#;
    let tree = tla_core::parse_to_syntax_tree(src);
    let config = Config {
        specification: Some("Spec".to_string()),
        ..Config::default()
    };
    let result = resolve_spec_from_config(&config, &tree);
    // Must be a cyclic reference error, NOT a successful resolution of Good
    assert!(
        result.is_err(),
        "Cyclic candidate must propagate as error, not silently resolve Good"
    );
    if let Err(CheckError::Config(ConfigCheckError::Specification(msg))) = &result {
        assert!(
            msg.contains("cyclic"),
            "Error should mention cyclic reference: {msg}"
        );
    } else {
        panic!("Expected Specification error, got: {result:?}");
    }
}

#[test]
fn test_recursive_spec_resolution_skips_non_spec_candidate_and_finds_match() {
    // A plain operator (not a spec wrapper) should be classified as NoMatch
    // and the fallback loop should continue to the next candidate.
    let src = r#"---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
Plain == x = 0
Good == Init /\ [][Next]_x
Spec == Plain /\ Good
===="#;
    let tree = tla_core::parse_to_syntax_tree(src);
    let config = Config {
        specification: Some("Spec".to_string()),
        ..Config::default()
    };
    let result = resolve_spec_from_config(&config, &tree).unwrap();
    assert_eq!(result.init, "Init");
    assert_eq!(result.next, "Next");
}
