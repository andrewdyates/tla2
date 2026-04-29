// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_has_liveness_properties_true_when_properties_present() {
    let config = Config {
        properties: vec!["Liveness".to_string()],
        ..Default::default()
    };
    assert!(config.has_liveness_properties());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_has_liveness_properties_false_when_empty() {
    let config = Config::default();
    assert!(!config.has_liveness_properties());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_fingerprint_liveness_warning_no_trace_mode_lists_property_names() {
    let config = Config {
        properties: vec!["EventuallyFoo".to_string(), "EventuallyBar".to_string()],
        ..Default::default()
    };

    let warning = config
        .fingerprint_liveness_warning(false, &[])
        .expect("warning should exist in fingerprint-only mode");
    assert!(warning.contains("fingerprint-only mode"));
    assert!(warning.contains("EventuallyFoo"));
    assert!(warning.contains("EventuallyBar"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_fingerprint_liveness_warning_absent_with_full_state_storage() {
    let config = Config {
        properties: vec!["EventuallyFoo".to_string()],
        ..Default::default()
    };
    assert!(config.fingerprint_liveness_warning(true, &[]).is_none());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_fingerprint_liveness_warning_absent_without_properties() {
    let config = Config::default();
    assert!(config.fingerprint_liveness_warning(false, &[]).is_none());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_validate_default_config_no_issues() {
    let config = Config::default();
    assert!(config.validate().is_empty());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_validate_init_next_only_no_issues() {
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };
    assert!(config.validate().is_empty());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_validate_specification_only_no_issues() {
    let config = Config {
        specification: Some("Spec".to_string()),
        ..Default::default()
    };
    assert!(config.validate().is_empty());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_specification_conflicts_with_init_next_detects_invalid_user_config() {
    let config = Config {
        specification: Some("Spec".to_string()),
        init: Some("Init".to_string()),
        ..Default::default()
    };
    assert!(config.specification_conflicts_with_init_next());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_runtime_model_config_strips_resolved_specification_only_after_init_and_next_exist() {
    let config = Config {
        specification: Some("Spec".to_string()),
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TypeOK".to_string()],
        ..Default::default()
    };

    let runtime = config.runtime_model_config();

    assert_eq!(runtime.specification, None);
    assert_eq!(runtime.init.as_deref(), Some("Init"));
    assert_eq!(runtime.next.as_deref(), Some("Next"));
    assert_eq!(runtime.invariants, config.invariants);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_runtime_model_config_preserves_unresolved_specification() {
    let config = Config {
        specification: Some("Spec".to_string()),
        ..Default::default()
    };

    let runtime = config.runtime_model_config();

    assert_eq!(runtime.specification.as_deref(), Some("Spec"));
    assert_eq!(runtime.init, None);
    assert_eq!(runtime.next, None);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_validate_specification_with_init_is_error() {
    let config = Config {
        specification: Some("Spec".to_string()),
        init: Some("Init".to_string()),
        ..Default::default()
    };
    let issues = config.validate();
    assert_eq!(issues.len(), 1);
    assert_eq!(issues[0], ConfigValidationIssue::SpecificationWithInitNext);
    assert!(issues[0].is_error());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_validate_specification_with_next_is_error() {
    let config = Config {
        specification: Some("Spec".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };
    let issues = config.validate();
    assert_eq!(issues.len(), 1);
    assert_eq!(issues[0], ConfigValidationIssue::SpecificationWithInitNext);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_validate_specification_with_init_and_next_is_error() {
    let config = Config {
        specification: Some("Spec".to_string()),
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };
    let issues = config.validate();
    assert_eq!(issues.len(), 1);
    assert!(issues[0].is_error());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_validate_por_without_properties_no_issues() {
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        por_enabled: true,
        ..Default::default()
    };
    assert!(
        config.validate().is_empty(),
        "POR should be accepted (Part of #3706)"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_validate_por_with_properties_no_issues() {
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        por_enabled: true,
        properties: vec!["Liveness".to_string()],
        liveness_execution: LivenessExecutionMode::OnTheFly,
        ..Default::default()
    };
    assert!(
        config.validate().is_empty(),
        "POR with liveness should be accepted (Part of #3706)"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_validate_por_runtime_no_issues() {
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        por_enabled: true,
        properties: vec!["Prop".to_string()],
        ..Default::default()
    };
    assert!(
        config.validate_runtime().is_empty(),
        "POR should pass runtime validation (Part of #3706)"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_validate_specification_with_init_and_por_returns_one_issue() {
    let config = Config {
        specification: Some("Spec".to_string()),
        init: Some("Init".to_string()),
        por_enabled: true,
        properties: vec!["Liveness".to_string()],
        ..Default::default()
    };
    let issues = config.validate();
    assert_eq!(issues.len(), 1);
    assert_eq!(issues[0], ConfigValidationIssue::SpecificationWithInitNext);
}
