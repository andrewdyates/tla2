// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for JSON value/output/suggestion/result serialization.

use super::*;
use crate::{CheckResult, CheckStats};

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_json_value_serialization() {
    let val = JsonValue::Int(42);
    let json = serde_json::to_string(&val)
        .expect("invariant: serialization succeeds for well-formed types");
    assert!(json.contains("\"type\":\"int\""));
    assert!(json.contains("\"value\":42"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_json_output_basic() {
    let output = JsonOutput::new(
        Path::new("/tmp/test.tla"),
        Some(Path::new("/tmp/test.cfg")),
        "Test",
        1,
    );
    let json = output
        .to_json()
        .expect("invariant: serialization succeeds for well-formed types");
    // Check basic structure
    assert!(json.contains("\"version\": \"1.3\""), "JSON: {}", json);
    assert!(json.contains("\"tool\": \"tla2\""), "JSON: {}", json);
    assert!(json.contains("\"soundness\":"), "JSON: {}", json);
    assert!(json.contains("\"completeness\":"), "JSON: {}", json);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_value_to_json() {
    use std::sync::Arc;
    assert!(matches!(
        value_to_json(&Value::Bool(true)),
        JsonValue::Bool(true)
    ));
    assert!(matches!(
        value_to_json(&Value::String(Arc::from("hello"))),
        JsonValue::String(s) if s == "hello"
    ));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_error_suggestion_serialization() {
    let suggestion = ErrorSuggestion {
        action: "Test action".to_string(),
        example: Some("Example code".to_string()),
        options: vec!["Option 1".to_string(), "Option 2".to_string()],
    };
    let json = serde_json::to_string(&suggestion)
        .expect("invariant: serialization succeeds for well-formed types");
    assert!(
        json.contains("\"action\":\"Test action\""),
        "JSON: {}",
        json
    );
    assert!(
        json.contains("\"example\":\"Example code\""),
        "JSON: {}",
        json
    );
    assert!(json.contains("\"options\":[\"Option 1\""), "JSON: {}", json);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_json_output_deserializes_without_actions_detected_field() {
    let legacy = serde_json::to_value(JsonOutput::new(
        Path::new("/tmp/test.tla"),
        Some(Path::new("/tmp/test.cfg")),
        "Test",
        1,
    ))
    .expect("invariant: serialization succeeds for well-formed types");

    let output: JsonOutput = serde_json::from_value(legacy)
        .expect("outputs without actions_detected should deserialize");

    assert!(output.actions_detected.is_empty());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_json_output_deserializes_legacy_actions_without_ids_using_distinct_fallback_ids() {
    let mut legacy = serde_json::to_value(JsonOutput::new(
        Path::new("/tmp/test.tla"),
        Some(Path::new("/tmp/test.cfg")),
        "Test",
        1,
    ))
    .expect("invariant: serialization succeeds for well-formed types");
    legacy["actions_detected"] = serde_json::json!([
        {
            "name": "Approve",
            "occurrences": 7,
            "percentage": 12.5
        },
        {
            "name": "Approve",
            "occurrences": 3
        }
    ]);

    let output: JsonOutput = serde_json::from_value(legacy)
        .expect("legacy action payloads without ids should stay readable");

    assert_eq!(output.actions_detected.len(), 2);
    assert_eq!(output.actions_detected[0].id, "detected:0");
    assert_eq!(output.actions_detected[1].id, "detected:1");
    assert_eq!(output.actions_detected[0].name, "Approve");
    assert_eq!(output.actions_detected[1].name, "Approve");
    assert_eq!(output.actions_detected[0].occurrences, 7);
    assert_eq!(output.actions_detected[1].occurrences, 3);
    assert_eq!(output.actions_detected[0].percentage, Some(12.5));
    assert_eq!(output.actions_detected[1].percentage, None);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_json_output_deserializes_duplicate_action_ids_with_unique_suffixes() {
    let mut legacy = serde_json::to_value(JsonOutput::new(
        Path::new("/tmp/test.tla"),
        Some(Path::new("/tmp/test.cfg")),
        "Test",
        1,
    ))
    .expect("invariant: serialization succeeds for well-formed types");
    legacy["actions_detected"] = serde_json::json!([
        {
            "id": "0:0-0",
            "name": "Approve",
            "occurrences": 7
        },
        {
            "id": "0:0-0",
            "name": "Approve",
            "occurrences": 3
        }
    ]);

    let output: JsonOutput = serde_json::from_value(legacy)
        .expect("duplicate action ids should be repaired during deserialization");

    assert_eq!(output.actions_detected.len(), 2);
    assert_eq!(output.actions_detected[0].id, "0:0-0#dup0");
    assert_eq!(output.actions_detected[1].id, "0:0-0#dup1");
    assert_eq!(output.actions_detected[0].name, "Approve");
    assert_eq!(output.actions_detected[1].name, "Approve");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_json_output_roundtrip_preserves_distinct_action_ids() {
    let stats = CheckStats {
        detected_actions: vec!["Send".to_string(), "Send".to_string(), "Recv".to_string()],
        detected_action_ids: vec![
            "3:5-9".to_string(),
            "7:5-9".to_string(),
            "11:5-9".to_string(),
        ],
        ..Default::default()
    };

    let output = JsonOutput::new(Path::new("/tmp/test.tla"), None, "Test", 1)
        .with_check_result(&CheckResult::Success(stats), Duration::from_secs(1));

    assert_eq!(output.actions_detected.len(), 3);
    assert_eq!(output.actions_detected[0].id, "3:5-9");
    assert_eq!(output.actions_detected[1].id, "7:5-9");
    assert_eq!(output.actions_detected[2].id, "11:5-9");

    let json = output.to_json().expect("serialization succeeds");
    let deserialized: JsonOutput =
        serde_json::from_str(&json).expect("round-trip deserialization succeeds");

    assert_eq!(deserialized.actions_detected.len(), 3);
    assert_eq!(deserialized.actions_detected[0].id, "3:5-9");
    assert_eq!(deserialized.actions_detected[1].id, "7:5-9");
    assert_eq!(deserialized.actions_detected[2].id, "11:5-9");
    assert_eq!(deserialized.actions_detected[0].name, "Send");
    assert_eq!(deserialized.actions_detected[1].name, "Send");
    assert_eq!(deserialized.actions_detected[2].name, "Recv");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_result_info_with_error_code() {
    let result = ResultInfo {
        status: "error".to_string(),
        error_type: Some("deadlock".to_string()),
        error_code: Some(error_codes::TLC_DEADLOCK.to_string()),
        error_message: Some("Deadlock detected".to_string()),
        violated_property: None,
        suggestion: Some(ErrorSuggestion {
            action: "No action enabled".to_string(),
            example: Some("Add --no-deadlock".to_string()),
            options: vec![],
        }),
    };
    let json = serde_json::to_string(&result)
        .expect("invariant: serialization succeeds for well-formed types");
    assert!(
        json.contains("\"error_code\":\"TLC_DEADLOCK\""),
        "JSON: {}",
        json
    );
    assert!(json.contains("\"suggestion\":{"), "JSON: {}", json);
}
