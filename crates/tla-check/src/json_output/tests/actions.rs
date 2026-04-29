// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for action metadata in JSON success output.

use super::*;
use crate::{CheckResult, CheckStats};

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_success_actions_detected_use_recorded_ids_without_coverage() {
    let stats = CheckStats {
        detected_actions: vec!["Foo".to_string(), "Foo".to_string()],
        detected_action_ids: vec!["7:10-13".to_string(), "7:20-23".to_string()],
        ..Default::default()
    };

    let output = JsonOutput::new(Path::new("/tmp/test.tla"), None, "Test", 1)
        .with_check_result(&CheckResult::Success(stats), Duration::from_secs(0));

    assert_eq!(output.actions_detected.len(), 2);
    assert_eq!(output.actions_detected[0].name, "Foo");
    assert_eq!(output.actions_detected[1].name, "Foo");
    assert_eq!(output.actions_detected[0].id, "7:10-13");
    assert_eq!(output.actions_detected[1].id, "7:20-23");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_success_actions_detected_fallback_ids_are_unique_without_recorded_ids() {
    let stats = CheckStats {
        detected_actions: vec!["Foo".to_string(), "Foo".to_string()],
        ..Default::default()
    };

    let output = JsonOutput::new(Path::new("/tmp/test.tla"), None, "Test", 1)
        .with_check_result(&CheckResult::Success(stats), Duration::from_secs(0));

    assert_eq!(output.actions_detected.len(), 2);
    assert_ne!(
        output.actions_detected[0].id, output.actions_detected[1].id,
        "legacy fallback ids must stay distinct even when action names collide"
    );
    assert_eq!(output.actions_detected[0].id, "detected:0");
    assert_eq!(output.actions_detected[1].id, "detected:1");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_success_actions_detected_duplicate_recorded_ids_are_disambiguated() {
    let stats = CheckStats {
        detected_actions: vec!["Foo".to_string(), "Foo".to_string()],
        detected_action_ids: vec!["0:0-0".to_string(), "0:0-0".to_string()],
        ..Default::default()
    };

    let output = JsonOutput::new(Path::new("/tmp/test.tla"), None, "Test", 1)
        .with_check_result(&CheckResult::Success(stats), Duration::from_secs(0));

    assert_eq!(output.actions_detected.len(), 2);
    assert_eq!(output.actions_detected[0].id, "0:0-0#dup0");
    assert_eq!(output.actions_detected[1].id, "0:0-0#dup1");
    assert_ne!(
        output.actions_detected[0].id, output.actions_detected[1].id,
        "duplicate recorded ids must be repaired before JSON emission"
    );
}
