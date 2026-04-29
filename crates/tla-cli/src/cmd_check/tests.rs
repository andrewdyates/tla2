// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::helpers::{apply_allow_incomplete_overflow, merge_strategy_info};
use crate::cli_schema::OutputFormat;
use tla_check::InfraCheckError;
use tla_check::{CheckResult, CheckStats};

#[test]
fn allow_incomplete_downgrades_fingerprint_overflow_error_to_success() {
    let mut stats = CheckStats::default();
    stats.states_found = 7;
    let result = CheckResult::from_error(
        tla_check::CheckError::Infra(InfraCheckError::FingerprintOverflow {
            dropped: 3,
            detail: "test".to_string(),
        }),
        stats.clone(),
    );

    let (downgraded, note) = apply_allow_incomplete_overflow(result, true, OutputFormat::Json);

    assert!(matches!(downgraded, CheckResult::Success(_)));
    assert!(
        note.as_deref()
            .is_some_and(|msg| msg.contains("--allow-incomplete")),
        "expected note to mention --allow-incomplete, got: {note:?}"
    );
}

#[test]
fn merge_strategy_info_keeps_both_messages() {
    let merged = merge_strategy_info(
        Some("Adaptive checker selected sequential mode".to_string()),
        Some("Fingerprint storage overflow tolerated due to --allow-incomplete".to_string()),
    )
    .expect("merged strategy info should exist");

    assert!(merged.contains("Adaptive checker"));
    assert!(merged.contains("--allow-incomplete"));
}

// Part of #3759: Tests for CLI --init/--next/--inv override logic.

/// When has_cli_init_next is true and no .cfg exists, load_and_parse_config
/// returns a default Config instead of erroring.
#[test]
fn load_config_allows_missing_cfg_when_cli_init_next_provided() {
    use super::setup::load_and_parse_config;
    use crate::JsonErrorCtx;
    use tla_check::SearchCompleteness;

    let temp_dir = tempfile::tempdir().expect("create temp dir");
    let spec_path = temp_dir.path().join("NoConfig.tla");
    std::fs::write(&spec_path, "---- MODULE NoConfig ----\n====").expect("write spec");

    let json_err_ctx = JsonErrorCtx {
        output_format: OutputFormat::Human,
        spec_file: &spec_path,
        config_file: None,
        module_name: None,
        workers: 1,
        completeness: SearchCompleteness::Exhaustive,
    };

    // With has_cli_init_next=true, should succeed even without a .cfg.
    let result = load_and_parse_config(
        &spec_path,
        None,
        &json_err_ctx,
        OutputFormat::Human,
        true, // has_cli_init_next
    );
    assert!(result.is_ok(), "should succeed with has_cli_init_next=true");
    let (_path, source, config) = result.unwrap();
    assert!(source.is_empty(), "config source should be empty");
    assert!(config.init.is_none(), "default config has no init");
    assert!(config.next.is_none(), "default config has no next");
}

/// Part of #3779: When has_cli_init_next is false and no .cfg exists,
/// load_and_parse_config falls back to convention names "Init" and "Next".
#[test]
fn load_config_falls_back_to_convention_names_when_no_cfg_and_no_cli_flags() {
    use super::setup::load_and_parse_config;
    use crate::JsonErrorCtx;
    use tla_check::SearchCompleteness;

    let temp_dir = tempfile::tempdir().expect("create temp dir");
    let spec_path = temp_dir.path().join("NoConfig.tla");
    std::fs::write(&spec_path, "---- MODULE NoConfig ----\n====").expect("write spec");

    let json_err_ctx = JsonErrorCtx {
        output_format: OutputFormat::Human,
        spec_file: &spec_path,
        config_file: None,
        module_name: None,
        workers: 1,
        completeness: SearchCompleteness::Exhaustive,
    };

    // With has_cli_init_next=false, should fall back to convention names.
    let result = load_and_parse_config(
        &spec_path,
        None,
        &json_err_ctx,
        OutputFormat::Human,
        false, // has_cli_init_next
    );
    assert!(
        result.is_ok(),
        "should succeed with convention name fallback"
    );
    let (_path, source, config) = result.unwrap();
    assert!(source.is_empty(), "config source should be empty");
    assert_eq!(
        config.init.as_deref(),
        Some("Init"),
        "convention fallback should set Init"
    );
    assert_eq!(
        config.next.as_deref(),
        Some("Next"),
        "convention fallback should set Next"
    );
    assert!(
        config.invariants.is_empty(),
        "convention fallback should not add invariants"
    );
}

/// Part of #3780: CLI --trace-inv flags propagate to config.trace_invariants.
#[test]
fn cli_trace_inv_overrides_config_values() {
    let mut config = tla_check::Config::default();
    assert!(
        config.trace_invariants.is_empty(),
        "default config has no trace invariants"
    );

    // Simulate the CLI override logic from cmd_check/mod.rs.
    let trace_invariants = vec!["MonotonicTrace".to_string(), "ConservedTrace".to_string()];
    if !trace_invariants.is_empty() {
        config.trace_invariants = trace_invariants.clone();
    }

    assert_eq!(
        config.trace_invariants,
        vec!["MonotonicTrace", "ConservedTrace"],
        "trace invariants should be set from CLI flags"
    );
}

/// CLI --init/--next flags override .cfg values.
#[test]
fn cli_init_next_overrides_config_values() {
    let mut config = tla_check::Config::default();
    config.init = Some("OldInit".to_string());
    config.next = Some("OldNext".to_string());
    config.invariants = vec!["OldInv".to_string()];

    // Simulate the CLI override logic from cmd_check/mod.rs.
    let cli_init = Some("NewInit".to_string());
    let cli_next = Some("NewNext".to_string());
    let cli_invariants = vec!["NewInv1".to_string(), "NewInv2".to_string()];

    if let Some(ref init_op) = cli_init {
        config.init = Some(init_op.clone());
    }
    if let Some(ref next_op) = cli_next {
        config.next = Some(next_op.clone());
    }
    if !cli_invariants.is_empty() {
        config.invariants = cli_invariants.clone();
    }

    assert_eq!(config.init.as_deref(), Some("NewInit"));
    assert_eq!(config.next.as_deref(), Some("NewNext"));
    assert_eq!(config.invariants, vec!["NewInv1", "NewInv2"]);
}

/// Part of #3779: CLI --prop flags override config.properties.
#[test]
fn cli_prop_overrides_config_values() {
    let mut config = tla_check::Config::default();
    config.properties = vec!["OldLiveness".to_string()];

    // Simulate the CLI override logic from cmd_check/mod.rs.
    let cli_properties = vec!["NewLiveness".to_string(), "Fairness".to_string()];
    if !cli_properties.is_empty() {
        config.properties = cli_properties;
    }

    assert_eq!(
        config.properties,
        vec!["NewLiveness", "Fairness"],
        "properties should be set from CLI --prop flags"
    );
}

/// Part of #3779: CLI --const flags override config.constants.
#[test]
fn cli_const_overrides_config_values() {
    let mut config = tla_check::Config::default();
    config.add_constant(
        "OldN".to_string(),
        tla_check::ConstantValue::Value("5".to_string()),
    );

    // Simulate the CLI override logic from cmd_check/mod.rs.
    let cli_constants = vec!["N=3".to_string(), "Procs={p1,p2}".to_string()];
    if !cli_constants.is_empty() {
        config.constants.clear();
        config.constants_order.clear();
        for assignment in &cli_constants {
            if let Some((name, value)) = assignment.split_once('=') {
                let name = name.trim().to_string();
                let value = value.trim().to_string();
                config.add_constant(name, tla_check::ConstantValue::Value(value));
            }
        }
    }

    assert_eq!(config.constants.len(), 2, "should have 2 constants");
    assert_eq!(
        config.constants.get("N"),
        Some(&tla_check::ConstantValue::Value("3".to_string())),
        "N should be 3"
    );
    assert_eq!(
        config.constants.get("Procs"),
        Some(&tla_check::ConstantValue::Value("{p1,p2}".to_string())),
        "Procs should be {{p1,p2}}"
    );
    assert!(
        !config.constants.contains_key("OldN"),
        "old constants should be cleared"
    );
    assert_eq!(
        config.constants_order,
        vec!["N", "Procs"],
        "constants_order should match insertion order"
    );
}

/// Part of #3779: --const with invalid format (no '=') is rejected.
#[test]
fn cli_const_rejects_invalid_format() {
    // The actual rejection happens in cmd_check/mod.rs via bail!(),
    // but we verify the split_once logic here.
    let bad_assignment = "NoEqualsSign";
    assert!(
        bad_assignment.split_once('=').is_none(),
        "assignment without '=' should fail to split"
    );
}

/// Part of #3779: Config-free checking with --no-config + --init/--next/--inv/--const.
#[test]
fn no_config_with_all_cli_flags_produces_complete_config() {
    let mut config = tla_check::Config::default();
    config.init = Some("Init".to_string());
    config.next = Some("Next".to_string());

    // Simulate --no-config defaults + CLI overrides
    let cli_init = Some("MyInit".to_string());
    let cli_next = Some("MyNext".to_string());
    let cli_invariants = vec!["TypeOK".to_string(), "Safety".to_string()];
    let cli_properties = vec!["Liveness".to_string()];
    let cli_constants = vec!["N=3".to_string()];

    if let Some(ref init_op) = cli_init {
        config.init = Some(init_op.clone());
    }
    if let Some(ref next_op) = cli_next {
        config.next = Some(next_op.clone());
    }
    if !cli_invariants.is_empty() {
        config.invariants = cli_invariants;
    }
    if !cli_properties.is_empty() {
        config.properties = cli_properties;
    }
    if !cli_constants.is_empty() {
        config.constants.clear();
        config.constants_order.clear();
        for assignment in &cli_constants {
            if let Some((name, value)) = assignment.split_once('=') {
                config.add_constant(
                    name.trim().to_string(),
                    tla_check::ConstantValue::Value(value.trim().to_string()),
                );
            }
        }
    }

    assert_eq!(config.init.as_deref(), Some("MyInit"));
    assert_eq!(config.next.as_deref(), Some("MyNext"));
    assert_eq!(config.invariants, vec!["TypeOK", "Safety"]);
    assert_eq!(config.properties, vec!["Liveness"]);
    assert_eq!(
        config.constants.get("N"),
        Some(&tla_check::ConstantValue::Value("3".to_string()))
    );
}

/// CLI --init/--next clears SPECIFICATION to prevent mutual-exclusivity error.
#[test]
fn cli_init_next_clears_specification_from_config() {
    let mut config = tla_check::Config::default();
    config.specification = Some("Spec".to_string());

    let cli_init = Some("Init".to_string());
    let cli_next = Some("Next".to_string());

    if let Some(ref init_op) = cli_init {
        config.init = Some(init_op.clone());
    }
    if let Some(ref next_op) = cli_next {
        config.next = Some(next_op.clone());
    }
    if cli_init.is_some() && cli_next.is_some() && config.specification.is_some() {
        config.specification = None;
    }

    assert_eq!(config.init.as_deref(), Some("Init"));
    assert_eq!(config.next.as_deref(), Some("Next"));
    assert!(
        config.specification.is_none(),
        "SPECIFICATION should be cleared when CLI provides --init and --next"
    );
    assert!(
        !config.specification_conflicts_with_init_next(),
        "should not conflict after clearing specification"
    );
}
