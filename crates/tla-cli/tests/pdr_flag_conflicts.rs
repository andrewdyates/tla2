// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for #3576: --pdr rejects unsupported explicit-state flags.
//!
//! These tests verify that clap rejects unsupported flag combinations at the
//! CLI level, before any spec parsing or model checking occurs.
//!
//! Run with: `cargo test -p tla-cli --features z4 --test pdr_flag_conflicts`
//! The --pdr CLI flag requires the z4 feature.

#![cfg(feature = "z4")]

mod common;

/// Helper: run tla2 with --pdr and an extra flag, expect clap conflict error.
fn assert_pdr_conflicts_with(flag: &str) {
    // Clap rejects conflicting args before looking at positional args,
    // so we don't need a real spec file.
    let args: Vec<&str> = vec!["check", "dummy.tla", "--pdr", flag];
    let (code, _stdout, stderr) = common::run_tla_parsed(&args);
    assert_ne!(
        code, 0,
        "--pdr {flag} should be rejected, but exited 0.\nstderr: {stderr}"
    );
    assert!(
        stderr.contains("cannot be used with") || stderr.contains("conflict"),
        "--pdr {flag} should produce a conflict error.\nstderr: {stderr}"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pdr_rejects_por() {
    assert_pdr_conflicts_with("--por");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pdr_rejects_coverage() {
    assert_pdr_conflicts_with("--coverage");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pdr_rejects_no_deadlock() {
    assert_pdr_conflicts_with("--no-deadlock");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pdr_rejects_max_states() {
    assert_pdr_conflicts_with("--max-states=100");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pdr_rejects_max_depth() {
    assert_pdr_conflicts_with("--max-depth=50");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pdr_rejects_store_states() {
    assert_pdr_conflicts_with("--store-states");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pdr_rejects_checkpoint() {
    assert_pdr_conflicts_with("--checkpoint=/tmp");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pdr_rejects_resume() {
    assert_pdr_conflicts_with("--resume=/tmp");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pdr_rejects_continue_on_error() {
    assert_pdr_conflicts_with("--continue-on-error");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pdr_rejects_profile_enum() {
    assert_pdr_conflicts_with("--profile-enum");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pdr_rejects_difftrace() {
    assert_pdr_conflicts_with("--difftrace");
}

/// Verify that --pdr alone (no conflicting flags) is accepted by clap.
/// The command will fail later (no real spec file), but it should NOT fail
/// due to argument conflicts.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pdr_alone_accepted_by_clap() {
    let dir = common::TempDir::new("pdr-alone");
    let (spec, cfg) = common::write_spec_and_config(
        &dir,
        "PdrAlone",
        r#"---- MODULE PdrAlone ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
Safety == x >= 0
===="#,
        "INIT Init\nNEXT Next\nINVARIANT Safety\n",
    );

    let spec_str = spec.to_str().unwrap();
    let cfg_str = cfg.to_str().unwrap();
    let args = vec!["check", spec_str, "--config", cfg_str, "--pdr"];
    let (_code, _stdout, stderr) = common::run_tla_parsed(&args);
    // Should not contain clap conflict error
    assert!(
        !stderr.contains("cannot be used with"),
        "--pdr alone should not trigger conflicts.\nstderr: {stderr}"
    );
}
