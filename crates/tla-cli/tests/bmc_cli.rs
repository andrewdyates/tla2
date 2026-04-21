// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(feature = "z4")]

use std::time::Duration;

mod common;

fn assert_bmc_conflicts_with(flag: &str) {
    let args: Vec<&str> = vec!["check", "dummy.tla", "--bmc", "5", flag];
    let (code, _stdout, stderr) = common::run_tla_parsed(&args);
    assert_ne!(
        code, 0,
        "--bmc 5 {flag} should be rejected, but exited 0.\nstderr: {stderr}"
    );
    assert!(
        stderr.contains("cannot be used with") || stderr.contains("conflict"),
        "--bmc 5 {flag} should produce a conflict error.\nstderr: {stderr}"
    );
}

fn run_bmc(args: &[&str]) -> (i32, String, String) {
    common::run_tla_parsed_with_timeout(args, Duration::from_secs(10))
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_rejects_workers() {
    assert_bmc_conflicts_with("--workers=2");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_rejects_no_deadlock() {
    assert_bmc_conflicts_with("--no-deadlock");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_rejects_tlc_tool_output() {
    let dir = common::TempDir::new("bmc-tool");
    let (spec, cfg) = common::write_spec_and_config(
        &dir,
        "BmcTool",
        r#"---- MODULE BmcTool ----
VARIABLE x
Init == x = 0
Next == x' = x
Safety == x = 0
===="#,
        "INIT Init\nNEXT Next\nINVARIANT Safety\n",
    );

    let spec_str = spec.to_str().unwrap();
    let cfg_str = cfg.to_str().unwrap();
    let args = vec![
        "check",
        spec_str,
        "--config",
        cfg_str,
        "--bmc",
        "1",
        "--tool",
        "--soundness",
        "heuristic",
    ];
    let (code, stdout, stderr) = run_bmc(&args);

    assert_ne!(
        code, 0,
        "BMC tool mode should fail\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    let combined = format!("{stdout}\n{stderr}");
    assert!(
        combined.contains("BMC output is not supported in --output tlc-tool mode"),
        "unexpected output\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_unsafe_counter_reports_violation() {
    let dir = common::TempDir::new("bmc-unsafe");
    let (spec, cfg) = common::write_spec_and_config(
        &dir,
        "BmcUnsafe",
        r#"---- MODULE BmcUnsafe ----
VARIABLE count
Init == count = 0
Next == count' = count + 1
Safety == count <= 1
===="#,
        "INIT Init\nNEXT Next\nINVARIANT Safety\n",
    );

    let spec_str = spec.to_str().unwrap();
    let cfg_str = cfg.to_str().unwrap();
    let args = vec![
        "check",
        spec_str,
        "--config",
        cfg_str,
        "--bmc",
        "5",
        "--soundness",
        "heuristic",
    ];
    let (code, stdout, stderr) = run_bmc(&args);

    assert_ne!(
        code, 0,
        "unsafe BMC run should fail\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stderr.contains("BMC: VIOLATION"),
        "expected violation output\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stderr.contains("depth 2"),
        "expected earliest violation depth in output\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_safe_counter_reports_bound_reached() {
    let dir = common::TempDir::new("bmc-safe");
    let (spec, cfg) = common::write_spec_and_config(
        &dir,
        "BmcSafe",
        r#"---- MODULE BmcSafe ----
VARIABLE x
Init == x \in {0, 1}
Next == x' = x
Safety == x >= 0
===="#,
        "INIT Init\nNEXT Next\nINVARIANT Safety\n",
    );

    let spec_str = spec.to_str().unwrap();
    let cfg_str = cfg.to_str().unwrap();
    let args = vec![
        "check",
        spec_str,
        "--config",
        cfg_str,
        "--bmc",
        "5",
        "--soundness",
        "heuristic",
    ];
    let (code, stdout, stderr) = run_bmc(&args);

    assert_eq!(
        code, 0,
        "safe BMC run should succeed\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stdout.contains("BMC: NO BUG FOUND up to depth 5."),
        "expected bound-reached output\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}
