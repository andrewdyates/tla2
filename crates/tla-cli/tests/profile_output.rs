// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! CLI regression tests for profiling output (--profile-enum, --profile-eval,
//! --profile-enum-detail). Part of #3261.

mod common;
use common::TempDir;

/// Test that --profile-eval and --profile-enum emit their sections on a
/// bounded (--max-states) release run. Regression test for #3261 original
/// report: bounded runs suppressed profiling output.
#[test]
#[cfg_attr(test, ntest::timeout(10000))]
fn bounded_release_profile_eval_and_enum_emit_on_state_limit() {
    let dir = TempDir::new("profile-output-eval-enum");
    let (spec, cfg) = common::write_spec_and_config(
        &dir,
        "ProfileProbe",
        r#"---- MODULE ProfileProbe ----
EXTENDS Integers
VARIABLE x

Init == x = 0
Next == x' = x + 1 /\ x < 10
====
"#,
        "INIT Init\nNEXT Next\n",
    );

    let (code, _stdout, stderr) = common::run_tla_parsed_with_env(
        &[
            "check",
            spec.to_str().unwrap(),
            "--config",
            cfg.to_str().unwrap(),
            "--workers",
            "1",
            "--max-states",
            "5",
            "--profile-enum",
            "--profile-eval",
            "--force",
            "--no-deadlock",
        ],
        &[],
        &[],
    );

    assert_eq!(code, 0, "expected success, stderr:\n{stderr}");
    assert!(
        stderr.contains("=== Enumeration Profile ==="),
        "stderr missing enum profile section\nstderr:\n{stderr}"
    );
    assert!(
        stderr.contains("=== Eval Profile ==="),
        "stderr missing eval profile section\nstderr:\n{stderr}"
    );
}

/// Test that --profile-enum-detail emits its section when the symbolic-
/// assignment evaluation path is exercised. This requires disabling the
/// compiled action path (TLA2_NO_COMPILED_ACTION=1) since the compiled
/// path does not increment the detail profiling counter.
///
/// The canary spec uses `x' \in {x, x+1, x+2}` as a standalone Next
/// expression (not wrapped in conjunction), which goes through the
/// unified_dispatch catch-all → extract_symbolic_assignments →
/// evaluate_symbolic_assignments, which increments PROF_ASSIGN_US.
#[test]
#[cfg_attr(test, ntest::timeout(10000))]
fn bounded_release_profile_enum_detail_emits_on_symbolic_assignment_canary() {
    let dir = TempDir::new("profile-output-detail");
    let (spec, cfg) = common::write_spec_and_config(
        &dir,
        "DetailProbe",
        r#"---- MODULE DetailProbe ----
EXTENDS Integers
VARIABLE x

Init == x \in {0, 1, 2}
Next == x' \in {x, x + 1, x + 2}
====
"#,
        "INIT Init\nNEXT Next\n",
    );

    let (code, _stdout, stderr) = common::run_tla_parsed_with_env(
        &[
            "check",
            spec.to_str().unwrap(),
            "--config",
            cfg.to_str().unwrap(),
            "--workers",
            "1",
            "--max-states",
            "500",
            "--profile-enum-detail",
            "--force",
            "--no-deadlock",
        ],
        // Disable compiled actions so the symbolic-assignment path is used.
        // The compiled action path does not exercise the detail profiling
        // counters (PROF_ASSIGN_US is only incremented in
        // evaluate_symbolic_assignments, which the compiled path bypasses).
        &[("TLA2_NO_COMPILED_ACTION", "1")],
        &[],
    );

    assert_eq!(code, 0, "expected success, stderr:\n{stderr}");
    assert!(
        stderr.contains("=== Enumeration Detail Profile ==="),
        "stderr missing detail profile section\nstderr:\n{stderr}"
    );
}

#[test]
#[cfg_attr(test, ntest::timeout(10000))]
fn bounded_release_subset_profile_emits_on_constrained_exists_canary() {
    let dir = TempDir::new("subset-profile-output");
    let (spec, cfg) = common::write_spec_and_config(
        &dir,
        "SubsetProfileProbe",
        r#"---- MODULE SubsetProfileProbe ----
VARIABLE rcvd

P == {1}
M == {"ECHO0", "ECHO1"}
Sent == P \X M

Init ==
  /\ rcvd = [i \in P |-> {}]

Receive(self) ==
  \E r \in SUBSET(Sent):
      /\ r \subseteq Sent
      /\ rcvd[self] \subseteq r
      /\ rcvd' = [rcvd EXCEPT ![self] = r]

Next == Receive(1)
====
"#,
        "INIT Init\nNEXT Next\n",
    );

    let (code, _stdout, stderr) = common::run_tla_parsed_with_env(
        &[
            "check",
            spec.to_str().unwrap(),
            "--config",
            cfg.to_str().unwrap(),
            "--workers",
            "1",
            "--max-states",
            "10",
            "--force",
            "--no-deadlock",
        ],
        &[("TLA2_SUBSET_PROFILE", "1")],
        &[],
    );

    assert_eq!(code, 0, "expected success, stderr:\n{stderr}");
    assert!(
        stderr.contains("=== SUBSET Profile ==="),
        "stderr missing subset profile section\nstderr:\n{stderr}"
    );
    assert!(
        stderr.contains("  constrained entries:"),
        "subset profile missing constrained entries line\nstderr:\n{stderr}"
    );
}

#[test]
#[cfg_attr(test, ntest::timeout(10000))]
fn bounded_release_subset_profile_emits_on_unified_constrained_exists_canary() {
    let dir = TempDir::new("subset-profile-unified-output");
    let (spec, cfg) = common::write_spec_and_config(
        &dir,
        "SubsetProfileUnifiedProbe",
        r#"---- MODULE SubsetProfileUnifiedProbe ----
VARIABLE rcvd

P == {1}
M == {"ECHO0", "ECHO1"}
Sent == P \X M

Init ==
  /\ rcvd = [i \in P |-> {}]

Receive(self) ==
  \E r \in SUBSET(Sent):
      /\ r \subseteq Sent
      /\ rcvd[self] \subseteq r
      /\ rcvd' = [rcvd EXCEPT ![self] = r]

Next == Receive(1)
====
"#,
        "INIT Init\nNEXT Next\n",
    );

    let (code, _stdout, stderr) = common::run_tla_parsed_with_env(
        &[
            "check",
            spec.to_str().unwrap(),
            "--config",
            cfg.to_str().unwrap(),
            "--workers",
            "1",
            "--max-states",
            "10",
            "--force",
            "--no-deadlock",
        ],
        &[
            ("TLA2_SUBSET_PROFILE", "1"),
            ("TLA2_NO_COMPILED_ACTION", "1"),
        ],
        &[],
    );

    assert_eq!(code, 0, "expected success, stderr:\n{stderr}");
    let entries_line = stderr
        .lines()
        .find(|line| line.contains("constrained entries:"))
        .expect("subset profile missing constrained entries line");
    let entries = entries_line
        .split_whitespace()
        .last()
        .expect("subset profile entries line should end with a count")
        .parse::<usize>()
        .expect("subset profile entries count should parse");
    assert!(
        entries > 0,
        "expected unified-only run to hit constrained subset profiling, stderr:\n{stderr}"
    );
}
