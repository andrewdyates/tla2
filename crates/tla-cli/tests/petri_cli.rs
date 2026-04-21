// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Integration tests for `tla2 petri`, `tla2 mcc`, and `tla2 petri-simplify`
//! CLI subcommands.

use std::time::Duration;

mod common;

/// Minimal P/T net: two places, one transition (P0 -> T0 -> P1), initial marking [1, 0].
const SIMPLE_PNML: &str = r#"<?xml version="1.0"?>
<pnml xmlns="http://www.pnml.org/version-2009/grammar/pnml">
  <net id="TestNet" type="http://www.pnml.org/version-2009/grammar/ptnet">
    <name><text>TestNet</text></name>
    <page id="p1">
      <place id="P0"><initialMarking><text>1</text></initialMarking></place>
      <place id="P1"/>
      <transition id="T0"><name><text>fire</text></name></transition>
      <arc id="a1" source="P0" target="T0"/>
      <arc id="a2" source="T0" target="P1"/>
    </page>
  </net>
</pnml>"#;

/// ReachabilityFireability property XML with one formula: EF is-fireable(T0).
const REACHABILITY_FIREABILITY_XML: &str = r#"<?xml version="1.0"?>
<property-set xmlns="http://mcc.lip6.fr/pnml">
  <property>
    <id>TestNet-ReachabilityFireability-0</id>
    <description>Can T0 fire?</description>
    <formula>
      <exists-path>
        <finally>
          <is-fireable>
            <transition>T0</transition>
          </is-fireable>
        </finally>
      </exists-path>
    </formula>
  </property>
</property-set>"#;

fn write_model_dir(dir: &common::TempDir) {
    std::fs::write(dir.path.join("model.pnml"), SIMPLE_PNML).expect("write model.pnml");
}

fn write_model_dir_with_properties(dir: &common::TempDir) {
    write_model_dir(dir);
    std::fs::write(
        dir.path.join("ReachabilityFireability.xml"),
        REACHABILITY_FIREABILITY_XML,
    )
    .expect("write ReachabilityFireability.xml");
}

fn run_petri(args: &[&str]) -> (i32, String, String) {
    common::run_tla_parsed_with_timeout(args, Duration::from_secs(30))
}

// ---------------------------------------------------------------------------
// tla2 petri
// ---------------------------------------------------------------------------

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn petri_reachability_deadlock_succeeds() {
    let dir = common::TempDir::new("petri-deadlock");
    write_model_dir(&dir);
    let model_path = dir.path.join("model.pnml");

    let (code, stdout, stderr) = run_petri(&[
        "petri",
        model_path.to_str().unwrap(),
        "--examination",
        "ReachabilityDeadlock",
    ]);
    assert_eq!(
        code, 0,
        "petri ReachabilityDeadlock should succeed.\nstdout: {stdout}\nstderr: {stderr}"
    );
    assert!(
        stdout.contains("FORMULA") && stdout.contains("TECHNIQUES"),
        "output should contain MCC FORMULA line.\nstdout: {stdout}"
    );
}

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn petri_state_space_succeeds() {
    let dir = common::TempDir::new("petri-statespace");
    write_model_dir(&dir);
    let model_path = dir.path.join("model.pnml");

    let (code, stdout, stderr) = run_petri(&[
        "petri",
        model_path.to_str().unwrap(),
        "--examination",
        "StateSpace",
    ]);
    assert_eq!(
        code, 0,
        "petri StateSpace should succeed.\nstdout: {stdout}\nstderr: {stderr}"
    );
    // StateSpace prints STATE_SPACE lines, not FORMULA.
    assert!(
        stdout.contains("STATE_SPACE") || stdout.contains("FORMULA"),
        "output should contain state-space or formula info.\nstdout: {stdout}"
    );
}

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn petri_reachability_fireability_succeeds() {
    let dir = common::TempDir::new("petri-reach-fire");
    write_model_dir_with_properties(&dir);
    let model_path = dir.path.join("model.pnml");

    let (code, stdout, stderr) = run_petri(&[
        "petri",
        model_path.to_str().unwrap(),
        "--examination",
        "ReachabilityFireability",
    ]);
    assert_eq!(
        code, 0,
        "petri ReachabilityFireability should succeed.\nstdout: {stdout}\nstderr: {stderr}"
    );
    assert!(
        stdout.contains("FORMULA"),
        "output should contain FORMULA line.\nstdout: {stdout}"
    );
}

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn petri_one_safe_succeeds() {
    let dir = common::TempDir::new("petri-onesafe");
    write_model_dir(&dir);
    let model_path = dir.path.join("model.pnml");

    let (code, stdout, stderr) = run_petri(&[
        "petri",
        model_path.to_str().unwrap(),
        "--examination",
        "OneSafe",
    ]);
    assert_eq!(
        code, 0,
        "petri OneSafe should succeed.\nstdout: {stdout}\nstderr: {stderr}"
    );
    assert!(
        stdout.contains("FORMULA"),
        "output should contain FORMULA line.\nstdout: {stdout}"
    );
}

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn petri_quasi_liveness_succeeds() {
    let dir = common::TempDir::new("petri-quasilive");
    write_model_dir(&dir);
    let model_path = dir.path.join("model.pnml");

    let (code, stdout, stderr) = run_petri(&[
        "petri",
        model_path.to_str().unwrap(),
        "--examination",
        "QuasiLiveness",
    ]);
    assert_eq!(
        code, 0,
        "petri QuasiLiveness should succeed.\nstdout: {stdout}\nstderr: {stderr}"
    );
    assert!(
        stdout.contains("FORMULA"),
        "output should contain FORMULA line.\nstdout: {stdout}"
    );
}

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn petri_stable_marking_succeeds() {
    let dir = common::TempDir::new("petri-stablemark");
    write_model_dir(&dir);
    let model_path = dir.path.join("model.pnml");

    let (code, stdout, stderr) = run_petri(&[
        "petri",
        model_path.to_str().unwrap(),
        "--examination",
        "StableMarking",
    ]);
    assert_eq!(
        code, 0,
        "petri StableMarking should succeed.\nstdout: {stdout}\nstderr: {stderr}"
    );
    assert!(
        stdout.contains("FORMULA"),
        "output should contain FORMULA line.\nstdout: {stdout}"
    );
}

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn petri_liveness_succeeds() {
    let dir = common::TempDir::new("petri-liveness");
    write_model_dir(&dir);
    let model_path = dir.path.join("model.pnml");

    let (code, stdout, stderr) = run_petri(&[
        "petri",
        model_path.to_str().unwrap(),
        "--examination",
        "Liveness",
    ]);
    assert_eq!(
        code, 0,
        "petri Liveness should succeed.\nstdout: {stdout}\nstderr: {stderr}"
    );
    assert!(
        stdout.contains("FORMULA"),
        "output should contain FORMULA line.\nstdout: {stdout}"
    );
}

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn petri_rejects_unknown_examination() {
    let dir = common::TempDir::new("petri-unknown-exam");
    write_model_dir(&dir);
    let model_path = dir.path.join("model.pnml");

    let (code, _stdout, stderr) = run_petri(&[
        "petri",
        model_path.to_str().unwrap(),
        "--examination",
        "BogusExamination",
    ]);
    assert_ne!(
        code, 0,
        "petri BogusExamination should fail.\nstderr: {stderr}"
    );
}

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn petri_rejects_missing_model() {
    let (code, _stdout, stderr) = run_petri(&[
        "petri",
        "/tmp/nonexistent-model-dir/model.pnml",
        "--examination",
        "ReachabilityDeadlock",
    ]);
    assert_ne!(
        code, 0,
        "petri with missing model should fail.\nstderr: {stderr}"
    );
}

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn petri_threads_flag_accepted() {
    let dir = common::TempDir::new("petri-threads");
    write_model_dir(&dir);
    let model_path = dir.path.join("model.pnml");

    let (code, stdout, stderr) = run_petri(&[
        "petri",
        model_path.to_str().unwrap(),
        "--examination",
        "ReachabilityDeadlock",
        "--threads",
        "2",
    ]);
    assert_eq!(
        code, 0,
        "petri with --threads 2 should succeed.\nstdout: {stdout}\nstderr: {stderr}"
    );
}

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn petri_storage_memory_flag_accepted() {
    let dir = common::TempDir::new("petri-storage");
    write_model_dir(&dir);
    let model_path = dir.path.join("model.pnml");

    let (code, stdout, stderr) = run_petri(&[
        "petri",
        model_path.to_str().unwrap(),
        "--examination",
        "ReachabilityDeadlock",
        "--storage",
        "memory",
    ]);
    assert_eq!(
        code, 0,
        "petri with --storage memory should succeed.\nstdout: {stdout}\nstderr: {stderr}"
    );
}

// ---------------------------------------------------------------------------
// tla2 mcc
// ---------------------------------------------------------------------------

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn mcc_with_dir_and_examination_succeeds() {
    let dir = common::TempDir::new("mcc-dir-exam");
    write_model_dir(&dir);

    let (code, stdout, stderr) = run_petri(&[
        "mcc",
        dir.path.to_str().unwrap(),
        "--examination",
        "ReachabilityDeadlock",
    ]);
    assert_eq!(
        code, 0,
        "mcc with dir and --examination should succeed.\nstdout: {stdout}\nstderr: {stderr}"
    );
    assert!(
        stdout.contains("FORMULA"),
        "output should contain FORMULA line.\nstdout: {stdout}"
    );
}

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn mcc_uses_bk_env_vars() {
    let dir = common::TempDir::new("mcc-bk-env");
    write_model_dir(&dir);
    let dir_str = dir.path.to_str().unwrap();

    let (code, stdout, stderr) = common::run_tla_parsed_with_env_timeout(
        &["mcc"],
        &[
            ("BK_INPUT", dir_str),
            ("BK_EXAMINATION", "ReachabilityDeadlock"),
        ],
        &[],
        Duration::from_secs(30),
    );
    assert_eq!(
        code, 0,
        "mcc with BK_INPUT/BK_EXAMINATION should succeed.\nstdout: {stdout}\nstderr: {stderr}"
    );
    assert!(
        stdout.contains("FORMULA"),
        "output should contain FORMULA line.\nstdout: {stdout}"
    );
}

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn mcc_fails_without_examination() {
    let dir = common::TempDir::new("mcc-no-exam");
    write_model_dir(&dir);

    // Remove BK_EXAMINATION from env to ensure it's truly missing.
    let (code, _stdout, stderr) = common::run_tla_parsed_with_env_timeout(
        &["mcc", dir.path.to_str().unwrap()],
        &[],
        &["BK_EXAMINATION"],
        Duration::from_secs(10),
    );
    assert_ne!(
        code, 0,
        "mcc without examination should fail.\nstderr: {stderr}"
    );
    assert!(
        stderr.contains("examination not specified"),
        "error should mention missing examination.\nstderr: {stderr}"
    );
}

// ---------------------------------------------------------------------------
// tla2 petri-simplify
// ---------------------------------------------------------------------------

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn petri_simplify_produces_json() {
    let dir = common::TempDir::new("petri-simplify");
    write_model_dir_with_properties(&dir);

    let (code, stdout, stderr) = run_petri(&[
        "petri-simplify",
        dir.path.to_str().unwrap(),
        "--examination",
        "ReachabilityFireability",
    ]);
    assert_eq!(
        code, 0,
        "petri-simplify should succeed.\nstdout: {stdout}\nstderr: {stderr}"
    );

    // Verify output is valid JSON with expected fields.
    let json: serde_json::Value =
        serde_json::from_str(&stdout).expect("output should be valid JSON");
    assert!(
        json.get("model_name").is_some(),
        "JSON should have model_name field.\nstdout: {stdout}"
    );
    assert!(
        json.get("examination").is_some(),
        "JSON should have examination field.\nstdout: {stdout}"
    );
    assert!(
        json.get("summary").is_some(),
        "JSON should have summary field.\nstdout: {stdout}"
    );
    assert!(
        json.get("properties").is_some(),
        "JSON should have properties field.\nstdout: {stdout}"
    );
    assert_eq!(
        json["examination"].as_str(),
        Some("ReachabilityFireability"),
        "examination field should match."
    );
    assert_eq!(
        json["source_kind"].as_str(),
        Some("ptnet"),
        "source_kind should be ptnet."
    );
}

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn petri_simplify_rejects_non_property_examination() {
    let dir = common::TempDir::new("petri-simplify-bad");
    write_model_dir(&dir);

    let (code, _stdout, stderr) = run_petri(&[
        "petri-simplify",
        dir.path.to_str().unwrap(),
        "--examination",
        "ReachabilityDeadlock",
    ]);
    assert_ne!(
        code, 0,
        "petri-simplify with ReachabilityDeadlock should fail (no property XML).\nstderr: {stderr}"
    );
}

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn petri_simplify_rejects_missing_model() {
    let (code, _stdout, stderr) = run_petri(&[
        "petri-simplify",
        "/tmp/nonexistent-model-dir",
        "--examination",
        "ReachabilityFireability",
    ]);
    assert_ne!(
        code, 0,
        "petri-simplify with missing model should fail.\nstderr: {stderr}"
    );
}
