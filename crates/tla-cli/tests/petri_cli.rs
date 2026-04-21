// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
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
// MCC format compliance: all non-property examinations produce valid output
// ---------------------------------------------------------------------------

/// Validate that a stdout line matches the MCC FORMULA output format.
/// Returns true if valid, false otherwise.
fn validate_mcc_formula_line(line: &str) -> bool {
    if !line.starts_with("FORMULA ") {
        return false;
    }
    if !line.contains(" TECHNIQUES ") {
        return false;
    }
    // Must end with technique name(s) — uppercase letters and underscores
    let after_techniques = line.split(" TECHNIQUES ").last().unwrap_or("");
    !after_techniques.trim().is_empty()
}

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn mcc_format_compliance_all_non_property_examinations() {
    // All 6 non-property examinations must produce valid FORMULA lines
    let non_property_exams = [
        "ReachabilityDeadlock",
        "StateSpace",
        "OneSafe",
        "QuasiLiveness",
        "StableMarking",
        "Liveness",
    ];

    let dir = common::TempDir::new("mcc-format-all");
    write_model_dir(&dir);

    for exam in non_property_exams {
        let (code, stdout, stderr) = run_petri(&[
            "mcc",
            dir.path.to_str().unwrap(),
            "--examination",
            exam,
        ]);
        assert_eq!(
            code, 0,
            "mcc {exam} should succeed.\nstdout: {stdout}\nstderr: {stderr}"
        );

        // Every non-empty stdout line must be a valid FORMULA line
        let formula_lines: Vec<&str> = stdout
            .lines()
            .filter(|l| !l.trim().is_empty())
            .collect();
        assert!(
            !formula_lines.is_empty(),
            "mcc {exam} should produce at least one FORMULA line.\nstdout: {stdout}"
        );
        for line in &formula_lines {
            assert!(
                validate_mcc_formula_line(line),
                "mcc {exam}: invalid MCC line format: '{line}'\nfull stdout: {stdout}"
            );
        }

        // Verify no debug/log output leaked to stdout
        for line in stdout.lines() {
            let trimmed = line.trim();
            if trimmed.is_empty() {
                continue;
            }
            assert!(
                trimmed.starts_with("FORMULA ") || trimmed.starts_with("STATE_SPACE"),
                "mcc {exam}: non-FORMULA output on stdout: '{trimmed}'"
            );
        }
    }
}

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn mcc_format_compliance_property_examination_without_xml_produces_cannot_compute() {
    // Property examinations without XML should produce CANNOT_COMPUTE
    let property_exams = [
        "ReachabilityCardinality",
        "ReachabilityFireability",
        "CTLCardinality",
        "CTLFireability",
        "LTLCardinality",
        "LTLFireability",
        "UpperBounds",
    ];

    let dir = common::TempDir::new("mcc-format-noprop");
    write_model_dir(&dir);
    // No property XML files written — just model.pnml

    for exam in property_exams {
        let (code, stdout, stderr) = run_petri(&[
            "mcc",
            dir.path.to_str().unwrap(),
            "--examination",
            exam,
        ]);
        // Should either succeed with CANNOT_COMPUTE or fail gracefully
        if code == 0 {
            // If it succeeds, stdout should contain CANNOT_COMPUTE
            let has_formula = stdout.contains("FORMULA");
            let has_cannot = stdout.contains("CANNOT_COMPUTE");
            assert!(
                has_formula || has_cannot,
                "mcc {exam}: succeeded but no FORMULA/CANNOT_COMPUTE output.\nstdout: {stdout}\nstderr: {stderr}"
            );
        }
        // Non-zero exit is also acceptable for missing XML (error reported on stderr)
    }
}

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn mcc_format_compliance_reachability_fireability_with_xml() {
    // With property XML, should produce valid FORMULA lines with TRUE/FALSE verdicts
    let dir = common::TempDir::new("mcc-format-props");
    write_model_dir_with_properties(&dir);

    let (code, stdout, stderr) = run_petri(&[
        "mcc",
        dir.path.to_str().unwrap(),
        "--examination",
        "ReachabilityFireability",
    ]);
    assert_eq!(
        code, 0,
        "mcc ReachabilityFireability with XML should succeed.\nstdout: {stdout}\nstderr: {stderr}"
    );

    let formula_lines: Vec<&str> = stdout
        .lines()
        .filter(|l| l.starts_with("FORMULA "))
        .collect();
    assert!(
        !formula_lines.is_empty(),
        "should produce at least one FORMULA line"
    );
    for line in &formula_lines {
        assert!(
            validate_mcc_formula_line(line),
            "invalid MCC format: {line}"
        );
        // Property verdicts should be TRUE, FALSE, or CANNOT_COMPUTE
        assert!(
            line.contains(" TRUE TECHNIQUES ")
                || line.contains(" FALSE TECHNIQUES ")
                || line.contains(" CANNOT_COMPUTE TECHNIQUES "),
            "property verdict should be TRUE/FALSE/CANNOT_COMPUTE: {line}"
        );
    }
}

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn mcc_bk_time_confinement_is_respected() {
    // BK_TIME_CONFINEMENT should be read and used as a deadline.
    // With a very short timeout, the tool should still exit cleanly (not crash).
    let dir = common::TempDir::new("mcc-timeout");
    write_model_dir(&dir);

    let (code, stdout, stderr) = common::run_tla_parsed_with_env_timeout(
        &[
            "mcc",
            dir.path.to_str().unwrap(),
            "--examination",
            "ReachabilityDeadlock",
        ],
        &[("BK_TIME_CONFINEMENT", "10")],
        &[],
        Duration::from_secs(30),
    );
    // Should exit cleanly (0) even with a tight timeout budget
    assert_eq!(
        code, 0,
        "mcc with BK_TIME_CONFINEMENT=10 should exit cleanly.\nstdout: {stdout}\nstderr: {stderr}"
    );
    // Should still produce FORMULA output (either a real answer or CANNOT_COMPUTE)
    assert!(
        stdout.contains("FORMULA"),
        "should produce FORMULA output even with timeout.\nstdout: {stdout}"
    );
}

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn mcc_stdout_only_formula_lines_no_debug() {
    // MCC infrastructure only parses FORMULA lines from stdout.
    // Any other output on stdout is a format violation.
    let dir = common::TempDir::new("mcc-clean-stdout");
    write_model_dir(&dir);

    let (code, stdout, _stderr) = run_petri(&[
        "mcc",
        dir.path.to_str().unwrap(),
        "--examination",
        "ReachabilityDeadlock",
    ]);
    assert_eq!(code, 0);

    for line in stdout.lines() {
        let trimmed = line.trim();
        if trimmed.is_empty() {
            continue;
        }
        // Only FORMULA lines should appear on stdout
        assert!(
            trimmed.starts_with("FORMULA "),
            "non-FORMULA output on stdout (format violation): '{trimmed}'"
        );
    }
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
