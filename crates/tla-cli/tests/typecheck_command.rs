// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration tests for `tla2 typecheck`.
//!
//! Part of #3791: standalone type checking command.

mod common;
use common::{run_tla_parsed, TempDir};

fn write_spec(dir: &TempDir, name: &str, source: &str) -> std::path::PathBuf {
    let path = dir.path.join(format!("{name}.tla"));
    std::fs::write(&path, source).expect("write spec");
    path
}

// ---------------------------------------------------------------------------
// Success cases
// ---------------------------------------------------------------------------

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn typecheck_well_typed_spec_exits_zero() {
    let dir = TempDir::new("typecheck-ok");
    let spec = write_spec(
        &dir,
        "Good",
        r#"
---- MODULE Good ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
TypeOK == x \in Int
====
"#,
    );

    let (code, stdout, stderr) = run_tla_parsed(&["typecheck", spec.to_str().unwrap()]);
    assert_eq!(
        code, 0,
        "expected exit 0 for well-typed spec\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stdout.contains("Module: Good"),
        "expected module name in output\nstdout:\n{stdout}"
    );
    assert!(
        stdout.contains("Type check passed"),
        "expected success summary\nstdout:\n{stdout}"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn typecheck_json_output_is_parseable() {
    let dir = TempDir::new("typecheck-json");
    let spec = write_spec(
        &dir,
        "JsonSpec",
        r#"
---- MODULE JsonSpec ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
====
"#,
    );

    let (code, stdout, stderr) =
        run_tla_parsed(&["typecheck", spec.to_str().unwrap(), "--output", "json"]);
    assert_eq!(
        code, 0,
        "expected exit 0\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    let json: serde_json::Value =
        serde_json::from_str(&stdout).expect("stdout should be valid JSON");
    assert_eq!(
        json["module"].as_str(),
        Some("JsonSpec"),
        "JSON module name mismatch"
    );
    assert!(
        json["file"].as_str().is_some(),
        "JSON should include file path"
    );
    assert!(
        json["operators"].is_array(),
        "JSON should have operators array"
    );
    assert!(json["errors"].is_array(), "JSON should have errors array");
    assert_eq!(
        json["errors"].as_array().unwrap().len(),
        0,
        "expected 0 errors for well-typed spec"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn typecheck_json_file_field_matches_input_path() {
    let dir = TempDir::new("typecheck-json-file");
    let spec = write_spec(
        &dir,
        "FilePath",
        r#"
---- MODULE FilePath ----
Foo == TRUE
====
"#,
    );

    let spec_str = spec.to_str().unwrap();
    let (code, stdout, _stderr) = run_tla_parsed(&["typecheck", spec_str, "--output", "json"]);
    assert_eq!(code, 0);

    let json: serde_json::Value = serde_json::from_str(&stdout).unwrap();
    assert_eq!(
        json["file"].as_str(),
        Some(spec_str),
        "JSON file field should match the input path"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn typecheck_human_output_shows_file_path() {
    let dir = TempDir::new("typecheck-human-file");
    let spec = write_spec(
        &dir,
        "HumanFile",
        r#"
---- MODULE HumanFile ----
Foo == 1 + 2
====
"#,
    );

    let spec_str = spec.to_str().unwrap();
    let (code, stdout, _stderr) = run_tla_parsed(&["typecheck", spec_str]);
    assert_eq!(code, 0);
    assert!(
        stdout.contains(&format!("File: {spec_str}")),
        "expected file path in human output\nstdout:\n{stdout}"
    );
}

// ---------------------------------------------------------------------------
// --infer-types flag
// ---------------------------------------------------------------------------

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn typecheck_infer_types_shows_variable_types() {
    let dir = TempDir::new("typecheck-infer");
    let spec = write_spec(
        &dir,
        "Infer",
        r#"
---- MODULE Infer ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
====
"#,
    );

    let (code, stdout, _stderr) =
        run_tla_parsed(&["typecheck", spec.to_str().unwrap(), "--infer-types"]);
    assert_eq!(code, 0);
    assert!(
        stdout.contains("Variables"),
        "expected variable section with --infer-types\nstdout:\n{stdout}"
    );
}

// ---------------------------------------------------------------------------
// Operator types
// ---------------------------------------------------------------------------

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn typecheck_reports_operator_types() {
    let dir = TempDir::new("typecheck-ops");
    let spec = write_spec(
        &dir,
        "Ops",
        r#"
---- MODULE Ops ----
BoolOp == TRUE /\ FALSE
IntOp == 1 + 2
SetOp == {1, 2, 3}
====
"#,
    );

    let (code, stdout, _stderr) =
        run_tla_parsed(&["typecheck", spec.to_str().unwrap(), "--output", "json"]);
    assert_eq!(code, 0);

    let json: serde_json::Value = serde_json::from_str(&stdout).unwrap();
    let ops = json["operators"].as_array().unwrap();

    let bool_op = ops.iter().find(|o| o["name"] == "BoolOp").unwrap();
    assert_eq!(bool_op["body_type"].as_str(), Some("Bool"));

    let int_op = ops.iter().find(|o| o["name"] == "IntOp").unwrap();
    assert_eq!(int_op["body_type"].as_str(), Some("Int"));

    let set_op = ops.iter().find(|o| o["name"] == "SetOp").unwrap();
    let set_type = set_op["body_type"].as_str().unwrap();
    // Set enums may infer as Set(Int) or Set(Dyn) depending on TIR type propagation
    assert!(
        set_type.starts_with("Set("),
        "expected Set type, got: {set_type}"
    );
}

// ---------------------------------------------------------------------------
// Annotation mismatch errors
// ---------------------------------------------------------------------------

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn typecheck_annotation_mismatch_exits_one() {
    let dir = TempDir::new("typecheck-ann-err");
    let spec = write_spec(
        &dir,
        "AnnMismatch",
        r#"
---- MODULE AnnMismatch ----
\* @type: Str;
Foo == 42
====
"#,
    );

    let (code, stdout, stderr) = run_tla_parsed(&["typecheck", spec.to_str().unwrap()]);
    assert_eq!(
        code, 1,
        "expected exit 1 for annotation mismatch\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stdout.contains("annotation mismatch"),
        "expected mismatch error in output\nstdout:\n{stdout}"
    );
    assert!(
        stdout.contains("FAILED"),
        "expected FAILED in summary\nstdout:\n{stdout}"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn typecheck_annotation_mismatch_json_has_location() {
    let dir = TempDir::new("typecheck-ann-loc");
    let spec = write_spec(
        &dir,
        "AnnLoc",
        r#"
---- MODULE AnnLoc ----
\* @type: Str;
Foo == 42
====
"#,
    );

    let spec_str = spec.to_str().unwrap();
    let (code, stdout, _stderr) = run_tla_parsed(&["typecheck", spec_str, "--output", "json"]);
    assert_eq!(code, 1);

    let json: serde_json::Value = serde_json::from_str(&stdout).unwrap();
    let errors = json["errors"].as_array().unwrap();
    assert!(!errors.is_empty(), "expected at least one error");

    let err = &errors[0];
    let location = &err["location"];
    assert!(
        location["file"].as_str().is_some(),
        "error location should have file path"
    );
    assert!(
        location["line"].as_u64().unwrap() > 0,
        "error location should have non-zero line"
    );
}

// ---------------------------------------------------------------------------
// Parse error handling
// ---------------------------------------------------------------------------

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn typecheck_parse_error_exits_nonzero() {
    let dir = TempDir::new("typecheck-parse-err");
    let spec = write_spec(
        &dir,
        "Bad",
        r#"
---- MODULE Bad ----
This is not valid TLA+ syntax !!!
====
"#,
    );

    let (code, _stdout, stderr) = run_tla_parsed(&["typecheck", spec.to_str().unwrap()]);
    assert_ne!(
        code, 0,
        "expected non-zero exit for parse error\nstderr:\n{stderr}"
    );
}

// ---------------------------------------------------------------------------
// Constants and variables
// ---------------------------------------------------------------------------

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn typecheck_json_reports_constants_and_variables() {
    let dir = TempDir::new("typecheck-const-var");
    let spec = write_spec(
        &dir,
        "ConstVar",
        r#"
---- MODULE ConstVar ----
CONSTANT N
VARIABLE x, y
Init == x = 0 /\ y = 0
Next == x' = x + 1 /\ y' = y + N
====
"#,
    );

    let (code, stdout, _stderr) =
        run_tla_parsed(&["typecheck", spec.to_str().unwrap(), "--output", "json"]);
    assert_eq!(code, 0);

    let json: serde_json::Value = serde_json::from_str(&stdout).unwrap();
    assert_eq!(
        json["constants"].as_array().unwrap(),
        &["N"],
        "expected CONSTANT N"
    );
    let var_names: Vec<&str> = json["variables"]
        .as_array()
        .unwrap()
        .iter()
        .map(|v| v["name"].as_str().unwrap())
        .collect();
    assert!(var_names.contains(&"x"), "expected variable x");
    assert!(var_names.contains(&"y"), "expected variable y");
}

// ---------------------------------------------------------------------------
// Summary counts
// ---------------------------------------------------------------------------

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn typecheck_json_summary_counts_operators() {
    let dir = TempDir::new("typecheck-summary");
    let spec = write_spec(
        &dir,
        "Summary",
        r#"
---- MODULE Summary ----
A == TRUE
B == 42
C == {1, 2}
====
"#,
    );

    let (code, stdout, _stderr) =
        run_tla_parsed(&["typecheck", spec.to_str().unwrap(), "--output", "json"]);
    assert_eq!(code, 0);

    let json: serde_json::Value = serde_json::from_str(&stdout).unwrap();
    let summary = &json["summary"];
    assert_eq!(
        summary["total_operators"].as_u64(),
        Some(3),
        "expected 3 operators"
    );
    assert_eq!(
        summary["total_errors"].as_u64(),
        Some(0),
        "expected 0 errors"
    );
}

// ---------------------------------------------------------------------------
// @type: annotation extraction
// ---------------------------------------------------------------------------

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn typecheck_json_reports_annotations() {
    let dir = TempDir::new("typecheck-annotations");
    let spec = write_spec(
        &dir,
        "Ann",
        r#"
---- MODULE Ann ----
\* @type: Bool;
Foo == TRUE
\* @type: Int;
Bar == 42
====
"#,
    );

    let (code, stdout, _stderr) =
        run_tla_parsed(&["typecheck", spec.to_str().unwrap(), "--output", "json"]);
    assert_eq!(code, 0);

    let json: serde_json::Value = serde_json::from_str(&stdout).unwrap();
    let annotations = json["annotations"].as_array().unwrap();
    assert_eq!(annotations.len(), 2);
    assert_eq!(annotations[0]["operator"].as_str(), Some("Foo"));
    assert_eq!(annotations[0]["annotation"].as_str(), Some("Bool"));
    assert_eq!(annotations[1]["operator"].as_str(), Some("Bar"));
    assert_eq!(annotations[1]["annotation"].as_str(), Some("Int"));
}

// ---------------------------------------------------------------------------
// Parameterized operators
// ---------------------------------------------------------------------------

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn typecheck_json_reports_parameterized_operator_params() {
    let dir = TempDir::new("typecheck-params");
    let spec = write_spec(
        &dir,
        "Params",
        r#"
---- MODULE Params ----
Add(a, b) == a + b
====
"#,
    );

    let (code, stdout, _stderr) =
        run_tla_parsed(&["typecheck", spec.to_str().unwrap(), "--output", "json"]);
    assert_eq!(code, 0);

    let json: serde_json::Value = serde_json::from_str(&stdout).unwrap();
    let ops = json["operators"].as_array().unwrap();
    let add = ops.iter().find(|o| o["name"] == "Add").unwrap();
    assert_eq!(
        add["params"].as_array().unwrap(),
        &["a", "b"],
        "expected params [a, b]"
    );
}
