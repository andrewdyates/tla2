// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration test exercising the pnml-tools public API surface.
//!
//! This test compiles as an external crate consumer, proving the facade
//! is coherent: types returned by the parser are usable with the explorer
//! and examination modules without reaching into crate-private internals.

use std::fs;
use std::io::Write;
use std::path::PathBuf;

use pnml_tools::examination::{
    collect_examination_with_dir, Examination, ExaminationRecord, ExaminationValue,
    StateSpaceReport, Verdict,
};
use pnml_tools::model::{collect_examination_for_model, load_model_dir, SourceNetKind};
use tempfile::TempDir;

/// Minimal PNML model: two places, one transition, one token.
const MINIMAL_PNML: &str = r#"<?xml version="1.0"?>
<pnml xmlns="http://www.pnml.org/version-2009/grammar/pnml">
  <net id="test" type="http://www.pnml.org/version-2009/grammar/ptnet">
    <page id="p1">
      <place id="P0"><initialMarking><text>1</text></initialMarking></place>
      <place id="P1"/>
      <transition id="T0"/>
      <arc id="a1" source="P0" target="T0"/>
      <arc id="a2" source="T0" target="P1"/>
    </page>
  </net>
</pnml>"#;

fn write_model(dir: &TempDir) {
    let path = dir.path().join("model.pnml");
    let mut f = std::fs::File::create(path).expect("create model.pnml");
    f.write_all(MINIMAL_PNML.as_bytes())
        .expect("write model.pnml");
}

fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
}

fn mcc_model_dir(model: &str) -> PathBuf {
    workspace_root()
        .join("benchmarks")
        .join("mcc")
        .join("2024")
        .join("INPUTS")
        .join(model)
}

fn has_mcc_benchmark(model: &str) -> bool {
    mcc_model_dir(model).join("model.pnml").exists()
}

#[test]
fn test_parse_returns_petri_net_via_crate_root() {
    let dir = TempDir::new().unwrap();
    write_model(&dir);

    let net: pnml_tools::PetriNet =
        pnml_tools::parser::parse_pnml_dir(dir.path()).expect("parse should succeed");

    assert_eq!(net.num_places(), 2);
    assert_eq!(net.num_transitions(), 1);
    assert_eq!(net.initial_marking, vec![1, 0]);
}

#[test]
fn test_place_and_transition_idx_types_accessible() {
    let dir = TempDir::new().unwrap();
    write_model(&dir);

    let net: pnml_tools::PetriNet = pnml_tools::parser::parse_pnml_dir(dir.path()).unwrap();

    // PlaceIdx and TransitionIdx are accessible via crate root
    let _place: pnml_tools::PlaceIdx = pnml_tools::PlaceIdx(0);
    let _trans: pnml_tools::TransitionIdx = pnml_tools::TransitionIdx(0);

    // PetriNet methods work with the index types
    assert!(net.is_enabled(&net.initial_marking, pnml_tools::TransitionIdx(0)));
}

#[test]
fn test_exploration_config_builder_api() {
    // ExplorationConfig is constructed via new() + chainable setters,
    // not struct literals (which #[non_exhaustive] prevents externally).
    let config = pnml_tools::explorer::ExplorationConfig::new(1000).with_workers(2);

    assert_eq!(config.max_states(), 1000);
    assert_eq!(config.workers(), 2);
    assert!(config.deadline().is_none());
}

#[test]
fn test_exploration_config_with_workers_clamps_zero() {
    let config = pnml_tools::explorer::ExplorationConfig::new(100).with_workers(0);

    assert_eq!(config.workers(), 1, "workers=0 should clamp to 1");
}

#[test]
fn test_exploration_config_default() {
    let config = pnml_tools::explorer::ExplorationConfig::default();

    assert_eq!(config.max_states(), 10_000_000);
    assert!(config.deadline().is_none());
    assert_eq!(config.workers(), 1);
}

#[test]
fn test_describe_auto_returns_auto_size_info() {
    let dir = TempDir::new().unwrap();
    write_model(&dir);

    let net = pnml_tools::parser::parse_pnml_dir(dir.path()).unwrap();
    let info = pnml_tools::explorer::ExplorationConfig::describe_auto(&net, None);

    assert_eq!(info.num_places, 2);
    assert!(info.packed_places <= info.num_places);
    assert!(info.bytes_per_place > 0);
    assert!(info.max_states > 0);
}

#[test]
fn test_auto_sized_config() {
    let dir = TempDir::new().unwrap();
    write_model(&dir);

    let net = pnml_tools::parser::parse_pnml_dir(dir.path()).unwrap();
    let config =
        pnml_tools::explorer::ExplorationConfig::auto_sized(&net, None, None).with_workers(2);

    assert!(config.max_states() > 0);
    assert_eq!(config.workers(), 2);
}

#[test]
fn test_examination_from_name() {
    let exam = pnml_tools::examination::Examination::from_name("ReachabilityDeadlock")
        .expect("valid examination name");
    assert_eq!(
        exam,
        pnml_tools::examination::Examination::ReachabilityDeadlock
    );
}

#[test]
fn test_error_type_accessible() {
    // PnmlError is accessible for match arms
    let dir = TempDir::new().unwrap();
    // No model.pnml in this directory
    let result = pnml_tools::parser::parse_pnml_dir(dir.path());
    assert!(result.is_err());
    match result.unwrap_err() {
        pnml_tools::error::PnmlError::Io { .. } => {}
        other => panic!("expected Io error, got: {other:?}"),
    }
}

#[test]
fn test_arc_type_accessible() {
    let dir = TempDir::new().unwrap();
    write_model(&dir);

    let net = pnml_tools::parser::parse_pnml_dir(dir.path()).unwrap();

    // Arc is accessible via crate root for inspecting transition structure
    let _arc: &pnml_tools::Arc = &net.transitions[0].inputs[0];
    assert_eq!(_arc.weight, 1);
}

// ---------------------------------------------------------------------------
// Typed examination result API (collect_examination_with_dir)
// ---------------------------------------------------------------------------

fn write_reachability_fireability_xml(dir: &TempDir) {
    // Property: EF(is-fireable(T0)) — T0 is fireable from initial state.
    let xml = r#"<?xml version="1.0"?>
<property-set xmlns="http://mcc.lip6.fr/">
  <property>
    <id>TestModel-ReachabilityFireability-00</id>
    <description>T0 fireable from initial</description>
    <formula>
      <exists-path>
        <finally>
          <is-fireable><transition>T0</transition></is-fireable>
        </finally>
      </exists-path>
    </formula>
  </property>
</property-set>"#;
    fs::write(dir.path().join("ReachabilityFireability.xml"), xml)
        .expect("write ReachabilityFireability.xml");
}

fn write_ctl_fireability_xml(dir: &TempDir) {
    // CTL property: EF(is-fireable(T0)) — there exists a path where T0 eventually fires.
    // In CTL, EF(phi) is TRUE iff some reachable state satisfies phi.
    // T0 is fireable in the initial state [1,0], so EF(is-fireable(T0)) = TRUE.
    let xml = r#"<?xml version="1.0"?>
<property-set xmlns="http://mcc.lip6.fr/">
  <property>
    <id>TestModel-CTLFireability-00</id>
    <description>EF fireable T0</description>
    <formula>
      <exists-path>
        <finally>
          <is-fireable><transition>T0</transition></is-fireable>
        </finally>
      </exists-path>
    </formula>
  </property>
</property-set>"#;
    fs::write(dir.path().join("CTLFireability.xml"), xml).expect("write CTLFireability.xml");
}

fn write_upper_bounds_xml(dir: &TempDir) {
    let xml = r#"<?xml version="1.0"?>
<property-set xmlns="http://mcc.lip6.fr/">
  <property>
    <id>TestModel-UpperBounds-00</id>
    <description>bound on P0</description>
    <formula>
      <place-bound>
        <place>P0</place>
      </place-bound>
    </formula>
  </property>
</property-set>"#;
    fs::write(dir.path().join("UpperBounds.xml"), xml).expect("write UpperBounds.xml");
}

#[test]
fn test_collect_non_property_deadlock_returns_typed_verdict() {
    let dir = TempDir::new().unwrap();
    write_model(&dir);

    let net = pnml_tools::parser::parse_pnml_dir(dir.path()).unwrap();
    let config = pnml_tools::explorer::ExplorationConfig::new(10_000);

    let records = collect_examination_with_dir(
        &net,
        "TestModel",
        dir.path(),
        Examination::ReachabilityDeadlock,
        &config,
    )
    .expect("collect should succeed");

    assert_eq!(records.len(), 1);
    assert_eq!(records[0].formula_id, "TestModel-ReachabilityDeadlock");
    // Minimal net deadlocks: P0→T0→P1, T0 fires once then no transition is enabled.
    assert_eq!(records[0].value, ExaminationValue::Verdict(Verdict::True));
}

#[test]
fn test_collect_non_property_state_space_returns_typed_stats() {
    let dir = TempDir::new().unwrap();
    write_model(&dir);

    let net = pnml_tools::parser::parse_pnml_dir(dir.path()).unwrap();
    let config = pnml_tools::explorer::ExplorationConfig::new(10_000);

    let records = collect_examination_with_dir(
        &net,
        "TestModel",
        dir.path(),
        Examination::StateSpace,
        &config,
    )
    .expect("collect should succeed");

    assert_eq!(records.len(), 1);
    assert_eq!(records[0].formula_id, "TestModel-StateSpace");
    let ExaminationValue::StateSpace(Some(report)) = &records[0].value else {
        panic!("expected StateSpace(Some(..)), got {:?}", records[0].value);
    };
    // 2 reachable states: [1,0] and [0,1]
    assert_eq!(report.states, 2);
}

#[test]
fn test_collect_property_reachability_fireability_returns_typed_verdicts() {
    let dir = TempDir::new().unwrap();
    write_model(&dir);
    write_reachability_fireability_xml(&dir);

    let net = pnml_tools::parser::parse_pnml_dir(dir.path()).unwrap();
    let config = pnml_tools::explorer::ExplorationConfig::new(10_000);

    let records = collect_examination_with_dir(
        &net,
        "TestModel",
        dir.path(),
        Examination::ReachabilityFireability,
        &config,
    )
    .expect("collect should succeed");

    assert_eq!(records.len(), 1);
    assert_eq!(
        records[0].formula_id,
        "TestModel-ReachabilityFireability-00"
    );
    // T0 is fireable from the initial marking [1,0].
    assert_eq!(records[0].value, ExaminationValue::Verdict(Verdict::True));
}

#[test]
fn test_collect_property_upper_bounds_returns_typed_bounds() {
    let dir = TempDir::new().unwrap();
    write_model(&dir);
    write_upper_bounds_xml(&dir);

    let net = pnml_tools::parser::parse_pnml_dir(dir.path()).unwrap();
    let config = pnml_tools::explorer::ExplorationConfig::new(10_000);

    let records = collect_examination_with_dir(
        &net,
        "TestModel",
        dir.path(),
        Examination::UpperBounds,
        &config,
    )
    .expect("collect should succeed");

    assert_eq!(records.len(), 1);
    assert_eq!(records[0].formula_id, "TestModel-UpperBounds-00");
    // P0 has at most 1 token across all reachable markings.
    assert_eq!(records[0].value, ExaminationValue::OptionalBound(Some(1)));
}

#[test]
fn test_collect_missing_property_xml_returns_error() {
    let dir = TempDir::new().unwrap();
    write_model(&dir);
    // No ReachabilityFireability.xml → should return Err

    let net = pnml_tools::parser::parse_pnml_dir(dir.path()).unwrap();
    let config = pnml_tools::explorer::ExplorationConfig::new(10_000);

    let result = collect_examination_with_dir(
        &net,
        "TestModel",
        dir.path(),
        Examination::ReachabilityFireability,
        &config,
    );

    assert!(
        result.is_err(),
        "missing property XML should return Err, got: {result:?}"
    );
}

#[test]
fn test_examination_record_to_mcc_line_verdict() {
    let record = ExaminationRecord::new(
        String::from("Model-ReachabilityDeadlock"),
        ExaminationValue::Verdict(Verdict::True),
    );
    assert_eq!(
        record.to_mcc_line(),
        "FORMULA Model-ReachabilityDeadlock TRUE TECHNIQUES EXPLICIT"
    );
}

#[test]
fn test_examination_record_to_mcc_line_bound() {
    let record = ExaminationRecord::new(
        String::from("Model-UpperBounds-00"),
        ExaminationValue::OptionalBound(Some(42)),
    );
    assert_eq!(
        record.to_mcc_line(),
        "FORMULA Model-UpperBounds-00 42 TECHNIQUES EXPLICIT"
    );
}

#[test]
fn test_examination_record_to_mcc_line_cannot_compute() {
    let record = ExaminationRecord::new(
        String::from("Model-UpperBounds-01"),
        ExaminationValue::OptionalBound(None),
    );
    assert_eq!(
        record.to_mcc_line(),
        "FORMULA Model-UpperBounds-01 CANNOT_COMPUTE TECHNIQUES EXPLICIT"
    );
}

#[test]
fn test_examination_record_to_mcc_line_state_space() {
    let record = ExaminationRecord::new(
        String::from("Model-StateSpace"),
        ExaminationValue::StateSpace(Some(StateSpaceReport::new(100, 250, 5, 12))),
    );
    let output = record.to_mcc_line();
    let lines: Vec<&str> = output.lines().collect();
    assert_eq!(lines.len(), 3, "StateSpace should produce 3 lines");
    assert_eq!(lines[0], "STATE_SPACE STATES 100 TECHNIQUES EXPLICIT");
    assert_eq!(
        lines[1],
        "STATE_SPACE MAX_TOKEN_IN_PLACE 5 TECHNIQUES EXPLICIT"
    );
    assert_eq!(lines[2], "STATE_SPACE MAX_TOKEN_SUM 12 TECHNIQUES EXPLICIT");
}

#[test]
fn test_verdict_re_exported_from_examination_module() {
    // Proves Verdict is accessible via pnml_tools::examination::Verdict
    let v: Verdict = Verdict::True;
    assert_eq!(v.to_string(), "TRUE");
}

#[test]
fn test_collect_ctl_fireability_returns_typed_verdicts() {
    let dir = TempDir::new().unwrap();
    write_model(&dir);
    write_ctl_fireability_xml(&dir);

    let net = pnml_tools::parser::parse_pnml_dir(dir.path()).unwrap();
    let config = pnml_tools::explorer::ExplorationConfig::new(10_000);

    let records = collect_examination_with_dir(
        &net,
        "TestModel",
        dir.path(),
        Examination::CTLFireability,
        &config,
    )
    .expect("collect should succeed");

    assert_eq!(records.len(), 1);
    assert_eq!(records[0].formula_id, "TestModel-CTLFireability-00");
    // EF(is-fireable(T0)): T0 is fireable in initial state [1,0] → TRUE
    assert_eq!(records[0].value, ExaminationValue::Verdict(Verdict::True));
}

// ---------------------------------------------------------------------------
// Fingerprint toggle contract (with_fingerprint_dedup recomputes budget)
// ---------------------------------------------------------------------------

#[test]
fn test_auto_sized_config_with_fingerprint_toggle_recomputes_budget() {
    let dir = TempDir::new().unwrap();
    write_model(&dir);

    let net = pnml_tools::parser::parse_pnml_dir(dir.path()).unwrap();
    let config_fp_on = pnml_tools::explorer::ExplorationConfig::auto_sized(&net, None, None);
    assert!(
        config_fp_on.fingerprint_dedup(),
        "auto_sized default should enable fingerprint dedup"
    );
    let budget_fp_on = config_fp_on.max_states();

    let config_fp_off = config_fp_on.with_fingerprint_dedup(false);
    assert!(!config_fp_off.fingerprint_dedup());
    let budget_fp_off = config_fp_off.max_states();

    // With fingerprint OFF, per-state memory is larger (packed marking vs u128
    // hash), so max_states must be smaller (or equal for tiny nets).
    assert!(
        budget_fp_off <= budget_fp_on,
        "fingerprint OFF budget ({budget_fp_off}) should be <= fingerprint ON ({budget_fp_on})"
    );

    // Round-tripping back to ON must restore the original budget.
    let config_back_on = config_fp_off.with_fingerprint_dedup(true);
    assert!(config_back_on.fingerprint_dedup());
    assert_eq!(
        config_back_on.max_states(),
        budget_fp_on,
        "round-trip toggle should restore original max_states"
    );
}

#[test]
fn test_explicit_config_fingerprint_toggle_preserves_max_states() {
    // A config created via new() has no auto-sizing basis, so toggling
    // fingerprint mode should NOT change max_states.
    let config = pnml_tools::explorer::ExplorationConfig::new(42);
    let toggled = config.with_fingerprint_dedup(false);
    assert!(!toggled.fingerprint_dedup());
    assert_eq!(
        toggled.max_states(),
        42,
        "explicit max_states should be preserved when fingerprint mode changes"
    );
}

// ---------------------------------------------------------------------------
// Model-based API (load_model_dir + collect_examination_for_model)
// ---------------------------------------------------------------------------

#[test]
fn test_load_model_dir_returns_prepared_model() {
    let dir = TempDir::new().unwrap();
    write_model(&dir);

    let model = load_model_dir(dir.path()).expect("load should succeed");

    assert_eq!(model.source_kind(), SourceNetKind::Pt);
    assert_eq!(model.net().num_places(), 2);
    assert_eq!(model.net().num_transitions(), 1);
    assert_eq!(model.model_dir(), dir.path());
}

#[test]
fn test_load_model_dir_malformed_colored_net_returns_parse_error() {
    // Minimal colored net without declarations — HLPNML parser attempts to
    // unfold but fails because the place has no sort declaration.
    let colored_pnml = r#"<?xml version="1.0"?>
<pnml xmlns="http://www.pnml.org/version-2009/grammar/pnml">
  <net id="test" type="http://www.pnml.org/version-2009/grammar/symmetricnet">
    <page id="p1"><place id="P0"/></page>
  </net>
</pnml>"#;
    let dir = TempDir::new().unwrap();
    let path = dir.path().join("model.pnml");
    fs::write(path, colored_pnml).unwrap();

    let result = load_model_dir(dir.path());

    assert!(result.is_err(), "malformed colored net should return Err");
    // Now attempts HLPNML parsing; a minimal net without declarations
    // produces MissingElement (place has empty sort_id).
    match result.unwrap_err() {
        pnml_tools::error::PnmlError::MissingElement(_) => {}
        other => panic!("expected MissingElement, got: {other:?}"),
    }
}

#[test]
fn test_load_model_dir_real_colored_model_supports_public_examination_api() {
    const MODEL: &str = "NeoElection-COL-2";

    if !has_mcc_benchmark(MODEL) {
        eprintln!("SKIP: {MODEL} benchmark not downloaded");
        return;
    }

    let model = load_model_dir(mcc_model_dir(MODEL)).expect("colored model should load");
    let config = pnml_tools::explorer::ExplorationConfig::new(1).with_workers(1);
    let records = collect_examination_for_model(&model, Examination::StateSpace, &config)
        .expect("StateSpace should execute through PreparedModel");

    assert_eq!(model.model_name(), MODEL);
    assert_eq!(model.source_kind(), SourceNetKind::SymmetricNet);
    assert!(
        model.net().num_places() > 0 && model.net().num_transitions() > 0,
        "colored fixture should unfold into a non-empty P/T net"
    );
    assert_eq!(records.len(), 1);
    assert_eq!(records[0].formula_id, format!("{MODEL}-StateSpace"));
    assert!(
        matches!(records[0].value, ExaminationValue::StateSpace(_)),
        "expected typed StateSpace result, got {:?}",
        records[0].value
    );
}

#[test]
fn test_collect_examination_for_model_real_colored_upper_bounds_returns_typed_records() {
    const MODEL: &str = "NeoElection-COL-2";

    if !has_mcc_benchmark(MODEL) {
        eprintln!("SKIP: {MODEL} benchmark not downloaded");
        return;
    }

    let model = load_model_dir(mcc_model_dir(MODEL)).expect("colored model should load");
    let config = pnml_tools::explorer::ExplorationConfig::new(1).with_workers(1);
    let records = collect_examination_for_model(&model, Examination::UpperBounds, &config)
        .expect("UpperBounds should execute through PreparedModel");

    assert!(
        !records.is_empty(),
        "UpperBounds should return typed records for the colored fixture"
    );
    assert!(
        records
            .iter()
            .all(|record| matches!(record.value, ExaminationValue::OptionalBound(_))),
        "expected OptionalBound rows from UpperBounds, got {:?}",
        records
    );
}

#[test]
fn test_collect_examination_for_model_deadlock() {
    let dir = TempDir::new().unwrap();
    write_model(&dir);

    let model = load_model_dir(dir.path()).expect("load should succeed");
    let config = pnml_tools::explorer::ExplorationConfig::new(10_000);

    let records = collect_examination_for_model(&model, Examination::ReachabilityDeadlock, &config)
        .expect("collect should succeed");

    assert_eq!(records.len(), 1);
    assert_eq!(records[0].value, ExaminationValue::Verdict(Verdict::True));
}

#[test]
fn test_collect_examination_for_model_property_examination() {
    let dir = TempDir::new().unwrap();
    write_model(&dir);
    write_reachability_fireability_xml(&dir);

    let model = load_model_dir(dir.path()).expect("load should succeed");
    let config = pnml_tools::explorer::ExplorationConfig::new(10_000);

    let records =
        collect_examination_for_model(&model, Examination::ReachabilityFireability, &config)
            .expect("collect should succeed");

    assert_eq!(records.len(), 1);
    assert_eq!(records[0].value, ExaminationValue::Verdict(Verdict::True));
}

#[test]
fn test_model_and_with_dir_apis_produce_same_results() {
    let dir = TempDir::new().unwrap();
    write_model(&dir);

    let model = load_model_dir(dir.path()).expect("load should succeed");
    let net = pnml_tools::parser::parse_pnml_dir(dir.path()).unwrap();
    let config = pnml_tools::explorer::ExplorationConfig::new(10_000);

    let model_records = collect_examination_for_model(&model, Examination::StateSpace, &config)
        .expect("model API should succeed");
    let dir_records = collect_examination_with_dir(
        &net,
        model.model_name(),
        dir.path(),
        Examination::StateSpace,
        &config,
    )
    .expect("dir API should succeed");

    assert_eq!(model_records.len(), dir_records.len());
    assert_eq!(model_records[0].value, dir_records[0].value);
}

#[test]
fn test_collect_simplification_report_for_model_property_examination() {
    let dir = TempDir::new().unwrap();
    write_model(&dir);
    write_reachability_fireability_xml(&dir);

    let model = load_model_dir(dir.path()).expect("load should succeed");
    let report = pnml_tools::model::collect_simplification_report_for_model(
        &model,
        Examination::ReachabilityFireability,
    )
    .expect("report should succeed for property examination");

    assert_eq!(report.properties.len(), 1, "one property in the XML");
    assert_eq!(report.summary.total_properties, 1);
}

#[test]
fn test_collect_simplification_report_for_model_rejects_non_property_examination() {
    let dir = TempDir::new().unwrap();
    write_model(&dir);

    let model = load_model_dir(dir.path()).expect("load should succeed");
    let result =
        pnml_tools::model::collect_simplification_report_for_model(&model, Examination::StateSpace);

    match result.unwrap_err() {
        pnml_tools::error::PnmlError::ExaminationDoesNotUsePropertyXml { examination } => {
            assert_eq!(examination, "StateSpace");
        }
        other => panic!("expected ExaminationDoesNotUsePropertyXml for StateSpace, got: {other:?}"),
    }
}

// test_pnml_simplify_report_colored_success_stays_machine_readable removed:
// pnml-simplify-report binary was deleted when pnml-tools became a thin wrapper
// over tla-petri. The functionality is now in `tla2 mcc --simplify-report`.
