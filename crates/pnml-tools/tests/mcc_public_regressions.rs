// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::fs;
use std::path::{Path, PathBuf};

use pnml_tools::examination::{Examination, ExaminationRecord, ExaminationValue, StateSpaceReport};
use pnml_tools::explorer::ExplorationConfig;
use pnml_tools::model::{collect_examination_for_model, load_model_dir};
use pnml_tools::output::Verdict;
use tempfile::TempDir;

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

fn mcc_model_dir_year(model: &str, year: &str) -> PathBuf {
    workspace_root()
        .join("benchmarks")
        .join("mcc")
        .join(year)
        .join(format!("INPUTS-{year}"))
        .join(model)
}

fn has_mcc_benchmark(model: &str) -> bool {
    mcc_model_dir(model).join("model.pnml").exists()
}

fn upper_bounds_registry(model: &str) -> Vec<u64> {
    let path = workspace_root()
        .join("registry")
        .join("mcc-labels")
        .join("upper-bounds-2024.csv");
    let contents = std::fs::read_to_string(path).expect("UpperBounds registry CSV should read");
    let line = contents
        .lines()
        .find(|line| line.starts_with(&format!("{model},")))
        .unwrap_or_else(|| panic!("registry should contain UpperBounds row for {model}"));
    let (_, raw_values) = line
        .split_once(',')
        .expect("UpperBounds registry row should contain a comma");
    raw_values
        .split_whitespace()
        .map(|value| {
            value
                .parse::<u64>()
                .unwrap_or_else(|err| panic!("registry value should parse: {err}"))
        })
        .collect()
}

fn formula_index(formula_id: &str) -> usize {
    formula_id
        .rsplit_once('-')
        .expect("formula id should contain an index suffix")
        .1
        .parse::<usize>()
        .expect("formula index should parse")
}

fn collect_model_exam(
    model_dir: &Path,
    examination: Examination,
    max_states: usize,
) -> Vec<ExaminationRecord> {
    let prepared = load_model_dir(model_dir).unwrap_or_else(|err| {
        panic!(
            "failed to load {} through public PreparedModel API: {err}",
            model_dir.display()
        )
    });
    let config = ExplorationConfig::new(max_states).with_workers(1);
    collect_examination_for_model(&prepared, examination, &config).unwrap_or_else(|err| {
        panic!(
            "failed to collect {examination:?} for {} via public API: {err}",
            model_dir.display()
        )
    })
}

fn extract_property_block(xml: &str, property_id: &str) -> String {
    let id_tag = format!("<id>{property_id}</id>");
    let id_pos = xml
        .find(&id_tag)
        .unwrap_or_else(|| panic!("UpperBounds.xml should contain property {property_id}"));
    let start = xml[..id_pos]
        .rfind("<property>")
        .unwrap_or_else(|| panic!("property block should start before {property_id}"));
    let end = xml[id_pos..]
        .find("</property>")
        .map(|offset| id_pos + offset + "</property>".len())
        .unwrap_or_else(|| panic!("property block should end after {property_id}"));
    xml[start..end].to_string()
}

fn single_property_upper_bounds_fixture(model: &str, property_id: &str) -> TempDir {
    let source_dir = mcc_model_dir(model);
    let source_xml = fs::read_to_string(source_dir.join("UpperBounds.xml"))
        .expect("UpperBounds.xml should read");
    let prefix_end = source_xml
        .find("<property>")
        .expect("UpperBounds.xml should contain at least one property");
    let suffix_start = source_xml
        .rfind("</property-set>")
        .expect("UpperBounds.xml should end with </property-set>");

    let fixture = TempDir::new().expect("temp fixture dir should create");
    fs::copy(
        source_dir.join("model.pnml"),
        fixture.path().join("model.pnml"),
    )
    .expect("model.pnml should copy into fixture");

    let mut filtered_xml = String::from(&source_xml[..prefix_end]);
    filtered_xml.push_str(&extract_property_block(&source_xml, property_id));
    filtered_xml.push('\n');
    filtered_xml.push_str(&source_xml[suffix_start..]);
    fs::write(fixture.path().join("UpperBounds.xml"), filtered_xml)
        .expect("filtered UpperBounds.xml should write");

    fixture
}

fn assert_upper_bounds_property_matches_registry(model: &str, property_id: &str) {
    if !has_mcc_benchmark(model) {
        eprintln!("SKIP: {model} benchmark not downloaded");
        return;
    }

    let fixture = single_property_upper_bounds_fixture(model, property_id);
    let expected = upper_bounds_registry(model)[formula_index(property_id)];
    let records = collect_model_exam(fixture.path(), Examination::UpperBounds, 1_000_000);
    assert_eq!(
        records.len(),
        1,
        "{model} fixture should emit one UpperBounds record"
    );
    assert_eq!(
        records[0].formula_id, property_id,
        "{model} fixture should preserve the requested UpperBounds property id"
    );

    match &records[0].value {
        ExaminationValue::OptionalBound(Some(bound)) => assert_eq!(
            *bound, expected,
            "{model} {property_id} should match the MCC UpperBounds registry"
        ),
        other => panic!(
            "{model} {property_id} should resolve to an exact UpperBounds value, got {other:?}"
        ),
    }
}

fn assert_state_space_fails_closed(model: &str) {
    if !has_mcc_benchmark(model) {
        eprintln!("SKIP: {model} benchmark not downloaded");
        return;
    }

    let records = collect_model_exam(&mcc_model_dir(model), Examination::StateSpace, 1);
    assert_eq!(
        records.len(),
        1,
        "{model} should emit one StateSpace record"
    );
    assert_eq!(
        records[0].formula_id,
        format!("{model}-StateSpace"),
        "{model} should preserve the canonical StateSpace formula id"
    );
    match &records[0].value {
        ExaminationValue::StateSpace(None) => {}
        other => panic!("{model} StateSpace should fail closed, got {other:?}"),
    }
}

#[test]
fn test_upper_bounds_public_api_matches_registry_for_swimmingpool_formula_03() {
    assert_upper_bounds_property_matches_registry(
        "SwimmingPool-PT-07",
        "SwimmingPool-PT-07-UpperBounds-03",
    );
}

#[test]
fn test_upper_bounds_public_api_matches_registry_for_nqueens_formula_00() {
    assert_upper_bounds_property_matches_registry("NQueens-PT-30", "NQueens-PT-30-UpperBounds-00");
}

#[test]
fn test_statespace_public_api_fails_closed_for_bridge_and_vehicles_colored_models() {
    for model in [
        "BridgeAndVehicles-COL-V04P05N02",
        "BridgeAndVehicles-COL-V10P10N10",
        "BridgeAndVehicles-COL-V20P20N10",
    ] {
        assert_state_space_fails_closed(model);
    }
}

#[test]
fn test_statespace_public_api_keeps_pt_bridge_and_vehicles_exact_control() {
    const MODEL: &str = "BridgeAndVehicles-PT-V04P05N02";

    if !has_mcc_benchmark(MODEL) {
        eprintln!("SKIP: {MODEL} benchmark not downloaded");
        return;
    }

    let records = collect_model_exam(&mcc_model_dir(MODEL), Examination::StateSpace, 10_000);
    assert_eq!(
        records.len(),
        1,
        "{MODEL} should emit one StateSpace record"
    );
    assert_eq!(
        records[0].formula_id,
        format!("{MODEL}-StateSpace"),
        "{MODEL} should preserve the canonical StateSpace formula id"
    );
    match &records[0].value {
        ExaminationValue::StateSpace(Some(stats)) => assert_eq!(
            *stats,
            StateSpaceReport::new(2874, 7160, 5, 17),
            "{MODEL} should preserve the exact PT control tuple"
        ),
        other => panic!("{MODEL} StateSpace should stay exact, got {other:?}"),
    }
}

/// GPPP-PT-C0010N1000000000 ReachabilityCardinality: verify LP-proven verdicts
/// match structural P-invariant analysis. The MCC ground truth labels for
/// properties /5, /10, /13, /15 are incorrect — LP correctly proves them via
/// P-invariants derived from the conserving structure of the glycolysis/pentose
/// phosphate pathway model. (#1516)
///
/// Key P-invariants (LP dual solutions):
///   a1 + a2 = 20  (initial: a1=20, a2=0)
///   GSH + 2*GSSG = 2e9  (initial: GSH=0, GSSG=1e9)
///   Metabolites (_3PG, E4P, Ru5P, etc.) bounded by pathway conservation
#[test]
fn test_gppp_reachability_cardinality_lp_verdicts_match_p_invariants() {
    const MODEL: &str = "GPPP-PT-C0010N1000000000";
    let model_dir = mcc_model_dir_year(MODEL, "2022");
    if !model_dir.join("model.pnml").exists() {
        eprintln!("SKIP: {MODEL} benchmark not downloaded");
        return;
    }

    let records = collect_model_exam(
        &model_dir,
        Examination::ReachabilityCardinality,
        100_000_000,
    );
    assert_eq!(
        records.len(),
        16,
        "{MODEL} should emit 16 ReachabilityCardinality records"
    );

    // Property /05: EF(... & GSH >= K & ...) where K > 2e9.
    // P-invariant: GSH + 2*GSSG = 2e9, so GSH <= 2e9 < K. EF(...) = FALSE.
    let rec05 = records
        .iter()
        .find(|r| r.formula_id.ends_with("-05"))
        .unwrap();
    assert_eq!(
        rec05.value,
        ExaminationValue::Verdict(Verdict::False),
        "{MODEL} property /05: P-invariant GSH+2*GSSG=2e9 proves EF unreachable"
    );

    // Property /10: EF(conjunction with _3PG >= 2533611531 and other large thresholds).
    // After double-negation elimination, all branches require metabolite counts
    // exceeding LP upper bounds (e.g., _3PG bounded well below 2.5e9 by pathway
    // conservation). Every branch of the disjunction is LP-infeasible → FALSE.
    let rec10 = records
        .iter()
        .find(|r| r.formula_id.ends_with("-10"))
        .unwrap();
    assert_eq!(
        rec10.value,
        ExaminationValue::Verdict(Verdict::False),
        "{MODEL} property /10: pathway conservation bounds prove EF unreachable"
    );

    // Property /13: AG(NOT^5(K <= a2)) simplifies to AG(a2 < K) where K=2751167421.
    // P-invariant: a1 + a2 = 20, so a2 <= 20 always. AG(...) = TRUE.
    let rec13 = records
        .iter()
        .find(|r| r.formula_id.ends_with("-13"))
        .unwrap();
    assert_eq!(
        rec13.value,
        ExaminationValue::Verdict(Verdict::True),
        "{MODEL} property /13: P-invariant a1+a2=20 proves AG holds"
    );

    // Property /15: AG(Ru5P <= 2525393503 OR ...).
    // First disjunct: Ru5P is bounded by pathway conservation well below 2.5e9,
    // so Ru5P <= 2525393503 always holds. AG(true OR ...) = TRUE.
    let rec15 = records
        .iter()
        .find(|r| r.formula_id.ends_with("-15"))
        .unwrap();
    assert_eq!(
        rec15.value,
        ExaminationValue::Verdict(Verdict::True),
        "{MODEL} property /15: pathway conservation bounds Ru5P, AG always holds"
    );
}
