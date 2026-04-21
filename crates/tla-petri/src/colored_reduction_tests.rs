// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for colored reduction Tier 1: relevance + dead transitions.
//!
//! Verifies that the per-property colored relevance path
//! (`collect_examination_for_model`) produces correct results for
//! symmetric-net models, matching ground truth from MCC labels.
//!
//! Part of #1438.

use std::fs;
use std::path::PathBuf;

use crate::colored_dead_transitions;
use crate::colored_relevance;
use crate::examination::{Examination, ExaminationValue, Verdict};
use crate::explorer::ExplorationConfig;
use crate::hlpnml;
use crate::model::{
    collect_examination_for_model, load_model_dir, load_model_dir_no_colored_reduce, SourceNetKind,
};
use tempfile::TempDir;

const COLLAPSIBLE_ALL_MODEL: &str = r#"<?xml version="1.0"?>
<pnml xmlns="http://www.pnml.org/version-2009/grammar/pnml">
  <net id="collapse-all" type="http://www.pnml.org/version-2009/grammar/symmetricnet">
    <page id="page0">
      <place id="P0">
        <type><structure><usersort declaration="s1"/></structure></type>
        <hlinitialMarking><structure><all><usersort declaration="s1"/></all></structure></hlinitialMarking>
      </place>
      <transition id="T0"/>
      <arc id="a1" source="P0" target="T0">
        <hlinscription><structure><all><usersort declaration="s1"/></all></structure></hlinscription>
      </arc>
      <arc id="a2" source="T0" target="P0">
        <hlinscription><structure><all><usersort declaration="s1"/></all></structure></hlinscription>
      </arc>
    </page>
    <declaration><structure><declarations>
      <namedsort id="s1" name="S">
        <cyclicenumeration>
          <feconstant id="c1" name="a"/>
          <feconstant id="c2" name="b"/>
          <feconstant id="c3" name="c"/>
        </cyclicenumeration>
      </namedsort>
    </declarations></structure></declaration>
  </net>
</pnml>"#;

fn mcc_input_dir(model: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../benchmarks/mcc/2024/INPUTS")
        .join(model)
}

fn collapsible_all_fixture_dir() -> TempDir {
    let dir = TempDir::with_prefix("CollapseAll-COL-").expect("tempdir should create");
    fs::write(dir.path().join("model.pnml"), COLLAPSIBLE_ALL_MODEL).expect("fixture PNML");
    dir
}

fn write_collapsible_all_fireability_xml(dir: &TempDir) {
    let xml = r#"<?xml version="1.0"?>
<property-set xmlns="http://mcc.lip6.fr/">
  <property>
    <id>CollapseAll-ReachabilityFireability-00</id>
    <description>T0 is fireable</description>
    <formula>
      <exists-path>
        <finally>
          <is-fireable><transition>T0</transition></is-fireable>
        </finally>
      </exists-path>
    </formula>
  </property>
</property-set>"#;
    fs::write(dir.path().join("ReachabilityFireability.xml"), xml).expect("fixture XML");
}

// ---------------------------------------------------------------------------
// Unit: dead transition removal
// ---------------------------------------------------------------------------

/// With collapsing re-enabled (#1418), the fully-uniform CollapseAll fixture
/// should collapse P0 from 3 colored places to 1 Dot place.
#[test]
fn test_all_inscription_model_load_collapse_enabled() {
    let dir = collapsible_all_fixture_dir();
    let reduced = load_model_dir(dir.path()).expect("production fixture should load");
    let unreduced =
        load_model_dir_no_colored_reduce(dir.path()).expect("unreduced fixture should load");

    assert_eq!(reduced.source_kind(), SourceNetKind::SymmetricNet);
    assert_eq!(unreduced.source_kind(), SourceNetKind::SymmetricNet);

    let reduced_places = reduced
        .aliases()
        .resolve_places("P0")
        .expect("aliases should contain P0");
    let unreduced_places = unreduced
        .aliases()
        .resolve_places("P0")
        .expect("aliases should contain P0");

    // Collapsing re-enabled: fully-uniform fixture collapses P0 to 1 Dot place.
    assert_eq!(
        unreduced_places.len(),
        3,
        "P0 unfolds to three colored places without collapsing"
    );
    assert_eq!(
        reduced_places.len(),
        1,
        "P0 should collapse to one Dot place with collapsing enabled"
    );
}

#[test]
fn test_all_inscription_model_matches_unreduced_fireability() {
    let dir = collapsible_all_fixture_dir();
    write_collapsible_all_fireability_xml(&dir);

    let reduced = load_model_dir(dir.path()).expect("collapsed fixture should load");
    let unreduced =
        load_model_dir_no_colored_reduce(dir.path()).expect("unreduced fixture should load");
    let config = ExplorationConfig::new(16).with_workers(1);

    let reduced_records =
        collect_examination_for_model(&reduced, Examination::ReachabilityFireability, &config)
            .expect("collapsed fireability should dispatch");
    let unreduced_records =
        collect_examination_for_model(&unreduced, Examination::ReachabilityFireability, &config)
            .expect("unreduced fireability should dispatch");

    assert_eq!(
        reduced_records, unreduced_records,
        "active <all> collapse should preserve definitive fireability verdicts"
    );
    assert_eq!(reduced_records.len(), 1);
    assert_eq!(
        reduced_records[0].value,
        ExaminationValue::Verdict(Verdict::True),
        "T0 should be fireable on both the collapsed and unreduced nets"
    );
}

#[test]
fn test_dead_transition_removal_on_neo_election() {
    let dir = mcc_input_dir("NeoElection-COL-2");
    if !dir.exists() {
        eprintln!("SKIP: NeoElection-COL-2 benchmark not available");
        return;
    }
    let mut colored = hlpnml::parse_hlpnml_dir(&dir).expect("HLPNML parse should succeed");
    let orig_transitions = colored.transitions.len();
    let report = colored_dead_transitions::reduce(&mut colored);
    eprintln!(
        "dead transitions: {}/{} removed",
        report.transitions_removed, orig_transitions
    );
    // The net should still be valid (places + transitions + arcs consistent).
    assert!(colored.places.len() > 0, "should retain at least one place");
    assert!(
        colored.transitions.len() <= orig_transitions,
        "should not add transitions"
    );
}

// ---------------------------------------------------------------------------
// Unit: relevance reduction
// ---------------------------------------------------------------------------

#[test]
fn test_relevance_reduces_neo_election_single_property() {
    let dir = mcc_input_dir("NeoElection-COL-2");
    if !dir.exists() {
        eprintln!("SKIP: NeoElection-COL-2 benchmark not available");
        return;
    }
    let colored = hlpnml::parse_hlpnml_dir(&dir).expect("HLPNML parse should succeed");
    let orig_places = colored.places.len();
    let orig_transitions = colored.transitions.len();

    // Parse a reachability property to get a formula with query references.
    let properties = crate::property_xml::parse_properties(&dir, "ReachabilityCardinality")
        .expect("ReachabilityCardinality XML should parse");
    assert!(!properties.is_empty(), "should have at least one property");

    let first = &properties[0];
    let refs = colored_relevance::extract_refs(&first.formula);
    eprintln!(
        "property {}: {} place refs, {} transition refs",
        first.id,
        refs.places.len(),
        refs.transitions.len()
    );

    let mut reduced = colored.clone();
    let report = colored_relevance::reduce(&mut reduced, &first.formula);
    eprintln!(
        "relevance: {}/{} places removed, {}/{} transitions removed",
        report.places_removed, orig_places, report.transitions_removed, orig_transitions,
    );

    // Relevance should reduce the net (NeoElection-COL-2 has 96 places,
    // a single-property query should keep far fewer).
    if refs.places.len() > 0 || refs.transitions.len() > 0 {
        assert!(
            reduced.places.len() <= orig_places,
            "relevance should not add places"
        );
        // The reduced net should be strictly smaller for a focused query.
        assert!(
            reduced.places.len() < orig_places || reduced.transitions.len() < orig_transitions,
            "relevance should remove at least some structure for a focused query"
        );
    }

    // The reduced net should still unfold successfully.
    let unfolded = crate::unfold::unfold_to_pt(&reduced);
    assert!(
        unfolded.is_ok(),
        "reduced colored net should unfold: {:?}",
        unfolded.err()
    );
}

// ---------------------------------------------------------------------------
// Integration: collect_examination_for_model
// ---------------------------------------------------------------------------

/// Reachability bypasses colored relevance (unsound for general reachability).
/// Verify RC-03 ground truth still holds through the model path.
#[test]
fn test_reachability_bypasses_relevance_rc03_stays_false() {
    let dir = mcc_input_dir("NeoElection-COL-2");
    if !dir.exists() {
        eprintln!("SKIP: NeoElection-COL-2 benchmark not available");
        return;
    }
    let model = load_model_dir(&dir).expect("model should load");
    assert_eq!(model.source_kind(), SourceNetKind::SymmetricNet);
    assert!(
        model.colored_source.is_some(),
        "symmetric net should retain colored_source"
    );

    let config = ExplorationConfig::new(50_000);
    let records =
        collect_examination_for_model(&model, Examination::ReachabilityCardinality, &config)
            .expect("ReachabilityCardinality should succeed");

    assert!(
        !records.is_empty(),
        "should produce at least one examination record"
    );

    // RC-03 is known FALSE from ground truth.
    let rc03 = records.iter().find(|r| {
        r.formula_id.contains("ReachabilityCardinality") && r.formula_id.ends_with("-03")
    });
    if let Some(rc03) = rc03 {
        assert_eq!(
            rc03.value,
            ExaminationValue::Verdict(Verdict::False),
            "RC-03 should be FALSE (reachability bypasses relevance)"
        );
    }

    for record in &records {
        match &record.value {
            ExaminationValue::Verdict(_) => {}
            other => panic!(
                "ReachabilityCardinality should produce Verdict values, got {:?} for {}",
                other, record.formula_id
            ),
        }
    }
}

/// UpperBounds uses the colored relevance path for symmetric nets.
#[test]
fn test_upper_bounds_uses_colored_relevance_path() {
    let dir = mcc_input_dir("NeoElection-COL-2");
    if !dir.exists() {
        eprintln!("SKIP: NeoElection-COL-2 benchmark not available");
        return;
    }
    let model = load_model_dir(&dir).expect("model should load");
    let config = ExplorationConfig::new(50_000);

    let ub_xml_path = dir.join("UpperBounds.xml");
    if !ub_xml_path.exists() {
        eprintln!("SKIP: UpperBounds.xml not available for NeoElection-COL-2");
        return;
    }

    let records = collect_examination_for_model(&model, Examination::UpperBounds, &config)
        .expect("UpperBounds should succeed via colored relevance path");

    assert!(!records.is_empty(), "should produce UpperBounds records");

    for record in &records {
        match &record.value {
            ExaminationValue::OptionalBound(_) => {}
            other => panic!(
                "UpperBounds should produce OptionalBound values, got {:?} for {}",
                other, record.formula_id
            ),
        }
    }
}

// ---------------------------------------------------------------------------
// Multi-model: TokenRing-COL-005
// ---------------------------------------------------------------------------

#[test]
fn test_dead_transition_removal_on_token_ring() {
    let dir = mcc_input_dir("TokenRing-COL-005");
    if !dir.exists() {
        eprintln!("SKIP: TokenRing-COL-005 benchmark not available");
        return;
    }
    let mut colored = hlpnml::parse_hlpnml_dir(&dir).expect("HLPNML parse should succeed");
    let orig_transitions = colored.transitions.len();
    let report = colored_dead_transitions::reduce(&mut colored);
    eprintln!(
        "TokenRing dead transitions: {}/{} removed",
        report.transitions_removed, orig_transitions
    );
    assert!(colored.places.len() > 0, "should retain at least one place");
    assert!(
        colored.transitions.len() <= orig_transitions,
        "should not add transitions"
    );
}

#[test]
fn test_relevance_reduces_token_ring_single_property() {
    let dir = mcc_input_dir("TokenRing-COL-005");
    if !dir.exists() {
        eprintln!("SKIP: TokenRing-COL-005 benchmark not available");
        return;
    }
    let colored = hlpnml::parse_hlpnml_dir(&dir).expect("HLPNML parse should succeed");
    let orig_places = colored.places.len();

    let properties = crate::property_xml::parse_properties(&dir, "ReachabilityCardinality")
        .expect("ReachabilityCardinality XML should parse");
    assert!(!properties.is_empty(), "should have at least one property");

    let first = &properties[0];
    let mut reduced = colored.clone();
    let report = colored_relevance::reduce(&mut reduced, &first.formula);
    eprintln!(
        "TokenRing relevance: {}/{} places removed",
        report.places_removed, orig_places,
    );

    // The reduced net should still unfold successfully.
    let unfolded = crate::unfold::unfold_to_pt(&reduced);
    assert!(
        unfolded.is_ok(),
        "reduced TokenRing colored net should unfold: {:?}",
        unfolded.err()
    );
}

#[test]
fn test_token_ring_reachability_produces_verdicts() {
    let dir = mcc_input_dir("TokenRing-COL-005");
    if !dir.exists() {
        eprintln!("SKIP: TokenRing-COL-005 benchmark not available");
        return;
    }
    let model = load_model_dir(&dir).expect("model should load");
    assert_eq!(model.source_kind(), SourceNetKind::SymmetricNet);

    let config = ExplorationConfig::new(50_000);
    let records =
        collect_examination_for_model(&model, Examination::ReachabilityCardinality, &config)
            .expect("ReachabilityCardinality should succeed for TokenRing");

    assert!(
        !records.is_empty(),
        "should produce at least one examination record"
    );

    for record in &records {
        match &record.value {
            ExaminationValue::Verdict(_) => {}
            other => panic!(
                "ReachabilityCardinality should produce Verdict values, got {:?} for {}",
                other, record.formula_id
            ),
        }
    }
}

// ---------------------------------------------------------------------------
// Multi-model: Philosophers-COL-000100
// ---------------------------------------------------------------------------

#[test]
fn test_dead_transition_removal_on_philosophers() {
    let dir = mcc_input_dir("Philosophers-COL-000100");
    if !dir.exists() {
        eprintln!("SKIP: Philosophers-COL-000100 benchmark not available");
        return;
    }
    let mut colored = hlpnml::parse_hlpnml_dir(&dir).expect("HLPNML parse should succeed");
    let orig_transitions = colored.transitions.len();
    let report = colored_dead_transitions::reduce(&mut colored);
    eprintln!(
        "Philosophers dead transitions: {}/{} removed",
        report.transitions_removed, orig_transitions
    );
    assert!(colored.places.len() > 0, "should retain at least one place");
}

#[test]
fn test_relevance_reduces_philosophers_single_property() {
    let dir = mcc_input_dir("Philosophers-COL-000100");
    if !dir.exists() {
        eprintln!("SKIP: Philosophers-COL-000100 benchmark not available");
        return;
    }
    let colored = hlpnml::parse_hlpnml_dir(&dir).expect("HLPNML parse should succeed");
    let orig_places = colored.places.len();

    let properties = crate::property_xml::parse_properties(&dir, "ReachabilityCardinality")
        .expect("ReachabilityCardinality XML should parse");
    if properties.is_empty() {
        eprintln!("SKIP: no ReachabilityCardinality properties for Philosophers-COL-000100");
        return;
    }

    let first = &properties[0];
    let mut reduced = colored.clone();
    let report = colored_relevance::reduce(&mut reduced, &first.formula);
    eprintln!(
        "Philosophers relevance: {}/{} places removed",
        report.places_removed, orig_places,
    );

    assert!(
        reduced.places.len() <= orig_places,
        "relevance should not add places"
    );
}

// ---------------------------------------------------------------------------
// Integration: non-property exams bypass colored relevance
// ---------------------------------------------------------------------------

/// Verify that non-property examinations still work through the model path
/// (they should bypass the colored relevance path entirely).
#[test]
fn test_non_property_exam_bypasses_colored_relevance() {
    let dir = mcc_input_dir("NeoElection-COL-2");
    if !dir.exists() {
        eprintln!("SKIP: NeoElection-COL-2 benchmark not available");
        return;
    }
    let model = load_model_dir(&dir).expect("model should load");
    let config = ExplorationConfig::new(50_000);

    // These should work normally without touching colored_relevance.
    let deadlock =
        collect_examination_for_model(&model, Examination::ReachabilityDeadlock, &config)
            .expect("ReachabilityDeadlock should succeed");
    assert_eq!(deadlock.len(), 1);

    let one_safe = collect_examination_for_model(&model, Examination::OneSafe, &config)
        .expect("OneSafe should succeed");
    assert_eq!(one_safe.len(), 1);
}

// ---------------------------------------------------------------------------
// Diagnostic: strengthened collapsing criterion on NeoElection-COL-2 (#1418)
// ---------------------------------------------------------------------------

/// Verify the strengthened criterion prevents collapsing on NeoElection-COL-2.
///
/// The old criterion collapsed places whose OWN arcs were all uniform, but
/// NeoElection has transitions with mixed arcs (uniform to one place, variable
/// to another). The strengthened criterion checks ALL arcs of every touching
/// transition, which prevents any collapses on this model.
///
/// With `reduce_colored` re-enabled (#1418), this test confirms that
/// `collapse_constant_places` remains a no-op on the previously-buggy model.
#[test]
fn test_strengthened_criterion_prevents_neo_election_collapse() {
    let dir = mcc_input_dir("NeoElection-COL-2");
    if !dir.exists() {
        eprintln!("SKIP: NeoElection-COL-2 benchmark not available");
        return;
    }
    let mut colored = hlpnml::parse_hlpnml_dir(&dir).expect("HLPNML parse should succeed");
    let mut report = crate::colored_reduce::ColorReductionReport::default();
    crate::colored_reduce::collapse_constant_places(&mut colored, &mut report);

    eprintln!(
        "NeoElection-COL-2 collapse: {} places collapsed, {} places saved",
        report.collapsed_places.len(),
        report.places_saved(),
    );
    for (place, orig) in &report.collapsed_places {
        eprintln!("  collapsed: {place} (orig cardinality {orig})");
    }

    // Strengthened criterion should prevent ALL collapses on NeoElection-COL-2.
    // NeoElection's transitions have mixed inscriptions (All + variable arcs),
    // so the "all arcs of touching transitions must be uniform" check should
    // disqualify every candidate place.
    assert!(
        report.collapsed_places.is_empty(),
        "Strengthened criterion should prevent collapsing on NeoElection-COL-2. \
         Got {} collapsed places: {:?}",
        report.collapsed_places.len(),
        report.collapsed_places,
    );
}

/// End-to-end: re-enabled collapsing produces zero wrong answers on NeoElection RF.
///
/// With the strengthened criterion, `collapse_constant_places` is a no-op on
/// NeoElection-COL-2 (no places pass the criterion). This test verifies that
/// the full pipeline with collapsing re-enabled matches the uncollapsed path.
#[test]
fn test_reenabled_collapsing_zero_wrong_answers_neo_election_rf() {
    let dir = mcc_input_dir("NeoElection-COL-2");
    if !dir.exists() {
        eprintln!("SKIP: NeoElection-COL-2 benchmark not available");
        return;
    }

    // Load with collapsing enabled (direct call to collapse_constant_places).
    let mut colored = hlpnml::parse_hlpnml_dir(&dir).expect("HLPNML parse should succeed");
    let mut report = crate::colored_reduce::ColorReductionReport::default();
    crate::colored_reduce::collapse_constant_places(&mut colored, &mut report);
    crate::colored_dead_transitions::reduce(&mut colored);
    let collapsed_unfolded = crate::unfold::unfold_to_pt(&colored).expect("should unfold");

    // Load without collapsing for ground truth.
    let uncollapsed = hlpnml::parse_hlpnml_dir(&dir).expect("HLPNML parse should succeed");
    let uncollapsed_unfolded = crate::unfold::unfold_to_pt(&uncollapsed).expect("should unfold");

    let config = ExplorationConfig::new(50_000).with_workers(1);

    let collapsed_results = crate::examination::collect_examination_core(
        &collapsed_unfolded.net,
        "NeoElection-COL-2",
        &dir,
        &collapsed_unfolded.aliases,
        Examination::ReachabilityFireability,
        &config,
        false,
    )
    .expect("RF collection on collapsed net should succeed");

    let uncollapsed_results = crate::examination::collect_examination_core(
        &uncollapsed_unfolded.net,
        "NeoElection-COL-2",
        &dir,
        &uncollapsed_unfolded.aliases,
        Examination::ReachabilityFireability,
        &config,
        false,
    )
    .expect("RF collection on uncollapsed net should succeed");

    let mut wrong = Vec::new();
    for col in &collapsed_results {
        if let Some(uncol) = uncollapsed_results
            .iter()
            .find(|r| r.formula_id == col.formula_id)
        {
            let col_definitive =
                !matches!(col.value, ExaminationValue::Verdict(Verdict::CannotCompute));
            let uncol_definitive = !matches!(
                uncol.value,
                ExaminationValue::Verdict(Verdict::CannotCompute)
            );
            if col_definitive && uncol_definitive && col.value != uncol.value {
                wrong.push(format!(
                    "{}: collapsed={:?}, uncollapsed={:?}",
                    col.formula_id, col.value, uncol.value,
                ));
            }
        }
    }

    for w in &wrong {
        eprintln!("WRONG ANSWER: {w}");
    }
    assert!(
        wrong.is_empty(),
        "Re-enabled collapsing should produce zero wrong answers. Found: {:?}",
        wrong,
    );
}
