// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use tempfile::TempDir;

use super::*;
use fixtures::*;

#[test]
fn test_identity_aliases_have_one_entry_per_place() {
    let dir = TempDir::new().unwrap();
    write_pnml(&dir, MINIMAL_PT_NET);

    let model = load_model_dir(dir.path()).expect("load should succeed");

    // P0 and P1 should each have one-element alias vectors
    assert_eq!(
        model.aliases.place_aliases.get("P0"),
        Some(&vec![PlaceIdx(0)])
    );
    assert_eq!(
        model.aliases.place_aliases.get("P1"),
        Some(&vec![PlaceIdx(1)])
    );
}

#[test]
fn test_identity_aliases_have_one_entry_per_transition() {
    let dir = TempDir::new().unwrap();
    write_pnml(&dir, MINIMAL_PT_NET);

    let model = load_model_dir(dir.path()).expect("load should succeed");

    assert_eq!(
        model.aliases.transition_aliases.get("T0"),
        Some(&vec![TransitionIdx(0)])
    );
}

#[test]
fn test_collect_examination_core_uses_place_aliases_for_upper_bounds() {
    let dir = TempDir::new().unwrap();
    write_pnml(&dir, UNFOLDED_ALIAS_PT_NET);
    write_upper_bounds_alias_xml(&dir);

    let model = load_model_dir(dir.path()).expect("load should succeed");
    let aliases = alias_enriched(&model);
    let records = collect_examination_core(
        model.net(),
        "AliasModel",
        dir.path(),
        &aliases,
        Examination::UpperBounds,
        &ExplorationConfig::new(32),
        false,
    )
    .expect("collection should succeed");

    assert_eq!(records.len(), 1);
    assert_eq!(
        records[0].value,
        ExaminationValue::OptionalBound(Some(2)),
        "place alias should expand to both unfolded Fork places",
    );
}

#[test]
fn test_collect_examination_core_uses_transition_aliases_for_fireability() {
    let dir = TempDir::new().unwrap();
    write_pnml(&dir, UNFOLDED_ALIAS_PT_NET);
    write_reachability_fireability_alias_xml(&dir);

    let model = load_model_dir(dir.path()).expect("load should succeed");
    let aliases = alias_enriched(&model);
    let records = collect_examination_core(
        model.net(),
        "AliasModel",
        dir.path(),
        &aliases,
        Examination::ReachabilityFireability,
        &ExplorationConfig::new(32),
        false,
    )
    .expect("collection should succeed");

    assert_eq!(records.len(), 1);
    assert_eq!(records[0].value, ExaminationValue::Verdict(Verdict::True));
}

#[test]
fn test_collect_examination_core_uses_place_aliases_for_tokens_count() {
    let dir = TempDir::new().unwrap();
    write_pnml(&dir, UNFOLDED_ALIAS_PT_NET);
    write_reachability_cardinality_alias_xml(&dir);

    let model = load_model_dir(dir.path()).expect("load should succeed");
    let aliases = alias_enriched(&model);
    let records = collect_examination_core(
        model.net(),
        "AliasModel",
        dir.path(),
        &aliases,
        Examination::ReachabilityCardinality,
        &ExplorationConfig::new(32),
        false,
    )
    .expect("collection should succeed");

    assert_eq!(records.len(), 1);
    assert_eq!(records[0].value, ExaminationValue::Verdict(Verdict::True));
}
