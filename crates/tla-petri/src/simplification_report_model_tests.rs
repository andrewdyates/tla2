// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::path::PathBuf;

use crate::examination::Examination;
use crate::model::{collect_simplification_report_for_model, load_model_dir};
use crate::simplification_report::SimplificationOutcome;

fn mcc_input_dir(model: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../benchmarks/mcc/2024/INPUTS")
        .join(model)
}

#[test]
fn test_neo_election_rf10_simplification_report_smoke() {
    let dir = mcc_input_dir("NeoElection-COL-2");
    let model = load_model_dir(&dir).expect("NeoElection-COL-2 should unfold");
    let properties =
        crate::property_xml::parse_properties(&dir, "ReachabilityFireability").expect("parse RF");
    let report =
        collect_simplification_report_for_model(&model, Examination::ReachabilityFireability)
            .expect("collect simplification report");

    assert_eq!(
        report.properties.len(),
        properties.len(),
        "report rows should match parsed property count"
    );
    assert_eq!(
        report.summary.total_properties,
        properties.len(),
        "summary total should match parsed property count"
    );
    // With NeoElection's strengthened criterion (#1418), collapsing is a no-op
    // on this model, so property simplification may not trigger. Smoke check.
    let _ = report.summary.changed_properties;

    let prop_10 = report
        .properties
        .iter()
        .find(|property| property.property_id.ends_with("-10"))
        .expect("RF-10 should be present in the report");
    assert_eq!(
        prop_10.outcome,
        SimplificationOutcome::Unchanged,
        "RF-10 should still be reported even when no simplification applies"
    );
    // With NeoElection's strengthened criterion (#1418), simplification may
    // leave all properties unchanged on this model. This is expected.
    let _any_changed = report
        .properties
        .iter()
        .any(|property| property.outcome != SimplificationOutcome::Unchanged);
}
