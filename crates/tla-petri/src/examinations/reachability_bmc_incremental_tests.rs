// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::fs;
#[cfg(unix)]
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};

use tempfile::TempDir;

use crate::petri_net::{Arc, PetriNet, PlaceIdx, PlaceInfo, TransitionInfo};
use crate::property_xml::PathQuantifier;
use crate::resolved_predicate::{ResolvedIntExpr, ResolvedPredicate};

use super::super::reachability::PropertyTracker;

fn place(id: &str) -> PlaceInfo {
    PlaceInfo {
        id: id.to_string(),
        name: None,
    }
}

fn arc(place: u32, weight: u64) -> Arc {
    Arc {
        place: PlaceIdx(place),
        weight,
    }
}

fn trans(id: &str, inputs: Vec<Arc>, outputs: Vec<Arc>) -> TransitionInfo {
    TransitionInfo {
        id: id.to_string(),
        name: None,
        inputs,
        outputs,
    }
}

fn producer_consumer_net() -> PetriNet {
    PetriNet {
        name: Some("test".to_string()),
        places: vec![place("p0"), place("p1")],
        transitions: vec![trans("t0", vec![arc(0, 1)], vec![arc(1, 1)])],
        initial_marking: vec![1, 0],
    }
}

fn write_fake_solver_script(dir: &Path, name: &str, body: &str) -> PathBuf {
    let path = dir.join(name);
    let script = format!("#!/bin/sh\nset -eu\n{body}\n");
    fs::write(&path, script).expect("failed to write fake solver script");
    #[cfg(unix)]
    {
        let mut perms = fs::metadata(&path)
            .expect("script metadata should exist")
            .permissions();
        perms.set_mode(0o755);
        fs::set_permissions(&path, perms).expect("failed to mark fake solver executable");
    }
    path
}

fn sample_trackers() -> Vec<PropertyTracker> {
    vec![
        PropertyTracker {
            id: "ef-reach".to_string(),
            quantifier: PathQuantifier::EF,
            predicate: ResolvedPredicate::IntLe(
                ResolvedIntExpr::Constant(1),
                ResolvedIntExpr::TokensCount(vec![PlaceIdx(1)]),
            ),
            verdict: None,
            resolved_by: None,
            flushed: false,
        },
        PropertyTracker {
            id: "ef-unreachable".to_string(),
            quantifier: PathQuantifier::EF,
            predicate: ResolvedPredicate::IntLe(
                ResolvedIntExpr::Constant(100),
                ResolvedIntExpr::TokensCount(vec![PlaceIdx(1)]),
            ),
            verdict: None,
            resolved_by: None,
            flushed: false,
        },
        PropertyTracker {
            id: "ag-counterexample".to_string(),
            quantifier: PathQuantifier::AG,
            predicate: ResolvedPredicate::IntLe(
                ResolvedIntExpr::TokensCount(vec![PlaceIdx(1)]),
                ResolvedIntExpr::Constant(0),
            ),
            verdict: None,
            resolved_by: None,
            flushed: false,
        },
    ]
}

fn tracker_summary(trackers: &[PropertyTracker]) -> Vec<(String, Option<bool>)> {
    trackers
        .iter()
        .map(|tracker| (tracker.id.clone(), tracker.verdict))
        .collect()
}

#[test]
fn test_bmc_seeding_falls_back_to_batch_when_incremental_probe_fails() {
    let net = producer_consumer_net();
    let tempdir = TempDir::new().expect("tempdir should create");
    let calls_path = tempdir.path().join("calls.log");
    let solver = write_fake_solver_script(
        tempdir.path(),
        "fake-z4-batch-only",
        &format!(
            "printf 'call\\n' >> \"{}\"\ncat >/dev/null\nprintf 'sat\\n'",
            calls_path.display()
        ),
    );
    let mut trackers = vec![PropertyTracker {
        id: "ef-reach".to_string(),
        quantifier: PathQuantifier::EF,
        predicate: ResolvedPredicate::IntLe(
            ResolvedIntExpr::Constant(1),
            ResolvedIntExpr::TokensCount(vec![PlaceIdx(1)]),
        ),
        verdict: None,
        resolved_by: None,
        flushed: false,
    }];

    super::run_bmc_seeding_with_solver_path(&net, &mut trackers, None, &solver);

    assert_eq!(
        trackers[0].verdict,
        Some(true),
        "batch fallback should preserve the original witness semantics"
    );
    assert_eq!(
        fs::read_to_string(&calls_path)
            .expect("call log should exist")
            .lines()
            .count(),
        2,
        "incremental probe should fail first, then batch fallback should rerun once"
    );
}

#[test]
fn test_incremental_bmc_matches_batch_verdicts_and_depth() {
    let Some(z4_path) = super::find_z4() else {
        eprintln!("SKIP: z4 not available for incremental-vs-batch parity test");
        return;
    };

    let net = producer_consumer_net();
    let tempdir = TempDir::new().expect("tempdir should create");
    let batch_calls_path = tempdir.path().join("batch-calls.log");
    let batch_solver = write_fake_solver_script(
        tempdir.path(),
        "z4-batch-proxy",
        &format!(
            "printf 'call\\n' >> \"{}\"\n\
stdin_copy=\"{}\"\n\
cat > \"$stdin_copy\"\n\
line_count=$(wc -l < \"$stdin_copy\")\n\
check_sat_count=$(grep -Fxc '(check-sat)' \"$stdin_copy\" || true)\n\
if [ \"$line_count\" -eq 3 ] && [ \"$check_sat_count\" -eq 1 ] && grep -Fqx '(push 1)' \"$stdin_copy\" && grep -Fqx '(pop 1)' \"$stdin_copy\"; then\n  exit 1\nfi\n\
exec \"{}\" -smt2 -in < \"$stdin_copy\"",
            batch_calls_path.display(),
            tempdir.path().join("batch-input.smt2").display(),
            z4_path.display()
        ),
    );

    let mut incremental_trackers = sample_trackers();
    let mut batch_trackers = sample_trackers();

    let incremental_depth =
        super::run_bmc_seeding_with_solver_path(&net, &mut incremental_trackers, None, &z4_path);
    let batch_depth =
        super::run_bmc_seeding_with_solver_path(&net, &mut batch_trackers, None, &batch_solver);

    assert_eq!(
        tracker_summary(&incremental_trackers),
        tracker_summary(&batch_trackers),
        "incremental BMC should preserve the same seeded verdicts as batch fallback"
    );
    assert_eq!(
        incremental_depth, batch_depth,
        "incremental BMC should stop deepening at the same depth as batch fallback"
    );
    assert_eq!(
        tracker_summary(&incremental_trackers),
        vec![
            ("ef-reach".to_string(), Some(true)),
            ("ef-unreachable".to_string(), None),
            ("ag-counterexample".to_string(), Some(false)),
        ],
        "the parity fixture should seed the EF witness and AG counterexample identically"
    );
    assert!(
        incremental_depth.is_some(),
        "both parity paths should complete at least one ladder depth"
    );
    assert_eq!(
        fs::read_to_string(&batch_calls_path)
            .expect("batch proxy call log should exist")
            .lines()
            .count(),
        6,
        "batch parity path should include one failed probe plus five batch depth invocations"
    );
}
