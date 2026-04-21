// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for k-induction encoding and integration.

use std::fs;
#[cfg(unix)]
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::sync::{Mutex, OnceLock};

use tempfile::TempDir;

use crate::petri_net::{Arc, PetriNet, PlaceIdx, PlaceInfo, TransitionInfo};
use crate::property_xml::PathQuantifier;
use crate::resolved_predicate::{ResolvedIntExpr, ResolvedPredicate};

use super::{
    encode_kinduction_script, encode_kinduction_script_with_strengthening, find_z4,
    run_kinduction_seeding, run_kinduction_seeding_with_solver_path, PropertyTracker, DEPTH_LADDER,
    KINDUCTION_DEPTH_LADDER,
};

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

fn mutex_net() -> PetriNet {
    PetriNet {
        name: Some("mutex".to_string()),
        places: vec![place("p0"), place("p1")],
        transitions: vec![
            trans("t_enter", vec![arc(0, 1)], vec![arc(1, 1)]),
            trans("t_exit", vec![arc(1, 1)], vec![arc(0, 1)]),
        ],
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

fn with_z4_path<T>(path: &Path, f: impl FnOnce() -> T) -> T {
    static LOCK: OnceLock<Mutex<()>> = OnceLock::new();
    let _guard = LOCK
        .get_or_init(|| Mutex::new(()))
        .lock()
        .expect("z4 env lock should not be poisoned");
    let previous = std::env::var("Z4_PATH").ok();
    std::env::set_var("Z4_PATH", path);
    let result = f();
    match previous {
        Some(value) => std::env::set_var("Z4_PATH", value),
        None => std::env::remove_var("Z4_PATH"),
    }
    result
}

#[test]
fn test_kinduction_script_has_no_initial_marking() {
    let net = producer_consumer_net();
    let trackers = vec![PropertyTracker {
        id: "ag-0".to_string(),
        quantifier: PathQuantifier::AG,
        predicate: ResolvedPredicate::IntLe(
            ResolvedIntExpr::Constant(0),
            ResolvedIntExpr::TokensCount(vec![PlaceIdx(0)]),
        ),
        verdict: None,
        resolved_by: None,
        flushed: false,
    }];

    let script = encode_kinduction_script(&net, &trackers, &[0], 1);
    assert!(!script.contains("(assert (= m_0_0 1))"));
    assert!(!script.contains("(assert (= m_0_1 0))"));
    assert!(script.contains("(assert (>= m_0_0 0))"));
    assert!(script.contains("(assert (>= m_0_1 0))"));
}

#[test]
fn test_kinduction_depth_ladder_matches_bmc_for_soundness() {
    assert_eq!(
        KINDUCTION_DEPTH_LADDER, DEPTH_LADDER,
        "k-induction cannot prove deeper than the BMC base case covers"
    );
}

#[test]
fn test_kinduction_script_ag_asserts_hypothesis_then_violation() {
    let net = producer_consumer_net();
    let trackers = vec![PropertyTracker {
        id: "ag-nonneg".to_string(),
        quantifier: PathQuantifier::AG,
        predicate: ResolvedPredicate::IntLe(
            ResolvedIntExpr::Constant(0),
            ResolvedIntExpr::TokensCount(vec![PlaceIdx(0)]),
        ),
        verdict: None,
        resolved_by: None,
        flushed: false,
    }];

    let script = encode_kinduction_script(&net, &trackers, &[0], 2);
    assert!(script.contains("(assert (<= 0 m_0_0))"));
    assert!(script.contains("(assert (<= 0 m_1_0))"));
    assert!(script.contains("(assert (not (<= 0 m_2_0)))"));
}

#[test]
fn test_kinduction_script_ef_asserts_negated_hypothesis() {
    let net = producer_consumer_net();
    let trackers = vec![PropertyTracker {
        id: "ef-0".to_string(),
        quantifier: PathQuantifier::EF,
        predicate: ResolvedPredicate::IntLe(
            ResolvedIntExpr::Constant(1),
            ResolvedIntExpr::TokensCount(vec![PlaceIdx(1)]),
        ),
        verdict: None,
        resolved_by: None,
        flushed: false,
    }];

    let script = encode_kinduction_script(&net, &trackers, &[0], 1);
    assert!(script.contains("(assert (not (<= 1 m_0_1)))"));
    assert!(script.contains("(assert (<= 1 m_1_1))"));
}

#[test]
fn test_kinduction_ag_proved_when_z4_available() {
    if find_z4().is_none() {
        eprintln!("z4 not available, skipping k-induction integration test");
        return;
    }

    let net = mutex_net();
    let mut trackers = vec![PropertyTracker {
        id: "ag-safe".to_string(),
        quantifier: PathQuantifier::AG,
        predicate: ResolvedPredicate::IntLe(
            ResolvedIntExpr::TokensCount(vec![PlaceIdx(0), PlaceIdx(1)]),
            ResolvedIntExpr::Constant(1),
        ),
        verdict: None,
        resolved_by: None,
        flushed: false,
    }];

    run_kinduction_seeding(&net, &mut trackers, None, Some(16));

    assert_eq!(
        trackers[0].verdict,
        Some(true),
        "k-induction should prove AG(p0+p1<=1) on mutex net"
    );
}

#[test]
fn test_kinduction_ef_false_when_z4_available() {
    if find_z4().is_none() {
        eprintln!("z4 not available, skipping k-induction integration test");
        return;
    }

    let net = mutex_net();
    let mut trackers = vec![PropertyTracker {
        id: "ef-unreach".to_string(),
        quantifier: PathQuantifier::EF,
        predicate: ResolvedPredicate::IntLe(
            ResolvedIntExpr::Constant(2),
            ResolvedIntExpr::TokensCount(vec![PlaceIdx(0), PlaceIdx(1)]),
        ),
        verdict: None,
        resolved_by: None,
        flushed: false,
    }];

    run_kinduction_seeding(&net, &mut trackers, None, Some(16));

    assert_eq!(
        trackers[0].verdict,
        Some(false),
        "k-induction should prove EF(p0+p1>=2) = FALSE on mutex net"
    );
}

#[test]
fn test_kinduction_sat_result_leaves_verdict_none() {
    if find_z4().is_none() {
        eprintln!("z4 not available, skipping k-induction integration test");
        return;
    }

    let net = producer_consumer_net();
    let mut trackers = vec![PropertyTracker {
        id: "ag-false".to_string(),
        quantifier: PathQuantifier::AG,
        predicate: ResolvedPredicate::IntLe(
            ResolvedIntExpr::Constant(1),
            ResolvedIntExpr::TokensCount(vec![PlaceIdx(0)]),
        ),
        verdict: None,
        resolved_by: None,
        flushed: false,
    }];

    run_kinduction_seeding(&net, &mut trackers, None, Some(16));

    assert_eq!(
        trackers[0].verdict, None,
        "k-induction SAT result should leave verdict None (inconclusive)"
    );
}

#[test]
fn test_kinduction_unknown_result_leaves_verdict_none_and_stops_deepening() {
    let net = producer_consumer_net();
    let tempdir = TempDir::new().expect("tempdir should create");
    let calls_path = tempdir.path().join("calls.log");
    let solver = write_fake_solver_script(
        tempdir.path(),
        "fake-z4-kinduction-unknown",
        &format!(
            "printf 'call\\n' >> \"{}\"\ncat >/dev/null\nprintf 'unknown\\n'",
            calls_path.display()
        ),
    );
    let mut trackers = vec![PropertyTracker {
        id: "ag-unknown".to_string(),
        quantifier: PathQuantifier::AG,
        predicate: ResolvedPredicate::IntLe(
            ResolvedIntExpr::Constant(1),
            ResolvedIntExpr::TokensCount(vec![PlaceIdx(0)]),
        ),
        verdict: None,
        resolved_by: None,
        flushed: false,
    }];

    run_kinduction_seeding_with_solver_path(&net, &mut trackers, None, &solver, 17);

    let solver_ran = calls_path.exists();
    if solver_ran {
        assert_eq!(trackers[0].verdict, None);
        assert_eq!(
            fs::read_to_string(&calls_path)
                .expect("call log should exist")
                .lines()
                .count(),
            1,
            "unknown should stop further deepening after the first solver call"
        );
    } else {
        assert_eq!(trackers[0].verdict, None);
    }
}

#[test]
fn test_kinduction_respects_max_kind_depth_with_fake_solver() {
    let net = producer_consumer_net();
    let tempdir = TempDir::new().expect("tempdir should create");
    let calls_path = tempdir.path().join("calls.log");
    let solver = write_fake_solver_script(
        tempdir.path(),
        "fake-z4-kinduction-depth-cap",
        &format!(
            "printf 'call\\n' >> \"{}\"\ncat >/dev/null\nprintf 'sat\\n'",
            calls_path.display()
        ),
    );
    let mut trackers = vec![PropertyTracker {
        id: "ag-false".to_string(),
        quantifier: PathQuantifier::AG,
        predicate: ResolvedPredicate::IntLe(
            ResolvedIntExpr::Constant(1),
            ResolvedIntExpr::TokensCount(vec![PlaceIdx(0)]),
        ),
        verdict: None,
        resolved_by: None,
        flushed: false,
    }];

    run_kinduction_seeding_with_solver_path(&net, &mut trackers, None, &solver, 2);

    assert_eq!(
        fs::read_to_string(&calls_path)
            .expect("call log should exist")
            .lines()
            .count(),
        2,
        "max_kind_depth=2 should only try ladder depths 1 and 2"
    );
    assert_eq!(
        trackers[0].verdict, None,
        "SAT results remain inconclusive while the depth cap controls deepening"
    );
}

#[test]
fn test_kinduction_without_base_case_skips_solver() {
    let net = mutex_net();
    let tempdir = TempDir::new().expect("tempdir should create");
    let calls_path = tempdir.path().join("calls.log");
    let solver = write_fake_solver_script(
        tempdir.path(),
        "fake-z4-kinduction-no-base-case",
        &format!(
            "printf 'call\\n' >> \"{}\"\ncat >/dev/null\nprintf 'unsat\\n'",
            calls_path.display()
        ),
    );
    let mut trackers = vec![PropertyTracker {
        id: "ag-safe".to_string(),
        quantifier: PathQuantifier::AG,
        predicate: ResolvedPredicate::IntLe(
            ResolvedIntExpr::TokensCount(vec![PlaceIdx(0), PlaceIdx(1)]),
            ResolvedIntExpr::Constant(1),
        ),
        verdict: None,
        resolved_by: None,
        flushed: false,
    }];

    with_z4_path(&solver, || {
        run_kinduction_seeding(&net, &mut trackers, None, None)
    });

    assert_eq!(
        trackers[0].verdict, None,
        "k-induction must not run without a BMC base case"
    );
    assert!(
        !calls_path.exists(),
        "k-induction should return before resolving or invoking a solver when no base case exists"
    );
}

#[test]
fn test_kinduction_unsat_sets_ag_true_with_fake_solver() {
    let net = mutex_net();
    let tempdir = TempDir::new().expect("tempdir should create");
    let solver = write_fake_solver_script(
        tempdir.path(),
        "fake-z4-kinduction-unsat",
        "cat >/dev/null\nprintf 'unsat\\n'",
    );
    let mut trackers = vec![PropertyTracker {
        id: "ag-safe".to_string(),
        quantifier: PathQuantifier::AG,
        predicate: ResolvedPredicate::IntLe(
            ResolvedIntExpr::TokensCount(vec![PlaceIdx(0), PlaceIdx(1)]),
            ResolvedIntExpr::Constant(1),
        ),
        verdict: None,
        resolved_by: None,
        flushed: false,
    }];

    run_kinduction_seeding_with_solver_path(&net, &mut trackers, None, &solver, 17);

    assert_eq!(
        trackers[0].verdict,
        Some(true),
        "k-induction UNSAT should set AG verdict to TRUE"
    );
}

#[test]
fn test_kinduction_unsat_sets_ef_false_with_fake_solver() {
    let net = mutex_net();
    let tempdir = TempDir::new().expect("tempdir should create");
    let solver = write_fake_solver_script(
        tempdir.path(),
        "fake-z4-kinduction-unsat-ef",
        "cat >/dev/null\nprintf 'unsat\\n'",
    );
    let mut trackers = vec![PropertyTracker {
        id: "ef-unreach".to_string(),
        quantifier: PathQuantifier::EF,
        predicate: ResolvedPredicate::IntLe(
            ResolvedIntExpr::Constant(2),
            ResolvedIntExpr::TokensCount(vec![PlaceIdx(0), PlaceIdx(1)]),
        ),
        verdict: None,
        resolved_by: None,
        flushed: false,
    }];

    run_kinduction_seeding_with_solver_path(&net, &mut trackers, None, &solver, 17);

    assert_eq!(
        trackers[0].verdict,
        Some(false),
        "k-induction UNSAT should set EF verdict to FALSE (AG(¬φ) proved)"
    );
}

#[test]
fn test_kinduction_strengthened_script_contains_parikh_and_state_equation() {
    let net = producer_consumer_net();
    let trackers = vec![PropertyTracker {
        id: "ag-0".to_string(),
        quantifier: PathQuantifier::AG,
        predicate: ResolvedPredicate::IntLe(
            ResolvedIntExpr::Constant(0),
            ResolvedIntExpr::TokensCount(vec![PlaceIdx(0)]),
        ),
        verdict: None,
        resolved_by: None,
        flushed: false,
    }];

    let script = encode_kinduction_script_with_strengthening(&net, &trackers, &[0], 1, true);

    assert!(script.contains("(declare-const parikh_0 Int)"));
    assert!(script.contains("(assert (>= parikh_0 0))"));
    assert!(script.contains("(assert (= m_0_0 (+ 1 (- parikh_0))))"));
    assert!(script.contains("(assert (= m_0_1 (+ 0 parikh_0)))"));
}

#[test]
fn test_kinduction_unstrengthened_script_has_no_parikh() {
    let net = producer_consumer_net();
    let trackers = vec![PropertyTracker {
        id: "ag-0".to_string(),
        quantifier: PathQuantifier::AG,
        predicate: ResolvedPredicate::IntLe(
            ResolvedIntExpr::Constant(0),
            ResolvedIntExpr::TokensCount(vec![PlaceIdx(0)]),
        ),
        verdict: None,
        resolved_by: None,
        flushed: false,
    }];

    let script = encode_kinduction_script_with_strengthening(&net, &trackers, &[0], 1, false);

    assert!(
        !script.contains("parikh_"),
        "unstrengthened script must NOT contain Parikh variables"
    );
}

#[test]
fn test_kinduction_strengthening_enables_proof_with_fake_solver() {
    let net = producer_consumer_net();
    let tempdir = TempDir::new().expect("tempdir should create");
    let solver = write_fake_solver_script(
        tempdir.path(),
        "fake-z4-state-eq",
        "INPUT=$(cat)\nif echo \"$INPUT\" | grep -q 'parikh_'; then\n  printf 'unsat\\n'\nelse\n  printf 'sat\\n'\nfi",
    );

    let mut trackers = vec![PropertyTracker {
        id: "ag-p1-le-1".to_string(),
        quantifier: PathQuantifier::AG,
        predicate: ResolvedPredicate::IntLe(
            ResolvedIntExpr::TokensCount(vec![PlaceIdx(1)]),
            ResolvedIntExpr::Constant(1),
        ),
        verdict: None,
        resolved_by: None,
        flushed: false,
    }];

    run_kinduction_seeding_with_solver_path(&net, &mut trackers, None, &solver, 17);

    assert_eq!(
        trackers[0].verdict,
        Some(true),
        "strengthened k-induction should prove AG(p1<=1) via fake solver detecting parikh_ vars"
    );
}

#[test]
fn test_kinduction_pinvariant_equalities_in_script() {
    // Mutex net: p0 + p1 is conserved (always = 1). The P-invariant
    // y = [1, 1] with token_count = 1 should appear as equalities at every step.
    let net = mutex_net();
    let trackers = vec![PropertyTracker {
        id: "ag-safe".to_string(),
        quantifier: PathQuantifier::AG,
        predicate: ResolvedPredicate::IntLe(
            ResolvedIntExpr::TokensCount(vec![PlaceIdx(0), PlaceIdx(1)]),
            ResolvedIntExpr::Constant(1),
        ),
        verdict: None,
        resolved_by: None,
        flushed: false,
    }];

    let script = encode_kinduction_script_with_strengthening(&net, &trackers, &[0], 1, true);

    // P-invariant: m_0_0 + m_0_1 = 1 at step 0
    assert!(
        script.contains("(assert (= (+ m_0_0 m_0_1) 1))"),
        "strengthened script should contain P-invariant equality at step 0.\nScript:\n{script}"
    );
    // P-invariant: m_1_0 + m_1_1 = 1 at step 1
    assert!(
        script.contains("(assert (= (+ m_1_0 m_1_1) 1))"),
        "strengthened script should contain P-invariant equality at step 1.\nScript:\n{script}"
    );
}

#[test]
fn test_kinduction_unstrengthened_script_has_no_pinvariant() {
    let net = mutex_net();
    let trackers = vec![PropertyTracker {
        id: "ag-safe".to_string(),
        quantifier: PathQuantifier::AG,
        predicate: ResolvedPredicate::IntLe(
            ResolvedIntExpr::TokensCount(vec![PlaceIdx(0), PlaceIdx(1)]),
            ResolvedIntExpr::Constant(1),
        ),
        verdict: None,
        resolved_by: None,
        flushed: false,
    }];

    let script = encode_kinduction_script_with_strengthening(&net, &trackers, &[0], 1, false);

    // Without strengthening, no P-invariant equalities should appear.
    assert!(
        !script.contains("(assert (= (+ m_0_0 m_0_1) 1))"),
        "unstrengthened script must not contain P-invariant equalities"
    );
}

#[test]
fn test_kinduction_pinvariant_strengthening_enables_proof_with_fake_solver() {
    let net = mutex_net();
    let tempdir = TempDir::new().expect("tempdir should create");
    // Match the exact P-invariant assertions so this regression fails if the
    // encoder keeps generic strengthening but stops emitting invariant rows.
    let solver = write_fake_solver_script(
        tempdir.path(),
        "fake-z4-pinvariant",
        "INPUT=$(cat)\nif printf '%s' \"$INPUT\" | grep -Fq '(assert (= (+ m_0_0 m_0_1) 1))' &&\n   printf '%s' \"$INPUT\" | grep -Fq '(assert (= (+ m_1_0 m_1_1) 1))'; then\n  printf 'unsat\\n'\nelse\n  printf 'sat\\n'\nfi",
    );

    let mut trackers = vec![PropertyTracker {
        id: "ag-safe".to_string(),
        quantifier: PathQuantifier::AG,
        predicate: ResolvedPredicate::IntLe(
            ResolvedIntExpr::TokensCount(vec![PlaceIdx(0), PlaceIdx(1)]),
            ResolvedIntExpr::Constant(1),
        ),
        verdict: None,
        resolved_by: None,
        flushed: false,
    }];

    run_kinduction_seeding_with_solver_path(&net, &mut trackers, None, &solver, 17);

    assert_eq!(
        trackers[0].verdict,
        Some(true),
        "P-invariant equalities should be sufficient for the fake solver to prove AG(p0+p1<=1)"
    );
}

#[test]
fn test_liveness_bmc_rejects_depth_two_only_kinduction_with_fake_solver() {
    let net = producer_consumer_net();
    let tempdir = TempDir::new().expect("tempdir should create");
    let calls_path = tempdir.path().join("calls.log");
    let script_path = tempdir.path().join("solver-input.smt2");
    let solver = write_fake_solver_script(
        tempdir.path(),
        "fake-z4-liveness-depth-filter",
        &format!(
            "cat > \"{}\"\n\
             if grep -q 'parikh_' \"{}\"; then\n\
               if grep -q 'stay_1' \"{}\" || grep -q 'm_2_' \"{}\"; then\n\
                 printf 'kinduction-depth>1\\n' >> \"{}\"\n\
                 printf 'unsat\\n'\n\
               else\n\
                 printf 'kinduction-depth1\\n' >> \"{}\"\n\
                 printf 'sat\\n'\n\
               fi\n\
             else\n\
               printf 'bmc\\n' >> \"{}\"\n\
               printf 'sat\\n'\n\
             fi",
            script_path.display(),
            script_path.display(),
            script_path.display(),
            script_path.display(),
            calls_path.display(),
            calls_path.display(),
            calls_path.display()
        ),
    );

    let result = with_z4_path(&solver, || {
        crate::examinations::global_properties_bmc::run_liveness_bmc(&net, None)
    });
    assert_eq!(
        result, None,
        "depth-1-only liveness must reject a solver that proves inductive only at depth >1"
    );

    let calls = fs::read_to_string(&calls_path).expect("call log should exist");
    assert_eq!(
        calls.lines().collect::<Vec<_>>(),
        vec!["kinduction-depth1"],
        "run_liveness_bmc must stop after the depth-1 k-induction failure"
    );
}

#[test]
fn test_kinduction_pinvariant_with_z4() {
    // Integration test: mutex net with P-invariant strengthening.
    // AG(p0 + p1 <= 1) is 1-inductive WITH P-invariant strengthening:
    // The invariant p0+p1=1 constrains all steps, so the solver can prove
    // that no reachable marking violates the bound.
    if find_z4().is_none() {
        eprintln!("z4 not available, skipping P-invariant k-induction integration test");
        return;
    }

    let net = mutex_net();
    let mut trackers = vec![PropertyTracker {
        id: "ag-safe".to_string(),
        quantifier: PathQuantifier::AG,
        predicate: ResolvedPredicate::IntLe(
            ResolvedIntExpr::TokensCount(vec![PlaceIdx(0), PlaceIdx(1)]),
            ResolvedIntExpr::Constant(1),
        ),
        verdict: None,
        resolved_by: None,
        flushed: false,
    }];

    run_kinduction_seeding(&net, &mut trackers, None, Some(16));

    assert_eq!(
        trackers[0].verdict,
        Some(true),
        "k-induction with P-invariant strengthening should prove AG(p0+p1<=1)"
    );
}
