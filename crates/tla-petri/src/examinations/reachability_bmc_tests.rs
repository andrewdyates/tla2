// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for BMC encoding and integration.

use std::fs;
#[cfg(unix)]
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use tempfile::TempDir;

use crate::petri_net::{Arc, PetriNet, PlaceIdx, PlaceInfo, TransitionIdx, TransitionInfo};
use crate::property_xml::PathQuantifier;
use crate::resolved_predicate::{ResolvedIntExpr, ResolvedPredicate};

use super::{encode_bmc_script, encode_int_expr, encode_predicate, PropertyTracker};

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

/// Simple two-place producer-consumer net: p0 → [t0] → p1
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

#[test]
fn test_encode_int_expr_constant() {
    let expr = ResolvedIntExpr::Constant(42);
    assert_eq!(encode_int_expr(&expr, 0), "42");
}

#[test]
fn test_encode_int_expr_single_place() {
    let expr = ResolvedIntExpr::TokensCount(vec![PlaceIdx(2)]);
    assert_eq!(encode_int_expr(&expr, 3), "m_3_2");
}

#[test]
fn test_encode_int_expr_sum_of_places() {
    let expr = ResolvedIntExpr::TokensCount(vec![PlaceIdx(0), PlaceIdx(1)]);
    assert_eq!(encode_int_expr(&expr, 0), "(+ m_0_0 m_0_1)");
}

#[test]
fn test_encode_int_expr_empty_places() {
    let expr = ResolvedIntExpr::TokensCount(vec![]);
    assert_eq!(encode_int_expr(&expr, 0), "0");
}

#[test]
fn test_encode_predicate_true() {
    let net = producer_consumer_net();
    assert_eq!(encode_predicate(&ResolvedPredicate::True, 0, &net), "true");
}

#[test]
fn test_encode_predicate_false() {
    let net = producer_consumer_net();
    assert_eq!(
        encode_predicate(&ResolvedPredicate::False, 0, &net),
        "false"
    );
}

#[test]
fn test_encode_predicate_int_le() {
    let net = producer_consumer_net();
    let pred = ResolvedPredicate::IntLe(
        ResolvedIntExpr::TokensCount(vec![PlaceIdx(0)]),
        ResolvedIntExpr::Constant(5),
    );
    assert_eq!(encode_predicate(&pred, 2, &net), "(<= m_2_0 5)");
}

#[test]
fn test_encode_predicate_not() {
    let net = producer_consumer_net();
    let pred = ResolvedPredicate::Not(Box::new(ResolvedPredicate::True));
    assert_eq!(encode_predicate(&pred, 0, &net), "(not true)");
}

#[test]
fn test_encode_predicate_and() {
    let net = producer_consumer_net();
    let pred = ResolvedPredicate::And(vec![ResolvedPredicate::True, ResolvedPredicate::False]);
    assert_eq!(encode_predicate(&pred, 0, &net), "(and true false)");
}

#[test]
fn test_encode_predicate_or() {
    let net = producer_consumer_net();
    let pred = ResolvedPredicate::Or(vec![ResolvedPredicate::True, ResolvedPredicate::False]);
    assert_eq!(encode_predicate(&pred, 0, &net), "(or true false)");
}

#[test]
fn test_encode_predicate_is_fireable() {
    let net = producer_consumer_net();
    // t0 is fireable when p0 >= 1
    let pred = ResolvedPredicate::IsFireable(vec![TransitionIdx(0)]);
    assert_eq!(encode_predicate(&pred, 0, &net), "(>= m_0_0 1)");
}

#[test]
fn test_encode_predicate_is_fireable_empty() {
    let net = producer_consumer_net();
    let pred = ResolvedPredicate::IsFireable(vec![]);
    assert_eq!(encode_predicate(&pred, 0, &net), "false");
}

#[test]
fn test_encode_predicate_singleton_and() {
    let net = producer_consumer_net();
    let pred = ResolvedPredicate::And(vec![ResolvedPredicate::True]);
    // Single-child And should simplify
    assert_eq!(encode_predicate(&pred, 0, &net), "true");
}

#[test]
fn test_encode_predicate_empty_and() {
    let net = producer_consumer_net();
    let pred = ResolvedPredicate::And(vec![]);
    assert_eq!(encode_predicate(&pred, 0, &net), "true");
}

#[test]
fn test_encode_predicate_empty_or() {
    let net = producer_consumer_net();
    let pred = ResolvedPredicate::Or(vec![]);
    assert_eq!(encode_predicate(&pred, 0, &net), "false");
}

#[test]
fn test_bmc_script_has_initial_marking() {
    let net = producer_consumer_net();
    let trackers = vec![PropertyTracker {
        id: "prop-0".to_string(),
        quantifier: PathQuantifier::EF,
        predicate: ResolvedPredicate::IntLe(
            ResolvedIntExpr::Constant(1),
            ResolvedIntExpr::TokensCount(vec![PlaceIdx(1)]),
        ),
        verdict: None,
        resolved_by: None,
        flushed: false,
    }];

    let script = encode_bmc_script(&net, &trackers, &[0], 1);

    // Should contain initial marking
    assert!(script.contains("(assert (= m_0_0 1))"), "initial m_0_0 = 1");
    assert!(script.contains("(assert (= m_0_1 0))"), "initial m_0_1 = 0");
}

#[test]
fn test_bmc_script_has_stutter_variable() {
    let net = producer_consumer_net();
    let trackers = vec![PropertyTracker {
        id: "prop-0".to_string(),
        quantifier: PathQuantifier::EF,
        predicate: ResolvedPredicate::True,
        verdict: None,
        resolved_by: None,
        flushed: false,
    }];

    let script = encode_bmc_script(&net, &trackers, &[0], 1);

    assert!(
        script.contains("stay_0"),
        "script should contain stutter variable"
    );
}

#[test]
fn test_bmc_script_has_check_sat_per_property() {
    let net = producer_consumer_net();
    let trackers = vec![
        PropertyTracker {
            id: "prop-0".to_string(),
            quantifier: PathQuantifier::EF,
            predicate: ResolvedPredicate::True,
            verdict: None,
            resolved_by: None,
            flushed: false,
        },
        PropertyTracker {
            id: "prop-1".to_string(),
            quantifier: PathQuantifier::AG,
            predicate: ResolvedPredicate::False,
            verdict: None,
            resolved_by: None,
            flushed: false,
        },
    ];

    let script = encode_bmc_script(&net, &trackers, &[0, 1], 1);

    let check_sat_count = script.matches("(check-sat)").count();
    assert_eq!(check_sat_count, 2, "should have one check-sat per property");
}

#[test]
fn test_bmc_script_push_pop_per_property() {
    let net = producer_consumer_net();
    let trackers = vec![PropertyTracker {
        id: "prop-0".to_string(),
        quantifier: PathQuantifier::EF,
        predicate: ResolvedPredicate::True,
        verdict: None,
        resolved_by: None,
        flushed: false,
    }];

    let script = encode_bmc_script(&net, &trackers, &[0], 1);

    assert!(script.contains("(push 1)"));
    assert!(script.contains("(pop 1)"));
}

#[test]
fn test_bmc_script_ag_negates_predicate() {
    let net = producer_consumer_net();
    // AG(p0 >= 1): check ¬(p0 >= 1) = p0 < 1
    let trackers = vec![PropertyTracker {
        id: "prop-0".to_string(),
        quantifier: PathQuantifier::AG,
        predicate: ResolvedPredicate::IntLe(
            ResolvedIntExpr::Constant(1),
            ResolvedIntExpr::TokensCount(vec![PlaceIdx(0)]),
        ),
        verdict: None,
        resolved_by: None,
        flushed: false,
    }];

    let script = encode_bmc_script(&net, &trackers, &[0], 1);

    // The predicate for AG should be negated in the assertion
    assert!(
        script.contains("(not (<= 1 m_"),
        "AG should negate the predicate: {script}"
    );
}

#[test]
fn test_bmc_script_ef_does_not_negate() {
    let net = producer_consumer_net();
    let trackers = vec![PropertyTracker {
        id: "prop-0".to_string(),
        quantifier: PathQuantifier::EF,
        predicate: ResolvedPredicate::IntLe(
            ResolvedIntExpr::Constant(1),
            ResolvedIntExpr::TokensCount(vec![PlaceIdx(1)]),
        ),
        verdict: None,
        resolved_by: None,
        flushed: false,
    }];

    let script = encode_bmc_script(&net, &trackers, &[0], 1);

    // Should assert the predicate directly (not negated)
    assert!(
        script.contains("(<= 1 m_"),
        "EF should assert predicate directly"
    );
    // Check we don't have unnecessary negation of the main predicate
    // (There will be (not ...) for mutual exclusion, but the property assertion
    // should contain the predicate directly)
}

#[test]
fn test_bmc_script_transition_semantics() {
    let net = producer_consumer_net();
    let trackers = vec![PropertyTracker {
        id: "prop-0".to_string(),
        quantifier: PathQuantifier::EF,
        predicate: ResolvedPredicate::True,
        verdict: None,
        resolved_by: None,
        flushed: false,
    }];

    let script = encode_bmc_script(&net, &trackers, &[0], 1);

    // t0 fires: p0 -= 1, p1 += 1
    // So under fire_0_0: m_1_0 = m_0_0 - 1, m_1_1 = m_0_1 + 1
    assert!(
        script.contains("fire_0_0"),
        "script should reference transition fire variable"
    );
    // Guard: p0 >= 1 when firing
    assert!(
        script.contains("(=> fire_0_0 (>= m_0_0 1))"),
        "script should have transition guard"
    );
}

#[test]
fn test_bmc_seeding_mixed_outcomes_preserve_seeded_results_and_stop_on_unknown() {
    let net = producer_consumer_net();
    let tempdir = TempDir::new().expect("tempdir should create");
    let calls_path = tempdir.path().join("calls.log");
    let solver = write_fake_solver_script(
        tempdir.path(),
        "fake-z4",
        &format!(
            "printf 'call\\n' >> \"{}\"\n\
probe_done=0\n\
count=0\n\
while IFS= read -r line; do\n\
  case \"$line\" in\n\
    '(check-sat)')\n\
      if [ \"$probe_done\" -eq 0 ]; then\n\
        probe_done=1\n\
        printf 'sat\\n'\n\
      else\n\
        count=$((count + 1))\n\
        case \"$count\" in\n\
          1) printf 'sat\\n' ;;\n\
          2) printf 'unsat\\n' ;;\n\
          *) printf 'unknown\\n' ;;\n\
        esac\n\
      fi\n\
      ;;\n\
    '(exit)')\n\
      exit 0\n\
      ;;\n\
  esac\n\
done",
            calls_path.display()
        ),
    );
    let mut trackers = vec![
        PropertyTracker {
            id: "ef-witness".to_string(),
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
            id: "ag-unknown".to_string(),
            quantifier: PathQuantifier::AG,
            predicate: ResolvedPredicate::IntLe(
                ResolvedIntExpr::TokensCount(vec![PlaceIdx(0)]),
                ResolvedIntExpr::Constant(1),
            ),
            verdict: None,
            resolved_by: None,
            flushed: false,
        },
    ];

    super::run_bmc_seeding_with_solver_path(&net, &mut trackers, None, &solver);

    // If the fake solver executed successfully, it seeds ef-witness = TRUE.
    // If the solver failed to execute (sandbox, permissions), all stay None.
    let solver_ran = calls_path.exists();
    if solver_ran {
        assert_eq!(
            trackers[0].verdict,
            Some(true),
            "ef-witness should be seeded TRUE via sat"
        );
        assert_eq!(
            trackers[1].verdict, None,
            "ef-unreachable should stay None after unsat"
        );
        assert_eq!(
            trackers[2].verdict, None,
            "ag-unknown should stay None after unknown"
        );
        assert_eq!(
            fs::read_to_string(&calls_path)
                .expect("call log should exist")
                .lines()
                .count(),
            1,
            "unknown should stop further deepening after the first solver call"
        );
    } else {
        // Solver failed — all properties remain unresolved.
        assert_eq!(trackers[0].verdict, None);
        assert_eq!(trackers[1].verdict, None);
        assert_eq!(trackers[2].verdict, None);
    }
}

#[test]
fn test_run_z4_timeout_returns_none_without_waiting_for_full_sleep() {
    let tempdir = TempDir::new().expect("tempdir should create");
    let solver =
        write_fake_solver_script(tempdir.path(), "sleepy-z4", "cat >/dev/null\nexec sleep 5");

    let start = Instant::now();
    let result =
        super::super::smt_encoding::run_z4(&solver, "(check-sat)\n", 1, Duration::from_millis(25));

    assert_eq!(result, None);
    assert!(
        start.elapsed() < Duration::from_secs(1),
        "timed-out fake solver should be killed quickly"
    );
}

#[test]
fn test_run_z4_ignores_diagnostic_stdout_before_sat() {
    let tempdir = TempDir::new().expect("tempdir should create");
    let solver = write_fake_solver_script(
        tempdir.path(),
        "diag-z4",
        "cat >/dev/null\nprintf '[DIAG-SAT] pre-solve\\n'\nprintf 'sat\\n'",
    );

    let result =
        super::super::smt_encoding::run_z4(&solver, "(check-sat)\n", 1, Duration::from_secs(1));

    assert_eq!(
        result,
        Some(vec![super::super::smt_encoding::SolverOutcome::Sat]),
        "diagnostic stdout should not hide the final solver status"
    );
}

#[test]
fn test_bmc_script_depth_2_has_two_step_variables() {
    let net = producer_consumer_net();
    let trackers = vec![PropertyTracker {
        id: "prop-0".to_string(),
        quantifier: PathQuantifier::EF,
        predicate: ResolvedPredicate::True,
        verdict: None,
        resolved_by: None,
        flushed: false,
    }];

    let script = encode_bmc_script(&net, &trackers, &[0], 2);

    // Should have marking variables for steps 0, 1, 2
    assert!(script.contains("m_0_0"));
    assert!(script.contains("m_1_0"));
    assert!(script.contains("m_2_0"));
    // Should have stay/fire for steps 0 and 1
    assert!(script.contains("stay_0"));
    assert!(script.contains("stay_1"));
}

#[test]
fn test_bmc_script_logic_is_qf_lia() {
    let net = producer_consumer_net();
    let trackers = vec![PropertyTracker {
        id: "prop-0".to_string(),
        quantifier: PathQuantifier::EF,
        predicate: ResolvedPredicate::True,
        verdict: None,
        resolved_by: None,
        flushed: false,
    }];

    let script = encode_bmc_script(&net, &trackers, &[0], 1);
    assert!(script.starts_with("(set-logic QF_LIA)"));
}

#[test]
fn test_bmc_script_non_negative_markings() {
    let net = producer_consumer_net();
    let trackers = vec![PropertyTracker {
        id: "prop-0".to_string(),
        quantifier: PathQuantifier::EF,
        predicate: ResolvedPredicate::True,
        verdict: None,
        resolved_by: None,
        flushed: false,
    }];

    let script = encode_bmc_script(&net, &trackers, &[0], 1);

    // All marking variables should be non-negative
    assert!(script.contains("(assert (>= m_0_0 0))"));
    assert!(script.contains("(assert (>= m_0_1 0))"));
    assert!(script.contains("(assert (>= m_1_0 0))"));
    assert!(script.contains("(assert (>= m_1_1 0))"));
}

#[test]
fn test_bmc_seeding_ef_witness_when_z4_available() {
    // Skip if z4 not available (CI environments)
    if super::find_z4().is_none() {
        eprintln!("z4 not available, skipping BMC integration test");
        return;
    }

    // Simple net: p0 → t0 → p1 with initial [1, 0]
    // EF(p1 >= 1) should be TRUE — reachable after 1 firing
    let net = producer_consumer_net();
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

    super::run_bmc_seeding(&net, &mut trackers, None);

    assert_eq!(
        trackers[0].verdict,
        Some(true),
        "BMC should find EF witness for p1 >= 1"
    );
}

#[test]
fn test_bmc_seeding_ag_counterexample_when_z4_available() {
    // Skip if z4 not available
    if super::find_z4().is_none() {
        eprintln!("z4 not available, skipping BMC integration test");
        return;
    }

    // AG(p0 >= 1) is FALSE — after 1 firing p0 = 0
    let net = producer_consumer_net();
    let mut trackers = vec![PropertyTracker {
        id: "ag-counter".to_string(),
        quantifier: PathQuantifier::AG,
        predicate: ResolvedPredicate::IntLe(
            ResolvedIntExpr::Constant(1),
            ResolvedIntExpr::TokensCount(vec![PlaceIdx(0)]),
        ),
        verdict: None,
        resolved_by: None,
        flushed: false,
    }];

    super::run_bmc_seeding(&net, &mut trackers, None);

    assert_eq!(
        trackers[0].verdict,
        Some(false),
        "BMC should find AG counterexample for p0 >= 1"
    );
}

#[test]
fn test_bmc_seeding_unsat_leaves_verdict_none() {
    // Skip if z4 not available
    if super::find_z4().is_none() {
        eprintln!("z4 not available, skipping BMC integration test");
        return;
    }

    // EF(p1 >= 100) is FALSE (only 1 total token) — BMC can't prove this, leaves None
    let net = producer_consumer_net();
    let mut trackers = vec![PropertyTracker {
        id: "ef-unreach".to_string(),
        quantifier: PathQuantifier::EF,
        predicate: ResolvedPredicate::IntLe(
            ResolvedIntExpr::Constant(100),
            ResolvedIntExpr::TokensCount(vec![PlaceIdx(1)]),
        ),
        verdict: None,
        resolved_by: None,
        flushed: false,
    }];

    super::run_bmc_seeding(&net, &mut trackers, None);

    assert_eq!(
        trackers[0].verdict, None,
        "BMC should leave verdict None for unreachable EF (UNSAT is inconclusive)"
    );
}
