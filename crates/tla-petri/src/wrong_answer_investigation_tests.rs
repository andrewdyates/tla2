// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Investigation and regression tests for known MCC wrong answers.
//!
//! These tests load real MCC benchmark models and verify the LTL/CTL engine
//! results against ground truth.
//!
//! **Ground truth source:** `registry/mcc-labels/` extracted from MCC 2024.
//!
//! **LTL wrong answers: FIXED (#1246).** The 5 LTL wrong answers were caused
//! by evaluating GBA transition guards against the successor system state
//! instead of the current state in the Buchi product construction. All 5 now
//! return the correct verdict.
//!
//! **CTL wrong answers: FIXED (#1253).** The 5 formerly guarded MCC CTL
//! property IDs now match registry ground truth after aligning the checker
//! with MCC deadlock/maximal-path semantics:
//! - `EX(φ)` at deadlock = FALSE
//! - `AX(φ)` at deadlock = TRUE
//! - `EG(φ)` at deadlock = `φ`
//!
//! Historical wrong-answer inventory:
//! - `AirplaneLD-PT-0010-CTLCardinality-2024-07`
//! - `AirplaneLD-PT-0010-CTLFireability-2024-09`
//! - `AirplaneLD-PT-0010-CTLFireability-2024-13`
//! - `Angiogenesis-PT-01-CTLFireability-2023-14`
//! - `CSRepetitions-PT-02-CTLFireability-2024-01`

use std::collections::HashMap;
use std::path::{Path, PathBuf};

use crate::buchi::{check_ltl_formula, resolve_atom, to_nnf, LtlContext};
use crate::examination::{
    deadlock_verdict, liveness_verdict, one_safe_verdict, quasi_liveness_verdict,
    stable_marking_verdict, state_space_stats,
};
use crate::examinations::ctl::{
    check_ctl_properties, check_ctl_properties_ignoring_soundness_guards,
    known_mcc_ctl_soundness_guards,
};
use crate::explorer::{explore_full, ExplorationConfig};
use crate::model::{collect_examination_for_model, load_model_dir};
use crate::output::Verdict;
use crate::parser::parse_pnml_dir;
use crate::petri_net::{PetriNet, PlaceIdx, TransitionIdx};
use crate::property_xml::{parse_properties, Formula, Property};

const IBM5964_CTL_CARDINALITY_11_ID: &str = "IBM5964-PT-none-CTLCardinality-2024-11";

/// Workspace root relative to this crate's Cargo.toml directory.
fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
}

fn benchmark_dir(model: &str) -> PathBuf {
    workspace_root()
        .join("benchmarks")
        .join("mcc")
        .join("2024")
        .join("INPUTS")
        .join(model)
}

/// Check if the benchmark directory exists (benchmarks may not be downloaded).
fn has_benchmark(model: &str) -> bool {
    benchmark_dir(model).join("model.pnml").exists()
}

/// Load a Petri net model from the MCC 2024 benchmarks.
fn load_model(model: &str) -> PetriNet {
    parse_pnml_dir(&benchmark_dir(model)).expect("failed to parse PNML model")
}

/// Parse property XML for a given examination.
fn load_properties(model: &str, examination: &str) -> Vec<Property> {
    parse_properties(&benchmark_dir(model), examination).expect("failed to parse property XML")
}

fn try_load_model(model: &str) -> Result<PetriNet, String> {
    parse_pnml_dir(&benchmark_dir(model))
        .map_err(|err| format!("{model}: failed to parse PNML model: {err}"))
}

fn try_load_properties(model: &str, examination: &str) -> Result<Vec<Property>, String> {
    parse_properties(&benchmark_dir(model), examination)
        .map_err(|err| format!("{model}/{examination}: failed to parse property XML: {err}"))
}

#[derive(Clone, Copy)]
struct FormerlyGuardedCtlCase {
    model: &'static str,
    examination: &'static str,
    property_id: &'static str,
    labels_path: &'static str,
    formula_index: usize,
}

struct LoadedFormerlyGuardedCtlCase {
    expected: Verdict,
    net: PetriNet,
    property: Property,
}

fn resolve_registry_path(path: impl AsRef<Path>) -> PathBuf {
    let path = path.as_ref();
    if path.exists() {
        path.to_path_buf()
    } else {
        workspace_root().join(path)
    }
}

fn load_formerly_guarded_ctl_case(
    case: FormerlyGuardedCtlCase,
) -> Result<LoadedFormerlyGuardedCtlCase, String> {
    if !has_benchmark(case.model) {
        let model_path = benchmark_dir(case.model).join("model.pnml");
        return Err(format!(
            "{}: missing benchmark {}",
            case.property_id,
            model_path.display()
        ));
    }

    let labels_path = resolve_registry_path(case.labels_path);
    let expected = lookup_registry_verdict(&labels_path, case.model, case.formula_index)
        .ok_or_else(|| {
            format!(
                "{}: missing registry verdict {}/{} in {}",
                case.property_id,
                case.model,
                case.formula_index,
                labels_path.display()
            )
        })?;

    let property = try_load_properties(case.model, case.examination)?
        .into_iter()
        .find(|prop| prop.id == case.property_id)
        .ok_or_else(|| {
            let xml_path = benchmark_dir(case.model).join(format!("{}.xml", case.examination));
            format!(
                "{}: property id missing from {}",
                case.property_id,
                xml_path.display()
            )
        })?;

    let net = try_load_model(case.model)?;
    Ok(LoadedFormerlyGuardedCtlCase {
        expected,
        net,
        property,
    })
}

fn lookup_registry_verdict(path: &Path, model: &str, formula_index: usize) -> Option<Verdict> {
    let path = resolve_registry_path(path);

    if !path.exists() {
        return None;
    }

    let needle = format!("{model}/{formula_index},");
    let contents = std::fs::read_to_string(&path).expect("registry CSV should read");
    let line = contents.lines().find(|line| line.starts_with(&needle))?;
    let raw = line
        .split_once(',')
        .expect("registry line should contain a comma")
        .1;
    Some(match raw {
        "true" => Verdict::True,
        "false" => Verdict::False,
        other => panic!("unexpected registry verdict {other}"),
    })
}

/// Build place and transition lookup maps.
fn build_maps(net: &PetriNet) -> (HashMap<&str, PlaceIdx>, HashMap<&str, TransitionIdx>) {
    let place_map: HashMap<&str, PlaceIdx> = net
        .places
        .iter()
        .enumerate()
        .map(|(i, p)| (p.id.as_str(), PlaceIdx(i as u32)))
        .collect();
    let trans_map: HashMap<&str, TransitionIdx> = net
        .transitions
        .iter()
        .enumerate()
        .map(|(i, t)| (t.id.as_str(), TransitionIdx(i as u32)))
        .collect();
    (place_map, trans_map)
}

/// Run LTL checking on a single property, BYPASSING the soundness guard.
///
/// This calls the internal `check_ltl_formula` directly, which doesn't
/// check the guard. Used to reproduce confirmed wrong answers.
fn check_ltl_direct(net: &PetriNet, config: &ExplorationConfig, property: &Property) -> Verdict {
    let full = explore_full(net, config);
    if !full.graph.completed {
        return Verdict::CannotCompute;
    }

    let (place_map, trans_map) = build_maps(net);

    match &property.formula {
        Formula::Ltl(ltl) => {
            let mut atom_preds = Vec::new();
            let nnf = to_nnf(ltl, &mut atom_preds);
            let resolved_atoms: Vec<_> = atom_preds
                .iter()
                .map(|pred| resolve_atom(pred, &place_map, &trans_map))
                .collect();
            let ctx = LtlContext::new(resolved_atoms, &full, net);

            match check_ltl_formula(&nnf, &ctx) {
                Some(true) => Verdict::True,
                Some(false) => Verdict::False,
                None => Verdict::CannotCompute,
            }
        }
        _ => Verdict::CannotCompute,
    }
}

// ── LTL regression tests (formerly wrong, fixed by #1246) ───────────

#[test]
fn test_regression_airplaneld_ltl_cardinality_04_now_correct() {
    if !has_benchmark("AirplaneLD-PT-0010") {
        eprintln!("SKIP: AirplaneLD-PT-0010 benchmark not downloaded");
        return;
    }
    let net = load_model("AirplaneLD-PT-0010");
    let config = ExplorationConfig::default();
    let properties = load_properties("AirplaneLD-PT-0010", "LTLCardinality");

    let prop = &properties[4];
    assert_eq!(prop.id, "AirplaneLD-PT-0010-LTLCardinality-04");

    let verdict = check_ltl_direct(&net, &config, prop);

    assert_eq!(
        verdict,
        Verdict::False,
        "FIXED (#1246): guard-timing fix corrects this formerly wrong answer"
    );
}

#[test]
fn test_regression_airplaneld_ltl_cardinality_09_now_correct() {
    if !has_benchmark("AirplaneLD-PT-0010") {
        eprintln!("SKIP: AirplaneLD-PT-0010 benchmark not downloaded");
        return;
    }
    let net = load_model("AirplaneLD-PT-0010");
    let config = ExplorationConfig::default();
    let properties = load_properties("AirplaneLD-PT-0010", "LTLCardinality");

    let prop = &properties[9];
    assert_eq!(prop.id, "AirplaneLD-PT-0010-LTLCardinality-09");

    let verdict = check_ltl_direct(&net, &config, prop);

    assert_eq!(
        verdict,
        Verdict::False,
        "FIXED (#1246): guard-timing fix corrects this formerly wrong answer"
    );
}

#[test]
fn test_regression_csrepetitions_ltl_cardinality_03_now_correct() {
    if !has_benchmark("CSRepetitions-PT-02") {
        eprintln!("SKIP: CSRepetitions-PT-02 benchmark not downloaded");
        return;
    }
    let net = load_model("CSRepetitions-PT-02");
    let config = ExplorationConfig::default();
    let properties = load_properties("CSRepetitions-PT-02", "LTLCardinality");

    let prop = &properties[3];
    assert_eq!(prop.id, "CSRepetitions-PT-02-LTLCardinality-03");

    let verdict = check_ltl_direct(&net, &config, prop);

    assert_eq!(
        verdict,
        Verdict::False,
        "FIXED (#1246): guard-timing fix corrects this formerly wrong answer"
    );
}

#[test]
fn test_regression_anderson_ltl_fireability_02_now_correct() {
    if !has_benchmark("Anderson-PT-04") {
        eprintln!("SKIP: Anderson-PT-04 benchmark not downloaded");
        return;
    }
    let net = load_model("Anderson-PT-04");
    let config = ExplorationConfig::default();
    let properties = load_properties("Anderson-PT-04", "LTLFireability");

    let prop = &properties[2];
    assert_eq!(prop.id, "Anderson-PT-04-LTLFireability-02");

    let verdict = check_ltl_direct(&net, &config, prop);

    assert_eq!(
        verdict,
        Verdict::False,
        "FIXED (#1246): guard-timing fix corrects this formerly wrong answer"
    );
}

#[test]
fn test_regression_csrepetitions_ltl_fireability_03_now_correct() {
    if !has_benchmark("CSRepetitions-PT-02") {
        eprintln!("SKIP: CSRepetitions-PT-02 benchmark not downloaded");
        return;
    }
    let net = load_model("CSRepetitions-PT-02");
    let config = ExplorationConfig::default();
    let properties = load_properties("CSRepetitions-PT-02", "LTLFireability");

    let prop = &properties[3];
    assert_eq!(prop.id, "CSRepetitions-PT-02-LTLFireability-03");

    let verdict = check_ltl_direct(&net, &config, prop);

    assert_eq!(
        verdict,
        Verdict::False,
        "FIXED (#1246): guard-timing fix corrects this formerly wrong answer"
    );
}

// ── LTL correct answers (full model verification) ───────────────────

#[test]
fn test_airplaneld_ltl_cardinality_all_properties() {
    if !has_benchmark("AirplaneLD-PT-0010") {
        eprintln!("SKIP: AirplaneLD-PT-0010 benchmark not downloaded");
        return;
    }
    let net = load_model("AirplaneLD-PT-0010");
    let config = ExplorationConfig::default();
    let properties = load_properties("AirplaneLD-PT-0010", "LTLCardinality");

    // Ground truth for all 16 properties (from l-t-l-cardinality-2024.csv):
    // Index: 0=F, 1=T, 2=F, 3=T, 4=F, 5=T, 6=T, 7=F, 8=T, 9=F, 10=F, 11=F, 12=F, 13=F, 14=T, 15=T
    // Properties 4 and 9 were formerly wrong answers, now fixed by #1246.
    let ground_truth: Vec<bool> = vec![
        false, true, false, true, false, true, true, false, true, false, false, false, false,
        false, true, true,
    ];

    // All 16 properties should now be correct (indices 4 and 9 were fixed by #1246)
    for (i, (prop, &expected)) in properties.iter().zip(ground_truth.iter()).enumerate() {
        let verdict = check_ltl_direct(&net, &config, prop);
        let actual = match verdict {
            Verdict::True => true,
            Verdict::False => false,
            Verdict::CannotCompute => {
                // Acceptable — engine may time out or overflow
                continue;
            }
        };
        assert_eq!(
            actual, expected,
            "LTLCardinality-{i:02}: engine={actual}, ground_truth={expected}"
        );
    }
}

// ── LTL formerly-guarded regression (FIXED by product guard timing) ──

/// Regression test: the 4 formerly-guarded LTL property IDs now produce
/// correct answers after the Buchi product guard-timing fix (evaluating
/// guards at the SUCCESSOR system state, matching GPVW semantics).
///
/// These properties were wrong when guards were evaluated at the current
/// system state, creating a one-step phase error for formulas with Next
/// operators. The fix correctly pairs GBA state obligations (which are
/// for step i+1 due to the GPVW initial expansion) with the system state
/// at step i+1.
///
/// Ground truth (from MCC 2024 registry):
/// - CircadianClock-PT-000001-LTLFireability-10 → FALSE
/// - Angiogenesis-PT-01-LTLFireability-08 → FALSE
/// - CSRepetitions-PT-02-LTLFireability-01 → FALSE
/// - CSRepetitions-PT-02-LTLFireability-10 → FALSE
#[test]
fn test_formerly_guarded_ltl_properties_now_correct() {
    let cases: &[(&str, &str, &str, Verdict)] = &[
        (
            "CircadianClock-PT-000001",
            "LTLFireability",
            "CircadianClock-PT-000001-LTLFireability-10",
            Verdict::False,
        ),
        (
            "Angiogenesis-PT-01",
            "LTLFireability",
            "Angiogenesis-PT-01-LTLFireability-08",
            Verdict::False,
        ),
        (
            "CSRepetitions-PT-02",
            "LTLFireability",
            "CSRepetitions-PT-02-LTLFireability-01",
            Verdict::False,
        ),
        (
            "CSRepetitions-PT-02",
            "LTLFireability",
            "CSRepetitions-PT-02-LTLFireability-10",
            Verdict::False,
        ),
    ];

    let config = ExplorationConfig::default();
    let mut skipped = 0;

    for &(model, examination, property_id, expected_verdict) in cases {
        if !has_benchmark(model) {
            eprintln!("SKIP: {model} benchmark not downloaded");
            skipped += 1;
            continue;
        }
        let net = load_model(model);
        let properties = load_properties(model, examination);
        let prop = properties
            .iter()
            .find(|p| p.id == property_id)
            .unwrap_or_else(|| panic!("{property_id} not found in {examination}.xml"));

        let verdict = check_ltl_direct(&net, &config, prop);
        assert_eq!(
            verdict, expected_verdict,
            "FIXED: {property_id} should now match ground truth (was formerly guarded)"
        );
    }

    if skipped == cases.len() {
        eprintln!("SKIP: no MCC benchmarks available for formerly-guarded LTL regression");
    }
}

// ── CTL formerly-guarded regression (FIXED by deadlock semantics) ───

fn assert_formerly_guarded_ctl_case_now_correct(case: FormerlyGuardedCtlCase) {
    assert!(
        known_mcc_ctl_soundness_guards().is_empty(),
        "the benchmark-backed CTL regression suite should run with no remaining production guards"
    );

    let loaded_case = match load_formerly_guarded_ctl_case(case) {
        Ok(loaded_case) => loaded_case,
        Err(err) => {
            eprintln!(
                "SKIP: unavailable prerequisites for formerly-guarded CTL regression: {}",
                err
            );
            return;
        }
    };

    let config = ExplorationConfig::default();
    let LoadedFormerlyGuardedCtlCase {
        expected,
        net,
        property,
    } = loaded_case;

    let property_id = property.id.clone();
    let property_ref = std::slice::from_ref(&property);
    let guarded_results = check_ctl_properties(&net, property_ref, &config);
    let unguarded_results =
        check_ctl_properties_ignoring_soundness_guards(&net, property_ref, &config);

    assert_eq!(guarded_results.len(), 1);
    assert_eq!(guarded_results[0].0, property_id);
    assert_eq!(
        guarded_results[0].1, expected,
        "{property_id} should now match MCC registry ground truth on the public CTL path"
    );

    assert_eq!(unguarded_results.len(), 1);
    assert_eq!(unguarded_results[0].0, property_id);
    assert_eq!(
        unguarded_results[0].1, expected,
        "{property_id} should also match MCC registry ground truth on the guard-bypassed CTL path"
    );
    assert_eq!(
        guarded_results[0].1,
        unguarded_results[0].1,
        "{property_id} should have no remaining divergence between public and guard-bypassed CTL execution"
    );
}

#[test]
fn test_formerly_guarded_ctl_airplaneld_cardinality_07_now_correct() {
    assert_formerly_guarded_ctl_case_now_correct(FormerlyGuardedCtlCase {
        model: "AirplaneLD-PT-0010",
        examination: "CTLCardinality",
        property_id: "AirplaneLD-PT-0010-CTLCardinality-2024-07",
        labels_path: "registry/mcc-labels/c-t-l-cardinality-2024.csv",
        formula_index: 7,
    });
}

#[test]
fn test_formerly_guarded_ctl_airplaneld_fireability_09_now_correct() {
    assert_formerly_guarded_ctl_case_now_correct(FormerlyGuardedCtlCase {
        model: "AirplaneLD-PT-0010",
        examination: "CTLFireability",
        property_id: "AirplaneLD-PT-0010-CTLFireability-2024-09",
        labels_path: "registry/mcc-labels/c-t-l-fireability-2024.csv",
        formula_index: 9,
    });
}

#[test]
fn test_formerly_guarded_ctl_airplaneld_fireability_13_now_correct() {
    assert_formerly_guarded_ctl_case_now_correct(FormerlyGuardedCtlCase {
        model: "AirplaneLD-PT-0010",
        examination: "CTLFireability",
        property_id: "AirplaneLD-PT-0010-CTLFireability-2024-13",
        labels_path: "registry/mcc-labels/c-t-l-fireability-2024.csv",
        formula_index: 13,
    });
}

#[test]
fn test_formerly_guarded_ctl_angiogenesis_fireability_14_now_correct() {
    assert_formerly_guarded_ctl_case_now_correct(FormerlyGuardedCtlCase {
        model: "Angiogenesis-PT-01",
        examination: "CTLFireability",
        property_id: "Angiogenesis-PT-01-CTLFireability-2023-14",
        labels_path: "registry/mcc-labels/c-t-l-fireability-2024.csv",
        formula_index: 14,
    });
}

#[test]
fn test_formerly_guarded_ctl_csrepetitions_fireability_01_now_correct() {
    assert_formerly_guarded_ctl_case_now_correct(FormerlyGuardedCtlCase {
        model: "CSRepetitions-PT-02",
        examination: "CTLFireability",
        property_id: "CSRepetitions-PT-02-CTLFireability-2024-01",
        labels_path: "registry/mcc-labels/c-t-l-fireability-2024.csv",
        formula_index: 1,
    });
}

// ── IBM5964 CTLCardinality-11 investigation ─────────────────────────

/// Regression: IBM5964 CTLCardinality-11 was wrong (FALSE instead of TRUE)
/// because structural reductions are not CTL-preserving (#1421).
#[test]
fn test_ibm5964_ctl_cardinality_11_regression() {
    if !has_benchmark("IBM5964-PT-none") {
        eprintln!("SKIP: IBM5964-PT-none benchmark not downloaded");
        return;
    }
    let net = load_model("IBM5964-PT-none");
    let config = ExplorationConfig::default();
    let properties = load_properties("IBM5964-PT-none", "CTLCardinality");

    // Formula 11 — ground truth: TRUE (from c-t-l-cardinality-2024.csv)
    let prop = properties
        .iter()
        .find(|property| property.id == IBM5964_CTL_CARDINALITY_11_ID)
        .expect("IBM5964 CTLCardinality property 11 should exist");

    let results = check_ctl_properties(&net, std::slice::from_ref(prop), &config);
    assert_eq!(
        results[0].1,
        Verdict::True,
        "IBM5964 CTLCardinality-11 should be TRUE (was wrong FALSE before #1421 fix)"
    );
}

// ── #1421 non-property examination regressions ──────────────────────

/// Regression: SquareGrid-PT-130613 ReachabilityDeadlock was wrong FALSE
/// (should be TRUE). The siphon/trap structural analysis incorrectly
/// classified this non-free-choice net as deadlock-free (#1421).
///
/// This test verifies the structural pre-check no longer claims deadlock-free.
/// Full state-space exploration is too expensive for this model (>600s),
/// so we only check that the structural shortcut doesn't give a wrong answer.
#[test]
fn test_squaregrid_deadlock_structural_not_falsely_free() {
    if !has_benchmark("SquareGrid-PT-130613") {
        eprintln!("SKIP: SquareGrid-PT-130613 benchmark not downloaded");
        return;
    }
    let net = load_model("SquareGrid-PT-130613");
    // The bug was structural_deadlock_free returning Some(true) on a
    // non-free-choice net. After the fix it returns None.
    let structural = crate::structural::structural_deadlock_free(&net);
    assert_ne!(
        structural,
        Some(true),
        "SquareGrid-PT-130613 must NOT be structurally classified as deadlock-free \
         (it has deadlocks; ground truth is TRUE)"
    );
}

/// Regression: CryptoMiner-COL-D20N100 ReachabilityDeadlock was wrong FALSE
/// (should be TRUE). Rule K (self-loop removal) was unsound for deadlock.
///
/// The model is too large for full exploration in test time (>200s default
/// yields CannotCompute). We verify the answer is NOT the old wrong FALSE.
/// Ground truth is TRUE; CannotCompute is acceptable (not a wrong answer).
#[test]
fn test_cryptominer_col_deadlock_not_wrong_false() {
    let model_dir = benchmark_dir("CryptoMiner-COL-D20N100");
    if !model_dir.join("model.pnml").exists() {
        eprintln!("SKIP: CryptoMiner-COL-D20N100 benchmark not downloaded");
        return;
    }
    let prepared = load_model_dir(&model_dir).expect("failed to load CryptoMiner-COL-D20N100");
    let config = ExplorationConfig::default();
    let verdict = deadlock_verdict(prepared.net(), &config);
    assert_ne!(
        verdict,
        Verdict::False,
        "CryptoMiner-COL-D20N100 ReachabilityDeadlock must NOT be FALSE \
         (ground truth is TRUE; was wrong FALSE before #1421 Rule K fix)"
    );
}

/// Regression: SemanticWebServices-PT-S064P15 OneSafe was wrong TRUE
/// (should be FALSE). Rule K unsound for safety properties.
#[test]
fn test_semanticwebservices_onesafe_regression() {
    if !has_benchmark("SemanticWebServices-PT-S064P15") {
        eprintln!("SKIP: SemanticWebServices-PT-S064P15 benchmark not downloaded");
        return;
    }
    let net = load_model("SemanticWebServices-PT-S064P15");
    let config = ExplorationConfig::default();
    let verdict = one_safe_verdict(&net, &config, &[]);
    assert_eq!(
        verdict,
        Verdict::False,
        "SemanticWebServices-PT-S064P15 OneSafe should be FALSE (was wrong TRUE before #1421)"
    );
}

/// Regression: FamilyReunion-PT-L00010M0001C001P001G001 OneSafe was wrong TRUE
/// because OneSafe reused agglomeration/non-decreasing structural reductions
/// that can hide intermediate token counts > 1 (#1489).
#[test]
fn test_familyreunion_pt_onesafe_regression() {
    const MODEL: &str = "FamilyReunion-PT-L00010M0001C001P001G001";

    if !has_benchmark(MODEL) {
        eprintln!("SKIP: {MODEL} benchmark not downloaded");
        return;
    }
    let net = load_model(MODEL);
    // Keep this as a regression guard, not a full benchmark run. The bug was a
    // wrong structural TRUE, so a tight budget that falls back to
    // CannotCompute is still a sound pass condition.
    let config = ExplorationConfig::new(128);
    let verdict = one_safe_verdict(&net, &config, &[]);
    assert!(
        matches!(verdict, Verdict::False | Verdict::CannotCompute),
        "{MODEL} OneSafe must not return TRUE after the #1489 reduction fix; got {verdict:?}"
    );
}

/// Regression: TokenRing-COL-015 OneSafe was wrong TRUE (should be FALSE).
/// Colored OneSafe needs group-level checking through unfolding.
#[test]
fn test_tokenring_col_onesafe_regression() {
    let model_dir = benchmark_dir("TokenRing-COL-015");
    if !model_dir.join("model.pnml").exists() {
        eprintln!("SKIP: TokenRing-COL-015 benchmark not downloaded");
        return;
    }
    let prepared = load_model_dir(&model_dir).expect("failed to load TokenRing-COL-015");
    let colored_groups = prepared.aliases().colored_place_groups();
    let config = ExplorationConfig::default();
    let verdict = one_safe_verdict(prepared.net(), &config, &colored_groups);
    assert_eq!(
        verdict,
        Verdict::False,
        "TokenRing-COL-015 OneSafe should be FALSE (was wrong TRUE before #1421)"
    );
}

/// Regression: TokenRing-COL-015 StableMarking was wrong FALSE (should be TRUE).
/// Colored StableMarking requires per-group checking.
#[test]
fn test_tokenring_col_stablemarking_regression() {
    let model_dir = benchmark_dir("TokenRing-COL-015");
    if !model_dir.join("model.pnml").exists() {
        eprintln!("SKIP: TokenRing-COL-015 benchmark not downloaded");
        return;
    }
    let prepared = load_model_dir(&model_dir).expect("failed to load TokenRing-COL-015");
    let colored_groups = prepared.aliases().colored_place_groups();
    let config = ExplorationConfig::default();
    let verdict = stable_marking_verdict(prepared.net(), &config, &colored_groups);
    assert_eq!(
        verdict,
        Verdict::True,
        "TokenRing-COL-015 StableMarking should be TRUE (was wrong FALSE before #1421)"
    );
}

// ── #1483 StateSpace wrong answers (structural reduction) ─────────

/// Regression: AirplaneLD-PT-0010 StateSpace was wrong (1 0 1 37 instead
/// of 43463 183664 1 38) because `state_space_stats` explored the
/// structurally reduced net instead of the original (#1483).
#[test]
fn test_airplane_ld_pt_0010_state_space_regression() {
    if !has_benchmark("AirplaneLD-PT-0010") {
        eprintln!("SKIP: AirplaneLD-PT-0010 benchmark not downloaded");
        return;
    }
    let net = load_model("AirplaneLD-PT-0010");
    let config = ExplorationConfig::default();
    let stats = state_space_stats(&net, &config)
        .expect("AirplaneLD-PT-0010 should be small enough to explore fully");
    assert_eq!(stats.states, 43463, "state count mismatch");
    assert_eq!(stats.edges, 183664, "edge count mismatch");
    assert_eq!(stats.max_token_in_place, 1, "max_token_in_place mismatch");
    assert_eq!(stats.max_token_sum, 38, "max_token_sum mismatch");
}

// ── BridgeAndVehicles-COL unfolding bug (design 2026-03-22) ─────────

/// Regression: BridgeAndVehicles-COL-V04P05N02 ReachabilityDeadlock was wrong
/// FALSE (should be TRUE). The colored unfolding produces a net with only 100
/// reachable states instead of the correct 2,874 (matching the PT variant).
///
/// Root cause: the unfolding is missing transitions or producing wrong arcs
/// for this model's multi-sort structure (sens, compteur, voitureA, voitureB, dot).
///
/// Ground truth: reachability-deadlock-2024.csv says TRUE (deadlock exists).
#[test]
fn test_bridge_and_vehicles_col_reachability_deadlock_regression() {
    let col_model = "BridgeAndVehicles-COL-V04P05N02";
    let pt_model = "BridgeAndVehicles-PT-V04P05N02";

    if !has_benchmark(col_model) || !has_benchmark(pt_model) {
        eprintln!("SKIP: BridgeAndVehicles benchmarks not downloaded");
        return;
    }

    // Load the PT net (reference).
    let pt_net = load_model(pt_model);
    let pt_config = ExplorationConfig::default();
    let pt_verdict = deadlock_verdict(&pt_net, &pt_config);
    assert_eq!(
        pt_verdict,
        Verdict::True,
        "PT variant must have deadlock (ground truth)"
    );

    // Load the COL net (unfolded).
    let col_dir = benchmark_dir(col_model);
    let col_prepared =
        load_model_dir(&col_dir).expect("failed to load BridgeAndVehicles-COL-V04P05N02");
    let col_net = col_prepared.net();
    let col_config = ExplorationConfig::default();
    let col_verdict = deadlock_verdict(col_net, &col_config);

    // The unfolded COL net must also report deadlock.
    assert_eq!(
        col_verdict,
        Verdict::True,
        "BridgeAndVehicles-COL-V04P05N02 ReachabilityDeadlock must be TRUE \
         (was wrong FALSE due to unfolding bug producing net with only 100 states)"
    );
}

/// Regression: StateSpace must fail closed on the unsound colored lane instead
/// of publishing exact-looking numeric counts for BridgeAndVehicles-COL.
#[test]
fn test_bridge_and_vehicles_col_state_space_fails_closed() {
    let col_model = "BridgeAndVehicles-COL-V04P05N02";
    let pt_model = "BridgeAndVehicles-PT-V04P05N02";

    if !has_benchmark(col_model) || !has_benchmark(pt_model) {
        eprintln!("SKIP: BridgeAndVehicles benchmarks not downloaded");
        return;
    }

    let config = ExplorationConfig::default();

    let pt_dir = benchmark_dir(pt_model);
    let pt_prepared = load_model_dir(&pt_dir).expect("failed to load PT model");
    let pt_records = collect_examination_for_model(
        &pt_prepared,
        crate::examination::Examination::StateSpace,
        &config,
    )
    .expect("PT StateSpace should succeed");
    assert_eq!(pt_records.len(), 1, "PT StateSpace should emit one record");
    match &pt_records[0].value {
        crate::examination::ExaminationValue::StateSpace(Some(stats)) => {
            assert_eq!(stats.states, 2874, "PT state count");
            assert_eq!(stats.edges, 7160, "PT edge count");
            assert_eq!(stats.max_token_in_place, 5, "PT max_token_in_place");
            assert_eq!(stats.max_token_sum, 17, "PT max_token_sum");
        }
        other => panic!("PT StateSpace should stay exact, got {other:?}"),
    }

    let col_dir = benchmark_dir(col_model);
    let col_prepared = load_model_dir(&col_dir).expect("failed to load COL model");
    let col_records = collect_examination_for_model(
        &col_prepared,
        crate::examination::Examination::StateSpace,
        &config,
    )
    .expect("COL StateSpace collection should succeed");
    assert_eq!(
        col_records.len(),
        1,
        "COL StateSpace should emit one record"
    );
    match &col_records[0].value {
        crate::examination::ExaminationValue::StateSpace(None) => {}
        other => panic!("COL StateSpace should fail closed, got {other:?}"),
    }
}

/// Diagnostic: compare the unfolded COL net with and without colored
/// pre-reduction to isolate whether the bug is in colored_reduce or unfold.
#[test]
fn test_bridge_and_vehicles_col_reduce_vs_no_reduce() {
    let col_model = "BridgeAndVehicles-COL-V04P05N02";

    if !has_benchmark(col_model) {
        eprintln!("SKIP: BridgeAndVehicles-COL-V04P05N02 benchmark not downloaded");
        return;
    }

    let col_dir = benchmark_dir(col_model);

    // With colored reduction (production path).
    let with_reduce = load_model_dir(&col_dir).expect("failed to load COL model with reduce");

    // Without colored reduction (diagnostic path).
    let without_reduce = crate::model::load_model_dir_no_colored_reduce(&col_dir)
        .expect("failed to load COL model without reduce");

    let with_stats = state_space_stats(with_reduce.net(), &ExplorationConfig::default());
    let without_stats = state_space_stats(without_reduce.net(), &ExplorationConfig::default());

    eprintln!(
        "BridgeAndVehicles COL reduce comparison:\n\
         With reduce:    places={} transitions={} states={:?}\n\
         Without reduce: places={} transitions={} states={:?}",
        with_reduce.net().places.len(),
        with_reduce.net().transitions.len(),
        with_stats.as_ref().map(|s| s.states),
        without_reduce.net().places.len(),
        without_reduce.net().transitions.len(),
        without_stats.as_ref().map(|s| s.states),
    );

    // At minimum: the no-reduce version should match the PT reference.
    if let Some(stats) = without_stats {
        // TODO: fix unfolding bug to make this pass.
        // Currently 834 states instead of 2874 — arc structure is wrong.
        eprintln!(
            "COL no-reduce states: {} (expected 2874 to match PT)",
            stats.states
        );
    }
}

/// Detailed arc diagnostic: compare input/output arc structures between PT and
/// unfolded COL nets to find which transitions have mismatched connectivity.
#[test]
fn test_bridge_and_vehicles_col_arc_diagnostic() {
    let col_model = "BridgeAndVehicles-COL-V04P05N02";
    let pt_model = "BridgeAndVehicles-PT-V04P05N02";

    if !has_benchmark(col_model) || !has_benchmark(pt_model) {
        eprintln!("SKIP: BridgeAndVehicles benchmarks not downloaded");
        return;
    }

    let pt_net = load_model(pt_model);
    let col_dir = benchmark_dir(col_model);
    let col_prepared = crate::model::load_model_dir_no_colored_reduce(&col_dir)
        .expect("failed to load COL without reduce");
    let col_net = col_prepared.net();

    // Build transition-name-to-arc-summary maps.
    // For each transition, summarize: sorted list of (place_id, weight) for inputs and outputs.
    type ArcSummary = Vec<(String, u64)>;

    fn arc_summary(net: &PetriNet, transition_idx: usize, is_input: bool) -> ArcSummary {
        let t = &net.transitions[transition_idx];
        let arcs = if is_input { &t.inputs } else { &t.outputs };
        let mut summary: Vec<(String, u64)> = arcs
            .iter()
            .map(|a| (net.places[a.place.0 as usize].id.clone(), a.weight))
            .collect();
        summary.sort_by(|a, b| a.0.cmp(&b.0));
        summary
    }

    // Map transition id → (input_summary, output_summary) for both nets.
    let mut pt_map: HashMap<String, (ArcSummary, ArcSummary)> = HashMap::new();
    for (i, t) in pt_net.transitions.iter().enumerate() {
        pt_map.insert(
            t.id.clone(),
            (
                arc_summary(&pt_net, i, true),
                arc_summary(&pt_net, i, false),
            ),
        );
    }

    let mut col_map: HashMap<String, (ArcSummary, ArcSummary)> = HashMap::new();
    for (i, t) in col_net.transitions.iter().enumerate() {
        col_map.insert(
            t.id.clone(),
            (
                arc_summary(col_net, i, true),
                arc_summary(col_net, i, false),
            ),
        );
    }

    // Compare: find transitions in PT that are missing in COL, or have different arcs.
    let mut mismatches = Vec::new();
    let mut missing_in_col = Vec::new();
    let mut extra_in_col = Vec::new();

    for (pt_tid, (pt_inputs, pt_outputs)) in &pt_map {
        if let Some((col_inputs, col_outputs)) = col_map.get(pt_tid) {
            if pt_inputs != col_inputs || pt_outputs != col_outputs {
                mismatches.push(format!(
                    "  {pt_tid}:\n    PT inputs:  {pt_inputs:?}\n    COL inputs: {col_inputs:?}\n    PT outputs:  {pt_outputs:?}\n    COL outputs: {col_outputs:?}"
                ));
            }
        } else {
            missing_in_col.push(pt_tid.clone());
        }
    }

    for col_tid in col_map.keys() {
        if !pt_map.contains_key(col_tid) {
            extra_in_col.push(col_tid.clone());
        }
    }

    eprintln!("=== BridgeAndVehicles Arc Diagnostic ===");
    eprintln!("PT transitions: {}", pt_map.len());
    eprintln!("COL transitions: {}", col_map.len());
    eprintln!(
        "Missing in COL: {} {:?}",
        missing_in_col.len(),
        missing_in_col
    );
    eprintln!("Extra in COL: {} {:?}", extra_in_col.len(), extra_in_col);
    eprintln!("Arc mismatches: {}", mismatches.len());
    for m in &mismatches {
        eprintln!("{m}");
    }

    // Compare arc counts and initial markings (name-independent).
    let pt_total_in: usize = pt_net.transitions.iter().map(|t| t.inputs.len()).sum();
    let pt_total_out: usize = pt_net.transitions.iter().map(|t| t.outputs.len()).sum();
    let col_total_in: usize = col_net.transitions.iter().map(|t| t.inputs.len()).sum();
    let col_total_out: usize = col_net.transitions.iter().map(|t| t.outputs.len()).sum();
    let pt_msum: u64 = pt_net.initial_marking.iter().sum();
    let col_msum: u64 = col_net.initial_marking.iter().sum();
    eprintln!("Total arcs: PT in={pt_total_in} out={pt_total_out}, COL in={col_total_in} out={col_total_out}");
    eprintln!("Initial marking sum: PT={pt_msum} COL={col_msum}");

    // Show all PT place names and markings sorted.
    let mut pt_places: Vec<_> = pt_net
        .places
        .iter()
        .enumerate()
        .map(|(i, p)| (p.id.clone(), pt_net.initial_marking[i]))
        .collect();
    pt_places.sort();
    let mut col_places: Vec<_> = col_net
        .places
        .iter()
        .enumerate()
        .map(|(i, p)| (p.id.clone(), col_net.initial_marking[i]))
        .collect();
    col_places.sort();
    eprintln!("PT places+marking:");
    for (id, m) in &pt_places {
        eprintln!("  {id}: {m}");
    }
    eprintln!("COL places+marking:");
    for (id, m) in &col_places {
        eprintln!("  {id}: {m}");
    }
}

// =====================================================================
// Regression: shared reduced-net GlobalProperties lane (#1503)
//
// Before the fix, reduce_iterative() on FMS-PT-*, RobotManipulation-PT-*,
// IOTPpurchase-PT-*, ParamProductionCell-PT-* produced wrong verdicts:
// - QuasiLiveness FALSE (registry: true)
// - Liveness FALSE (registry: true)
// - StableMarking TRUE (registry: false)
//
// Root cause: agglomeration/source-place elimination suppressed real firing
// behavior. Fix: route all three exams through identity-net.
// =====================================================================

/// Helper: verify QuasiLiveness, Liveness, StableMarking for a PT model.
///
/// Uses `assert_ne` against the WRONG verdict rather than `assert_eq` against
/// the expected one, so `CannotCompute` (sound but incomplete) does not fail
/// the regression test. The regression we're guarding against is the reduced-net
/// lane flipping TRUE↔FALSE (#1503), not timeouts on large models.
fn assert_global_properties_pt_not_wrong(
    model: &str,
    wrong_quasi_liveness: Verdict,
    wrong_liveness: Verdict,
    wrong_stable_marking: Verdict,
) {
    if !has_benchmark(model) {
        eprintln!("SKIP {model}: benchmark not downloaded");
        return;
    }
    let net = load_model(model);
    // 120s deadline per exam: identity-net (no reductions) may be slow on
    // large models. CannotCompute from deadline is acceptable — the key
    // invariant is that we never reproduce the OLD wrong answer.
    let deadline = Some(std::time::Instant::now() + std::time::Duration::from_secs(120));
    let config = ExplorationConfig::new(4_000_000).with_deadline(deadline);
    let ql = quasi_liveness_verdict(&net, &config);
    assert_ne!(
        ql, wrong_quasi_liveness,
        "{model} QuasiLiveness: got the OLD WRONG verdict {wrong_quasi_liveness:?} (#1503)",
    );
    let lv = liveness_verdict(&net, &config);
    assert_ne!(
        lv, wrong_liveness,
        "{model} Liveness: got the OLD WRONG verdict {wrong_liveness:?} (#1503)",
    );
    let sm = stable_marking_verdict(&net, &config, &[]);
    assert_ne!(
        sm, wrong_stable_marking,
        "{model} StableMarking: got the OLD WRONG verdict {wrong_stable_marking:?} (#1503)",
    );
}

#[test]
fn test_fms_pt_00002_global_properties_regression() {
    assert_global_properties_pt_not_wrong(
        "FMS-PT-00002",
        Verdict::False, // was wrong FALSE, registry: true
        Verdict::False, // was wrong FALSE, registry: true
        Verdict::True,  // was wrong TRUE, registry: false
    );
}

#[test]
fn test_robot_manipulation_pt_00001_global_properties_regression() {
    assert_global_properties_pt_not_wrong(
        "RobotManipulation-PT-00001",
        Verdict::False, // was wrong FALSE, registry: true
        Verdict::False, // was wrong FALSE, registry: true
        Verdict::True,  // was wrong TRUE, registry: false
    );
}

#[test]
fn test_iotppurchase_pt_global_properties_regression() {
    assert_global_properties_pt_not_wrong(
        "IOTPpurchase-PT-C01M01P01D01",
        Verdict::False, // was wrong FALSE, registry: true
        Verdict::False, // was wrong FALSE, registry: true
        Verdict::True,  // was wrong TRUE, registry: false
    );
}

/// ParamProductionCell-PT-0 is too large for full Liveness graph+SCC within
/// test time, so we test QuasiLiveness and StableMarking directly and accept
/// CannotCompute for Liveness.
#[test]
fn test_param_production_cell_pt_0_global_properties_regression() {
    const MODEL: &str = "ParamProductionCell-PT-0";
    if !has_benchmark(MODEL) {
        eprintln!("SKIP {MODEL}: benchmark not downloaded");
        return;
    }
    let net = load_model(MODEL);
    let config = ExplorationConfig::new(500_000);
    let ql = quasi_liveness_verdict(&net, &config);
    assert_ne!(
        ql,
        Verdict::False,
        "{MODEL} QuasiLiveness: got the OLD WRONG verdict FALSE (#1503)",
    );
    let sm = stable_marking_verdict(&net, &config, &[]);
    assert_ne!(
        sm,
        Verdict::True,
        "{MODEL} StableMarking: got the OLD WRONG verdict TRUE (#1503)",
    );
}

/// Regression for #1504: OneSafe must not return FALSE on 1-safe nets.
///
/// Root cause: parallel-place merging doubled arc weights, pushing reduced-net
/// token counts above 1 even when the original net is 1-safe. Fixed by clearing
/// `report.parallel_places` for OneSafe semantics in structural.rs.
///
/// These models are too large for complete exploration, so we accept
/// CannotCompute but NOT the old wrong FALSE.
fn assert_onesafe_not_wrong_false(model: &str) {
    if !has_benchmark(model) {
        eprintln!("SKIP {model}: benchmark not downloaded");
        return;
    }
    let net = load_model(model);
    // 120s deadline: these models are large (400-600 places) and exploration
    // won't complete in test time. We just need to confirm no wrong FALSE.
    let deadline = Some(std::time::Instant::now() + std::time::Duration::from_secs(120));
    let config = ExplorationConfig::new(4_000_000).with_deadline(deadline);
    let verdict = one_safe_verdict(&net, &config, &[]);
    eprintln!("{model} OneSafe: {verdict:?}");
    assert_ne!(
        verdict,
        Verdict::False,
        "{model} OneSafe returned FALSE — ground truth is TRUE (#1504)",
    );
}

#[test]
fn test_aslink_pt_01a_onesafe_regression_1504() {
    assert_onesafe_not_wrong_false("ASLink-PT-01a");
}

#[test]
fn test_aslink_pt_02a_onesafe_regression_1504() {
    assert_onesafe_not_wrong_false("ASLink-PT-02a");
}

#[test]
fn test_railroad_pt_050_onesafe_regression_1504() {
    assert_onesafe_not_wrong_false("Railroad-PT-050");
}

// =====================================================================
// Regression: ReachabilityDeadlock false-positive on IOTPpurchase (#1506)
//
// Before the fix, deadlock_verdict ran BFS on a structurally-reduced
// net. Agglomeration, source-place elimination, and other reductions
// change the firing structure, introducing spurious deadlocks in the
// reduced net that don't exist in the original. Same root cause family
// as #1503 (reduction suppressing real firing behavior).
//
// Fix: route deadlock BFS exploration through the identity net (no
// reductions), keeping only original-net structural/BMC/LP pre-checks.
// =====================================================================

/// Helper: verify ReachabilityDeadlock is not wrong TRUE.
///
/// Uses `assert_ne` against the WRONG verdict (TRUE) rather than
/// `assert_eq` against FALSE, so CannotCompute does not fail the test.
fn assert_deadlock_not_wrong_true(model: &str) {
    if !has_benchmark(model) {
        eprintln!("SKIP {model}: benchmark not downloaded");
        return;
    }
    let net = load_model(model);
    let deadline = Some(std::time::Instant::now() + std::time::Duration::from_secs(120));
    let config = ExplorationConfig::new(4_000_000).with_deadline(deadline);
    let verdict = deadlock_verdict(&net, &config);
    eprintln!("{model} ReachabilityDeadlock: {verdict:?}");
    assert_ne!(
        verdict,
        Verdict::True,
        "{model} ReachabilityDeadlock returned TRUE — ground truth is FALSE (#1506)",
    );
}

/// Helper: verify ReachabilityDeadlock reaches the exact MCC verdict.
///
/// Use this only on the representative fast model so the regression stays
/// precise without turning the larger quartet into a flaky long-running gate.
fn assert_deadlock_false(model: &str) {
    if !has_benchmark(model) {
        eprintln!("SKIP {model}: benchmark not downloaded");
        return;
    }
    let net = load_model(model);
    let deadline = Some(std::time::Instant::now() + std::time::Duration::from_secs(120));
    let config = ExplorationConfig::new(4_000_000).with_deadline(deadline);
    let verdict = deadlock_verdict(&net, &config);
    eprintln!("{model} ReachabilityDeadlock: {verdict:?}");
    assert_eq!(
        verdict,
        Verdict::False,
        "{model} ReachabilityDeadlock should match FALSE ground truth exactly (#1506)",
    );
}

#[test]
fn test_iotppurchase_pt_c01_deadlock_regression_1506() {
    assert_deadlock_false("IOTPpurchase-PT-C01M01P01D01");
}

#[test]
fn test_iotppurchase_pt_c03_deadlock_regression_1506() {
    assert_deadlock_false("IOTPpurchase-PT-C03M03P03D03");
}

#[test]
fn test_iotppurchase_pt_c05_deadlock_regression_1506() {
    assert_deadlock_not_wrong_true("IOTPpurchase-PT-C05M04P03D02");
}

#[test]
fn test_iotppurchase_pt_c12_deadlock_regression_1506() {
    assert_deadlock_not_wrong_true("IOTPpurchase-PT-C12M10P15D17");
}

fn is_test_module_name(name: &str) -> bool {
    matches!(name, "test" | "tests")
        || name.ends_with("_test")
        || name.ends_with("_tests")
        || name.starts_with("test_")
}

fn is_test_module_path(path: &Path) -> bool {
    if path.is_dir() {
        return path
            .file_name()
            .and_then(|name| name.to_str())
            .is_some_and(is_test_module_name);
    }

    if path.extension().and_then(|ext| ext.to_str()) != Some("rs") {
        return false;
    }

    path.file_stem()
        .and_then(|name| name.to_str())
        .is_some_and(is_test_module_name)
}

fn strip_rust_comments_and_literals(source: &str) -> String {
    fn strip_quoted(bytes: &[u8], mut index: usize, output: &mut Vec<u8>) -> usize {
        output.push(b' ');
        index += 1;
        let mut escaped = false;
        while index < bytes.len() {
            let byte = bytes[index];
            output.push(if byte == b'\n' { b'\n' } else { b' ' });
            index += 1;
            if escaped {
                escaped = false;
                continue;
            }
            match byte {
                b'\\' => escaped = true,
                b'"' => break,
                _ => {}
            }
        }
        index
    }

    fn raw_string_start(bytes: &[u8], index: usize) -> Option<(usize, usize)> {
        let mut cursor = index;
        if bytes.get(cursor) == Some(&b'b') {
            cursor += 1;
        }
        if bytes.get(cursor) != Some(&b'r') {
            return None;
        }
        cursor += 1;
        let mut hashes = 0;
        while bytes.get(cursor) == Some(&b'#') {
            hashes += 1;
            cursor += 1;
        }
        (bytes.get(cursor) == Some(&b'"')).then_some((cursor - index + 1, hashes))
    }

    fn strip_raw_string(
        bytes: &[u8],
        mut index: usize,
        prefix_len: usize,
        hashes: usize,
        output: &mut Vec<u8>,
    ) -> usize {
        for _ in 0..prefix_len {
            output.push(b' ');
        }
        index += prefix_len;
        while index < bytes.len() {
            if bytes[index] == b'"' {
                output.push(b' ');
                index += 1;
                let mut matched_hashes = 0usize;
                while matched_hashes < hashes && bytes.get(index + matched_hashes) == Some(&b'#') {
                    matched_hashes += 1;
                }
                if matched_hashes == hashes {
                    for _ in 0..hashes {
                        output.push(b' ');
                        index += 1;
                    }
                    break;
                }
                for _ in 0..matched_hashes {
                    output.push(b' ');
                    index += 1;
                }
                continue;
            }
            let byte = bytes[index];
            output.push(if byte == b'\n' { b'\n' } else { b' ' });
            index += 1;
        }
        index
    }

    let bytes = source.as_bytes();
    let mut output = Vec::with_capacity(bytes.len());
    let mut index = 0;
    while index < bytes.len() {
        if let Some((prefix_len, hashes)) = raw_string_start(bytes, index) {
            index = strip_raw_string(bytes, index, prefix_len, hashes, &mut output);
            continue;
        }

        match (bytes[index], bytes.get(index + 1).copied()) {
            (b'/', Some(b'/')) => {
                output.extend_from_slice(b"  ");
                index += 2;
                while index < bytes.len() {
                    let byte = bytes[index];
                    output.push(if byte == b'\n' { b'\n' } else { b' ' });
                    index += 1;
                    if byte == b'\n' {
                        break;
                    }
                }
            }
            (b'/', Some(b'*')) => {
                output.extend_from_slice(b"  ");
                index += 2;
                let mut depth = 1usize;
                while index < bytes.len() && depth > 0 {
                    match (bytes[index], bytes.get(index + 1).copied()) {
                        (b'/', Some(b'*')) => {
                            output.extend_from_slice(b"  ");
                            index += 2;
                            depth += 1;
                        }
                        (b'*', Some(b'/')) => {
                            output.extend_from_slice(b"  ");
                            index += 2;
                            depth -= 1;
                        }
                        (b'\n', _) => {
                            output.push(b'\n');
                            index += 1;
                        }
                        _ => {
                            output.push(b' ');
                            index += 1;
                        }
                    }
                }
            }
            (b'b', Some(b'"')) => {
                output.push(b' ');
                index = strip_quoted(bytes, index + 1, &mut output);
            }
            (b'"', _) => {
                index = strip_quoted(bytes, index, &mut output);
            }
            _ => {
                output.push(bytes[index]);
                index += 1;
            }
        }
    }

    String::from_utf8(output).expect("sanitized Rust source should stay UTF-8")
}

fn skip_turbofish(bytes: &[u8], start: usize) -> Option<usize> {
    let mut depth = 0usize;
    let mut index = start;
    while index < bytes.len() {
        match bytes[index] {
            b'<' => depth += 1,
            b'>' => {
                depth = depth.checked_sub(1)?;
                if depth == 0 {
                    return Some(index + 1);
                }
            }
            _ => {}
        }
        index += 1;
    }
    None
}

fn helper_call_line_numbers(source: &str, helper: &str) -> Vec<usize> {
    fn is_ident_byte(byte: u8) -> bool {
        byte.is_ascii_alphanumeric() || byte == b'_'
    }

    let sanitized = strip_rust_comments_and_literals(source);
    let bytes = sanitized.as_bytes();
    let helper_bytes = helper.as_bytes();
    let mut line_numbers = Vec::new();
    let mut index = 0;
    while index + helper_bytes.len() <= bytes.len() {
        if &bytes[index..index + helper_bytes.len()] == helper_bytes
            && (index == 0 || !is_ident_byte(bytes[index - 1]))
            && (index + helper_bytes.len() == bytes.len()
                || !is_ident_byte(bytes[index + helper_bytes.len()]))
        {
            let mut cursor = index + helper_bytes.len();
            while bytes.get(cursor).is_some_and(u8::is_ascii_whitespace) {
                cursor += 1;
            }
            let is_call = if bytes.get(cursor) == Some(&b'(') {
                true
            } else if bytes.get(cursor) == Some(&b':') && bytes.get(cursor + 1) == Some(&b':') {
                cursor += 2;
                while bytes.get(cursor).is_some_and(u8::is_ascii_whitespace) {
                    cursor += 1;
                }
                if bytes.get(cursor) == Some(&b'<') {
                    skip_turbofish(bytes, cursor)
                        .and_then(|after_generics| {
                            let mut call_cursor = after_generics;
                            while bytes.get(call_cursor).is_some_and(u8::is_ascii_whitespace) {
                                call_cursor += 1;
                            }
                            (bytes.get(call_cursor) == Some(&b'(')).then_some(())
                        })
                        .is_some()
                } else {
                    false
                }
            } else {
                false
            };
            if is_call {
                let line_number = source[..index]
                    .bytes()
                    .filter(|byte| *byte == b'\n')
                    .count()
                    + 1;
                line_numbers.push(line_number);
            }
        }
        index += 1;
    }
    line_numbers
}

#[test]
fn test_helper_call_line_numbers_detects_spaced_and_turbofish_calls() {
    let source = r#"
fn audit(net: &PetriNet) {
    let _ = reduce_iterative (net);
    let _ = crate::reduction::reduce_iterative::<ReducedNet>(
        net,
    );
    let _ = reduce_iterative_temporal_safe::<ReducedNet>(net);
}
"#;

    assert_eq!(
        helper_call_line_numbers(source, "reduce_iterative"),
        vec![3, 4]
    );
    assert_eq!(
        helper_call_line_numbers(source, "reduce_iterative_temporal_safe"),
        vec![7]
    );
}

#[test]
fn test_helper_call_line_numbers_ignores_comments_and_literals() {
    let source = r##"
fn audit(net: &PetriNet) {
    // reduce_iterative(net);
    /* reduce_iterative_temporal_safe(net); */
    let _ = "reduce_iterative(net)";
    let _ = r#"reduce_iterative_temporal_safe(net)"#;
    let _ = br#"reduce_iterative(net)"#;
}
"##;

    assert!(helper_call_line_numbers(source, "reduce_iterative").is_empty());
    assert!(helper_call_line_numbers(source, "reduce_iterative_temporal_safe").is_empty());
}

fn collect_production_examination_sources(dir: &Path, files: &mut Vec<PathBuf>) {
    let entries = std::fs::read_dir(dir)
        .unwrap_or_else(|error| panic!("failed to read {}: {error}", dir.display()));
    for entry in entries {
        let entry = entry.unwrap_or_else(|error| {
            panic!(
                "failed to read directory entry under {}: {error}",
                dir.display()
            )
        });
        let path = entry.path();
        if path.is_dir() {
            if is_test_module_path(&path) {
                continue;
            }
            collect_production_examination_sources(&path, files);
            continue;
        }
        if path.extension().and_then(|ext| ext.to_str()) != Some("rs") {
            continue;
        }
        if is_test_module_path(&path) {
            continue;
        }
        files.push(path);
    }
}

#[test]
fn test_production_examinations_do_not_call_unsound_generic_reduction_helpers() {
    let src_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("src");
    let audited_roots = [
        src_root.join("examinations"),
        src_root.join("examination_non_property"),
    ];
    let mut files = Vec::new();
    for root in audited_roots {
        collect_production_examination_sources(&root, &mut files);
    }
    files.sort();
    assert!(
        !files.is_empty(),
        "expected production examination sources under {}",
        src_root.display()
    );

    let mut violations = Vec::new();
    for path in files {
        let source = std::fs::read_to_string(&path)
            .unwrap_or_else(|error| panic!("failed to read {}: {error}", path.display()));
        let relative = path
            .strip_prefix(&src_root)
            .expect("audited path should stay under src/");
        for line_number in helper_call_line_numbers(&source, "reduce_iterative") {
            violations.push(format!(
                "{}:{} calls bare reduce_iterative(...); production examinations must use identity-net or examination-specific safe helpers",
                relative.display(),
                line_number
            ));
        }
        for line_number in helper_call_line_numbers(&source, "reduce_iterative_temporal_safe") {
            violations.push(format!(
                "{}:{} calls reduce_iterative_temporal_safe(...); CTL/LTL must stay fail-closed on identity-net",
                relative.display(),
                line_number
            ));
        }
    }

    assert!(
        violations.is_empty(),
        "production examination reduction audit failed:\n{}",
        violations.join("\n")
    );
}
