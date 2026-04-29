// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Z4 BCP integration tests — verified BCP component drops into z4-sat.
//!
//! These tests model-check the BCP (Boolean Constraint Propagation / Unit
//! Propagation) TLA+ spec from `specs/z4/BCP.tla` and verify exact state
//! counts against TLC baselines.
//!
//! BCP is the core inference engine of a CDCL SAT solver. The TLA+ spec
//! models assignment, trail, unit propagation, conflict detection, quiescence,
//! and decision branching. Four invariants are verified:
//!
//!   - TypeOK: type correctness of assignment, conflict, propagating
//!   - TrailConsistent: trail agrees with assignment function
//!   - NoSpuriousConflict: conflict only when a clause is genuinely all-false
//!   - PropagationSound: every implied literal is forced by its reason clause
//!
//! Two configurations are tested:
//!   1. MCBCP (3 variables, 4 clauses — satisfiable): 32 states
//!   2. MCBCP_Pigeon (6 variables, 9 clauses — pigeonhole 3->2, UNSAT): 1208 states
//!
//! Codegen investigation: the BCP spec is NOT yet compatible with tla-codegen
//! due to: (a) CONSTANTS requiring operator replacement via cfg, (b) EXTENDS
//! resolution not supported in codegen, (c) temporal operators in Spec.
//! See #3729 for the codegen-on-TIR prerequisite.
//!
//! Part of #3743

mod common;

use std::path::PathBuf;

use tla_check::{resolve_spec_from_config_with_extends, CheckResult, Config, ModelChecker};
use tla_core::ast::Unit;
use tla_core::{lower, parse_to_syntax_tree, FileId, ModuleLoader};

/// Returns the path to `specs/z4/` in the workspace root.
fn z4_spec_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../specs/z4")
        .canonicalize()
        .expect("specs/z4 directory should exist")
}

/// Load a z4 spec from .tla + .cfg, returning everything needed for ModelChecker.
///
/// Handles EXTENDS resolution (e.g., MCBCP extends BCP which extends Integers,
/// Sequences, FiniteSets) and CONSTANT operator replacement (e.g., NumVars <- MCNumVars).
fn load_z4_spec(
    spec_name: &str,
    cfg_name: &str,
) -> (
    tla_core::ast::Module,
    Vec<tla_core::ast::Module>,
    Config,
    Vec<tla_check::FairnessConstraint>,
    bool,
) {
    let spec_dir = z4_spec_dir();
    let spec_path = spec_dir.join(format!("{spec_name}.tla"));
    let cfg_path = spec_dir.join(format!("{cfg_name}.cfg"));

    let spec_source = std::fs::read_to_string(&spec_path)
        .unwrap_or_else(|e| panic!("Failed to read {}: {e}", spec_path.display()));
    let tree = parse_to_syntax_tree(&spec_source);
    let mut module = lower(FileId(0), &tree)
        .module
        .unwrap_or_else(|| panic!("{spec_name}.tla should lower successfully"));
    tla_core::compute_is_recursive(&mut module);

    let mut loader = ModuleLoader::new(&spec_path);
    loader.seed_from_syntax_tree(&tree, &spec_path);
    loader
        .load_extends(&module)
        .unwrap_or_else(|e| panic!("{spec_name} EXTENDS should load: {e:?}"));

    let (extended_modules_for_resolve, _instanced) =
        loader.modules_for_semantic_resolution(&module);
    let checker_modules = loader
        .modules_for_model_checking(&module)
        .into_iter()
        .cloned()
        .collect::<Vec<_>>();
    let extended_syntax_trees: Vec<_> = extended_modules_for_resolve
        .iter()
        .filter_map(|m| loader.get(m.name.node.as_str()).map(|l| &l.syntax_tree))
        .collect();

    let config_source = std::fs::read_to_string(&cfg_path)
        .unwrap_or_else(|e| panic!("Failed to read {}: {e}", cfg_path.display()));
    let mut config = Config::parse(&config_source)
        .unwrap_or_else(|errors| panic!("{cfg_name}.cfg parse failed: {errors:?}"));
    let resolved = resolve_spec_from_config_with_extends(&config, &tree, &extended_syntax_trees)
        .unwrap_or_else(|e| panic!("{spec_name} SPECIFICATION resolution failed: {e:?}"));
    if config.init.is_none() {
        config.init = Some(resolved.init.clone());
    }
    if config.next.is_none() {
        config.next = Some(resolved.next.clone());
    }

    (
        module,
        checker_modules,
        config,
        resolved.fairness,
        resolved.stuttering_allowed,
    )
}

/// Run the model checker on a z4 spec, returning (states_found, initial_states, transitions).
fn run_z4_spec(spec_name: &str, cfg_name: &str) -> (CheckResult, usize, usize, usize) {
    let (module, checker_modules, config, fairness, stuttering_allowed) =
        load_z4_spec(spec_name, cfg_name);
    let refs = checker_modules.iter().collect::<Vec<_>>();

    let mut checker = ModelChecker::new_with_extends(&module, &refs, &config);
    checker.set_store_states(true);
    checker.set_fairness(fairness);
    checker.set_stuttering_allowed(stuttering_allowed);

    let result = checker.check();
    match &result {
        CheckResult::Success(stats) => (
            result.clone(),
            stats.states_found,
            stats.initial_states,
            stats.transitions,
        ),
        other => (other.clone(), 0, 0, 0),
    }
}

// ============================================================================
// Test 1: MCBCP — 3-variable satisfiable SAT instance
// ============================================================================
//
// Clauses: {1,2}, {-1,3}, {-2,-3}, {1,-2,3}
// Variables: x1, x2, x3
// Satisfiable (e.g., x1=T, x2=F, x3=T)
//
// TLC baseline: 32 distinct states, 1 initial state, 46 transitions
// All 4 invariants (TypeOK, TrailConsistent, NoSpuriousConflict, PropagationSound) hold.

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn z4_bcp_3var_sat_state_count_matches_tlc() {
    let (result, states_found, initial_states, transitions) = run_z4_spec("MCBCP", "MCBCP");

    match &result {
        CheckResult::Success(_) => {}
        other => {
            panic!("MCBCP (3-var SAT) should succeed with no invariant violations, got: {other:?}")
        }
    }

    assert_eq!(
        states_found, 32,
        "MCBCP (3-var SAT): TLC baseline is 32 distinct states, got {states_found}"
    );
    assert_eq!(
        initial_states, 1,
        "MCBCP should have exactly 1 initial state (all UNSET), got {initial_states}"
    );
    assert_eq!(
        transitions, 46,
        "MCBCP: TLC baseline is 46 transitions, got {transitions}"
    );
}

// ============================================================================
// Test 2: MCBCP with CHECK_DEADLOCK FALSE — same 3-variable instance
// ============================================================================
//
// Same spec, but with deadlock check explicitly disabled. State count should
// be identical. Tests that the cfg directive is respected.

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn z4_bcp_3var_sat_no_deadlock_check() {
    let (result, states_found, _initial, _transitions) = run_z4_spec("MCBCP", "MCBCP_noDeadlock");

    match &result {
        CheckResult::Success(_) => {}
        other => panic!("MCBCP with CHECK_DEADLOCK FALSE should succeed, got: {other:?}"),
    }

    assert_eq!(
        states_found, 32,
        "MCBCP with no-deadlock: should still find 32 distinct states, got {states_found}"
    );
}

// ============================================================================
// Test 3: MCBCP_Pigeon — pigeonhole 3->2 (UNSAT instance)
// ============================================================================
//
// 3 pigeons into 2 holes: UNSAT. 6 variables, 9 clauses.
// BCP + decisions explores all possible assignments, always reaching conflict.
//
// TLC baseline: 1208 distinct states, 1 initial state, 2047 transitions
// All 4 invariants hold (the spec correctly detects conflicts without spurious claims).

#[cfg_attr(test, ntest::timeout(60000))]
#[test]
fn z4_bcp_pigeonhole_unsat_state_count_matches_tlc() {
    let (result, states_found, initial_states, transitions) =
        run_z4_spec("MCBCP_Pigeon", "MCBCP_Pigeon");

    match &result {
        CheckResult::Success(_) => {}
        other => panic!(
            "MCBCP_Pigeon (pigeonhole 3->2) should succeed with no invariant violations, got: {other:?}"
        ),
    }

    assert_eq!(
        states_found, 1208,
        "MCBCP_Pigeon: TLC baseline is 1208 distinct states, got {states_found}"
    );
    assert_eq!(
        initial_states, 1,
        "MCBCP_Pigeon should have exactly 1 initial state, got {initial_states}"
    );
    assert_eq!(
        transitions, 2047,
        "MCBCP_Pigeon: TLC baseline is 2047 transitions, got {transitions}"
    );
}

// ============================================================================
// Test 4: Invariant verification — all 4 BCP invariants pass on both instances
// ============================================================================
//
// This test explicitly verifies that the config contains exactly 4 invariants
// and that the model checker validated all of them without violation.

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn z4_bcp_all_four_invariants_verified() {
    let expected_invariants = [
        "TypeOK",
        "TrailConsistent",
        "NoSpuriousConflict",
        "PropagationSound",
    ];

    // Check MCBCP config has all 4 invariants
    let (_module, _checker_modules, config, _fairness, _stuttering) =
        load_z4_spec("MCBCP", "MCBCP");
    assert_eq!(
        config.invariants.len(),
        4,
        "MCBCP config should have exactly 4 invariants, got: {:?}",
        config.invariants
    );
    for inv in &expected_invariants {
        assert!(
            config.invariants.contains(&inv.to_string()),
            "MCBCP config missing invariant: {inv}"
        );
    }

    // Check MCBCP_Pigeon config has all 4 invariants
    let (_module, _checker_modules, config, _fairness, _stuttering) =
        load_z4_spec("MCBCP_Pigeon", "MCBCP_Pigeon");
    assert_eq!(
        config.invariants.len(),
        4,
        "MCBCP_Pigeon config should have exactly 4 invariants, got: {:?}",
        config.invariants
    );
    for inv in &expected_invariants {
        assert!(
            config.invariants.contains(&inv.to_string()),
            "MCBCP_Pigeon config missing invariant: {inv}"
        );
    }

    // Run both and verify success (no invariant violation)
    let (result_3var, _, _, _) = run_z4_spec("MCBCP", "MCBCP");
    match &result_3var {
        CheckResult::Success(_) => {}
        CheckResult::InvariantViolation { invariant, .. } => {
            panic!("MCBCP: invariant {invariant} violated — BCP spec has a soundness bug");
        }
        other => panic!("MCBCP: unexpected result: {other:?}"),
    }

    let (result_pigeon, _, _, _) = run_z4_spec("MCBCP_Pigeon", "MCBCP_Pigeon");
    match &result_pigeon {
        CheckResult::Success(_) => {}
        CheckResult::InvariantViolation { invariant, .. } => {
            panic!("MCBCP_Pigeon: invariant {invariant} violated — BCP spec has a soundness bug");
        }
        other => panic!("MCBCP_Pigeon: unexpected result: {other:?}"),
    }
}

// ============================================================================
// Test 5: BCP spec structure validation
// ============================================================================
//
// Verify that the BCP spec defines the expected operators and variables.
// This ensures the spec structure matches what the z4-sat solver requires.

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn z4_bcp_spec_structure_has_expected_operators() {
    let spec_dir = z4_spec_dir();
    let bcp_path = spec_dir.join("BCP.tla");

    let bcp_source = std::fs::read_to_string(&bcp_path)
        .unwrap_or_else(|e| panic!("Failed to read BCP.tla: {e}"));
    let tree = parse_to_syntax_tree(&bcp_source);
    let module = lower(FileId(0), &tree)
        .module
        .expect("BCP.tla should lower successfully");

    // Extract variables, constants, and operators from module units
    let mut var_names: Vec<String> = Vec::new();
    let mut const_names: Vec<String> = Vec::new();
    let mut op_names: Vec<String> = Vec::new();

    for unit in &module.units {
        match &unit.node {
            Unit::Variable(vars) => {
                for v in vars {
                    var_names.push(v.node.clone());
                }
            }
            Unit::Constant(consts) => {
                for c in consts {
                    const_names.push(c.name.node.clone());
                }
            }
            Unit::Operator(op) => {
                op_names.push(op.name.node.clone());
            }
            _ => {}
        }
    }

    // Verify state variables
    assert!(
        var_names.contains(&"assignment".to_string()),
        "BCP must define 'assignment' variable"
    );
    assert!(
        var_names.contains(&"trail".to_string()),
        "BCP must define 'trail' variable"
    );
    assert!(
        var_names.contains(&"conflict".to_string()),
        "BCP must define 'conflict' variable"
    );
    assert!(
        var_names.contains(&"propagating".to_string()),
        "BCP must define 'propagating' variable"
    );
    assert_eq!(var_names.len(), 4, "BCP should have exactly 4 variables");

    // Verify CONSTANTS
    assert!(
        const_names.contains(&"NumVars".to_string()),
        "BCP must declare NumVars CONSTANT"
    );
    assert!(
        const_names.contains(&"Clauses".to_string()),
        "BCP must declare Clauses CONSTANT"
    );

    // Verify key operators exist
    let expected_ops = [
        "Var",
        "Positive",
        "LitTrue",
        "LitFalse",
        "LitUnset",
        "ClauseSat",
        "ClauseConflict",
        "ClauseUnit",
        "UnitLit",
        "LitValue",
        "Init",
        "Next",
        "Propagate",
        "DetectConflict",
        "Quiesce",
        "Decide",
        "Done",
        "TrailConsistent",
        "NoSpuriousConflict",
        "PropagationSound",
        "TypeOK",
        "Spec",
    ];
    for expected in &expected_ops {
        assert!(
            op_names.iter().any(|n| n == expected),
            "BCP.tla missing expected operator: {expected}"
        );
    }
}
