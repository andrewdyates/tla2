// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Integration tests for sunder repo TLA+ specs (#2830).
//!
//! These are real-world specs from the sunder infrastructure tool that exercise
//! Integers, Sequences, FiniteSets, TLC modules, records, model values, and
//! bounded model checking patterns. All specs use `SPECIFICATION Spec` with
//! safety-only invariants (liveness properties are commented out in cfgs).
//!
//! TLC baselines:
//!   - cargo_lock:                    PASS, 8,075,970 distinct states
//!   - cargo_lock_with_toctou:        ERROR (MutualExclusion invariant violation)
//!   - iteration_tags:                PASS, 514 distinct states
//!   - iteration_tags_with_commit_failure: PASS, 9,289 distinct states

use std::path::PathBuf;

use tla_check::{
    resolve_spec_from_config_with_extends, CheckResult, Config, FairnessConstraint, ModelChecker,
};
use tla_core::{lower, parse_to_syntax_tree, FileId, ModuleLoader};

/// Resolve the workspace-root-relative `tests/specs/sunder/` directory.
fn sunder_spec_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/specs/sunder")
        .canonicalize()
        .expect("tests/specs/sunder directory should exist")
}

/// Load a sunder spec from .tla + .cfg, returning everything needed for ModelChecker.
fn load_sunder_spec(
    name: &str,
) -> (
    tla_core::ast::Module,
    Vec<tla_core::ast::Module>,
    Config,
    Vec<FairnessConstraint>,
    bool,
) {
    let spec_dir = sunder_spec_dir();
    let spec_path = spec_dir.join(format!("{name}.tla"));
    let cfg_path = spec_dir.join(format!("{name}.cfg"));

    let spec_source = std::fs::read_to_string(&spec_path)
        .unwrap_or_else(|e| panic!("Failed to read {}: {e}", spec_path.display()));
    let tree = parse_to_syntax_tree(&spec_source);
    let mut module = lower(FileId(0), &tree)
        .module
        .unwrap_or_else(|| panic!("{name}.tla should lower successfully"));
    tla_core::compute_is_recursive(&mut module);

    let mut loader = ModuleLoader::new(&spec_path);
    loader.seed_from_syntax_tree(&tree, &spec_path);
    loader
        .load_extends(&module)
        .unwrap_or_else(|e| panic!("{name} EXTENDS should load: {e:?}"));

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
        .unwrap_or_else(|errors| panic!("{name}.cfg parse failed: {errors:?}"));
    let resolved = resolve_spec_from_config_with_extends(&config, &tree, &extended_syntax_trees)
        .unwrap_or_else(|e| panic!("{name} SPECIFICATION resolution failed: {e:?}"));
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

fn run_and_assert_pass(name: &str, expected_states: usize) {
    let (module, checker_modules, config, fairness, stuttering_allowed) = load_sunder_spec(name);
    let refs = checker_modules.iter().collect::<Vec<_>>();

    let mut checker = ModelChecker::new_with_extends(&module, &refs, &config);
    checker.set_store_states(true);
    checker.set_fairness(fairness);
    checker.set_stuttering_allowed(stuttering_allowed);

    match checker.check() {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, expected_states,
                "sunder/{name}: expected {expected_states} states (TLC baseline), got {}",
                stats.states_found
            );
        }
        CheckResult::LivenessViolation { property, .. } => {
            panic!("sunder/{name}: unexpected liveness violation for {property}");
        }
        other => panic!("sunder/{name}: expected pass, got {other:?}"),
    }
}

fn run_and_assert_invariant_violation(name: &str, expected_invariant: &str) {
    let (module, checker_modules, config, fairness, stuttering_allowed) = load_sunder_spec(name);
    let refs = checker_modules.iter().collect::<Vec<_>>();

    let mut checker = ModelChecker::new_with_extends(&module, &refs, &config);
    checker.set_store_states(true);
    checker.set_fairness(fairness);
    checker.set_stuttering_allowed(stuttering_allowed);

    match checker.check() {
        CheckResult::InvariantViolation { invariant, .. } => {
            assert_eq!(
                invariant, expected_invariant,
                "sunder/{name}: expected invariant violation for {expected_invariant}, got {invariant}"
            );
        }
        CheckResult::Error { error, .. } => {
            // TLC also finds this invariant violation — expected behavior.
            let error_str = format!("{error:?}");
            assert!(
                error_str.contains("Invariant") || error_str.contains("invariant"),
                "sunder/{name}: expected invariant violation, got: {error_str}"
            );
        }
        CheckResult::Success(stats) => {
            panic!(
                "sunder/{name}: expected invariant violation but passed with {} states",
                stats.states_found
            );
        }
        other => panic!("sunder/{name}: expected invariant violation, got {other:?}"),
    }
}

// ---- Small specs: always run ----

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn sunder_iteration_tags_passes_with_tlc_parity() {
    // TLC: 514 distinct states, 1204 states generated
    run_and_assert_pass("iteration_tags", 514);
}

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn sunder_iteration_tags_with_commit_failure_passes_with_tlc_parity() {
    // TLC: 9289 distinct states, 25657 states generated
    run_and_assert_pass("iteration_tags_with_commit_failure", 9289);
}

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn sunder_cargo_lock_with_toctou_finds_mutual_exclusion_violation() {
    // TLC finds MutualExclusion violation (TOCTOU bug) — both processes in "holding" state.
    // This is the intended behavior: the spec demonstrates a real TOCTOU race condition.
    run_and_assert_invariant_violation("cargo_lock_with_toctou", "MutualExclusion");
}

// ---- Medium spec: release-only (8M states, ~60s on TLC) ----

#[cfg_attr(test, ntest::timeout(120000))]
#[cfg(not(debug_assertions))]
#[test]
fn sunder_cargo_lock_passes_with_tlc_parity() {
    // TLC: 8,075,970 distinct states, 34,359,259 states generated, ~59s
    // Liveness properties (Progress, EventualAcquire) are stretch goals —
    // they require SPECIFICATION FairSpec and are commented out in the cfg.
    run_and_assert_pass("cargo_lock", 8_075_970);
}
