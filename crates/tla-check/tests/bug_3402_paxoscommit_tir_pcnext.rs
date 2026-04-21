// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression test for #3402: `TLA2_TIR_EVAL=PCNext` must preserve the
//! depth-bounded PaxosCommit state count.

mod common;

use common::{tlaplus_examples_dir, EnvVarGuard};
use tla_check::{
    resolve_spec_from_config_with_extends, CheckResult, CheckStats, Config, LimitType, ModelChecker,
};
use tla_core::{lower, parse_to_syntax_tree, FileId, ModuleLoader};

fn load_paxoscommit() -> (
    tla_core::ast::Module,
    Vec<tla_core::ast::Module>,
    Config,
    Vec<tla_check::FairnessConstraint>,
    bool,
) {
    let spec_dir = tlaplus_examples_dir().join("specifications/transaction_commit");
    let spec_path = spec_dir.join("PaxosCommit.tla");
    let cfg_path = spec_dir.join("PaxosCommit.cfg");

    tla_core::clear_global_name_interner();
    let spec_source = std::fs::read_to_string(&spec_path)
        .unwrap_or_else(|e| panic!("Failed to read {}: {}", spec_path.display(), e));
    let tree = parse_to_syntax_tree(&spec_source);
    let mut module = lower(FileId(0), &tree)
        .module
        .expect("PaxosCommit should lower successfully");
    tla_core::compute_is_recursive(&mut module);

    let mut loader = ModuleLoader::new(&spec_path);
    loader.seed_from_syntax_tree(&tree, &spec_path);
    loader
        .load_extends(&module)
        .expect("PaxosCommit EXTENDS dependencies should load");
    loader
        .load_instances(&module)
        .expect("PaxosCommit INSTANCE dependencies should load");

    let (extended_modules_for_resolve, instanced_modules_for_resolve) =
        loader.modules_for_semantic_resolution(&module);
    let checker_modules = loader
        .modules_for_model_checking(&module)
        .into_iter()
        .cloned()
        .collect::<Vec<_>>();
    let spec_scope_module_names: Vec<&str> = extended_modules_for_resolve
        .iter()
        .chain(instanced_modules_for_resolve.iter())
        .map(|m| m.name.node.as_str())
        .collect();
    let extended_syntax_trees: Vec<_> = spec_scope_module_names
        .iter()
        .filter_map(|name| loader.get(name).map(|loaded| &loaded.syntax_tree))
        .collect();

    let config_source = std::fs::read_to_string(&cfg_path)
        .unwrap_or_else(|e| panic!("Failed to read {}: {}", cfg_path.display(), e));
    let mut config = Config::parse(&config_source).unwrap_or_else(|errors| {
        panic!(
            "Failed to parse {}: {} error(s)",
            cfg_path.display(),
            errors.len()
        )
    });
    let resolved = resolve_spec_from_config_with_extends(&config, &tree, &extended_syntax_trees)
        .expect("PaxosCommit SPECIFICATION should resolve across extended modules");
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

fn run_paxoscommit_depth_10(
    module: &tla_core::ast::Module,
    checker_modules: &[tla_core::ast::Module],
    config: &Config,
    fairness: Vec<tla_check::FairnessConstraint>,
    stuttering_allowed: bool,
) -> tla_check::CheckStats {
    tla_check::eval::clear_for_test_reset();

    let checker_module_refs = checker_modules.iter().collect::<Vec<_>>();
    let mut checker = ModelChecker::new_with_extends(module, &checker_module_refs, config);
    checker.set_max_depth(10);
    checker.set_fairness(fairness);
    checker.set_stuttering_allowed(stuttering_allowed);

    match checker.check() {
        CheckResult::LimitReached { limit_type, stats } => {
            assert_eq!(limit_type, LimitType::Depth, "expected depth-bounded run");
            stats
        }
        other => panic!("expected depth-bounded PaxosCommit run, got: {other:?}"),
    }
}

fn assert_depth_10_stats_match(expected: &CheckStats, actual: &CheckStats, label: &str) {
    assert_eq!(
        actual.initial_states, expected.initial_states,
        "{label}: initial-state count must match legacy depth-10 baseline"
    );
    assert_eq!(
        actual.states_found, expected.states_found,
        "{label}: distinct-state count must match legacy depth-10 baseline"
    );
    assert_eq!(
        actual.transitions, expected.transitions,
        "{label}: transition count must match legacy depth-10 baseline"
    );
    assert_eq!(
        actual.max_depth, expected.max_depth,
        "{label}: reached depth must match legacy depth-10 baseline"
    );
}

/// Part of #3354: `TLA2_LEGACY_EVAL` removed. This function now runs the
/// default TIR path and asserts the known baseline state count directly.
fn run_baseline_paxoscommit_depth_10(
    module: &tla_core::ast::Module,
    checker_modules: &[tla_core::ast::Module],
    config: &Config,
    fairness: &[tla_check::FairnessConstraint],
    stuttering_allowed: bool,
) -> CheckStats {
    let baseline_stats = {
        let _tir_eval = EnvVarGuard::remove("TLA2_TIR_EVAL");
        let _tir_parity = EnvVarGuard::remove("TLA2_TIR_PARITY");
        let _tir_leaf_parity = EnvVarGuard::remove("TLA2_TIR_LEAF_PARITY");
        run_paxoscommit_depth_10(
            module,
            checker_modules,
            config,
            fairness.to_vec(),
            stuttering_allowed,
        )
    };
    assert_eq!(
        baseline_stats.states_found, 52_833,
        "depth-10 PaxosCommit baseline should stay pinned for #3402"
    );
    baseline_stats
}

fn run_tir_paxoscommit_depth_10(
    module: &tla_core::ast::Module,
    checker_modules: &[tla_core::ast::Module],
    config: &Config,
    fairness: &[tla_check::FairnessConstraint],
    stuttering_allowed: bool,
    tir_eval: Option<&str>,
) -> CheckStats {
    match tir_eval {
        Some(mode) => {
            let _tir_eval = EnvVarGuard::set("TLA2_TIR_EVAL", Some(mode));
            let _tir_parity = EnvVarGuard::remove("TLA2_TIR_PARITY");
            let _tir_leaf_parity = EnvVarGuard::remove("TLA2_TIR_LEAF_PARITY");
            run_paxoscommit_depth_10(
                module,
                checker_modules,
                config,
                fairness.to_vec(),
                stuttering_allowed,
            )
        }
        None => {
            let _tir_eval = EnvVarGuard::remove("TLA2_TIR_EVAL");
            let _tir_parity = EnvVarGuard::remove("TLA2_TIR_PARITY");
            let _tir_leaf_parity = EnvVarGuard::remove("TLA2_TIR_LEAF_PARITY");
            run_paxoscommit_depth_10(
                module,
                checker_modules,
                config,
                fairness.to_vec(),
                stuttering_allowed,
            )
        }
    }
}

#[cfg_attr(test, ntest::timeout(180000))]
#[test]
fn bug_3402_paxoscommit_default_tir_matches_legacy_depth_count() {
    let (module, checker_modules, config, fairness, stuttering_allowed) = load_paxoscommit();
    let legacy_stats = run_baseline_paxoscommit_depth_10(
        &module,
        &checker_modules,
        &config,
        &fairness,
        stuttering_allowed,
    );

    let default_tir_stats = run_tir_paxoscommit_depth_10(
        &module,
        &checker_modules,
        &config,
        &fairness,
        stuttering_allowed,
        None,
    );
    assert_depth_10_stats_match(
        &legacy_stats,
        &default_tir_stats,
        "Bug #3402 regression: default TIR PaxosCommit depth-10 run",
    );
    assert_eq!(
        default_tir_stats.states_found, 52_833,
        "Bug #3402 regression: default TIR depth-10 count should match TLC/legacy"
    );
}

#[cfg_attr(test, ntest::timeout(180000))]
#[test]
fn bug_3402_paxoscommit_pcnext_tir_matches_legacy_depth_count() {
    let (module, checker_modules, config, fairness, stuttering_allowed) = load_paxoscommit();
    let legacy_stats = run_baseline_paxoscommit_depth_10(
        &module,
        &checker_modules,
        &config,
        &fairness,
        stuttering_allowed,
    );

    let tir_stats = run_tir_paxoscommit_depth_10(
        &module,
        &checker_modules,
        &config,
        &fairness,
        stuttering_allowed,
        Some("PCNext"),
    );

    assert_depth_10_stats_match(
        &legacy_stats,
        &tir_stats,
        "Bug #3402 regression: TLA2_TIR_EVAL=PCNext PaxosCommit depth-10 run",
    );
    assert_eq!(
        tir_stats.states_found, 52_833,
        "Bug #3402 regression: depth-10 PaxosCommit TIR count should match TLC/legacy"
    );
}

#[cfg_attr(test, ntest::timeout(300000))]
#[test]
fn bug_3402_paxoscommit_default_tir_stays_stable_across_runs() {
    let (module, checker_modules, config, fairness, stuttering_allowed) = load_paxoscommit();
    let legacy_stats = run_baseline_paxoscommit_depth_10(
        &module,
        &checker_modules,
        &config,
        &fairness,
        stuttering_allowed,
    );

    for run_idx in 1..=2 {
        let stats = run_tir_paxoscommit_depth_10(
            &module,
            &checker_modules,
            &config,
            &fairness,
            stuttering_allowed,
            None,
        );
        let label = format!("Bug #3402 regression: default TIR PaxosCommit depth-10 run {run_idx}");
        assert_depth_10_stats_match(&legacy_stats, &stats, &label);
        assert_eq!(
            stats.states_found, 52_833,
            "Bug #3402 regression: default TIR run {run_idx} should match TLC/legacy"
        );
    }
}

#[cfg_attr(test, ntest::timeout(300000))]
#[test]
fn bug_3402_paxoscommit_pcnext_tir_stays_stable_across_runs() {
    let (module, checker_modules, config, fairness, stuttering_allowed) = load_paxoscommit();
    let legacy_stats = run_baseline_paxoscommit_depth_10(
        &module,
        &checker_modules,
        &config,
        &fairness,
        stuttering_allowed,
    );

    for run_idx in 1..=2 {
        let stats = run_tir_paxoscommit_depth_10(
            &module,
            &checker_modules,
            &config,
            &fairness,
            stuttering_allowed,
            Some("PCNext"),
        );
        let label = format!("Bug #3402 regression: PCNext PaxosCommit depth-10 run {run_idx}");
        assert_depth_10_stats_match(&legacy_stats, &stats, &label);
        assert_eq!(
            stats.states_found, 52_833,
            "Bug #3402 regression: PCNext run {run_idx} should match TLC/legacy"
        );
    }
}
