// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

mod common;

use common::EnvVarGuard;
use std::path::PathBuf;
use tla_check::{resolve_spec_from_config_with_extends, CheckResult, Config, ParallelChecker};
use tla_core::{lower, parse_to_syntax_tree, FileId, ModuleLoader};

fn run_mcboulanger_small_parallel(
    workers: usize,
    force_batch: bool,
    shared_queue: bool,
) -> (usize, usize, usize) {
    let _force_batch_guard = EnvVarGuard::set("TLA2_FORCE_BATCH", force_batch.then_some("1"));
    let _shared_queue_guard = EnvVarGuard::set("TLA2_SHARED_QUEUE", shared_queue.then_some("1"));

    let spec_path =
        common::tlaplus_examples_dir().join("specifications/Bakery-Boulangerie/MCBoulanger.tla");
    let cfg_path =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/test_specs/MCBoulanger_small.cfg");

    let spec_source = std::fs::read_to_string(&spec_path)
        .unwrap_or_else(|e| panic!("Failed to read {}: {}", spec_path.display(), e));
    let tree = parse_to_syntax_tree(&spec_source);
    let mut module = lower(FileId(0), &tree)
        .module
        .expect("MCBoulanger should lower successfully");
    tla_core::compute_is_recursive(&mut module);

    let mut loader = ModuleLoader::new(&spec_path);
    loader.seed_from_syntax_tree(&tree, &spec_path);
    loader
        .load_extends(&module)
        .expect("MCBoulanger EXTENDS dependencies should load");
    loader
        .load_instances(&module)
        .expect("MCBoulanger INSTANCE dependencies should load");

    let (extended_modules_for_resolve, instanced_modules_for_resolve) =
        loader.modules_for_semantic_resolution(&module);
    let checker_modules = loader.modules_for_model_checking(&module);
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
        .expect("MCBoulanger_small SPECIFICATION should resolve across extended modules");
    if config.init.is_none() {
        config.init = Some(resolved.init.clone());
    }
    if config.next.is_none() {
        config.next = Some(resolved.next.clone());
    }

    let mut checker =
        ParallelChecker::new_with_extends(&module, &checker_modules, &config, workers);
    checker.set_fairness(resolved.fairness);
    checker.set_stuttering_allowed(resolved.stuttering_allowed);

    match checker.check() {
        CheckResult::Success(stats) => {
            (stats.states_found, stats.initial_states, stats.transitions)
        }
        other => panic!("MCBoulanger_small parallel run should succeed, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(120000))]
#[test]
fn test_parallel_mcboulanger_small_matches_force_batch_real_spec() {
    let default = run_mcboulanger_small_parallel(2, false, false);
    let forced_batch = run_mcboulanger_small_parallel(2, true, false);

    assert_eq!(
        default.0, 522,
        "Default parallel MCBoulanger_small should match TLC's 522 distinct states"
    );
    assert_eq!(
        forced_batch.0, 522,
        "Force-batch MCBoulanger_small should match TLC's 522 distinct states"
    );
    assert_eq!(
        default, forced_batch,
        "Default constrained streaming must match the legacy force-batch lane on MCBoulanger_small"
    );
}

#[cfg_attr(test, ntest::timeout(120000))]
#[test]
fn test_parallel_mcboulanger_small_shared_queue_matches_default_real_spec() {
    let default = run_mcboulanger_small_parallel(2, false, false);
    let shared_queue = run_mcboulanger_small_parallel(2, false, true);

    assert_eq!(
        default.0, 522,
        "Default parallel MCBoulanger_small should match TLC's 522 distinct states"
    );
    assert_eq!(
        shared_queue.0, 522,
        "Shared-queue MCBoulanger_small should match TLC's 522 distinct states"
    );
    assert_eq!(
        default, shared_queue,
        "Shared-queue MCBoulanger_small must match the default parallel lane exactly"
    );
}
