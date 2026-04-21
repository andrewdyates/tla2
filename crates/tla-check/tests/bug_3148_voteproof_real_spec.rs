// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression test for #3148: VoteProof false positive.
//!
//! VoteProof should pass with the TLC baseline state count. This exercises the
//! evaluator paths touched by the scope-id cache-key changes through the real
//! byzpaxos spec.

mod common;

use tla_check::{CheckResult, Config, ModelChecker};
use tla_core::{lower, parse_to_syntax_tree, FileId, ModuleLoader};

#[cfg_attr(test, ntest::timeout(120000))]
#[test]
fn bug_3148_voteproof_real_spec_passes_with_tlc_state_parity() {
    let spec_dir = common::tlaplus_examples_dir().join("specifications/byzpaxos");
    let spec_path = spec_dir.join("VoteProof.tla");
    let cfg_path = spec_dir.join("VoteProof.cfg");

    let spec_source = std::fs::read_to_string(&spec_path)
        .unwrap_or_else(|e| panic!("Failed to read {}: {}", spec_path.display(), e));
    let tree = parse_to_syntax_tree(&spec_source);
    let mut module = lower(FileId(0), &tree)
        .module
        .expect("VoteProof should lower successfully");
    tla_core::compute_is_recursive(&mut module);

    let mut loader = ModuleLoader::new(&spec_path);
    loader.seed_from_syntax_tree(&tree, &spec_path);
    loader
        .load_extends(&module)
        .expect("VoteProof EXTENDS dependencies should load");
    loader
        .load_instances(&module)
        .expect("VoteProof INSTANCE dependencies should load");

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
    let resolved =
        tla_check::resolve_spec_from_config_with_extends(&config, &tree, &extended_syntax_trees)
            .expect("VoteProof SPECIFICATION should resolve across extended modules");
    if config.init.is_none() {
        config.init = Some(resolved.init.clone());
    }
    if config.next.is_none() {
        config.next = Some(resolved.next.clone());
    }

    let mut checker = ModelChecker::new_with_extends(&module, &checker_modules, &config);
    checker.set_store_states(true);
    checker.set_fairness(resolved.fairness);
    checker.set_stuttering_allowed(resolved.stuttering_allowed);

    match checker.check() {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 6_962,
                "Bug #3148 regression: VoteProof should match TLC's 6,962 states, got {}",
                stats.states_found
            );
        }
        other => panic!("Bug #3148 regression: VoteProof should pass, got {other:?}"),
    }
}
