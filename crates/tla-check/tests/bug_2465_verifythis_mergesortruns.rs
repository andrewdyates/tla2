// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression test for #2465: VerifyThis `MergesortRuns` false positive.
//!
//! Root cause: zero-arg LET Tier 1.5 caching in `tla-eval` permanently keyed a
//! branch-sensitive LET body by only the first observed local dependency set.
//! In `MergeAcc`, helpers like `copy1` and `copy2` first execute on a branch
//! that reads only `t1` or `t2`, then later execute on branches that also read
//! `r1`, `r2`, `di1`, `di2`, `ri1`, and `ri2`. Reusing the under-keyed cache
//! entry produced a bogus merged output and violated `PermutationCorrect`.

use std::path::PathBuf;
use tla_check::{resolve_spec_from_config_with_extends, CheckResult, Config, ModelChecker};
use tla_core::{lower, parse_to_syntax_tree, FileId, ModuleLoader};

fn verifythis_practice_dir() -> PathBuf {
    let home = std::env::var("HOME").expect("HOME environment variable not set");
    PathBuf::from(home).join("win-all-software-proof-competitions/benchmarks/verifythis/practice")
}

#[cfg_attr(test, ntest::timeout(60000))]
#[test]
fn bug_2465_mergesortruns_real_spec_passes_with_tlc_state_parity() {
    let spec_dir = verifythis_practice_dir().join("2022-c2-mergesort-runs");
    let spec_path = spec_dir.join("MergesortRuns.tla");
    let cfg_path = spec_dir.join("MergesortRuns.cfg");

    let spec_source = std::fs::read_to_string(&spec_path)
        .unwrap_or_else(|e| panic!("Failed to read {}: {}", spec_path.display(), e));
    let tree = parse_to_syntax_tree(&spec_source);
    let mut module = lower(FileId(0), &tree)
        .module
        .expect("MergesortRuns should lower successfully");
    tla_core::compute_is_recursive(&mut module);

    let mut loader = ModuleLoader::new(&spec_path);
    loader.seed_from_syntax_tree(&tree, &spec_path);
    loader
        .load_extends(&module)
        .expect("MergesortRuns EXTENDS dependencies should load");
    loader
        .load_instances(&module)
        .expect("MergesortRuns INSTANCE dependencies should load");

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
        .expect("MergesortRuns SPECIFICATION should resolve across extended modules");
    if config.init.is_none() {
        config.init = Some(resolved.init.clone());
    }
    if config.next.is_none() {
        config.next = Some(resolved.next.clone());
    }
    config.normalize_resolved_specification();

    let mut checker = ModelChecker::new_with_extends(&module, &checker_modules, &config);
    checker.set_store_states(true);
    checker.set_fairness(resolved.fairness);
    checker.set_stuttering_allowed(resolved.stuttering_allowed);

    match checker.check() {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 1_092,
                "Bug #2465 regression: MergesortRuns should match TLC's 1,092 states, got {}",
                stats.states_found
            );
        }
        other => panic!(
            "Bug #2465 regression: MergesortRuns should pass its VerifyThis safety invariants, got {other:?}"
        ),
    }
}
