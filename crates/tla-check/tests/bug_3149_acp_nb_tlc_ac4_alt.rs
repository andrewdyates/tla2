// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression test for #3149: ACP_NB_TLC false positive on AC4_alt.

mod common;

use tla_check::ParallelChecker;
use tla_check::{resolve_spec_from_config_with_extends, CheckResult, Config, ModelChecker};
use tla_core::{lower, parse_to_syntax_tree, FileId, ModuleLoader};

fn load_acp_nb_tlc_modules(
    property_filter: Option<&[&str]>,
) -> (
    tla_core::ast::Module,
    Vec<tla_core::ast::Module>,
    Config,
    Vec<tla_check::FairnessConstraint>,
    bool,
) {
    let spec_dir = common::tlaplus_examples_dir().join("specifications/acp");
    let spec_path = spec_dir.join("ACP_NB_TLC.tla");
    let cfg_path = spec_dir.join("ACP_NB_TLC.cfg");

    let spec_source = std::fs::read_to_string(&spec_path)
        .unwrap_or_else(|e| panic!("Failed to read {}: {}", spec_path.display(), e));
    let tree = parse_to_syntax_tree(&spec_source);
    let mut module = lower(FileId(0), &tree)
        .module
        .expect("ACP_NB_TLC should lower successfully");
    tla_core::compute_is_recursive(&mut module);

    let mut loader = ModuleLoader::new(&spec_path);
    loader.seed_from_syntax_tree(&tree, &spec_path);
    loader
        .load_extends(&module)
        .expect("ACP_NB_TLC EXTENDS dependencies should load");
    loader
        .load_instances(&module)
        .expect("ACP_NB_TLC INSTANCE dependencies should load");

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
    if let Some(props) = property_filter {
        config.properties = props.iter().map(|s| (*s).to_string()).collect();
    }
    let resolved = resolve_spec_from_config_with_extends(&config, &tree, &extended_syntax_trees)
        .expect("ACP_NB_TLC SPECIFICATION should resolve across extended modules");
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

fn assert_acp_passes(result: CheckResult, checker_name: &str, expected_states: usize) {
    match result {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, expected_states,
                "Bug #3149 regression: {checker_name} should match TLC's {expected_states} states, got {}",
                stats.states_found
            );
        }
        other => {
            panic!("Bug #3149 regression: {checker_name} should pass ACP_NB_TLC, got {other:?}")
        }
    }
}

#[cfg_attr(test, ntest::timeout(120000))]
#[test]
fn bug_3149_acp_nb_tlc_ac4_alt_passes_with_tlc_state_parity() {
    let (module, checker_modules, config, fairness, stuttering_allowed) =
        load_acp_nb_tlc_modules(Some(&["AC4_alt"]));
    let checker_module_refs = checker_modules.iter().collect::<Vec<_>>();

    let mut checker = ModelChecker::new_with_extends(&module, &checker_module_refs, &config);
    checker.set_store_states(true);
    checker.set_fairness(fairness.clone());
    checker.set_stuttering_allowed(stuttering_allowed);
    assert_acp_passes(checker.check(), "sequential checker", 4_284);

    let mut par_checker =
        ParallelChecker::new_with_extends(&module, &checker_module_refs, &config, 2);
    par_checker.set_store_states(true);
    par_checker.set_fairness(fairness);
    par_checker.set_stuttering_allowed(stuttering_allowed);
    assert_acp_passes(par_checker.check(), "parallel checker", 4_284);
}

/// Verify all 6 ACP properties pass together (full config, not just AC4_alt).
/// TLC baseline: 4,284 distinct states with AC1, AC2, AC3_1, AC4_alt (safety)
/// and AC3_2, AC5 (liveness with WF fairness).
#[cfg_attr(test, ntest::timeout(120000))]
#[test]
fn bug_3149_acp_nb_tlc_all_properties_pass_with_tlc_state_parity() {
    let (module, checker_modules, config, fairness, stuttering_allowed) =
        load_acp_nb_tlc_modules(None);
    let checker_module_refs = checker_modules.iter().collect::<Vec<_>>();

    let mut checker = ModelChecker::new_with_extends(&module, &checker_module_refs, &config);
    checker.set_store_states(true);
    checker.set_fairness(fairness.clone());
    checker.set_stuttering_allowed(stuttering_allowed);
    assert_acp_passes(checker.check(), "sequential checker (all props)", 4_284);

    let mut par_checker =
        ParallelChecker::new_with_extends(&module, &checker_module_refs, &config, 2);
    par_checker.set_store_states(true);
    par_checker.set_fairness(fairness);
    par_checker.set_stuttering_allowed(stuttering_allowed);
    assert_acp_passes(par_checker.check(), "parallel checker (all props)", 4_284);
}
