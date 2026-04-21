// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

mod common;

use std::collections::BTreeMap;

use common::EnvVarGuard;
use tla_check::eval::clear_for_test_reset;
use tla_check::{resolve_spec_from_config_with_extends, CheckResult, Config, ModelChecker};
use tla_core::{clear_global_name_interner, lower, parse_to_syntax_tree, FileId, ModuleLoader};
use tla_eval::tir::{enable_tir_eval_probe, tir_eval_probe_snapshot, TirEvalProbeCounts};

fn probe_counts(snapshot: &BTreeMap<String, TirEvalProbeCounts>, name: &str) -> TirEvalProbeCounts {
    snapshot.get(name).copied().unwrap_or_default()
}

fn probe_delta(
    before: &BTreeMap<String, TirEvalProbeCounts>,
    after: &BTreeMap<String, TirEvalProbeCounts>,
    name: &str,
) -> TirEvalProbeCounts {
    let before_counts = probe_counts(before, name);
    let after_counts = probe_counts(after, name);
    TirEvalProbeCounts {
        expr_evals: after_counts
            .expr_evals
            .saturating_sub(before_counts.expr_evals),
        named_op_evals: after_counts
            .named_op_evals
            .saturating_sub(before_counts.named_op_evals),
    }
}

/// Real-spec regression for #3352.
///
/// `MCTwoPhase` imports `Init`, `Next`, and `Inv` from a bare `INSTANCE
/// TwoPhase` declaration while supplying the module's `XInit`/`XAct`
/// parameters via implicit same-name substitutions from the wrapper module.
/// Before #3352, `TirProgram::can_lower_operator()` rejected these imported
/// operators, so the sequential checker silently stayed on AST evaluation.
#[cfg_attr(test, ntest::timeout(60000))]
#[test]
fn test_tir_eval_real_mctwophase_instance_wrapper_hits_probes_and_matches_tlc() {
    let _eval_guard = EnvVarGuard::set("TLA2_TIR_EVAL", Some("all"));
    let _parity_guard = EnvVarGuard::remove("TLA2_TIR_PARITY");

    clear_for_test_reset();
    clear_global_name_interner();
    enable_tir_eval_probe();
    let before = tir_eval_probe_snapshot();

    let spec_dir = common::tlaplus_examples_dir().join("specifications/TwoPhase");
    let spec_path = spec_dir.join("MCTwoPhase.tla");
    let cfg_path = spec_dir.join("MCTwoPhase.cfg");

    let spec_source = std::fs::read_to_string(&spec_path)
        .unwrap_or_else(|e| panic!("Failed to read {}: {}", spec_path.display(), e));
    let tree = parse_to_syntax_tree(&spec_source);
    let mut module = lower(FileId(0), &tree)
        .module
        .expect("MCTwoPhase should lower successfully");
    tla_core::compute_is_recursive(&mut module);

    let mut loader = ModuleLoader::new(&spec_path);
    loader.seed_from_syntax_tree(&tree, &spec_path);
    loader
        .load_extends(&module)
        .expect("MCTwoPhase EXTENDS dependencies should load");
    loader
        .load_instances(&module)
        .expect("MCTwoPhase INSTANCE dependencies should load");

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
        .expect("MCTwoPhase SPECIFICATION should resolve across extended modules");
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
                stats.initial_states, 1,
                "MCTwoPhase should keep the single TLC initial state"
            );
            assert_eq!(
                stats.states_found, 4,
                "MCTwoPhase should keep TLC's 4 reachable states under TIR eval"
            );
        }
        other => panic!("MCTwoPhase should complete cleanly under TIR eval=all, got {other:?}"),
    }

    let after = tir_eval_probe_snapshot();
    let next_delta = probe_delta(&before, &after, "Next");
    assert!(
        next_delta.expr_evals > 0,
        "expected imported Next from bare INSTANCE TwoPhase to hit the TIR expr probe, delta={next_delta:?}"
    );

    let inv_delta = probe_delta(&before, &after, "Inv");
    assert!(
        inv_delta.expr_evals > 0,
        "expected imported Inv from bare INSTANCE TwoPhase to hit the TIR expr probe, delta={inv_delta:?}"
    );
}
