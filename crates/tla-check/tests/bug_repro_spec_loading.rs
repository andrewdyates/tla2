// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Bug reproductions that load real specs from tlaplus-examples.
//! Split from bug_repro_recent.rs — Part of #3671

mod common;

use tla_check::{resolve_spec_from_config_with_extends, CheckResult, Config, ModelChecker};
use tla_core::{lower, parse_to_syntax_tree, FileId, ModuleLoader};

// ============================================================================
// Bug #3118: MCAlternatingBit live diagnose undercounts states (192 vs TLC 240)
// ============================================================================

/// Bug #3118: the real MCAlternatingBit spec must preserve TLC's 240 reachable
/// states when inline liveness is active.
///
/// This uses the actual tlaplus-examples spec/config pair because the regression
/// depends on the full SPECIFICATION + PROPERTY + fairness shape, not just the
/// smaller synthetic patterns covered by unit tests.
#[cfg_attr(test, ntest::timeout(60000))]
#[test]
fn test_bug_3118_mcalternatingbit_state_count_parity() {
    let _guard = common::EnvVarGuard::remove("TLA2_SKIP_LIVENESS");

    let spec_dir = common::tlaplus_examples_dir().join("specifications/SpecifyingSystems/TLC");
    let spec_path = spec_dir.join("MCAlternatingBit.tla");
    let cfg_path = spec_dir.join("MCAlternatingBit.cfg");

    let spec_source = std::fs::read_to_string(&spec_path)
        .unwrap_or_else(|e| panic!("Failed to read {}: {}", spec_path.display(), e));
    let tree = parse_to_syntax_tree(&spec_source);
    let mut module = lower(FileId(0), &tree)
        .module
        .expect("MCAlternatingBit should lower successfully");
    tla_core::compute_is_recursive(&mut module);

    let mut loader = ModuleLoader::new(&spec_path);
    loader.seed_from_syntax_tree(&tree, &spec_path);
    loader
        .load_extends(&module)
        .expect("MCAlternatingBit EXTENDS dependencies should load");
    loader
        .load_instances(&module)
        .expect("MCAlternatingBit INSTANCE dependencies should load");

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
        .expect("SPECIFICATION should resolve across extended modules");
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
                stats.states_found, 240,
                "Bug #3118 regression: MCAlternatingBit should match TLC's 240 states"
            );
        }
        other => {
            panic!("Bug #3118 regression: MCAlternatingBit did not complete cleanly: {other:?}")
        }
    }
}

// ============================================================================
// Bug #3125: EWD840_json false positive — transitive state-level wrapper
// misclassified as constant, causing setup-time evaluation of TLCSet("exit", TRUE)
// ============================================================================

/// Bug #3125: A zero-arg operator whose body transitively references state
/// variables through an Ident chain must NOT be precomputed as a constant.
/// The old shallow `body_references_state_var` gate missed transitive state
/// dependency through `Ident` references, causing setup-time evaluation of
/// operators like EWD840_json's `JsonInv` (which wraps state-level `Inv`).
///
/// This test verifies the precompute gate correctly skips state-level wrappers.
/// Pattern: `Wrapper == Inv` where `Inv` depends on state variable `x`.
/// Without the fix, `Wrapper` would be misclassified as constant and eagerly
/// evaluated during setup (causing undefined-variable errors or wrong results).
///
/// The fix replaces the shallow syntactic gate with `AstToLive::get_level_with_ctx`
/// which follows operator references transitively — matching TLC's `getLevelBound`.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_bug_3125_transitive_state_wrapper_not_precomputed() {
    let spec = r#"
---- MODULE Bug3125TransitiveStateWrapper ----
EXTENDS Naturals

VARIABLE x

Init == x = 0

Next == x' = (x + 1) % 3

\* State-level invariant (directly references x)
Inv == x \in 0..2

\* Wrapper — body is Ident("Inv"), no direct Expr::StateVar.
\* Pre-#3125: shallow gate misclassified as constant, setup tried to evaluate.
\* Post-#3125: semantic level check sees transitive state dependency, skips.
Wrapper == Inv

====
"#;

    let config_src = r#"
INIT Init
NEXT Next
INVARIANT Wrapper
CHECK_DEADLOCK FALSE
"#;

    let module = common::parse_module(spec);
    let config = Config::parse(config_src).expect("config should parse");

    let result = tla_check::check_module(&module, &config);
    match result {
        CheckResult::Success(stats) => {
            // 3 states: x=0, x=1, x=2 (cycle: 0->1->2->0)
            assert_eq!(
                stats.states_found, 3,
                "Bug #3125 regression: expected 3 states (x in 0..2), got {}",
                stats.states_found
            );
        }
        other => {
            panic!(
                "Bug #3125 regression: spec with transitive state wrapper should succeed \
                 but got: {other:?}. If the precompute gate is broken, Wrapper would be \
                 evaluated at setup time without state bindings."
            );
        }
    }
}

// ============================================================================
// Bug #3125 real-spec: EWD840_json must pass with TLC state parity (1566).
// ============================================================================

/// Bug #3125: EWD840_json's `JsonInv` uses labeled disjunction where the
/// second disjunct calls `TLCSet("exit", TRUE)`. Two fixes are needed:
///
/// 1. **Precompute gate**: The shallow syntactic `body_references_state_var`
///    gate missed transitive state dependency through `Expr::Ident` chains.
///    Replaced with `AstToLive::get_level_with_ctx` (semantic level check).
///
/// 2. **Compiled guard Label transparency**: `Expr::Label` nodes fell through
///    to opaque `Fallback` guards, preventing `CompiledGuard::Or` from
///    short-circuiting. When `Inv` (first disjunct) is TRUE, the Export
///    disjunct containing `TLCSet("exit", TRUE)` must never be evaluated.
///
/// This test loads the real EWD840_json spec and asserts exact TLC parity.
#[cfg_attr(test, ntest::timeout(60000))]
#[test]
fn test_bug_3125_ewd840_json_passes_with_tlc_state_parity() {
    let spec_dir = common::tlaplus_examples_dir().join("specifications/ewd840");
    let spec_path = spec_dir.join("EWD840_json.tla");
    let cfg_path = spec_dir.join("EWD840_json.cfg");

    let spec_source = std::fs::read_to_string(&spec_path)
        .unwrap_or_else(|e| panic!("Failed to read {}: {}", spec_path.display(), e));
    let tree = parse_to_syntax_tree(&spec_source);
    let mut module = lower(FileId(0), &tree)
        .module
        .expect("EWD840_json should lower successfully");
    tla_core::compute_is_recursive(&mut module);

    let mut loader = ModuleLoader::new(&spec_path);
    loader.seed_from_syntax_tree(&tree, &spec_path);
    loader
        .load_extends(&module)
        .expect("EWD840_json EXTENDS dependencies should load");
    loader
        .load_instances(&module)
        .expect("EWD840_json INSTANCE dependencies should load");

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
        .expect("SPECIFICATION should resolve across extended modules");
    if config.init.is_none() {
        config.init = Some(resolved.init.clone());
    }
    if config.next.is_none() {
        config.next = Some(resolved.next.clone());
    }

    let mut checker = ModelChecker::new_with_extends(&module, &checker_modules, &config);
    checker.set_stuttering_allowed(resolved.stuttering_allowed);

    match checker.check() {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 1566,
                "Bug #3125 regression: EWD840_json should match TLC's 1566 states, got {}",
                stats.states_found
            );
        }
        other => {
            panic!(
                "Bug #3125 regression: EWD840_json should pass but got: {other:?}. \
                 If labeled disjunction Or short-circuit is broken, TLCSet(\"exit\", TRUE) \
                 fires during runtime invariant checking."
            )
        }
    }
}
