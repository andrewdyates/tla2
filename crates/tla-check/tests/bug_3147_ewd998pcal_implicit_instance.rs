// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression test for #3147: EWD998PCal false positive.
//!
//! Implicit INSTANCE substitution where a VARIABLE in the instanced module
//! maps to a DEFINED OPERATOR in the outer module. The defined operator
//! computes its value from a different variable (like EWD998PCal's `pending`
//! which reads from `network`).

mod common;

use tla_check::{CheckResult, Config, ModelChecker};
use tla_core::FileId;

#[cfg(not(debug_assertions))]
use tla_core::{lower, parse_to_syntax_tree, ModuleLoader};

/// Abstract module with a VARIABLE `derived` that will be mapped to a
/// defined operator in the concrete module (mimics EWD998's `pending`).
fn abstract_module() -> tla_core::ast::Module {
    common::parse_module_strict_with_id(
        r#"
---- MODULE Abstract ----
EXTENDS Integers

VARIABLE x, derived

Init == x = 0 /\ derived = 0

Next == /\ x' = (x + 1) % 3
        /\ derived' = x'

vars == <<x, derived>>

Spec == Init /\ [][Next]_vars
====
"#,
        FileId(1),
    )
}

/// Smaller #3147 reproducer: the instanced module updates a VARIABLE via EXCEPT,
/// while the concrete module supplies that variable through a zero-arg operator
/// derived from a different concrete state variable.
fn abstract_except_module() -> tla_core::ast::Module {
    common::parse_module_strict_with_id(
        r#"
---- MODULE AbstractExcept ----
EXTENDS Integers

Node == 0 .. 2

VARIABLE active, counter, pending, token, step

Init ==
    /\ active = [i \in Node |-> i = 2]
    /\ counter = [i \in Node |-> IF i = 2 THEN 1 ELSE 0]
    /\ pending = [i \in Node |-> IF i = 0 THEN 1 ELSE 0]
    /\ token = [pos |-> 0, q |-> 0, color |-> "black"]
    /\ step = 0

SendMsg(i) ==
    /\ step = 0
    /\ counter' = [counter EXCEPT ![i] = @ + 1]
    /\ pending' = [pending EXCEPT ![(i + 2) % 3] = @ + 1]
    /\ UNCHANGED <<active, token>>
    /\ step' = 1

Stutter ==
    /\ step = 1
    /\ step' = 1
    /\ UNCHANGED <<active, counter, pending, token>>

Next == SendMsg(2) \/ Stutter

vars == <<active, counter, pending, token, step>>

Spec == Init /\ [][Next]_vars
====
"#,
        FileId(2),
    )
}

fn property_config(property: &str) -> Config {
    Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec![property.to_string()],
        check_deadlock: false,
        ..Default::default()
    }
}

fn assert_property_success(result: CheckResult, expected_states: usize, label: &str) {
    match result {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, expected_states,
                "Bug #3147: expected {expected_states} distinct states for {label}, got {}",
                stats.states_found
            );
        }
        CheckResult::PropertyViolation { property, .. } => {
            panic!("Bug #3147 regression: PROPERTY '{property}' falsely violated for {label}");
        }
        other => panic!("Bug #3147 regression: unexpected result for {label}: {other:?}"),
    }
}

#[cfg(not(debug_assertions))]
fn check_real_ewd998() -> CheckResult {
    let spec_dir = common::tlaplus_examples_dir().join("specifications/ewd998");
    let spec_path = spec_dir.join("EWD998PCal.tla");
    let cfg_path = spec_dir.join("EWD998PCal.cfg");

    let spec_source = std::fs::read_to_string(&spec_path)
        .unwrap_or_else(|e| panic!("Failed to read {}: {}", spec_path.display(), e));
    let tree = parse_to_syntax_tree(&spec_source);
    let mut module = lower(FileId(0), &tree)
        .module
        .expect("EWD998PCal should lower successfully");
    tla_core::compute_is_recursive(&mut module);

    let mut loader = ModuleLoader::new(&spec_path);
    loader.seed_from_syntax_tree(&tree, &spec_path);
    loader
        .load_extends(&module)
        .expect("EWD998PCal EXTENDS dependencies should load");
    loader
        .load_instances(&module)
        .expect("EWD998PCal INSTANCE dependencies should load");

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
            .expect("EWD998PCal SPECIFICATION should resolve across extended modules");
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
    checker.check()
}

/// Concrete module: has `raw` variable, derives `derived` from it via operator.
/// Uses implicit INSTANCE (matching names), where Abstract's VARIABLE `derived`
/// is substituted with the outer module's OPERATOR `derived` (computed from `raw`).
///
/// This mimics EWD998PCal where EWD998's `pending` VARIABLE maps to
/// EWD998PCal's `pending` OPERATOR (computed from `network`).
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn bug_3147_implicit_instance_var_to_operator() {
    let abstract_mod = abstract_module();

    let concrete = common::parse_module_strict_with_id(
        r#"
---- MODULE Concrete ----
EXTENDS Integers

VARIABLE x, raw

\* `derived` is a DEFINED OPERATOR, not a variable.
\* It reads from `raw` to compute the derived value.
derived == raw

Init == x = 0 /\ raw = 0

Next == /\ x' = (x + 1) % 3
        /\ raw' = x'

vars == <<x, raw>>

Spec == Init /\ [][Next]_vars

\* Implicit INSTANCE: Abstract's VARIABLE `derived` maps to
\* Concrete's OPERATOR `derived` (since names match).
A == INSTANCE Abstract

ASpec == A!Spec
====
"#,
        FileId(0),
    );

    let config = property_config("ASpec");
    let mut checker = ModelChecker::new_with_extends(&concrete, &[&abstract_mod], &config);
    assert_property_success(
        checker.check(),
        3,
        "simple implicit INSTANCE variable-to-operator mapping",
    );
}

/// Direct committed regression for the reduced EXCEPT-based false positive from #3147.
///
/// This is smaller than the real EWD998PCal spec but preserves the critical shape:
/// - implicit INSTANCE
/// - abstract VARIABLE supplied by a concrete zero-arg operator
/// - action updates that variable through EXCEPT
/// - promoted PROPERTY checked as an implied action
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn bug_3147_implicit_instance_except_var_to_operator() {
    let abstract_mod = abstract_except_module();

    let concrete = common::parse_module_strict_with_id(
        r#"
---- MODULE ConcreteExcept ----
EXTENDS Integers

Node == 0 .. 2

VARIABLES active, counter, raw, net, step

pending == raw
token == net

Init ==
    /\ active = [i \in Node |-> i = 2]
    /\ counter = [i \in Node |-> IF i = 2 THEN 1 ELSE 0]
    /\ raw = [i \in Node |-> IF i = 0 THEN 1 ELSE 0]
    /\ net = [pos |-> 0, q |-> 0, color |-> "black"]
    /\ step = 0

SendConcrete ==
    /\ step = 0
    /\ counter' = [counter EXCEPT ![2] = @ + 1]
    /\ raw' = [raw EXCEPT ![1] = @ + 1]
    /\ step' = 1
    /\ UNCHANGED <<active, net>>

StutterConcrete ==
    /\ step = 1
    /\ step' = 1
    /\ UNCHANGED <<active, counter, raw, net>>

Next == SendConcrete \/ StutterConcrete

vars == <<active, counter, raw, net, step>>

A == INSTANCE AbstractExcept

ASpec == A!Spec
====
"#,
        FileId(3),
    );

    let config = property_config("ASpec");
    let mut checker = ModelChecker::new_with_extends(&concrete, &[&abstract_mod], &config);
    assert_property_success(checker.check(), 2, "reduced implicit INSTANCE EXCEPT repro");
}

/// Real-spec regression for #3147 using the tlaplus-examples EWD998PCal spec.
///
/// The synthetic harness above proves the basic implicit-substitution path, but
/// the live false positive depends on the full PlusCal refinement mapping:
/// inner `pending`/`token` VARIABLES map to outer zero-arg operators derived
/// from `network`, and the PROPERTY is checked under the fair outer SPECIFICATION.
#[cfg(not(debug_assertions))]
#[cfg_attr(test, ntest::timeout(180000))]
#[test]
fn bug_3147_ewd998pcal_real_spec_passes_with_tlc_state_parity() {
    assert_property_success(check_real_ewd998(), 321_370, "real EWD998PCal spec");
}
