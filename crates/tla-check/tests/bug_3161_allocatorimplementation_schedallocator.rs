// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for #3161: AllocatorImplementation liveness false positive.
//!
//! Root cause: ENABLED dispatch did not rebuild a full instance-operator scope
//! for complex module references like `Sched!Schedule`, so it could fall back to
//! normal evaluation and hit primed variables without a next-state context.
//! That made `WF_vars(Sched!Schedule)` appear vacuously satisfied on unfair
//! stuttering loops.

mod common;

#[cfg(not(debug_assertions))]
use tla_check::resolve_spec_from_config_with_extends;
use tla_check::{CheckResult, Config, ModelChecker};
use tla_core::FileId;

#[cfg(not(debug_assertions))]
use std::path::PathBuf;
#[cfg(not(debug_assertions))]
use tla_core::{lower, parse_to_syntax_tree, ModuleLoader};

#[cfg(not(debug_assertions))]
fn load_allocator_modules() -> (
    tla_core::ast::Module,
    Vec<tla_core::ast::Module>,
    Config,
    Vec<tla_check::FairnessConstraint>,
    bool,
) {
    let spec_dir = common::tlaplus_examples_dir().join("specifications/allocator");
    let spec_path = spec_dir.join("AllocatorImplementation.tla");
    let cfg_path = spec_dir.join("AllocatorImplementation.cfg");

    let spec_source = std::fs::read_to_string(&spec_path)
        .unwrap_or_else(|e| panic!("Failed to read {}: {}", spec_path.display(), e));
    let tree = parse_to_syntax_tree(&spec_source);
    let mut module = lower(FileId(0), &tree)
        .module
        .expect("AllocatorImplementation should lower successfully");
    tla_core::compute_is_recursive(&mut module);

    let mut loader = ModuleLoader::new(&spec_path);
    loader.seed_from_syntax_tree(&tree, &spec_path);
    loader
        .load_extends(&module)
        .expect("AllocatorImplementation EXTENDS dependencies should load");
    loader
        .load_instances(&module)
        .expect("AllocatorImplementation INSTANCE dependencies should load");

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
        .expect("AllocatorImplementation SPECIFICATION should resolve across extended modules");
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

fn assert_passes_with_states(result: CheckResult, label: &str, expected_states: usize) {
    match result {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, expected_states,
                "Bug #3161 regression: {label} should match TLC's {expected_states} states, got {}",
                stats.states_found
            );
        }
        CheckResult::LivenessViolation { property, .. } => {
            panic!(
                "Bug #3161 regression: {label} should not report a liveness violation for {property}"
            );
        }
        other => panic!("Bug #3161 regression: {label} should pass, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn bug_3161_enabled_instance_action_recurses_into_module_ref_body() {
    let scheduler = common::parse_module_strict_with_id(
        r#"
---- MODULE Scheduler ----
EXTENDS Naturals

VARIABLE x

Schedule == x' = x + 1

====
"#,
        FileId(1),
    );

    let concrete = common::parse_module_strict_with_id(
        r#"
---- MODULE ConcreteScheduler ----
EXTENDS Naturals

VARIABLE x

Init == x = 0
Next == x' = x

Sched == INSTANCE Scheduler

\* ENABLED Sched!Schedule must recurse into the instanced action body and
\* find the witness x' = x + 1 instead of evaluating it as a plain boolean.
Inv == ENABLED Sched!Schedule

====
"#,
        FileId(0),
    );

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Inv".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new_with_extends(&concrete, &[&scheduler], &config);
    checker.set_store_states(true);
    assert_passes_with_states(
        checker.check(),
        "ENABLED Sched!Schedule in invariant context",
        1,
    );
}

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn bug_3161_enabled_complex_instance_schedule_uses_constraint_propagation() {
    let scheduler = common::parse_module_strict_with_id(
        r#"
---- MODULE SchedulerTemporal ----
EXTENDS FiniteSets, Sequences, TLC

VARIABLES unsat, alloc, sched

PermSeqs(S) ==
  LET perms[ss \in SUBSET S] ==
       IF ss = {} THEN { << >> }
       ELSE LET ps == [ x \in ss |-> { Append(sq,x) : sq \in perms[ss \ {x}] } ]
            IN UNION { ps[x] : x \in ss }
  IN perms[S]

Range(f) == { f[x] : x \in DOMAIN f }

toSchedule == { c \in 1..3 : unsat[c] # {} /\ c \notin Range(sched) }

Schedule ==
  /\ toSchedule # {}
  /\ \E sq \in PermSeqs(toSchedule) : sched' = sched \circ sq
  /\ UNCHANGED <<unsat, alloc>>

====
"#,
        FileId(2),
    );

    let concrete = common::parse_module_strict_with_id(
        r#"
---- MODULE ConcreteSchedulerTemporal ----
EXTENDS FiniteSets, Sequences, TLC

VARIABLES unsat, alloc, sched, requests, holding, network

Init ==
  /\ unsat = [c \in 1..3 |-> 1..2]
  /\ alloc = [c \in 1..3 |-> {}]
  /\ sched = << >>
  /\ requests = [c \in 1..3 |-> 1..2]
  /\ holding = [c \in 1..3 |-> {}]
  /\ network = {}

Sched == INSTANCE SchedulerTemporal

Schedule ==
  /\ Sched!Schedule
  /\ UNCHANGED <<requests, holding, network>>

Next == UNCHANGED <<unsat, alloc, sched, requests, holding, network>>

InvInner == ENABLED Sched!Schedule
InvOuter == ENABLED Schedule

====
"#,
        FileId(3),
    );

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["InvInner".to_string(), "InvOuter".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new_with_extends(&concrete, &[&scheduler], &config);
    checker.set_store_states(true);
    assert_passes_with_states(
        checker.check(),
        "ENABLED Schedule / ENABLED Sched!Schedule on complex helper-op instance body",
        1,
    );
}

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn bug_3161_enabled_instance_with_substitution_keeps_outer_operator_binding() {
    let inner = common::parse_module_strict_with_id(
        r#"
---- MODULE InnerEnabled ----
EXTENDS Naturals

CONSTANT K
VARIABLE x

Op == x' = K

====
"#,
        FileId(4),
    );

    let outer = common::parse_module_strict_with_id(
        r#"
---- MODULE OuterEnabled ----
EXTENDS Naturals

VARIABLE x

I(n) == INSTANCE InnerEnabled WITH K <- n

Init == x = 0
Next == x' = x

Test(n) == ENABLED I(n)!Op
Inv == Test(1)

====
"#,
        FileId(5),
    );

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Inv".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new_with_extends(&outer, &[&inner], &config);
    checker.set_store_states(true);
    assert_passes_with_states(
        checker.check(),
        "ENABLED I(n)!Op should preserve outer operator bindings across INSTANCE WITH",
        1,
    );
}

#[cfg_attr(test, ntest::timeout(120000))]
#[cfg(not(debug_assertions))]
#[test]
fn bug_3161_allocatorimplementation_passes_with_tlc_state_parity() {
    let (module, checker_modules, config, fairness, stuttering_allowed) = load_allocator_modules();
    let checker_module_refs = checker_modules.iter().collect::<Vec<_>>();

    let mut checker = ModelChecker::new_with_extends(&module, &checker_module_refs, &config);
    checker.set_store_states(true);
    checker.set_fairness(fairness);
    checker.set_stuttering_allowed(stuttering_allowed);
    assert_passes_with_states(
        checker.check(),
        "AllocatorImplementation sequential checker",
        17_701,
    );
}
