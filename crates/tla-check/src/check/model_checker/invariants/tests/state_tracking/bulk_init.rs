// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for bulk init solve, precheck, and VIEW dedup.

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_solve_predicate_for_states_to_bulk_direct_constraints() {
    let module = parse_module(
        r#"
---- MODULE InitBulkDirect ----
VARIABLE x
Init == x \in {0, 1}
Next == x' = x
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };
    let mut mc = ModelChecker::new(&module, &config);

    let bulk_init = mc
        .solve_predicate_for_states_to_bulk("Init")
        .expect("bulk solve should succeed")
        .expect("direct-constraint init should stream to bulk");
    let enumeration = bulk_init.enumeration;
    let storage = bulk_init.storage;

    assert_eq!(storage.len(), 2);
    assert_eq!(enumeration.generated, 2);
    assert_eq!(enumeration.added, 2);
    let mut seen = Vec::new();
    for i in 0..storage.len() {
        seen.push(storage.get_state(i as u32)[0].clone());
    }
    seen.sort();
    seen.dedup();
    assert_eq!(seen, vec![Value::int(0), Value::int(1)]);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_solve_predicate_for_states_to_bulk_fallback_candidate_filtering() {
    let module = parse_module(
        r#"
---- MODULE InitBulkFallback ----
VARIABLE x
TypeOK == x \in {0, 1, 2}
Init == x > 0 /\ x < 2
Next == x' = x
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };
    let mut mc = ModelChecker::new(&module, &config);

    let bulk_init = mc
        .solve_predicate_for_states_to_bulk("Init")
        .expect("bulk solve should succeed")
        .expect("fallback via TypeOK should stream to bulk");
    let enumeration = bulk_init.enumeration;
    let storage = bulk_init.storage;

    assert_eq!(storage.len(), 1);
    assert_eq!(enumeration.generated, 1);
    assert_eq!(enumeration.added, 1);
    assert_eq!(storage.get_state(0)[0], Value::int(1));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_solve_predicate_for_states_to_bulk_setpred_membership() {
    let module = parse_module(
        r#"
---- MODULE InitBulkSetPred ----
VARIABLE x
Init == x \in {y \in {0, 1} : y = 0} \/ x \in {y \in {0, 1} : y = 0}
Next == x' = x
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };
    let mut mc = ModelChecker::new(&module, &config);

    let bulk_init = mc
        .solve_predicate_for_states_to_bulk("Init")
        .expect("bulk solve should not error");

    // The bulk path now handles set-predicate membership correctly.
    // {y \in {0, 1} : y = 0} = {0}, so Init == x \in {0} => x = 0.
    let bulk_init = bulk_init.expect("set-predicate membership should be handled by bulk path");
    let storage = bulk_init.storage;
    assert_eq!(storage.len(), 1, "should produce exactly 1 initial state");
    assert_eq!(storage.get_state(0)[0], Value::int(0), "x should be 0");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_init_bfs_dedups_view_collapsed_initial_fingerprints() {
    let module = parse_module(
        r#"
---- MODULE InitViewDedup ----
VARIABLE x
Init == x \in {0, 1}
Next == FALSE
View == 0
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        view: Some("View".to_string()),
        ..Default::default()
    };

    // The raw init enumeration should still produce two states. The duplicate
    // suppression we want to verify happens later, when the BFS init path
    // fingerprints states through VIEW and admits only the first fingerprint.
    let mut bulk_probe = ModelChecker::new(&module, &config);
    let bulk_init = bulk_probe
        .generate_initial_states_to_bulk("Init")
        .expect("bulk init generation should succeed")
        .expect("direct-constraint init should stream to bulk");
    assert_eq!(
        bulk_init.enumeration.generated, 2,
        "pre-dedup bulk enumeration should generate both raw init states"
    );
    assert_eq!(
        bulk_init.enumeration.added, 2,
        "bulk sink should preserve both raw init states before VIEW-based dedup"
    );
    assert_eq!(
        bulk_init.storage.len(),
        2,
        "bulk storage should contain both raw init states before BFS admission"
    );

    for store_states in [false, true] {
        let mut mc = ModelChecker::new(&module, &config);
        mc.set_deadlock_check(false);
        mc.set_store_states(store_states);

        match mc.check() {
            CheckResult::Success(stats) => {
                assert_eq!(
                    stats.initial_states,
                    1,
                    "VIEW-collapsed init states should admit exactly one initial state in {} mode",
                    if store_states {
                        "full-state"
                    } else {
                        "fingerprint-only"
                    }
                );
                assert_eq!(
                    stats.states_found, 1,
                    "VIEW-collapsed init states should produce exactly one reachable state in {} mode",
                    if store_states { "full-state" } else { "fingerprint-only" }
                );
            }
            other => panic!(
                "expected Success for VIEW-collapsed init dedup in {} mode, got {other:?}",
                if store_states {
                    "full-state"
                } else {
                    "fingerprint-only"
                }
            ),
        }
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_solve_predicate_for_states_to_bulk_lazy_record_filter_membership_3228() {
    let module = parse_module(
        r#"
---- MODULE InitBulkCoffeeCanShape ----
EXTENDS Naturals
VARIABLE can

Can == [black : 0..2, white : 0..2]
Init == can \in {c \in Can : c.black + c.white \in 1..2}
Next == can' = can
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };
    let mut mc = ModelChecker::new(&module, &config);

    let bulk_init = mc
        .solve_predicate_for_states_to_bulk("Init")
        .expect("bulk solve should succeed")
        .expect("CoffeeCan-shaped init should stream to bulk");
    let enumeration = bulk_init.enumeration;
    let storage = bulk_init.storage;

    assert_eq!(storage.len(), 5, "expected 5 valid record states");
    assert_eq!(enumeration.generated, 5);
    assert_eq!(enumeration.added, 5);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_solve_predicate_for_states_to_bulk_prechecked_stops_on_invariant_violation() {
    let module = parse_module(
        r#"
---- MODULE InitBulkPrecheckedStop ----
VARIABLE x, y, z
Init ==
    /\ x \in 0..9
    /\ y \in 0..9
    /\ z \in 0..9
Inv == x = 1
Next == FALSE
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Inv".to_string()],
        ..Default::default()
    };
    let mut mc = ModelChecker::new(&module, &config);

    match mc.solve_predicate_for_states_to_bulk_prechecked("Init") {
        Err(CheckResult::InvariantViolation {
            invariant, trace, ..
        }) => {
            assert_eq!(invariant, "Inv");
            assert_eq!(
                trace.states.len(),
                1,
                "init violation should report one state"
            );
            let state = &trace.states[0];
            assert_eq!(state.get("x"), Some(&Value::int(0)));
            assert_eq!(state.get("y"), Some(&Value::int(0)));
            assert_eq!(state.get("z"), Some(&Value::int(0)));
        }
        Ok(Some(_)) => panic!("expected init invariant violation from prechecked bulk solve"),
        Ok(None) => panic!("expected init invariant violation from prechecked bulk solve"),
        Err(other) => {
            panic!("expected init invariant violation from prechecked bulk solve, got {other:?}")
        }
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_solve_predicate_for_states_to_bulk_prechecked_applies_constraints_before_invariants() {
    let module = parse_module(
        r#"
---- MODULE InitBulkPrecheckedConstraints ----
VARIABLE x
Init == x \in {0, 1}
Allowed == x = 1
Inv == x = 1
Next == FALSE
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        constraints: vec!["Allowed".to_string()],
        invariants: vec!["Inv".to_string()],
        ..Default::default()
    };
    let mut mc = ModelChecker::new(&module, &config);

    let bulk_init = mc
        .solve_predicate_for_states_to_bulk_prechecked("Init")
        .expect("constraint-pruned prechecked bulk solve should succeed")
        .expect("direct constraint init should stream to bulk");
    let enumeration = bulk_init.enumeration;
    let storage = bulk_init.storage;

    assert_eq!(
        enumeration.generated, 1,
        "only the constraint-admitted state should survive prechecked enumeration"
    );
    assert_eq!(enumeration.added, 1);
    assert_eq!(storage.len(), 1);
    assert_eq!(storage.get_state(0)[0], Value::int(1));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_solve_predicate_for_states_to_bulk_prechecked_stops_on_property_init_violation() {
    let module = parse_module(
        r#"
---- MODULE InitBulkPrecheckedProperty ----
VARIABLE x
Init == x \in {0, 1}
BadInit == x = 1
Next == FALSE
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["BadInit".to_string()],
        ..Default::default()
    };
    let mut mc = ModelChecker::new(&module, &config);
    let classification = crate::checker_ops::classify_property_safety_parts(
        &mc.ctx,
        &config.properties,
        &mc.module.op_defs,
    );
    assert_eq!(
        classification.init_predicates.len(),
        1,
        "BadInit should classify as an init predicate for the prechecked helper"
    );
    mc.compiled.property_init_predicates = classification.init_predicates;

    match mc.solve_predicate_for_states_to_bulk_prechecked("Init") {
        Err(CheckResult::PropertyViolation {
            property,
            kind,
            trace,
            ..
        }) => {
            assert_eq!(property, "BadInit");
            assert_eq!(kind, crate::check::PropertyViolationKind::StateLevel);
            assert_eq!(
                trace.states.len(),
                1,
                "init property violation should report one state"
            );
            let state = &trace.states[0];
            assert_eq!(state.get("x"), Some(&Value::int(0)));
        }
        Ok(Some(_)) => panic!("expected init property violation from prechecked bulk solve"),
        Ok(None) => panic!("expected init property violation from prechecked bulk solve"),
        Err(other) => {
            panic!("expected init property violation from prechecked bulk solve, got {other:?}")
        }
    }
}
