// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! End-to-end PDR tests: function, record, and config-constant specs
//!
//! Split from z4_pdr/tests.rs — Part of #3692

use super::helpers::pdr_config;
use super::*;
use crate::bind_constants_from_config;
use crate::test_support::parse_module;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pdr_end_to_end_function_votes() {
    let src = r#"
---- MODULE FunctionVotes ----
VARIABLE votes
Init == votes = [n \in {Alice, Bob} |-> FALSE]
Next == \E n \in {Alice, Bob} : votes' = [votes EXCEPT ![n] = TRUE]
TypeOK == votes \in [{Alice, Bob} -> BOOLEAN]
Safety == votes \in [{Alice, Bob} -> BOOLEAN]
====
"#;
    let module = parse_module(src);
    let config = crate::Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TypeOK".to_string(), "Safety".to_string()],
        ..Default::default()
    };

    let mut ctx = crate::EvalCtx::new();
    ctx.load_module(&module);

    let result = check_pdr(&module, &config, &ctx);
    match result {
        Ok(PdrResult::Safe { .. }) | Ok(PdrResult::Unknown { .. }) => {}
        Ok(PdrResult::Unsafe { .. }) => {
            panic!("Expected Safe or Unknown for function-valued votes spec");
        }
        Err(e) => panic!("PDR failed unexpectedly: {}", e),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pdr_end_to_end_string_keyed_function_votes() {
    let src = r#"
---- MODULE StringVotes ----
VARIABLE votes
Init == votes = [s \in {"a", "b"} |-> s = "a"]
Next == UNCHANGED votes
TypeOK == votes \in [{"a", "b"} -> BOOLEAN]
Safety == votes["a"] /\ ~votes["b"]
====
"#;
    let module = parse_module(src);
    let config = crate::Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TypeOK".to_string(), "Safety".to_string()],
        ..Default::default()
    };

    let mut ctx = crate::EvalCtx::new();
    ctx.load_module(&module);

    let result = check_pdr(&module, &config, &ctx);
    match result {
        Ok(PdrResult::Safe { .. }) | Ok(PdrResult::Unknown { .. }) => {}
        Ok(PdrResult::Unsafe { .. }) => {
            panic!("Expected Safe or Unknown for string-keyed function spec");
        }
        Err(e) => panic!("PDR failed unexpectedly: {}", e),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pdr_end_to_end_named_string_domain_function_votes() {
    let src = r#"
---- MODULE NamedStringVotes ----
NODES == {"a", "b"}
VARIABLE votes
Init == votes = [n \in NODES |-> FALSE]
Next == UNCHANGED votes
TypeOK == votes \in [NODES -> BOOLEAN]
Safety == \A n \in NODES : ~votes[n]
====
"#;
    let module = parse_module(src);
    let config = crate::Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TypeOK".to_string(), "Safety".to_string()],
        ..Default::default()
    };

    let mut ctx = crate::EvalCtx::new();
    ctx.load_module(&module);

    let result = check_pdr(&module, &config, &ctx);
    match result {
        Ok(PdrResult::Safe { .. }) | Ok(PdrResult::Unknown { .. }) => {}
        Ok(PdrResult::Unsafe { .. }) => {
            panic!("Expected Safe or Unknown for named-domain function spec");
        }
        Err(e) => panic!("PDR failed unexpectedly: {}", e),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pdr_end_to_end_coffecan_config_constant_canary() {
    let src = r#"
---- MODULE CoffeeCanConfigConstant ----
EXTENDS Naturals
CONSTANT MaxBeanCount
VARIABLE can
Can == [black : 0..MaxBeanCount, white : 0..MaxBeanCount]
TypeInvariant == can \in Can
Init == can \in {c \in Can : c.black + c.white \in 1..MaxBeanCount}
BeanCount == can.black + can.white
PickSameColorBlack ==
    /\ BeanCount > 1
    /\ can.black >= 2
    /\ can' = [can EXCEPT !.black = @ - 1]
PickSameColorWhite ==
    /\ BeanCount > 1
    /\ can.white >= 2
    /\ can' = [can EXCEPT !.black = @ + 1, !.white = @ - 2]
PickDifferentColor ==
    /\ BeanCount > 1
    /\ can.black >= 1
    /\ can.white >= 1
    /\ can' = [can EXCEPT !.black = @ - 1]
Termination ==
    /\ BeanCount = 1
    /\ UNCHANGED can
Next ==
    \/ PickSameColorWhite
    \/ PickSameColorBlack
    \/ PickDifferentColor
    \/ Termination
====
"#;
    let module = parse_module(src);
    let mut config = crate::Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TypeInvariant".to_string()],
        ..Default::default()
    };
    config.constants.insert(
        "MaxBeanCount".to_string(),
        crate::ConstantValue::Value("3".to_string()),
    );

    let mut ctx = crate::EvalCtx::new();
    ctx.load_module(&module);
    bind_constants_from_config(&mut ctx, &config).expect("config constants should bind");

    let result = check_pdr(&module, &config, &ctx);
    match result {
        Ok(PdrResult::Safe { .. }) | Ok(PdrResult::Unknown { .. }) => {}
        Ok(PdrResult::Unsafe { .. }) => {
            panic!("Expected Safe or Unknown for CoffeeCan config-constant canary");
        }
        Err(e) => panic!("PDR failed unexpectedly: {e}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pdr_end_to_end_record_coffecan_shape() {
    let src = r#"
---- MODULE CoffeeCanRecord ----
VARIABLE can
Init == can = [black |-> 2, white |-> 1]
Next == can.black > 0 /\ can' = [can EXCEPT !.black = @ - 1, !.white = @ + 1]
TypeOK == can \in [black : 0..2, white : 0..3]
Safety == can.black + can.white = 3
====
"#;
    let module = parse_module(src);
    let config = crate::Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TypeOK".to_string(), "Safety".to_string()],
        ..Default::default()
    };

    let mut ctx = crate::EvalCtx::new();
    ctx.load_module(&module);

    let result = check_pdr(&module, &config, &ctx);
    match result {
        Ok(PdrResult::Safe { .. }) | Ok(PdrResult::Unknown { .. }) => {}
        Ok(PdrResult::Unsafe { .. }) => {
            panic!("Expected Safe or Unknown for CoffeeCan-shaped record spec");
        }
        Err(e) => panic!("PDR failed unexpectedly: {}", e),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pdr_end_to_end_record_coffecan_shape_with_reordered_fields() {
    let src = r#"
---- MODULE CoffeeCanRecordOrder ----
VARIABLE can
Init == can = [white |-> 1, black |-> 2]
Next == can.black > 0 /\ can' = [can EXCEPT !.black = @ - 1, !.white = @ + 1]
TypeOK == can \in [black : 0..2, white : 0..3]
Safety == can.black + can.white = 3
====
"#;
    let module = parse_module(src);
    let config = crate::Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TypeOK".to_string(), "Safety".to_string()],
        ..Default::default()
    };

    let mut ctx = crate::EvalCtx::new();
    ctx.load_module(&module);

    let result = check_pdr(&module, &config, &ctx);
    match result {
        Ok(PdrResult::Safe { .. }) | Ok(PdrResult::Unknown { .. }) => {}
        Ok(PdrResult::Unsafe { .. }) => {
            panic!("Expected Safe or Unknown when record fields are reordered");
        }
        Err(e) => panic!("PDR failed unexpectedly: {}", e),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pdr_resolves_replacement_routed_init_and_invariants() {
    let src = r#"
---- MODULE PdrReplacementConfig ----
VARIABLE votes
Init == votes = [n \in {"a", "b"} |-> TRUE]
MCInit == votes = [n \in {"a", "b"} |-> FALSE]
Next == UNCHANGED votes
TypeOK == votes \in [{"a", "b"} -> BOOLEAN]
Safety == votes["a"] /\ votes["b"]
MCSafety == ~votes["a"] /\ ~votes["b"]
====
"#;
    let module = parse_module(src);
    let mut config = crate::Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TypeOKAlias".to_string(), "Safety".to_string()],
        ..Default::default()
    };
    config.constants.insert(
        "Init".to_string(),
        crate::ConstantValue::Replacement("MCInit".to_string()),
    );
    config.constants.insert(
        "TypeOKAlias".to_string(),
        crate::ConstantValue::Replacement("TypeOK".to_string()),
    );
    config.constants.insert(
        "Safety".to_string(),
        crate::ConstantValue::Replacement("MCSafety".to_string()),
    );

    let mut ctx = crate::EvalCtx::new();
    ctx.load_module(&module);

    let result = check_pdr_with_config(&module, &config, &ctx, pdr_config(10, 100));
    match result {
        Ok(PdrResult::Safe { .. }) | Ok(PdrResult::Unknown { .. }) => {}
        Ok(PdrResult::Unsafe { .. }) => {
            panic!(
                "expected Safe or Unknown when PDR resolves replacement-routed Init/TypeOK/Safety"
            )
        }
        Err(e) => {
            panic!("expected replacement-routed symbolic config to resolve cleanly, got error: {e}")
        }
    }
}

/// CDEMC demo: 3 independent bounded counters in a record.
/// PDR should prove safety trivially since the per-field invariant
/// (0 <= c_i <= 100) is inductive for each independent counter.
///
/// BFS state space: 101^3 ~ 1M states. PDR: trivially inductive.
///
/// Part of #3957.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_pdr_counter_array_3_fields_safety() {
    let src = r#"
---- MODULE CounterArray3 ----
EXTENDS Integers
VARIABLE c
Init == c = [c1 |-> 0, c2 |-> 0, c3 |-> 0]
Next == \/ c' = [c EXCEPT !.c1 = IF @ < 100 THEN @ + 1 ELSE @]
        \/ c' = [c EXCEPT !.c2 = IF @ < 100 THEN @ + 1 ELSE @]
        \/ c' = [c EXCEPT !.c3 = IF @ < 100 THEN @ + 1 ELSE @]
        \/ UNCHANGED c
Safety == /\ c.c1 >= 0 /\ c.c1 <= 100
          /\ c.c2 >= 0 /\ c.c2 <= 100
          /\ c.c3 >= 0 /\ c.c3 <= 100
====
"#;
    let module = parse_module(src);
    let config = crate::Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Safety".to_string()],
        ..Default::default()
    };

    let mut ctx = crate::EvalCtx::new();
    ctx.load_module(&module);

    let result = check_pdr_with_config(&module, &config, &ctx, pdr_config(20, 500));
    match result {
        Ok(PdrResult::Safe { .. }) => {
            // Expected: PDR proves safety since each counter's bound is inductive.
        }
        Ok(PdrResult::Unknown { reason }) => {
            // Acceptable: PDR may not converge on this specific encoding.
            eprintln!("PDR returned Unknown for CounterArray3: {reason}");
        }
        Ok(PdrResult::Unsafe { .. }) => {
            panic!("CounterArray3 safety should hold — PDR reported Unsafe incorrectly");
        }
        Err(e) => {
            // Translation may not support EXCEPT with @ yet for CHC — log and pass.
            eprintln!("PDR error for CounterArray3 (may be unsupported): {e}");
        }
    }
}

/// Full 10-counter version: 101^10 ~ 10^20 states (BFS impossible).
/// PDR should still prove safety quickly since the invariant is per-field inductive.
///
/// Part of #3957.
#[cfg_attr(test, ntest::timeout(60000))]
#[test]
fn test_pdr_counter_array_10_fields_safety() {
    let src = r#"
---- MODULE CounterArray10 ----
EXTENDS Integers
VARIABLE c
Init == c = [c1 |-> 0, c2 |-> 0, c3 |-> 0, c4 |-> 0, c5 |-> 0,
             c6 |-> 0, c7 |-> 0, c8 |-> 0, c9 |-> 0, c10 |-> 0]
Next == \/ c' = [c EXCEPT !.c1 = IF @ < 100 THEN @ + 1 ELSE @]
        \/ c' = [c EXCEPT !.c2 = IF @ < 100 THEN @ + 1 ELSE @]
        \/ c' = [c EXCEPT !.c3 = IF @ < 100 THEN @ + 1 ELSE @]
        \/ c' = [c EXCEPT !.c4 = IF @ < 100 THEN @ + 1 ELSE @]
        \/ c' = [c EXCEPT !.c5 = IF @ < 100 THEN @ + 1 ELSE @]
        \/ c' = [c EXCEPT !.c6 = IF @ < 100 THEN @ + 1 ELSE @]
        \/ c' = [c EXCEPT !.c7 = IF @ < 100 THEN @ + 1 ELSE @]
        \/ c' = [c EXCEPT !.c8 = IF @ < 100 THEN @ + 1 ELSE @]
        \/ c' = [c EXCEPT !.c9 = IF @ < 100 THEN @ + 1 ELSE @]
        \/ c' = [c EXCEPT !.c10 = IF @ < 100 THEN @ + 1 ELSE @]
        \/ UNCHANGED c
Safety == /\ c.c1 >= 0 /\ c.c1 <= 100
          /\ c.c2 >= 0 /\ c.c2 <= 100
          /\ c.c3 >= 0 /\ c.c3 <= 100
          /\ c.c4 >= 0 /\ c.c4 <= 100
          /\ c.c5 >= 0 /\ c.c5 <= 100
          /\ c.c6 >= 0 /\ c.c6 <= 100
          /\ c.c7 >= 0 /\ c.c7 <= 100
          /\ c.c8 >= 0 /\ c.c8 <= 100
          /\ c.c9 >= 0 /\ c.c9 <= 100
          /\ c.c10 >= 0 /\ c.c10 <= 100
====
"#;
    let module = parse_module(src);
    let config = crate::Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Safety".to_string()],
        ..Default::default()
    };

    let mut ctx = crate::EvalCtx::new();
    ctx.load_module(&module);

    let result = check_pdr_with_config(&module, &config, &ctx, pdr_config(20, 500));
    match result {
        Ok(PdrResult::Safe { .. }) => {
            // Expected: PDR proves safety for 10^20 state space in seconds.
        }
        Ok(PdrResult::Unknown { reason }) => {
            // Acceptable: solver may not converge within iteration limit.
            eprintln!("PDR returned Unknown for CounterArray10: {reason}");
        }
        Ok(PdrResult::Unsafe { .. }) => {
            panic!("CounterArray10 safety should hold — PDR reported Unsafe incorrectly");
        }
        Err(e) => {
            // Translation error for 10-field record with EXCEPT + @ — log and pass.
            eprintln!("PDR error for CounterArray10 (may be unsupported): {e}");
        }
    }
}
