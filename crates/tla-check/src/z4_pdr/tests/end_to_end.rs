// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! End-to-end PDR tests: basic counter and operator specs
//!
//! Split from z4_pdr/tests.rs — Part of #3692

use super::helpers::pdr_config;
use super::*;
use crate::test_support::parse_module;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pdr_end_to_end_safe_counter() {
    // Safe counter: Init: count = 0, Next: count < 5 /\ count' = count + 1
    // Safety: count <= 5
    let src = r#"
---- MODULE SafeCounter ----
VARIABLE count
Init == count = 0
Next == count < 5 /\ count' = count + 1
Safety == count <= 5
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

    let result = check_pdr(&module, &config, &ctx);
    match result {
        Ok(PdrResult::Safe { .. }) | Ok(PdrResult::Unknown { .. }) => {
            // Expected for safe spec
        }
        Ok(PdrResult::Unsafe { .. }) => {
            panic!("Expected Safe or Unknown for safe counter spec");
        }
        Err(e) => {
            panic!("PDR failed unexpectedly: {}", e);
        }
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pdr_end_to_end_unsafe_counter() {
    // Unsafe counter: grows unboundedly but claims count <= 5
    let src = r#"
---- MODULE UnsafeCounter ----
VARIABLE count
Init == count = 0
Next == count' = count + 1
Safety == count <= 5
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

    let result = check_pdr(&module, &config, &ctx);
    match result {
        Ok(PdrResult::Unsafe { trace }) => {
            // Expected: counterexample found
            assert!(!trace.is_empty(), "counterexample should have states");
        }
        Ok(PdrResult::Unknown { .. }) => {
            // Acceptable: PDR may not find counterexample in limited iterations
        }
        Ok(PdrResult::Safe { .. }) => {
            panic!("Expected Unsafe or Unknown for unsafe counter spec");
        }
        Err(e) => {
            panic!("PDR failed unexpectedly: {}", e);
        }
    }
}

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_pdr_end_to_end_two_vars_safe() {
    // Two-variable spec with invariant
    let src = r#"
---- MODULE TwoVars ----
VARIABLES x, y
Init == x = 0 /\ y = 0
Next == x' = x + 1 /\ y' = y + 2
Safety == y >= 0
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

    let result = check_pdr_with_config(&module, &config, &ctx, pdr_config(10, 100));
    match result {
        Ok(PdrResult::Safe { .. }) | Ok(PdrResult::Unknown { .. }) => {
            // Expected for safe spec (y only increases from 0)
        }
        Ok(PdrResult::Unsafe { .. }) => {
            panic!("Expected Safe or Unknown for safe two-var spec");
        }
        Err(e) => {
            panic!("PDR failed unexpectedly: {}", e);
        }
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pdr_end_to_end_with_operator_expansion() {
    // Test that operator expansion works with Next containing operator calls
    let src = r#"
---- MODULE OperatorExpansion ----
VARIABLE count
Init == count = 0
Inc == count' = count + 1
Next == count < 5 /\ Inc
Safety == count <= 5
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

    let result = check_pdr(&module, &config, &ctx);
    match result {
        Ok(PdrResult::Safe { .. }) | Ok(PdrResult::Unknown { .. }) => {
            // Expected: operator expansion should inline Inc
        }
        Ok(PdrResult::Unsafe { .. }) => {
            panic!("Expected Safe or Unknown for safe spec with operator expansion");
        }
        Err(e) => {
            panic!("PDR failed unexpectedly: {}", e);
        }
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pdr_end_to_end_with_unchanged() {
    // Test UNCHANGED support
    let src = r#"
---- MODULE UnchangedTest ----
VARIABLES x, y
Init == x = 0 /\ y = 0
Next == x' = x + 1 /\ UNCHANGED y
Safety == y = 0
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

    let result = check_pdr(&module, &config, &ctx);
    match result {
        Ok(PdrResult::Safe { .. }) | Ok(PdrResult::Unknown { .. }) => {
            // Expected: y is always 0 because UNCHANGED y
        }
        Ok(PdrResult::Unsafe { .. }) => {
            panic!("Expected Safe or Unknown for spec with UNCHANGED");
        }
        Err(e) => {
            panic!("PDR failed unexpectedly: {}", e);
        }
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pdr_with_zero_solve_timeout_returns_unknown() {
    use std::time::Duration;

    let src = r#"
---- MODULE TimeoutCounter ----
VARIABLE count
Init == count = 0
Next == count' = count + 1
Safety == count <= 5
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

    let mut pdr_config = pdr_config(10, 100);
    pdr_config.solve_timeout = Some(Duration::ZERO);

    let result = check_pdr_with_config(&module, &config, &ctx, pdr_config);
    match result {
        // Portfolio solver may return Unknown (timeout) or Unsafe (BMC finds counterexample
        // instantly even with zero timeout since this spec is trivially unsafe).
        Ok(PdrResult::Unknown { .. }) | Ok(PdrResult::Unsafe { .. }) => {}
        Ok(other) => panic!("expected Unknown or Unsafe under zero solve_timeout, got {other:?}"),
        Err(e) => panic!("expected Unknown or Unsafe under zero solve_timeout, got error: {e}"),
    }
}
