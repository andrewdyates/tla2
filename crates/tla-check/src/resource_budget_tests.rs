// Copyright 2026 Dropbox Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Tests for resource_budget.rs. Extracted to keep that file under 500 lines.

use super::resource_budget::*;
use crate::enumerate::{Constraint, InitDomain};
use num_bigint::BigInt;
use std::sync::Arc;

#[test]
fn test_unlimited_has_all_zeros() {
    let budget = ResourceBudget::unlimited();
    assert_eq!(budget.max_states, 0);
    assert_eq!(budget.max_depth, 0);
    assert_eq!(budget.memory_bytes, 0);
    assert_eq!(budget.disk_bytes, 0);
    assert_eq!(budget.timeout_secs, 0);
    assert!(!budget.has_disk_limit());
    assert!(!budget.has_memory_limit());
}

#[test]
fn test_safe_defaults_has_memory_on_supported_platform() {
    let budget = ResourceBudget::safe_defaults();
    if cfg!(any(target_os = "macos", target_os = "linux")) {
        assert!(
            budget.memory_bytes > 0,
            "safe defaults should auto-detect memory on this platform"
        );
        assert!(
            budget.has_memory_limit(),
            "safe defaults should have memory limit"
        );
    }
}

#[test]
fn test_safe_defaults_has_disk_on_supported_platform() {
    let budget = ResourceBudget::safe_defaults();
    if cfg!(any(target_os = "macos", target_os = "linux")) {
        assert!(
            budget.disk_bytes > 0,
            "safe defaults should auto-detect disk on this platform"
        );
        assert!(
            budget.has_disk_limit(),
            "safe defaults should have disk limit"
        );
    }
}

#[test]
fn test_builder_pattern() {
    let budget = ResourceBudget::unlimited()
        .with_max_states(1000)
        .with_max_depth(50)
        .with_memory_bytes(1024 * 1024 * 512)
        .with_disk_bytes(1024 * 1024 * 1024)
        .with_timeout_secs(300);

    assert_eq!(budget.max_states, 1000);
    assert_eq!(budget.max_depth, 50);
    assert_eq!(budget.memory_bytes, 512 * 1024 * 1024);
    assert_eq!(budget.disk_bytes, 1024 * 1024 * 1024);
    assert_eq!(budget.timeout_secs, 300);
}

#[test]
fn test_default_is_safe_defaults() {
    let default_budget = ResourceBudget::default();
    let safe_budget = ResourceBudget::safe_defaults();
    assert_eq!(default_budget.max_states, safe_budget.max_states);
    assert_eq!(default_budget.max_depth, safe_budget.max_depth);
    assert_eq!(default_budget.timeout_secs, safe_budget.timeout_secs);
    assert_eq!(
        default_budget.has_memory_limit(),
        safe_budget.has_memory_limit(),
    );
    assert_eq!(
        default_budget.has_disk_limit(),
        safe_budget.has_disk_limit()
    );
}

#[test]
fn test_format_bytes_preserves_small_limits() {
    assert_eq!(format_bytes(1), "1 B");
    assert_eq!(format_bytes(1536), "1.5 KiB");
    assert_eq!(format_bytes(2 * 1024 * 1024), "2.0 MiB");
}

#[test]
fn test_available_disk_bytes_cwd_returns_some_on_supported_platform() {
    if cfg!(any(target_os = "macos", target_os = "linux")) {
        let avail = available_disk_bytes_cwd();
        let bytes = avail.expect("disk query should succeed on this platform");
        assert!(
            bytes > 100_000_000,
            "available disk too small ({bytes} bytes)"
        );
    }
}

#[test]
fn test_available_disk_bytes_path_returns_some_on_supported_platform() {
    if cfg!(any(target_os = "macos", target_os = "linux")) {
        let avail = available_disk_bytes(std::path::Path::new("/tmp"));
        let bytes = avail.expect("disk query should succeed on /tmp");
        assert!(
            bytes > 100_000_000,
            "available disk on /tmp too small ({bytes} bytes)"
        );
    }
}

// --- StateSpaceEstimate tests ---

fn make_vars(names: &[&str]) -> Vec<Arc<str>> {
    names.iter().map(|n| Arc::from(*n)).collect()
}

#[test]
fn test_estimate_empty_branches_returns_zero() {
    let vars = make_vars(&["x", "y"]);
    let est = estimate_init_state_space(&[], &vars);
    assert_eq!(est.initial_states_upper_bound, Some(0));
    assert_eq!(est.branch_count, 0);
    assert!(est.is_bounded());
}

#[test]
fn test_estimate_single_eq_per_var() {
    let vars = make_vars(&["x", "y"]);
    let branches = vec![vec![
        Constraint::Eq("x".to_string(), crate::Value::Int(BigInt::from(0).into())),
        Constraint::Eq("y".to_string(), crate::Value::Int(BigInt::from(1).into())),
    ]];
    let est = estimate_init_state_space(&branches, &vars);
    assert_eq!(est.initial_states_upper_bound, Some(1));
    assert!(est.is_bounded());
    assert!(est.unbounded_vars.is_empty());
}

#[test]
fn test_estimate_concrete_domain() {
    let vars = make_vars(&["x", "y"]);
    let branches = vec![vec![
        Constraint::In(
            "x".to_string(),
            InitDomain::Concrete(vec![
                crate::Value::Int(BigInt::from(1).into()),
                crate::Value::Int(BigInt::from(2).into()),
                crate::Value::Int(BigInt::from(3).into()),
            ]),
        ),
        Constraint::Eq("y".to_string(), crate::Value::Bool(true)),
    ]];
    let est = estimate_init_state_space(&branches, &vars);
    assert_eq!(est.initial_states_upper_bound, Some(3));
    assert_eq!(est.variable_domains[0], ("x".to_string(), Some(3)));
    assert_eq!(est.variable_domains[1], ("y".to_string(), Some(1)));
}

#[test]
fn test_estimate_disjunctive_branches() {
    let vars = make_vars(&["x", "y"]);
    let branches = vec![
        vec![
            Constraint::Eq("x".to_string(), crate::Value::Int(BigInt::from(0).into())),
            Constraint::Eq("y".to_string(), crate::Value::Int(BigInt::from(0).into())),
        ],
        vec![
            Constraint::In(
                "x".to_string(),
                InitDomain::Concrete(vec![
                    crate::Value::Int(BigInt::from(1).into()),
                    crate::Value::Int(BigInt::from(2).into()),
                ]),
            ),
            Constraint::In(
                "y".to_string(),
                InitDomain::Concrete(vec![
                    crate::Value::Int(BigInt::from(3).into()),
                    crate::Value::Int(BigInt::from(4).into()),
                    crate::Value::Int(BigInt::from(5).into()),
                ]),
            ),
        ],
    ];
    let est = estimate_init_state_space(&branches, &vars);
    assert_eq!(est.initial_states_upper_bound, Some(7));
    assert_eq!(est.branch_count, 2);
}

#[test]
fn test_estimate_unconstrained_var_is_unbounded() {
    let vars = make_vars(&["x", "y"]);
    let branches = vec![vec![Constraint::Eq(
        "x".to_string(),
        crate::Value::Int(BigInt::from(0).into()),
    )]];
    let est = estimate_init_state_space(&branches, &vars);
    assert_eq!(est.initial_states_upper_bound, None);
    assert!(!est.is_bounded());
    assert!(est.unbounded_vars.contains(&"y".to_string()));
}

#[test]
fn test_estimate_deferred_counts_as_one() {
    let vars = make_vars(&["x"]);
    let branches = vec![vec![Constraint::Deferred(
        "x".to_string(),
        Box::new(tla_core::Spanned {
            node: tla_core::ast::Expr::Bool(true),
            span: tla_core::Span::dummy(),
        }),
    )]];
    let est = estimate_init_state_space(&branches, &vars);
    assert_eq!(est.initial_states_upper_bound, Some(1));
}

#[test]
fn test_estimate_exceeds_states() {
    let est = StateSpaceEstimate {
        initial_states_upper_bound: Some(1_000_000),
        variable_domains: vec![("x".to_string(), Some(1_000_000))],
        unbounded_vars: Vec::new(),
        branch_count: 1,
    };
    assert!(est.exceeds_states(999_999));
    assert!(!est.exceeds_states(1_000_000));
    assert!(!est.exceeds_states(1_000_001));
}

#[test]
fn test_estimate_memory_bytes() {
    let est = StateSpaceEstimate {
        initial_states_upper_bound: Some(1000),
        variable_domains: vec![],
        unbounded_vars: Vec::new(),
        branch_count: 1,
    };
    assert_eq!(est.estimated_memory_bytes(), Some(8000));
}
