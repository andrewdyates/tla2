// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Integration tests for #3176: disk-backed BFS successor cache.
//!
//! These tests validate that the disk-backed successor cache preserves
//! liveness results on a larger graph than the 3-state unit regressions and
//! provides a deterministic bounded-memory proxy where the historical
//! in-memory successor cache hits an entry budget while the disk backend
//! completes the same spec.

mod common;

use tla_check::{resolve_spec_from_config, CheckResult};
use tla_check::{
    set_liveness_inmemory_successor_limit_override, set_use_disk_successors_override, Config,
};
use tla_core::{lower, parse_to_syntax_tree, FileId};

fn check_liveness(
    src: &str,
    property: &str,
    use_disk_successors: bool,
    in_memory_successor_limit: Option<usize>,
) -> CheckResult {
    let _skip_guard = common::EnvVarGuard::remove("TLA2_SKIP_LIVENESS");
    let _disk_graph_guard = common::EnvVarGuard::remove("TLA2_LIVENESS_DISK_GRAPH");
    let _disk_successor_env_guard = common::EnvVarGuard::remove("TLA2_LIVENESS_DISK_SUCCESSORS");
    let _node_limit_env_guard = common::EnvVarGuard::remove("TLA2_LIVENESS_INMEMORY_NODE_LIMIT");
    let _successor_limit_env_guard =
        common::EnvVarGuard::remove("TLA2_LIVENESS_INMEMORY_SUCCESSOR_LIMIT");
    let _disk_successor_override = set_use_disk_successors_override(use_disk_successors);
    let _successor_limit_override =
        set_liveness_inmemory_successor_limit_override(in_memory_successor_limit);

    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.expect("module lowering should succeed");

    let spec_config = Config {
        specification: Some("Spec".to_string()),
        ..Default::default()
    };
    let resolved =
        resolve_spec_from_config(&spec_config, &tree).expect("spec resolution should succeed");

    let config = Config {
        init: Some(resolved.init.clone()),
        next: Some(resolved.next.clone()),
        properties: vec![property.to_string()],
        ..Default::default()
    };

    let mut checker = tla_check::ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    checker.set_store_states(true);
    checker.set_fairness(resolved.fairness);
    checker.set_stuttering_allowed(resolved.stuttering_allowed);
    checker.check()
}

const LARGE_CYCLIC_COUNTER_SPEC: &str = r#"
---- MODULE LargeCyclicCounter ----
EXTENDS Integers

VARIABLE x

Init == x = 0

Next ==
    \/ /\ x < 999
       /\ x' = x + 1
    \/ /\ x = 999
       /\ x' = 0

Spec == Init /\ [][Next]_x /\ WF_x(Next)

AlwaysEventuallyZero == []<>(x = 0)
====
"#;

#[cfg_attr(test, ntest::timeout(120000))]
#[test]
fn liveness_disk_successor_backend_large_spec_parity() {
    let in_memory = check_liveness(
        LARGE_CYCLIC_COUNTER_SPEC,
        "AlwaysEventuallyZero",
        false,
        None,
    );
    match &in_memory {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 1000,
                "in-memory successor cache should preserve the 1000-state liveness result"
            );
        }
        other => panic!("expected in-memory successor cache success, got: {other:?}"),
    }

    let disk = check_liveness(
        LARGE_CYCLIC_COUNTER_SPEC,
        "AlwaysEventuallyZero",
        true,
        None,
    );
    match &disk {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 1000,
                "disk successor cache should preserve the 1000-state liveness result"
            );
        }
        other => panic!("expected disk successor cache success, got: {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(120000))]
#[test]
fn liveness_disk_successor_backend_completes_under_inmemory_entry_pressure() {
    // Part of #4080: With auto-migration, the in-memory backend gracefully
    // migrates to disk when the entry limit is approached (at 80% of limit).
    // Both backends now complete successfully — the in-memory backend no
    // longer returns a hard error.
    const SUCCESSOR_LIMIT: usize = 256;

    // With auto-migration, the in-memory path should succeed by migrating
    // to disk when it hits 80% of the 256 entry limit (~204 entries).
    let in_memory = check_liveness(
        LARGE_CYCLIC_COUNTER_SPEC,
        "AlwaysEventuallyZero",
        false,
        Some(SUCCESSOR_LIMIT),
    );
    match &in_memory {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 1000,
                "auto-migrating successor cache should complete the 1000-state spec"
            );
        }
        other => panic!(
            "expected auto-migrating successor cache to succeed, got: {other:?}"
        ),
    }

    let disk = check_liveness(
        LARGE_CYCLIC_COUNTER_SPEC,
        "AlwaysEventuallyZero",
        true,
        Some(SUCCESSOR_LIMIT),
    );
    match &disk {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 1000,
                "disk successor cache should complete under the same entry budget"
            );
        }
        other => {
            panic!("disk successor cache should bypass the in-memory entry budget, got: {other:?}")
        }
    }
}
