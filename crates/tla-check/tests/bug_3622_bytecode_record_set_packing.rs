// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

mod common;

use tla_check::{check_module, CheckResult, Config};
use tla_eval::clear_for_test_reset;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bytecode_record_set_field_packing_passes_real_check_path() {
    let _bytecode_vm = common::EnvVarGuard::set("TLA2_BYTECODE_VM", Some("1"));
    let _bytecode_stats = common::EnvVarGuard::set("TLA2_BYTECODE_VM_STATS", Some("1"));
    clear_for_test_reset();

    let module = common::parse_module(
        r#"
---- MODULE BytecodeInvariantRecordSetPacking ----
People == {1}
Floor == {1}
OtherFloor == {2}
VARIABLE personState
Init == personState = [p \in People |-> [location |-> 1, destination |-> 1, waiting |-> FALSE]]
Next == personState' = personState
TypeInvariant ==
    personState \in [People -> [location : Floor \cup OtherFloor, destination : Floor, waiting : BOOLEAN]]
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TypeInvariant".to_string()],
        ..Default::default()
    };

    let enabled = check_module(&module, &config);

    let _bytecode_vm = common::EnvVarGuard::set("TLA2_BYTECODE_VM", Some("0"));
    let _bytecode_stats = common::EnvVarGuard::set("TLA2_BYTECODE_VM_STATS", Some("0"));
    clear_for_test_reset();
    let baseline = check_module(&module, &config);

    let enabled_states = match enabled {
        CheckResult::Success(stats) => stats.states_found,
        other => panic!("expected bytecode-enabled model check success, got: {other:?}"),
    };
    let baseline_states = match baseline {
        CheckResult::Success(stats) => stats.states_found,
        other => panic!("expected bytecode-disabled model check success, got: {other:?}"),
    };

    assert_eq!(
        enabled_states, 1,
        "expected one stable state from Init / stuttering Next"
    );
    assert_eq!(
        enabled_states, baseline_states,
        "bytecode enablement must preserve the real check result for record-set invariant packing",
    );
}
