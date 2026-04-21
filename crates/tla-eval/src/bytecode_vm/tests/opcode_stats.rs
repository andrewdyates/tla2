// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::{exec_simple, exec_with_next, make_func, ConstantPool, Opcode, Value};
use crate::{
    aggregate_opcode_stats, clear_diagnostic_counters, merge_opcode_stats_current_thread,
    opcode_stats, OpcodeStats,
};
use std::sync::{LazyLock, Mutex, MutexGuard};

static OPCODE_STATS_TEST_LOCK: LazyLock<Mutex<()>> = LazyLock::new(|| Mutex::new(()));

struct OpcodeStatsGuard {
    _lock: MutexGuard<'static, ()>,
    _override: crate::bytecode_vm::OpcodeStatsTestOverrideGuard,
}

impl OpcodeStatsGuard {
    fn enabled() -> Self {
        let lock = OPCODE_STATS_TEST_LOCK
            .lock()
            .unwrap_or_else(|err| err.into_inner());
        clear_diagnostic_counters();
        let override_guard = crate::bytecode_vm::set_opcode_stats_test_override(Some(true));
        Self {
            _lock: lock,
            _override: override_guard,
        }
    }
}

impl Drop for OpcodeStatsGuard {
    fn drop(&mut self) {
        clear_diagnostic_counters();
    }
}

#[test]
fn test_opcode_stats_count_scalar_categories() {
    let _guard = OpcodeStatsGuard::enabled();

    let result = exec_simple(
        vec![
            Opcode::LoadImm { rd: 0, value: 1 },
            Opcode::LoadImm { rd: 1, value: 2 },
            Opcode::AddInt {
                rd: 2,
                r1: 0,
                r2: 1,
            },
            Opcode::Eq {
                rd: 3,
                r1: 2,
                r2: 2,
            },
            Opcode::LoadBool { rd: 4, value: true },
            Opcode::And {
                rd: 5,
                r1: 3,
                r2: 4,
            },
            Opcode::Ret { rs: 5 },
        ],
        5,
    );

    assert_eq!(result, Value::Bool(true));

    let expected = OpcodeStats {
        arithmetic: 1,
        comparison: 1,
        logic: 1,
        control_flow: 1,
        other: 3,
        ..OpcodeStats::default()
    };
    assert_eq!(opcode_stats(), expected);
    assert_eq!(aggregate_opcode_stats(), expected);
}

#[test]
fn test_opcode_stats_count_quantifier_and_state_access_categories() {
    let _guard = OpcodeStatsGuard::enabled();

    let quant_result = exec_simple(
        vec![
            Opcode::SetEnum {
                rd: 0,
                start: 0,
                count: 0,
            },
            Opcode::ForallBegin {
                rd: 1,
                r_binding: 2,
                r_domain: 0,
                loop_end: 3,
            },
            Opcode::LoadBool {
                rd: 3,
                value: false,
            },
            Opcode::ForallNext {
                rd: 1,
                r_binding: 2,
                r_body: 3,
                loop_begin: -1,
            },
            Opcode::Ret { rs: 1 },
        ],
        3,
    );
    assert_eq!(quant_result, Value::Bool(true));

    let state = vec![Value::SmallInt(10)];
    let next_state = vec![Value::SmallInt(10)];
    let mut constants = ConstantPool::new();
    let start = constants.add_value(Value::SmallInt(0));
    let unchanged = make_func(
        "unchanged".to_string(),
        0,
        vec![
            Opcode::Unchanged {
                rd: 0,
                start,
                count: 1,
            },
            Opcode::Ret { rs: 0 },
        ],
        0,
    );
    let unchanged_result = exec_with_next(unchanged, constants, &state, Some(&next_state));
    assert_eq!(unchanged_result, Value::Bool(true));

    let expected = OpcodeStats {
        control_flow: 2,
        state_access: 1,
        set_ops: 1,
        quantifier: 1,
        ..OpcodeStats::default()
    };
    assert_eq!(opcode_stats(), expected);
    assert_eq!(aggregate_opcode_stats(), expected);
}

#[test]
fn test_opcode_stats_aggregate_include_merged_worker_thread() {
    let _guard = OpcodeStatsGuard::enabled();

    let handle = std::thread::spawn(|| {
        let _override = crate::bytecode_vm::set_opcode_stats_test_override(Some(true));
        let result = exec_simple(
            vec![Opcode::LoadImm { rd: 0, value: 7 }, Opcode::Ret { rs: 0 }],
            0,
        );
        assert_eq!(result, Value::SmallInt(7));
        assert_eq!(
            opcode_stats(),
            OpcodeStats {
                control_flow: 1,
                other: 1,
                ..OpcodeStats::default()
            }
        );
        merge_opcode_stats_current_thread();
    });

    handle.join().expect("worker thread should join cleanly");

    assert_eq!(opcode_stats(), OpcodeStats::default());
    assert_eq!(
        aggregate_opcode_stats(),
        OpcodeStats {
            control_flow: 1,
            other: 1,
            ..OpcodeStats::default()
        }
    );
}
