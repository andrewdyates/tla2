// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Worker-local current-state helper for the `#3337` parallel ArrayState lane.
//!
//! This module keeps the treatment-lane decision and current-state conversion
//! out of `work_item.rs` so queue ownership and transport logic stay unchanged.

use crate::state::worker_value_hash::{parallel_worker_values, WorkerArrayState};
use crate::state::ArrayState;
use crate::Value;

/// Build a worker-local current-state copy when the `#3337` treatment lane is
/// enabled and the state only contains the currently supported top-level
/// families from the design.
pub(super) fn maybe_worker_current_state(current: &ArrayState) -> Option<WorkerArrayState> {
    maybe_worker_current_state_if_enabled(current, parallel_worker_values())
}

fn maybe_worker_current_state_if_enabled(
    current: &ArrayState,
    worker_values_enabled: bool,
) -> Option<WorkerArrayState> {
    if !worker_values_enabled {
        return None;
    }
    let vals = current.materialize_values();
    if !supports_worker_value_lane(&vals) {
        return None;
    }
    Some(WorkerArrayState::from_array_state(current))
}

fn supports_worker_value_lane(values: &[Value]) -> bool {
    values.iter().all(value_supported)
}

fn value_supported(value: &Value) -> bool {
    matches!(
        value,
        Value::Bool(_)
            | Value::SmallInt(_)
            | Value::String(_)
            | Value::ModelValue(_)
            | Value::Set(_)
            | Value::Func(_)
            | Value::IntFunc(_)
            | Value::Seq(_)
            | Value::Tuple(_)
            | Value::Record(_)
    )
}

#[cfg(test)]
mod tests {
    use super::{maybe_worker_current_state_if_enabled, supports_worker_value_lane};
    use crate::state::ArrayState;
    use crate::value::{IntIntervalFunc, SortedSet};
    use crate::Value;
    use std::sync::Arc;

    #[test]
    fn test_supports_worker_value_lane_accepts_hot_top_level_families() {
        let values = vec![
            Value::Bool(true),
            Value::SmallInt(1),
            Value::string("x"),
            Value::ModelValue(Arc::from("mv")),
            Value::Set(Arc::new(SortedSet::from_iter([Value::SmallInt(1)]))),
            Value::Func(Arc::new(crate::value::FuncValue::from_sorted_entries(
                vec![(Value::SmallInt(1), Value::SmallInt(2))],
            ))),
            Value::IntFunc(Arc::new(IntIntervalFunc::new(
                1,
                1,
                vec![Value::SmallInt(2)],
            ))),
            Value::Seq(Arc::new(vec![Value::SmallInt(3)].into())),
            Value::Tuple(vec![Value::SmallInt(4)].into()),
            Value::record([("f", Value::SmallInt(5))]),
        ];

        assert!(supports_worker_value_lane(&values));
    }

    #[test]
    fn test_supports_worker_value_lane_rejects_out_of_scope_families() {
        use crate::value::IntervalValue;
        let values = [Value::Interval(Arc::new(IntervalValue::new(
            num_bigint::BigInt::from(1),
            num_bigint::BigInt::from(10),
        )))];
        assert!(!supports_worker_value_lane(&values));
    }

    #[test]
    fn test_maybe_worker_current_state_if_enabled_builds_worker_copy() {
        let current = ArrayState::from_values(vec![
            Value::SmallInt(1),
            Value::record([("f", Value::SmallInt(2))]),
        ]);

        let worker_state = maybe_worker_current_state_if_enabled(&current, true)
            .expect("supported values should enter the worker-value lane when enabled");

        let materialized = current.materialize_values();
        assert_eq!(worker_state.values(), materialized.as_slice());
        assert_ne!(worker_state.values().as_ptr(), materialized.as_ptr());
    }

    #[test]
    fn test_maybe_worker_current_state_if_enabled_respects_disable_gate() {
        let current = ArrayState::from_values(vec![Value::SmallInt(1)]);
        assert!(
            maybe_worker_current_state_if_enabled(&current, false).is_none(),
            "disabled treatment must keep the shared current-state path"
        );
    }
}
