// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::compute_fingerprint_from_compact_values;
use crate::state::compute_fingerprint_from_array;
use crate::var_index::VarRegistry;
use crate::Value;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_compute_fingerprint_from_compact_values_matches_value_array() {
    let registry = VarRegistry::from_names(["x", "y"]);
    let values = vec![
        Value::record([("x", Value::SmallInt(1))]),
        Value::seq(vec![Value::SmallInt(2), Value::Bool(false)]),
    ];
    let compact: Vec<tla_value::CompactValue> = values
        .iter()
        .cloned()
        .map(tla_value::CompactValue::from)
        .collect();

    assert_eq!(
        compute_fingerprint_from_compact_values(&compact, &registry),
        compute_fingerprint_from_array(&values, &registry),
        "compact-array raw fingerprint must match the Value-array baseline"
    );
}
