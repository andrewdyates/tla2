// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Error path tests for `iter_set_tlc_normalized`.

use super::super::super::*;

// === Error: non-set value ===

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tlc_normalized_error_on_non_set() {
    let v = Value::int(42);
    let result = v.iter_set_tlc_normalized();
    assert!(result.is_err(), "Expected error for non-set value");
}
