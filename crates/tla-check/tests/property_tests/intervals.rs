// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::helpers::eval_str;
use proptest::prelude::*;
use tla_check::Value;

proptest! {

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_interval_membership(lo in -10i32..10, hi in -10i32..20, x in -15i32..25) {
        // x \in lo..hi <=> lo <= x /\ x <= hi
        if lo <= hi {
            let lhs = eval_str(&format!(r#"{} \in {}..{}"#, x, lo, hi)).unwrap();
            let expected = lo <= x && x <= hi;
            prop_assert_eq!(lhs, Value::Bool(expected));
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_interval_cardinality(lo in -10i32..10, hi in -10i32..20) {
        // Cardinality(lo..hi) = Max(0, hi - lo + 1)
        let result = eval_str(&format!("Cardinality({}..{})", lo, hi)).unwrap();
        let expected = if hi >= lo { (hi - lo + 1) as i64 } else { 0 };
        prop_assert_eq!(result, Value::SmallInt(expected));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_interval_bounds(lo in -10i32..10, hi in -10i32..20) {
        // lo \in lo..hi if lo <= hi
        if lo <= hi {
            let result = eval_str(&format!(r#"{} \in {}..{}"#, lo, lo, hi)).unwrap();
            prop_assert_eq!(result, Value::Bool(true));

            let result = eval_str(&format!(r#"{} \in {}..{}"#, hi, lo, hi)).unwrap();
            prop_assert_eq!(result, Value::Bool(true));
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_interval_outside_bounds(lo in -10i32..10, hi in -10i32..20) {
        // (lo - 1) \notin lo..hi
        if lo <= hi {
            let result = eval_str(&format!(r#"{} \in {}..{}"#, lo - 1, lo, hi)).unwrap();
            prop_assert_eq!(result, Value::Bool(false));

            let result = eval_str(&format!(r#"{} \in {}..{}"#, hi + 1, lo, hi)).unwrap();
            prop_assert_eq!(result, Value::Bool(false));
        }
    }
}
