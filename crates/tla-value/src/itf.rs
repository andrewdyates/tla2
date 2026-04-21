// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Informal Trace Format (ITF) JSON serialization for TLA+ values.
//!
//! ITF is a JSON-based community standard used by Apalache and other TLA+ tooling
//! for counterexample trace interchange. Specification:
//! <https://apalache.informal.systems/docs/adr/015adr-trace.html>
//!
//! This module provides the core `value_to_itf` conversion from `Value` to
//! `serde_json::Value`. Trace-level serialization (states, traces) lives in
//! higher-level crates that have access to state/trace types.
//!
//! Part of #3753.

use serde_json::{json, Value as JsonValue};

use crate::Value;

/// Convert a TLA+ `Value` to its ITF JSON representation.
///
/// ITF encoding rules (per ADR-015):
/// - Booleans: plain JSON `true`/`false`
/// - Integers: `{"#bigint": "123"}`
/// - Strings: `{"#tla": "\"hello\""}`  (TLA+ string literal with escaped quotes)
/// - Sets: `{"#set": [elem1, elem2, ...]}`
/// - Tuples: `{"#tup": [elem1, elem2, ...]}`
/// - Sequences: `{"#tup": [elem1, elem2, ...]}` (same as tuples in ITF)
/// - Records: plain JSON objects with field names as keys
/// - Functions: `{"#map": [[key1, val1], [key2, val2], ...]}`
/// - Model values: `{"#tla": "model_value_name"}`
/// - Lazy/symbolic values: `{"#tla": "<display string>"}` (fallback)
#[must_use]
pub fn value_to_itf(value: &Value) -> JsonValue {
    match value {
        Value::Bool(b) => JsonValue::Bool(*b),

        Value::SmallInt(n) => json!({ "#bigint": n.to_string() }),

        Value::Int(n) => json!({ "#bigint": n.to_string() }),

        Value::String(s) => {
            // ITF encodes strings as TLA+ string literals: "\"hello\""
            json!({ "#tla": format!("\"{}\"", escape_tla_string(s)) })
        }

        Value::ModelValue(s) => {
            // Model values are represented as unquoted TLA+ identifiers.
            json!({ "#tla": s.as_ref() })
        }

        Value::Set(sorted_set) => {
            let elements: Vec<JsonValue> = sorted_set.iter().map(value_to_itf).collect();
            json!({ "#set": elements })
        }

        Value::Interval(iv) => {
            // Materialize the interval into a set of bigints.
            let elements: Vec<JsonValue> = iv
                .iter()
                .map(|n| json!({ "#bigint": n.to_string() }))
                .collect();
            json!({ "#set": elements })
        }

        Value::Tuple(elems) => {
            let elements: Vec<JsonValue> = elems.iter().map(value_to_itf).collect();
            json!({ "#tup": elements })
        }

        Value::Seq(seq) => {
            // TLA+ sequences are represented as tuples in ITF.
            let elements: Vec<JsonValue> = seq.iter().map(value_to_itf).collect();
            json!({ "#tup": elements })
        }

        Value::Record(rec) => {
            let mut obj = serde_json::Map::new();
            for (key, val) in rec.iter_str() {
                obj.insert(key.to_string(), value_to_itf(val));
            }
            JsonValue::Object(obj)
        }

        Value::Func(func) => {
            let pairs: Vec<JsonValue> = func
                .mapping_iter()
                .map(|(k, v)| json!([value_to_itf(k), value_to_itf(v)]))
                .collect();
            json!({ "#map": pairs })
        }

        Value::IntFunc(func) => {
            // Use explicit deref to call IntIntervalFunc::min() instead of Ord::min().
            let func_ref: &crate::IntIntervalFunc = func;
            let func_min = func_ref.min();
            let pairs: Vec<JsonValue> = func_ref
                .values()
                .iter()
                .enumerate()
                .map(|(i, v)| {
                    let key = json!({ "#bigint": (func_min + i as i64).to_string() });
                    json!([key, value_to_itf(v)])
                })
                .collect();
            json!({ "#map": pairs })
        }

        // Lazy/symbolic values: fall back to TLA+ string representation.
        // These should not normally appear in counterexample traces since the
        // model checker materializes values, but we handle them defensively.
        Value::Subset(..)
        | Value::FuncSet(..)
        | Value::RecordSet(..)
        | Value::TupleSet(..)
        | Value::SetCup(..)
        | Value::SetCap(..)
        | Value::SetDiff(..)
        | Value::SetPred(..)
        | Value::KSubset(..)
        | Value::BigUnion(..)
        | Value::LazyFunc(..)
        | Value::Closure(..)
        | Value::StringSet
        | Value::AnySet
        | Value::SeqSet(..) => {
            json!({ "#tla": format!("{}", value) })
        }
    }
}

/// Escape special characters in a TLA+ string for ITF encoding.
///
/// TLA+ strings use `\"` for embedded quotes and `\\` for literal backslashes.
fn escape_tla_string(s: &str) -> String {
    let mut result = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '"' => result.push_str("\\\""),
            '\\' => result.push_str("\\\\"),
            _ => result.push(c),
        }
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{RecordBuilder, SeqValue, SetBuilder, SortedSet};
    use num_bigint::BigInt;
    use std::sync::Arc;

    /// Shorthand for creating a `Value::SmallInt` in tests.
    fn int(n: i64) -> Value {
        Value::SmallInt(n)
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_itf_value_bool_true() {
        assert_eq!(value_to_itf(&Value::Bool(true)), json!(true));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_itf_value_bool_false() {
        assert_eq!(value_to_itf(&Value::Bool(false)), json!(false));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_itf_value_small_int() {
        assert_eq!(value_to_itf(&int(42)), json!({"#bigint": "42"}));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_itf_value_negative_int() {
        assert_eq!(value_to_itf(&int(-7)), json!({"#bigint": "-7"}));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_itf_value_zero() {
        assert_eq!(value_to_itf(&int(0)), json!({"#bigint": "0"}));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_itf_value_big_int() {
        let big = Value::Int(Arc::new(BigInt::from(i64::MAX) + BigInt::from(1)));
        let result = value_to_itf(&big);
        assert_eq!(result, json!({"#bigint": "9223372036854775808"}));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_itf_value_string() {
        let s = Value::String(Arc::from("hello"));
        assert_eq!(value_to_itf(&s), json!({"#tla": "\"hello\""}));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_itf_value_string_with_quotes() {
        let s = Value::String(Arc::from("say \"hi\""));
        assert_eq!(value_to_itf(&s), json!({"#tla": "\"say \\\"hi\\\"\""}));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_itf_value_empty_set() {
        let set = Value::empty_set();
        assert_eq!(value_to_itf(&set), json!({"#set": []}));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_itf_value_set_of_ints() {
        let mut builder = SetBuilder::new();
        builder.insert(int(1));
        builder.insert(int(2));
        builder.insert(int(3));
        let set = builder.build_value();
        let result = value_to_itf(&set);
        // Sets are sorted, so order is deterministic.
        assert_eq!(
            result,
            json!({"#set": [{"#bigint": "1"}, {"#bigint": "2"}, {"#bigint": "3"}]})
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_itf_value_tuple() {
        let t = Value::Tuple(Arc::from(vec![int(1), Value::Bool(true), int(3)]));
        assert_eq!(
            value_to_itf(&t),
            json!({"#tup": [{"#bigint": "1"}, true, {"#bigint": "3"}]})
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_itf_value_sequence() {
        let seq = Value::Seq(Arc::new(SeqValue::from_vec(vec![int(10), int(20)])));
        assert_eq!(
            value_to_itf(&seq),
            json!({"#tup": [{"#bigint": "10"}, {"#bigint": "20"}]})
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_itf_value_record() {
        let mut builder = RecordBuilder::new();
        builder.insert_str("a", int(1));
        builder.insert_str("b", Value::Bool(true));
        let rec = Value::Record(builder.build());
        let result = value_to_itf(&rec);
        let obj = result.as_object().expect("record should be JSON object");
        assert_eq!(obj.get("a"), Some(&json!({"#bigint": "1"})));
        assert_eq!(obj.get("b"), Some(&json!(true)));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_itf_value_model_value() {
        let mv = Value::ModelValue(Arc::from("p1"));
        assert_eq!(value_to_itf(&mv), json!({"#tla": "p1"}));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_itf_value_func_map() {
        use crate::FuncValue;
        // f = ("a" :> 1) @@ ("b" :> 2)
        let func = Value::Func(Arc::new(FuncValue::from_sorted_entries(vec![
            (Value::String(Arc::from("a")), int(1)),
            (Value::String(Arc::from("b")), int(2)),
        ])));
        let result = value_to_itf(&func);
        // ITF map encoding: {"#map": [[key1, val1], [key2, val2]]}
        let pairs = result["#map"].as_array().expect("#map should be array");
        assert_eq!(pairs.len(), 2);
        assert_eq!(pairs[0], json!([{"#tla": "\"a\""}, {"#bigint": "1"}]));
        assert_eq!(pairs[1], json!([{"#tla": "\"b\""}, {"#bigint": "2"}]));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_itf_value_interval() {
        use crate::IntervalValue;
        // 1..3 should materialize to {"#set": [1, 2, 3]}
        let iv = Value::Interval(Arc::new(IntervalValue::new(
            num_bigint::BigInt::from(1),
            num_bigint::BigInt::from(3),
        )));
        assert_eq!(
            value_to_itf(&iv),
            json!({"#set": [{"#bigint": "1"}, {"#bigint": "2"}, {"#bigint": "3"}]})
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_itf_value_empty_interval() {
        use crate::IntervalValue;
        // 5..3 is an empty interval
        let iv = Value::Interval(Arc::new(IntervalValue::new(
            num_bigint::BigInt::from(5),
            num_bigint::BigInt::from(3),
        )));
        assert_eq!(value_to_itf(&iv), json!({"#set": []}));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_itf_value_nested_set_of_records() {
        // {[a |-> 1], [a |-> 2]} — set containing records
        let mut builder1 = RecordBuilder::new();
        builder1.insert_str("a", int(1));
        let mut builder2 = RecordBuilder::new();
        builder2.insert_str("a", int(2));
        let mut set_builder = SetBuilder::new();
        set_builder.insert(Value::Record(builder1.build()));
        set_builder.insert(Value::Record(builder2.build()));
        let result = value_to_itf(&set_builder.build_value());
        let elements = result["#set"].as_array().expect("#set should be array");
        assert_eq!(elements.len(), 2);
        // Records inside sets should be plain JSON objects (not #map).
        assert!(elements[0].is_object());
        assert!(elements[1].is_object());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_itf_escape_tla_string_no_special() {
        assert_eq!(escape_tla_string("hello"), "hello");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_itf_escape_tla_string_with_quotes_and_backslashes() {
        assert_eq!(escape_tla_string(r#"a"b\c"#), r#"a\"b\\c"#);
    }
}
