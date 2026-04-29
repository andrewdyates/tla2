// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use num_bigint::BigInt;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_big_int_json_round_trip_is_non_lossy() {
    let cases = [
        "9223372036854775808",  // i64::MAX + 1
        "-9223372036854775809", // i64::MIN - 1
        "1234567890123456789012345678901234567890",
    ];

    for dec in cases {
        let original = Value::big_int(dec.parse::<BigInt>().unwrap());
        let json_val = value_to_json(&original);
        assert_eq!(json_val, JsonValue::BigInt(dec.to_string()));

        let encoded = serde_json::to_string(&json_val).unwrap();
        assert!(encoded.contains("\"type\":\"big_int\""), "json={encoded}");

        let decoded_json: JsonValue = serde_json::from_str(&encoded).unwrap();
        let round_tripped = json_to_value(&decoded_json).unwrap();
        assert_eq!(round_tripped, original);
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_json_to_value_undefined_is_an_error() {
    let err = json_to_value(&JsonValue::Undefined).unwrap_err();
    assert!(matches!(err, JsonValueDecodeError::Undefined));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_json_to_value_interval_decodes_big_int_bounds() {
    let json = JsonValue::Interval {
        lo: "9223372036854775808".to_string(),  // i64::MAX + 1
        hi: "-9223372036854775809".to_string(), // i64::MIN - 1
    };

    let val = json_to_value(&json).unwrap();
    match &val {
        Value::Interval(iv) => {
            assert_eq!(iv.low().to_string(), "9223372036854775808");
            assert_eq!(iv.high().to_string(), "-9223372036854775809");
        }
        other => panic!("expected Value::Interval, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_json_to_value_interval_rejects_invalid_big_int() {
    let json = JsonValue::Interval {
        lo: "nope".to_string(),
        hi: "2".to_string(),
    };

    let err = json_to_value(&json).unwrap_err();
    assert!(matches!(err, JsonValueDecodeError::InvalidBigInt { .. }));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_json_to_value_model_value_round_trip() {
    let json = JsonValue::ModelValue("mv_json_codec".to_string());
    let decoded = json_to_value(&json).unwrap();
    assert_eq!(decoded, Value::try_model_value("mv_json_codec").unwrap());

    let decoded_with_path = json_to_value_with_path(&json).unwrap();
    assert_eq!(decoded_with_path, decoded);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_json_to_value_with_path_reports_sequence_interval_index() {
    let json = JsonValue::Seq(vec![JsonValue::Interval {
        lo: "not-a-bigint".to_string(),
        hi: "2".to_string(),
    }]);

    let err = json_to_value_with_path(&json).unwrap_err();
    assert_eq!(err.path, "$.value[0].value.lo");
    assert!(matches!(
        err.source,
        JsonValueDecodeError::InvalidBigInt { ref value } if value == "not-a-bigint"
    ));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_params_from_json_valid_typed_params() {
    let params = serde_json::json!({
        "req_id": {"type": "int", "value": 42},
        "user": {"type": "string", "value": "alice"}
    });

    let result = params_from_json(&params).unwrap();
    assert_eq!(result.len(), 2);
    assert_eq!(result.get("req_id"), Some(&JsonValue::Int(42)));
    assert_eq!(
        result.get("user"),
        Some(&JsonValue::String("alice".to_string()))
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_params_from_json_empty_object() {
    let params = serde_json::json!({});
    let result = params_from_json(&params).unwrap();
    assert!(result.is_empty());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_params_from_json_null_returns_empty() {
    let params = serde_json::Value::Null;
    let result = params_from_json(&params).unwrap();
    assert!(result.is_empty());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_params_from_json_invalid_plain_json() {
    // Plain JSON values that aren't JsonValue-encoded should fail
    let params = serde_json::json!({
        "req_id": 42,  // Not a valid JsonValue encoding
        "user": "alice"
    });

    let err = params_from_json(&params).unwrap_err();
    match err {
        ParamsDecodeError::InvalidJsonValue { key, .. } => {
            // Should fail on first non-JsonValue key (order may vary)
            assert!(key == "req_id" || key == "user");
        }
        other => panic!("expected InvalidJsonValue, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_params_from_json_not_an_object() {
    let params = serde_json::json!([1, 2, 3]);
    let err = params_from_json(&params).unwrap_err();
    assert!(matches!(
        err,
        ParamsDecodeError::NotAnObject {
            actual_type: "array"
        }
    ));

    let params = serde_json::json!(42);
    let err = params_from_json(&params).unwrap_err();
    assert!(matches!(
        err,
        ParamsDecodeError::NotAnObject {
            actual_type: "number"
        }
    ));

    let params = serde_json::json!("string");
    let err = params_from_json(&params).unwrap_err();
    assert!(matches!(
        err,
        ParamsDecodeError::NotAnObject {
            actual_type: "string"
        }
    ));

    let params = serde_json::json!(true);
    let err = params_from_json(&params).unwrap_err();
    assert!(matches!(
        err,
        ParamsDecodeError::NotAnObject {
            actual_type: "boolean"
        }
    ));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_params_from_json_complex_types() {
    let params = serde_json::json!({
        "set_val": {"type": "set", "value": [{"type": "int", "value": 1}, {"type": "int", "value": 2}]},
        "tuple_val": {"type": "tuple", "value": [{"type": "string", "value": "a"}, {"type": "int", "value": 3}]}
    });

    let result = params_from_json(&params).unwrap();
    assert_eq!(result.len(), 2);
    assert!(matches!(result.get("set_val"), Some(JsonValue::Set(_))));
    assert!(matches!(result.get("tuple_val"), Some(JsonValue::Tuple(_))));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_params_from_json_additional_types() {
    // Test bool, record, and model_value types
    let params = serde_json::json!({
        "flag": {"type": "bool", "value": true},
        "rec": {"type": "record", "value": {"x": {"type": "int", "value": 1}}},
        "mv": {"type": "model_value", "value": "mc_val"}
    });

    let result = params_from_json(&params).unwrap();
    assert_eq!(result.len(), 3);
    assert_eq!(result.get("flag"), Some(&JsonValue::Bool(true)));
    assert!(matches!(result.get("rec"), Some(JsonValue::Record(_))));
    assert_eq!(
        result.get("mv"),
        Some(&JsonValue::ModelValue("mc_val".to_string()))
    );
}
