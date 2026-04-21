// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use num_bigint::BigInt;
use std::collections::HashMap;
use std::sync::Arc;

use tla_check::{
    json_to_value, json_to_value_with_path, value_to_json, IntervalValue, JsonValue,
    JsonValueDecodeError, Value,
};

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn json_codec_big_int_round_trip_does_not_truncate() {
    let n = BigInt::from(i64::MAX) + BigInt::from(1);
    let v = Value::big_int(n.clone());

    let json = value_to_json(&v);
    assert!(matches!(json, JsonValue::BigInt(ref s) if s == &n.to_string()));

    let back = json_to_value(&json).unwrap();
    assert_eq!(back, v);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn json_codec_interval_round_trip_is_structured() {
    let lo = BigInt::from(1);
    let hi = BigInt::from(1_000_000_000i64);
    let v = Value::Interval(Arc::new(IntervalValue::new(lo.clone(), hi.clone())));

    let json = value_to_json(&v);
    match json {
        JsonValue::Interval {
            lo: ref lo_s,
            hi: ref hi_s,
        } => {
            assert_eq!(lo_s, &lo.to_string());
            assert_eq!(hi_s, &hi.to_string());
        }
        other => panic!("expected interval encoding, got {other:?}"),
    }

    let back = json_to_value(&json).unwrap();
    assert_eq!(back, v);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn json_codec_decode_undefined_is_error() {
    let err = json_to_value(&JsonValue::Undefined).unwrap_err();
    assert!(
        matches!(err, JsonValueDecodeError::Undefined),
        "got {err:?}"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn json_codec_decode_invalid_big_int_is_error() {
    let err = json_to_value(&JsonValue::BigInt("not-a-number".to_string())).unwrap_err();
    match err {
        JsonValueDecodeError::InvalidBigInt { value } => assert_eq!(value, "not-a-number"),
        other => panic!("unexpected error: {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn json_codec_function_decode_rejects_domain_key_missing_mapping() {
    let json = JsonValue::Function {
        domain: vec![JsonValue::Int(1), JsonValue::Int(2)],
        mapping: vec![(JsonValue::Int(1), JsonValue::Bool(true))],
    };

    let err = json_to_value(&json).unwrap_err();
    match err {
        JsonValueDecodeError::FunctionDomainMissingKey { key } => assert_eq!(key, "2"),
        other => panic!("unexpected error: {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn json_codec_function_decode_rejects_mapping_key_not_in_domain() {
    let json = JsonValue::Function {
        domain: vec![],
        mapping: vec![(JsonValue::Int(2), JsonValue::Bool(true))],
    };

    let err = json_to_value(&json).unwrap_err();
    match err {
        JsonValueDecodeError::FunctionMappingKeyNotInDomain { key } => assert_eq!(key, "2"),
        other => panic!("unexpected error: {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn json_codec_function_decode_rejects_domain_string_key_missing_mapping() {
    let json = JsonValue::Function {
        domain: vec![JsonValue::String("a".to_string())],
        mapping: vec![],
    };

    let err = json_to_value(&json).unwrap_err();
    match err {
        JsonValueDecodeError::FunctionDomainMissingKey { key } => assert_eq!(key, "a"),
        other => panic!("unexpected error: {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn json_codec_function_decode_rejects_mapping_string_key_not_in_domain() {
    let json = JsonValue::Function {
        domain: vec![],
        mapping: vec![(JsonValue::String("b".to_string()), JsonValue::Bool(true))],
    };

    let err = json_to_value(&json).unwrap_err();
    match err {
        JsonValueDecodeError::FunctionMappingKeyNotInDomain { key } => assert_eq!(key, "b"),
        other => panic!("unexpected error: {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn json_codec_function_decode_rejects_domain_big_int_key_missing_mapping() {
    let json = JsonValue::Function {
        domain: vec![JsonValue::BigInt("2".to_string())],
        mapping: vec![],
    };

    let err = json_to_value(&json).unwrap_err();
    match err {
        JsonValueDecodeError::FunctionDomainMissingKey { key } => assert_eq!(key, "2"),
        other => panic!("unexpected error: {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn json_codec_function_decode_rejects_mapping_big_int_key_not_in_domain() {
    let json = JsonValue::Function {
        domain: vec![],
        mapping: vec![(JsonValue::BigInt("2".to_string()), JsonValue::Bool(true))],
    };

    let err = json_to_value(&json).unwrap_err();
    match err {
        JsonValueDecodeError::FunctionMappingKeyNotInDomain { key } => assert_eq!(key, "2"),
        other => panic!("unexpected error: {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn json_codec_function_decode_missing_key_takes_less_branch() {
    let json = JsonValue::Function {
        domain: vec![JsonValue::Int(1), JsonValue::Int(3)],
        mapping: vec![(JsonValue::Int(3), JsonValue::Bool(true))],
    };

    let err = json_to_value(&json).unwrap_err();
    match err {
        JsonValueDecodeError::FunctionDomainMissingKey { key } => assert_eq!(key, "1"),
        other => panic!("unexpected error: {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn json_codec_function_decode_extra_key_takes_greater_branch() {
    let json = JsonValue::Function {
        domain: vec![JsonValue::Int(3)],
        mapping: vec![(JsonValue::Int(1), JsonValue::Bool(true))],
    };

    let err = json_to_value(&json).unwrap_err();
    match err {
        JsonValueDecodeError::FunctionMappingKeyNotInDomain { key } => assert_eq!(key, "1"),
        other => panic!("unexpected error: {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn json_codec_function_decode_rejects_duplicate_domain_key() {
    let json = JsonValue::Function {
        domain: vec![JsonValue::Int(1), JsonValue::Int(1)],
        mapping: vec![(JsonValue::Int(1), JsonValue::Bool(true))],
    };

    let err = json_to_value(&json).unwrap_err();
    match err {
        JsonValueDecodeError::DuplicateFunctionDomainKey { key } => assert_eq!(key, "1"),
        other => panic!("unexpected error: {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn json_codec_function_decode_rejects_duplicate_mapping_key() {
    let json = JsonValue::Function {
        domain: vec![JsonValue::Int(1)],
        mapping: vec![
            (JsonValue::Int(1), JsonValue::Bool(true)),
            (JsonValue::Int(1), JsonValue::Bool(false)),
        ],
    };

    let err = json_to_value(&json).unwrap_err();
    match err {
        JsonValueDecodeError::DuplicateFunctionKey { key } => assert_eq!(key, "1"),
        other => panic!("unexpected error: {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn json_codec_function_decode_canonicalizes_domain_and_mapping_order() {
    let json = JsonValue::Function {
        domain: vec![JsonValue::Int(2), JsonValue::Int(1)],
        mapping: vec![
            (JsonValue::Int(2), JsonValue::Bool(false)),
            (JsonValue::Int(1), JsonValue::Bool(true)),
        ],
    };

    let v = json_to_value(&json).unwrap();
    let back = value_to_json(&v);
    assert_eq!(
        back,
        JsonValue::Function {
            domain: vec![JsonValue::Int(1), JsonValue::Int(2)],
            mapping: vec![
                (JsonValue::Int(1), JsonValue::Bool(true)),
                (JsonValue::Int(2), JsonValue::Bool(false)),
            ],
        }
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn json_codec_decode_invalid_big_int_includes_path() {
    let err = json_to_value_with_path(&JsonValue::BigInt("not-a-number".to_string())).unwrap_err();
    assert_eq!(err.path, "$.value");
    match err.source {
        JsonValueDecodeError::InvalidBigInt { value } => assert_eq!(value, "not-a-number"),
        other => panic!("unexpected error: {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn json_codec_decode_undefined_includes_type_path() {
    let err = json_to_value_with_path(&JsonValue::Undefined).unwrap_err();
    assert_eq!(err.path, "$.type");
    assert!(
        matches!(&err.source, JsonValueDecodeError::Undefined),
        "got {err:?}"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn json_codec_interval_decode_invalid_lo_includes_path() {
    let json = JsonValue::Interval {
        lo: "bad".to_string(),
        hi: "1".to_string(),
    };
    let err = json_to_value_with_path(&json).unwrap_err();
    assert_eq!(err.path, "$.value.lo");
    match err.source {
        JsonValueDecodeError::InvalidBigInt { value } => assert_eq!(value, "bad"),
        other => panic!("unexpected error: {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn json_codec_record_field_decode_includes_path() {
    let mut fields = HashMap::new();
    fields.insert("x".to_string(), JsonValue::BigInt("bad".to_string()));
    let json = JsonValue::Record(fields);

    let err = json_to_value_with_path(&json).unwrap_err();
    assert_eq!(err.path, "$.value.x.value");
    assert!(matches!(
        err.source,
        JsonValueDecodeError::InvalidBigInt { .. }
    ));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn json_codec_record_unsafe_key_decode_includes_quoted_path() {
    let mut fields = HashMap::new();
    fields.insert("a.b".to_string(), JsonValue::BigInt("bad".to_string()));
    let json = JsonValue::Record(fields);

    let err = json_to_value_with_path(&json).unwrap_err();
    assert_eq!(err.path, "$.value[\"a.b\"].value");
    assert!(matches!(
        err.source,
        JsonValueDecodeError::InvalidBigInt { .. }
    ));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn json_codec_record_decode_is_key_sorted_for_determinism() {
    let mut fields = HashMap::new();
    fields.insert("z".to_string(), JsonValue::BigInt("bad_z".to_string()));
    fields.insert("a".to_string(), JsonValue::BigInt("bad_a".to_string()));
    let json = JsonValue::Record(fields);

    let err = json_to_value_with_path(&json).unwrap_err();
    assert_eq!(err.path, "$.value.a.value");
    match err.source {
        JsonValueDecodeError::InvalidBigInt { value } => assert_eq!(value, "bad_a"),
        other => panic!("unexpected error: {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn json_codec_record_decode_is_key_sorted_for_determinism_without_path() {
    let mut fields = HashMap::new();
    fields.insert("z".to_string(), JsonValue::BigInt("bad_z".to_string()));
    fields.insert("a".to_string(), JsonValue::BigInt("bad_a".to_string()));
    let json = JsonValue::Record(fields);

    let err = json_to_value(&json).unwrap_err();
    match err {
        JsonValueDecodeError::InvalidBigInt { value } => assert_eq!(value, "bad_a"),
        other => panic!("unexpected error: {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn json_codec_function_decode_missing_key_includes_key_path() {
    let json = JsonValue::Function {
        domain: vec![JsonValue::Int(1), JsonValue::Int(2)],
        mapping: vec![(JsonValue::Int(1), JsonValue::Bool(true))],
    };

    let err = json_to_value_with_path(&json).unwrap_err();
    assert_eq!(err.path, "$.value.domain[1]");
    match err.source {
        JsonValueDecodeError::FunctionDomainMissingKey { key } => assert_eq!(key, "2"),
        other => panic!("unexpected error: {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn json_codec_function_decode_extra_key_includes_key_path() {
    let json = JsonValue::Function {
        domain: vec![],
        mapping: vec![(JsonValue::Int(2), JsonValue::Bool(true))],
    };

    let err = json_to_value_with_path(&json).unwrap_err();
    assert_eq!(err.path, "$.value.mapping[0][0]");
    match err.source {
        JsonValueDecodeError::FunctionMappingKeyNotInDomain { key } => assert_eq!(key, "2"),
        other => panic!("unexpected error: {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn json_codec_function_duplicate_domain_key_includes_duplicate_path() {
    let json = JsonValue::Function {
        domain: vec![JsonValue::Int(1), JsonValue::Int(1)],
        mapping: vec![(JsonValue::Int(1), JsonValue::Bool(true))],
    };

    let err = json_to_value_with_path(&json).unwrap_err();
    assert_eq!(err.path, "$.value.domain[1]");
    match err.source {
        JsonValueDecodeError::DuplicateFunctionDomainKey { key } => assert_eq!(key, "1"),
        other => panic!("unexpected error: {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn json_codec_function_duplicate_mapping_key_includes_duplicate_path() {
    let json = JsonValue::Function {
        domain: vec![JsonValue::Int(1)],
        mapping: vec![
            (JsonValue::Int(1), JsonValue::Bool(true)),
            (JsonValue::Int(1), JsonValue::Bool(false)),
        ],
    };

    let err = json_to_value_with_path(&json).unwrap_err();
    assert_eq!(err.path, "$.value.mapping[1][0]");
    match err.source {
        JsonValueDecodeError::DuplicateFunctionKey { key } => assert_eq!(key, "1"),
        other => panic!("unexpected error: {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn json_codec_record_non_identifier_key_quotes_path() {
    let json = JsonValue::Record(HashMap::from([("x-y".to_string(), JsonValue::Undefined)]));

    let err = json_to_value_with_path(&json).unwrap_err();
    assert_eq!(err.path, "$.value[\"x-y\"].type");
    assert!(matches!(err.source, JsonValueDecodeError::Undefined));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn json_codec_function_decode_missing_key_picks_smallest_key_deterministically() {
    let json = JsonValue::Function {
        domain: vec![JsonValue::Int(2), JsonValue::Int(1)],
        mapping: vec![],
    };

    let err = json_to_value(&json).unwrap_err();
    match err {
        JsonValueDecodeError::FunctionDomainMissingKey { key } => assert_eq!(key, "1"),
        other => panic!("unexpected error: {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn json_codec_function_decode_extra_key_picks_smallest_key_deterministically() {
    let json = JsonValue::Function {
        domain: vec![],
        mapping: vec![
            (JsonValue::Int(2), JsonValue::Bool(true)),
            (JsonValue::Int(1), JsonValue::Bool(false)),
        ],
    };

    let err = json_to_value(&json).unwrap_err();
    match err {
        JsonValueDecodeError::FunctionMappingKeyNotInDomain { key } => assert_eq!(key, "1"),
        other => panic!("unexpected error: {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn json_codec_function_decode_missing_key_path_points_to_original_index() {
    let json = JsonValue::Function {
        domain: vec![JsonValue::Int(2), JsonValue::Int(1)],
        mapping: vec![],
    };

    let err = json_to_value_with_path(&json).unwrap_err();
    assert_eq!(err.path, "$.value.domain[1]");
    match err.source {
        JsonValueDecodeError::FunctionDomainMissingKey { key } => assert_eq!(key, "1"),
        other => panic!("unexpected error: {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn json_codec_function_decode_extra_key_path_points_to_original_index() {
    let json = JsonValue::Function {
        domain: vec![],
        mapping: vec![
            (JsonValue::Int(2), JsonValue::Bool(true)),
            (JsonValue::Int(1), JsonValue::Bool(false)),
        ],
    };

    let err = json_to_value_with_path(&json).unwrap_err();
    assert_eq!(err.path, "$.value.mapping[1][0]");
    match err.source {
        JsonValueDecodeError::FunctionMappingKeyNotInDomain { key } => assert_eq!(key, "1"),
        other => panic!("unexpected error: {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn json_codec_function_duplicate_domain_key_uses_original_index_of_second_occurrence() {
    let json = JsonValue::Function {
        domain: vec![JsonValue::Int(1), JsonValue::Int(2), JsonValue::Int(1)],
        mapping: vec![
            (JsonValue::Int(1), JsonValue::Bool(true)),
            (JsonValue::Int(2), JsonValue::Bool(false)),
        ],
    };

    let err = json_to_value_with_path(&json).unwrap_err();
    assert_eq!(err.path, "$.value.domain[2]");
    match err.source {
        JsonValueDecodeError::DuplicateFunctionDomainKey { key } => assert_eq!(key, "1"),
        other => panic!("unexpected error: {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn json_codec_function_duplicate_mapping_key_uses_original_index_of_second_occurrence() {
    let json = JsonValue::Function {
        domain: vec![JsonValue::Int(1), JsonValue::Int(2)],
        mapping: vec![
            (JsonValue::Int(1), JsonValue::Bool(true)),
            (JsonValue::Int(2), JsonValue::Bool(true)),
            (JsonValue::Int(1), JsonValue::Bool(false)),
        ],
    };

    let err = json_to_value_with_path(&json).unwrap_err();
    assert_eq!(err.path, "$.value.mapping[2][0]");
    match err.source {
        JsonValueDecodeError::DuplicateFunctionKey { key } => assert_eq!(key, "1"),
        other => panic!("unexpected error: {other:?}"),
    }
}
