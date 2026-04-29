// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Json module tests — ToJson, ToJsonArray, ToJsonObject, JsonSerialize,
//! JsonDeserialize, ndJsonSerialize, ndJsonDeserialize, IOEnv.
//!
//! Extracted from property_tests.rs lines 3500-3748.
//! Part of #1371.

use std::time::{SystemTime, UNIX_EPOCH};

use tla_check::Value;

use super::helpers::{eval_str, parse_module, tla_path_literal, unique_temp_path};

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_to_json_boolean() {
    let result = eval_str(r#"ToJson(TRUE)"#).unwrap();
    assert_eq!(result.as_string().unwrap(), "true");

    let result = eval_str(r#"ToJson(FALSE)"#).unwrap();
    assert_eq!(result.as_string().unwrap(), "false");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_to_json_integer() {
    let result = eval_str(r#"ToJson(42)"#).unwrap();
    assert_eq!(result.as_string().unwrap(), "42");

    let result = eval_str(r#"ToJson(-123)"#).unwrap();
    assert_eq!(result.as_string().unwrap(), "-123");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_to_json_string() {
    let result = eval_str(r#"ToJson("hello")"#).unwrap();
    assert_eq!(result.as_string().unwrap(), "\"hello\"");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_to_json_sequence() {
    let result = eval_str(r#"ToJson(<<1, 2, 3>>)"#).unwrap();
    assert_eq!(result.as_string().unwrap(), "[1,2,3]");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_to_json_set() {
    let result = eval_str(r#"ToJson({1, 2, 3})"#).unwrap();
    // Sets are converted to arrays
    let json = result.as_string().unwrap();
    assert!(json.starts_with('['));
    assert!(json.ends_with(']'));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_to_json_record() {
    let result = eval_str(r#"ToJson([a |-> 1, b |-> 2])"#).unwrap();
    let json = result.as_string().unwrap();
    assert!(json.starts_with('{'));
    assert!(json.ends_with('}'));
    assert!(json.contains("\"a\":1") || json.contains("\"a\": 1"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_to_json_nested() {
    let result = eval_str(r#"ToJson(<<[a |-> 1], [a |-> 2]>>)"#).unwrap();
    let json = result.as_string().unwrap();
    // Should be a JSON array of objects
    assert!(json.starts_with('['));
    assert!(json.contains("\"a\""));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_to_json_array_sequence() {
    let result = eval_str(r#"ToJsonArray(<<1, 2, 3>>)"#).unwrap();
    assert_eq!(result.as_string().unwrap(), "[1,2,3]");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_to_json_array_set() {
    let result = eval_str(r#"ToJsonArray({1, 2, 3})"#).unwrap();
    let json = result.as_string().unwrap();
    assert!(json.starts_with('['));
    assert!(json.ends_with(']'));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_to_json_object_record() {
    let result = eval_str(r#"ToJsonObject([x |-> 10, y |-> 20])"#).unwrap();
    let json = result.as_string().unwrap();
    assert!(json.starts_with('{'));
    assert!(json.ends_with('}'));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_to_json_object_tuple_uses_sequence_indices() {
    let result = eval_str(r#"ToJsonObject(<<[x |-> 1], [x |-> 2]>>)"#).unwrap();
    let json = result.as_string().unwrap();
    assert_eq!(json, r#"{"1":{"x":1},"2":{"x":2}}"#);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_json_serialize_returns_true() {
    // JsonSerialize should return TRUE (stub implementation)
    let result = eval_str(r#"JsonSerialize("test.json", <<1, 2, 3>>)"#).unwrap();
    assert_eq!(result, Value::Bool(true));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_json_deserialize_reads_file() {
    let path = unique_temp_path("json");
    std::fs::write(&path, r#"{"x":10,"y":{"z":"ok"},"arr":[1,2]}"#).unwrap();

    let expr = format!(r#"JsonDeserialize("{}")"#, tla_path_literal(&path));
    let result = eval_str(&expr).unwrap();
    std::fs::remove_file(&path).unwrap();

    let rec = result.as_record().expect("Expected record");
    assert_eq!(rec.get("x"), Some(&Value::int(10)));

    let nested = rec
        .get("y")
        .and_then(Value::as_record)
        .expect("Expected nested record for y");
    assert_eq!(
        nested.get("z"),
        Some(&Value::String("ok".to_string().into()))
    );

    let arr = rec
        .get("arr")
        .and_then(Value::as_seq)
        .expect("Expected tuple/sequence for arr");
    assert_eq!(arr.len(), 2);
    assert_eq!(arr[0], Value::int(1));
    assert_eq!(arr[1], Value::int(2));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ndjson_serialize_returns_true() {
    // ndJsonSerialize should return TRUE (stub implementation)
    let result = eval_str(r#"ndJsonSerialize("test.ndjson", <<1, 2, 3>>)"#).unwrap();
    assert_eq!(result, Value::Bool(true));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ndjson_deserialize_reads_lines() {
    let path = unique_temp_path("ndjson");
    let contents = r#"{"N":3}
{"event":">","pkt":{"msg":{"type":"tok"}}}
"#;
    std::fs::write(&path, contents).unwrap();

    let expr = format!(r#"ndJsonDeserialize("{}")"#, tla_path_literal(&path));
    let result = eval_str(&expr).unwrap();
    std::fs::remove_file(&path).unwrap();

    let seq = result.as_seq().expect("Expected sequence");
    assert_eq!(seq.len(), 2);

    let first = seq[0].as_record().expect("Expected first line as record");
    assert_eq!(first.get("N"), Some(&Value::int(3)));

    let second = seq[1].as_record().expect("Expected second line as record");
    let pkt = second
        .get("pkt")
        .and_then(Value::as_record)
        .expect("Expected pkt record");
    let msg = pkt
        .get("msg")
        .and_then(Value::as_record)
        .expect("Expected msg record");
    assert_eq!(
        msg.get("type"),
        Some(&Value::String("tok".to_string().into()))
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ndjson_deserialize_prefers_builtin_over_placeholder_stub() {
    let path = unique_temp_path("ndjson");
    std::fs::write(&path, "{\"N\":3}\n").unwrap();

    let json_stub = parse_module(
        r#"
---- MODULE Json ----
ndJsonDeserialize(absoluteFilename) == CHOOSE val : TRUE
====
"#,
    );

    let main_src = format!(
        r#"
---- MODULE Main ----
EXTENDS Json
Op == ndJsonDeserialize("{}")[1].N
====
"#,
        tla_path_literal(&path)
    );
    let main = parse_module(&main_src);

    let mut ctx = tla_check::EvalCtx::new();
    ctx.load_module(&json_stub);
    ctx.load_module(&main);

    let result = ctx.eval_op("Op").expect("Op should evaluate");
    assert_eq!(result, Value::int(3));

    std::fs::remove_file(&path).unwrap();
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ioenv_prefers_builtin_over_placeholder_stub() {
    let key = format!(
        "TLA2_IOENV_TEST_KEY_{}",
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("system time before UNIX_EPOCH")
            .as_nanos()
    );
    let expected = "ok";
    let _guard = super::helpers::EnvVarGuard::set(&key, Some(expected));

    let ioutils_stub = parse_module(
        r#"
---- MODULE IOUtils ----
IOEnv == CHOOSE env : TRUE
====
"#,
    );

    let main_src = format!(
        r#"
---- MODULE Main ----
EXTENDS IOUtils
Op == IOEnv.{key}
====
"#
    );
    let main = parse_module(&main_src);

    let mut ctx = tla_check::EvalCtx::new();
    ctx.load_module(&ioutils_stub);
    ctx.load_module(&main);

    let result = ctx.eval_op("Op").expect("Op should evaluate");
    assert_eq!(result, Value::String(expected.to_string().into()));
}
