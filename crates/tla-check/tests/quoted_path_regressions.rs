// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use tla_check::{
    json_to_value_with_path, read_trace_events, read_trace_jsonl, JsonValue, JsonValueDecodeError,
    TraceEventSink, TraceHeader, TraceInputFormat, TraceParseError, TraceStep,
};

#[derive(Default)]
struct CollectSink {
    header: Option<TraceHeader>,
    steps: Vec<TraceStep>,
}

impl TraceEventSink for CollectSink {
    fn on_header(&mut self, header: TraceHeader) {
        self.header = Some(header);
    }

    fn on_step(&mut self, step: TraceStep) {
        self.steps.push(step);
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn json_decode_error_quotes_unsafe_state_key_in_path() {
    let input = r#"{"version":"1","module":"Spec","variables":["a b"],"steps":[{"index":0,"state":{"a b":1}}]}"#;
    let mut sink = CollectSink::default();
    let err = read_trace_events(input.as_bytes(), TraceInputFormat::Json, &mut sink).unwrap_err();

    match &err {
        TraceParseError::JsonDecodePath { path, .. } => {
            assert_eq!(path, r#"$.steps[0].state["a b"]"#);
        }
        other => panic!("unexpected error: {other:?}"),
    }
    let msg = err.to_string();
    assert!(msg.contains(r#"$.steps[0].state["a b"]"#), "message: {msg}");
    assert!(sink.header.is_none());
    assert!(sink.steps.is_empty());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn jsonl_decode_error_quotes_unsafe_state_key_in_path() {
    let input = concat!(
        r#"{"type":"header","version":"1","module":"Spec","variables":["a b"]}"#,
        "\n",
        r#"{"type":"step","index":0,"state":{"a b":1}}"#,
        "\n"
    );
    let mut sink = CollectSink::default();
    let err = read_trace_jsonl(input.as_bytes(), &mut sink).unwrap_err();
    match &err {
        TraceParseError::JsonlDecode { line_no, path, .. } => {
            assert_eq!(*line_no, 2);
            assert_eq!(path, r#"$.state["a b"]"#);
        }
        other => panic!("unexpected error: {other:?}"),
    }
    let msg = err.to_string();
    assert!(msg.contains(r#"$.state["a b"]"#), "message: {msg}");
    assert!(msg.contains("line 2"), "message: {msg}");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn json_to_value_with_path_quotes_unsafe_record_key() {
    let json = JsonValue::Record(std::collections::HashMap::from([(
        "a b".to_string(),
        JsonValue::Interval {
            lo: "nope".to_string(),
            hi: "2".to_string(),
        },
    )]));

    let err = json_to_value_with_path(&json).unwrap_err();
    assert_eq!(err.path, r#"$.value["a b"].value.lo"#);
    assert!(matches!(
        err.source,
        JsonValueDecodeError::InvalidBigInt { .. }
    ));
    let msg = err.to_string();
    assert!(msg.contains(r#"$.value["a b"].value.lo"#), "message: {msg}");
}
