// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::path::Path;

use crate::json_output::JsonValue;

use super::parse::{read_trace_events, read_trace_json, read_trace_jsonl};
use super::{
    resolve_trace_input_format, TraceEventSink, TraceHeader, TraceInputFormat,
    TraceInputFormatSelection, TraceParseError, TraceSourceHint, TraceStep,
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
fn resolve_trace_input_format_auto_prefers_jsonl_by_extension() {
    let p = Path::new("trace.jsonl");
    let format =
        resolve_trace_input_format(TraceInputFormatSelection::Auto, TraceSourceHint::Path(p));
    assert_eq!(format, TraceInputFormat::Jsonl);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn resolve_trace_input_format_auto_defaults_to_json_on_stdin() {
    let format =
        resolve_trace_input_format(TraceInputFormatSelection::Auto, TraceSourceHint::Stdin);
    assert_eq!(format, TraceInputFormat::Json);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn json_decode_error_includes_path() {
    // Malformed `JsonValue` under `steps[0].state.x` (should be an object with `{type, value}`).
    let input = r#"{"version":"1","module":"Spec","variables":["x"],"steps":[{"index":0,"state":{"x":1}}]}"#;
    let mut sink = CollectSink::default();
    let err = read_trace_events(input.as_bytes(), TraceInputFormat::Json, &mut sink).unwrap_err();

    match &err {
        TraceParseError::JsonDecodePath { path, .. } => {
            assert!(
                path.starts_with("$.steps[0].state.x"),
                "unexpected path: {path:?}"
            );
        }
        other => panic!("unexpected error: {other:?}"),
    }
    let msg = err.to_string();
    assert!(msg.contains("$.steps[0].state.x"), "message: {msg}");
    assert!(sink.header.is_none());
    assert!(sink.steps.is_empty());
}

#[derive(Default)]
struct CountSink {
    header: Option<TraceHeader>,
    steps: usize,
    last_index: Option<usize>,
}

impl TraceEventSink for CountSink {
    fn on_header(&mut self, header: TraceHeader) {
        self.header = Some(header);
    }

    fn on_step(&mut self, step: TraceStep) {
        self.steps += 1;
        self.last_index = step.index;
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn jsonl_parses_header_and_steps() {
    let input = r#"

{"type":"header","version":"1","module":"Spec","variables":["x","y"]}
{"type":"step","index":0,"state":{"x":{"type":"int","value":1}}}
{"type":"step","index":1,"state":{"x":{"type":"int","value":2},"y":{"type":"int","value":10}}}
"#;

    let mut sink = CollectSink::default();
    read_trace_jsonl(input.as_bytes(), &mut sink).unwrap();
    assert_eq!(
        sink.header,
        Some(TraceHeader {
            version: "1".to_string(),
            module: "Spec".to_string(),
            variables: vec!["x".to_string(), "y".to_string()],
        })
    );
    assert_eq!(sink.steps.len(), 2);
    assert_eq!(sink.steps[0].index, Some(0));
    assert!(matches!(
        sink.steps[0].state.get("x"),
        Some(&JsonValue::Int(1))
    ));
    assert_eq!(sink.steps[1].index, Some(1));
    assert!(matches!(
        sink.steps[1].state.get("y"),
        Some(&JsonValue::Int(10))
    ));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn jsonl_rejects_step_before_header() {
    let input = r#"{"type":"step","index":0,"state":{"x":{"type":"int","value":1}}}"#;
    let mut sink = CollectSink::default();
    let err = read_trace_jsonl(input.as_bytes(), &mut sink).unwrap_err();
    assert!(matches!(err, TraceParseError::JsonlMissingHeader { .. }));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn jsonl_rejects_empty_input() {
    let input = "\n \n\t\n";
    let mut sink = CollectSink::default();
    let err = read_trace_jsonl(input.as_bytes(), &mut sink).unwrap_err();
    assert!(matches!(err, TraceParseError::JsonlMissingHeaderAtEof));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn jsonl_rejects_empty_string() {
    let input = "";
    let mut sink = CollectSink::default();
    let err = read_trace_jsonl(input.as_bytes(), &mut sink).unwrap_err();
    assert!(matches!(err, TraceParseError::JsonlMissingHeaderAtEof));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn jsonl_rejects_header_only() {
    let input = r#"{"type":"header","version":"1","module":"Spec","variables":["x"]}"#;
    let mut sink = CollectSink::default();
    let err = read_trace_jsonl(input.as_bytes(), &mut sink).unwrap_err();
    assert!(matches!(err, TraceParseError::MissingAnySteps { .. }));
    assert!(sink.header.is_none());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn jsonl_rejects_duplicate_variables_in_header() {
    let input = r#"
{"type":"header","version":"1","module":"Spec","variables":["x","x"]}
{"type":"step","index":0,"state":{"x":{"type":"int","value":1}}}
"#;
    let mut sink = CollectSink::default();
    let err = read_trace_jsonl(input.as_bytes(), &mut sink).unwrap_err();
    assert!(matches!(err, TraceParseError::DuplicateVariable { .. }));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn jsonl_accepts_utf8_bom_on_first_line() {
    let input = "\u{feff}{\"type\":\"header\",\"version\":\"1\",\"module\":\"Spec\",\"variables\":[\"x\"]}\n{\"type\":\"step\",\"index\":0,\"state\":{\"x\":{\"type\":\"int\",\"value\":1}}}\n";
    let mut sink = CollectSink::default();
    read_trace_jsonl(input.as_bytes(), &mut sink).unwrap();
    assert!(sink.header.is_some());
    assert_eq!(sink.steps.len(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn jsonl_decode_error_prefix_does_not_panic_on_unicode_boundaries() {
    let input = format!("{}\n", "€".repeat(67));
    let mut sink = CollectSink::default();
    let err = read_trace_jsonl(input.as_bytes(), &mut sink).unwrap_err();
    assert!(matches!(err, TraceParseError::JsonlDecode { .. }));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn jsonl_decode_error_includes_json_path() {
    let input = concat!(
        r#"{"type":"header","version":"1","module":"Spec","variables":["x"]}"#,
        "\n",
        r#"{"type":"step","index":0,"state":{"x":1}}"#,
        "\n"
    );
    let mut sink = CollectSink::default();
    let err = read_trace_jsonl(input.as_bytes(), &mut sink).unwrap_err();
    match &err {
        TraceParseError::JsonlDecode { line_no, path, .. } => {
            assert_eq!(*line_no, 2);
            assert!(
                path.starts_with("$.state.x"),
                "expected path to start with $.state.x, got {path:?}"
            );
        }
        other => panic!("unexpected error: {other:?}"),
    }
    let msg = err.to_string();
    assert!(msg.contains("$.state.x"), "message: {msg}");
    assert!(msg.contains("line 2"), "message: {msg}");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn jsonl_decode_error_prefix_uses_trimmed_line() {
    let input = "   not-json\n";
    let mut sink = CollectSink::default();
    let err = read_trace_jsonl(input.as_bytes(), &mut sink).unwrap_err();
    match err {
        TraceParseError::JsonlDecode {
            raw_line_prefix, ..
        } => {
            assert_eq!(raw_line_prefix, "not-json");
        }
        _ => panic!("unexpected error: {err:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn jsonl_decode_error_prefix_strips_utf8_bom() {
    let input = "\u{feff}not-json\n";
    let mut sink = CollectSink::default();
    let err = read_trace_jsonl(input.as_bytes(), &mut sink).unwrap_err();
    match err {
        TraceParseError::JsonlDecode {
            raw_line_prefix, ..
        } => {
            assert_eq!(raw_line_prefix, "not-json");
        }
        _ => panic!("unexpected error: {err:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn jsonl_parses_multi_thousand_step_trace() {
    use std::fmt::Write;

    const N: usize = 5000;

    // Rough capacity estimate: ~70 bytes/step + header.
    let mut input = String::with_capacity(128 + N * 80);
    input.push_str(r#"{"type":"header","version":"1","module":"Spec","variables":["x"]}"#);
    input.push('\n');
    for i in 0..N {
        write!(
            &mut input,
            r#"{{"type":"step","state":{{"x":{{"type":"int","value":{i}}}}}}}"#
        )
        .unwrap();
        input.push('\n');
    }

    let mut sink = CountSink::default();
    read_trace_jsonl(input.as_bytes(), &mut sink).unwrap();
    assert!(sink.header.is_some());
    assert_eq!(sink.steps, N);
    assert_eq!(sink.last_index, Some(N - 1));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn jsonl_rejects_second_header() {
    let input = r#"
{"type":"header","version":"1","module":"Spec","variables":["x"]}
{"type":"step","index":0,"state":{"x":{"type":"int","value":1}}}
{"type":"header","version":"1","module":"Spec","variables":["x"]}
"#;
    let mut sink = CollectSink::default();
    let err = read_trace_jsonl(input.as_bytes(), &mut sink).unwrap_err();
    assert!(matches!(err, TraceParseError::JsonlUnexpectedHeader { .. }));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn jsonl_rejects_unknown_variable() {
    let input = r#"
{"type":"header","version":"1","module":"Spec","variables":["x"]}
{"type":"step","index":0,"state":{"y":{"type":"int","value":1}}}
"#;
    let mut sink = CollectSink::default();
    let err = read_trace_jsonl(input.as_bytes(), &mut sink).unwrap_err();
    assert!(matches!(err, TraceParseError::UnknownVariable { .. }));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn jsonl_rejects_non_contiguous_index() {
    let input = r#"
{"type":"header","version":"1","module":"Spec","variables":["x"]}
{"type":"step","index":0,"state":{"x":{"type":"int","value":1}}}
{"type":"step","index":2,"state":{"x":{"type":"int","value":2}}}
"#;
    let mut sink = CollectSink::default();
    let err = read_trace_jsonl(input.as_bytes(), &mut sink).unwrap_err();
    assert!(matches!(err, TraceParseError::StepIndexMismatch { .. }));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn json_reuses_step_validation() {
    let input = r#"
{
  "version":"1",
  "module":"Spec",
  "variables":["x"],
  "steps":[
    {"index":0,"state":{"x":{"type":"int","value":1}}},
    {"index":1,"state":{"x":{"type":"int","value":2}}}
  ]
}
"#;

    let mut sink = CollectSink::default();
    read_trace_json(input.as_bytes(), &mut sink).unwrap();
    assert_eq!(sink.steps.len(), 2);
    assert!(matches!(
        sink.steps[1].state.get("x"),
        Some(&JsonValue::Int(2))
    ));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn json_rejects_empty_steps() {
    let input = r#"
{
  "version":"1",
  "module":"Spec",
  "variables":["x"],
  "steps":[]
}
"#;

    let mut sink = CollectSink::default();
    let err = read_trace_json(input.as_bytes(), &mut sink).unwrap_err();
    assert!(matches!(err, TraceParseError::MissingAnySteps { .. }));
    assert!(sink.header.is_none());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn json_rejects_duplicate_variables_in_header() {
    let input = r#"
{
  "version":"1",
  "module":"Spec",
  "variables":["x","x"],
  "steps":[
    {"index":0,"state":{"x":{"type":"int","value":1}}}
  ]
}
"#;

    let mut sink = CollectSink::default();
    let err = read_trace_json(input.as_bytes(), &mut sink).unwrap_err();
    assert!(matches!(err, TraceParseError::DuplicateVariable { .. }));
    assert!(sink.header.is_none());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn json_accepts_utf8_bom_on_first_byte() {
    let input = b"\xef\xbb\xbf{\"version\":\"1\",\"module\":\"Spec\",\"variables\":[\"x\"],\"steps\":[{\"index\":0,\"state\":{\"x\":{\"type\":\"int\",\"value\":1}}}]}";
    let mut sink = CollectSink::default();
    read_trace_json(&input[..], &mut sink).unwrap();
    assert!(sink.header.is_some());
    assert_eq!(sink.steps.len(), 1);
}
