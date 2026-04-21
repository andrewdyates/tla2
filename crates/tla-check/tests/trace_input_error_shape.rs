// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use tla_check::{
    read_trace_events, TraceEventSink, TraceHeader, TraceInputFormat, TraceParseError, TraceStep,
};

#[derive(Default)]
struct Sink {
    header: Option<TraceHeader>,
    steps: usize,
}

impl TraceEventSink for Sink {
    fn on_header(&mut self, header: TraceHeader) {
        self.header = Some(header);
    }

    fn on_step(&mut self, _step: TraceStep) {
        self.steps += 1;
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn json_decode_path_error_carries_line_column() {
    // Malformed `JsonValue` under `steps[0].state.x` (should be an object with `{type, value}`).
    let input = br#"{"version":"1","module":"Spec","variables":["x"],"steps":[{"index":0,"state":{"x":1}}]}"#;

    let mut sink = Sink::default();
    let err = read_trace_events(input.as_slice(), TraceInputFormat::Json, &mut sink).unwrap_err();
    match err {
        TraceParseError::JsonDecodePath {
            path,
            line,
            column,
            source: _,
        } => {
            assert!(path.starts_with("$.steps[0].state.x"), "path={path:?}");
            assert_eq!(line, 1, "line={line}");
            assert!(column >= 1, "column={column}");
        }
        other => panic!("unexpected error: {other:?}"),
    }

    assert!(sink.header.is_none());
    assert_eq!(sink.steps, 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn json_decode_path_error_quotes_non_identifier_state_keys() {
    // Malformed `JsonValue` under `steps[0].state["x-y"]` (should be an object with `{type, value}`).
    let input =
        br#"{"version":"1","module":"Spec","variables":["x-y"],"steps":[{"index":0,"state":{"x-y":1}}]}"#;

    let mut sink = Sink::default();
    let err = read_trace_events(input.as_slice(), TraceInputFormat::Json, &mut sink).unwrap_err();
    match err {
        TraceParseError::JsonDecodePath { path, .. } => {
            assert!(
                path.starts_with("$.steps[0].state[\"x-y\"]"),
                "path={path:?}"
            );
        }
        other => panic!("unexpected error: {other:?}"),
    }

    assert!(sink.header.is_none());
    assert_eq!(sink.steps, 0);
}
