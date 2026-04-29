// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::path::Path;

use tla_check::{
    resolve_trace_input_format, TraceInputFormat, TraceInputFormatSelection, TraceSourceHint,
};

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn auto_prefers_jsonl_by_extension() {
    let format = resolve_trace_input_format(
        TraceInputFormatSelection::Auto,
        TraceSourceHint::Path(Path::new("trace.jsonl")),
    );
    assert_eq!(format, TraceInputFormat::Jsonl);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn auto_defaults_to_json_on_stdin() {
    let format =
        resolve_trace_input_format(TraceInputFormatSelection::Auto, TraceSourceHint::Stdin);
    assert_eq!(format, TraceInputFormat::Json);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn explicit_always_resolves_to_itself() {
    assert_eq!(
        resolve_trace_input_format(TraceInputFormatSelection::Json, TraceSourceHint::Unknown),
        TraceInputFormat::Json
    );
    assert_eq!(
        resolve_trace_input_format(TraceInputFormatSelection::Jsonl, TraceSourceHint::Unknown),
        TraceInputFormat::Jsonl
    );
}
