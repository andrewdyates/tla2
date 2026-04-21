// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Format-only trace validation (no spec required).

use std::fs::File;
use std::io::{self, Read};
use std::path::Path;

use anyhow::{Context, Result};
use tla_check::{
    read_trace_events, resolve_trace_input_format, TraceEventSink, TraceHeader,
    TraceInputFormatSelection, TraceSourceHint, TraceStep,
};

use super::TraceInputFormatArg;

/// Format-only validation (original behavior).
pub(crate) fn cmd_trace_validate_format(
    path: &Path,
    input_format: TraceInputFormatArg,
) -> Result<()> {
    let selection = TraceInputFormatSelection::from(input_format);
    let hint = if path.as_os_str() == "-" {
        TraceSourceHint::Stdin
    } else {
        TraceSourceHint::Path(path)
    };
    let format = resolve_trace_input_format(selection, hint);

    let reader: Box<dyn Read> = if path.as_os_str() == "-" {
        Box::new(io::stdin().lock())
    } else {
        Box::new(File::open(path).with_context(|| format!("open {}", path.display()))?)
    };

    let mut sink = CountSink::default();
    let parse = read_trace_events(reader, format, &mut sink)
        .with_context(|| format!("parse trace {} as {:?}", path.display(), format));
    if path.as_os_str() == "-" && matches!(input_format, TraceInputFormatArg::Auto) {
        parse
            .context("hint: stdin `auto` defaults to JSON; use `--input-format jsonl` for JSONL")?;
    } else {
        parse?;
    }

    let header = sink
        .header
        .as_ref()
        .context("trace parser did not deliver a header")?;

    println!(
        "OK: parsed {} steps (module {}, {} vars)",
        sink.steps,
        header.module,
        header.variables.len()
    );
    Ok(())
}

#[derive(Default)]
struct CountSink {
    header: Option<TraceHeader>,
    steps: usize,
}

impl TraceEventSink for CountSink {
    fn on_header(&mut self, header: TraceHeader) {
        self.header = Some(header);
    }

    fn on_step(&mut self, _step: TraceStep) {
        self.steps += 1;
    }
}
