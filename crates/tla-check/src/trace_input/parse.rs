// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Trace input parsing implementation (JSON + JSONL readers).

use std::collections::{HashMap, HashSet};
use std::io::{self, BufRead, BufReader, Read};

use serde::de::DeserializeOwned;
use serde::Deserialize;

use crate::json_output::JsonValue;
use crate::json_path::format_json_path;

use super::{
    TraceActionLabel, TraceEventSink, TraceHeader, TraceInputFormat, TraceParseError, TraceStep,
};

#[derive(Debug, Deserialize)]
struct TraceJsonlTag {
    #[serde(rename = "type")]
    ty: String,
}

#[derive(Debug, Deserialize)]
struct TraceJsonlHeaderLine {
    version: String,
    module: String,
    variables: Vec<String>,
}

#[derive(Debug, Deserialize)]
struct TraceJsonlStepLine {
    #[serde(default)]
    index: Option<usize>,
    state: HashMap<String, JsonValue>,
    #[serde(default)]
    action: Option<TraceActionLabel>,
}

#[derive(Debug, Deserialize)]
struct TraceJsonFile {
    version: String,
    module: String,
    variables: Vec<String>,
    steps: Vec<TraceStep>,
}

pub fn read_trace_events<R: Read, S: TraceEventSink>(
    reader: R,
    format: TraceInputFormat,
    sink: &mut S,
) -> Result<(), TraceParseError> {
    match format {
        TraceInputFormat::Json => read_trace_json(reader, sink),
        TraceInputFormat::Jsonl => read_trace_jsonl(BufReader::new(reader), sink),
    }
}

pub fn read_trace_json<R: Read, S: TraceEventSink>(
    reader: R,
    sink: &mut S,
) -> Result<(), TraceParseError> {
    let mut reader = BufReader::new(reader);
    strip_utf8_bom_bytes(&mut reader)?;
    let mut de = serde_json::Deserializer::from_reader(reader);
    let file: TraceJsonFile = match serde_path_to_error::deserialize(&mut de) {
        Ok(file) => file,
        Err(e) => {
            let path = format_json_path(e.path());
            let source = e.into_inner();
            return Err(TraceParseError::JsonDecodePath {
                path,
                line: source.line(),
                column: source.column(),
                source,
            });
        }
    };
    if file.steps.is_empty() {
        return Err(TraceParseError::MissingAnySteps {
            where_: "json steps".to_string(),
        });
    }

    let header = TraceHeader {
        version: file.version,
        module: file.module,
        variables: file.variables,
    };
    let vars = build_var_set(&header.variables, "json header")?;
    sink.on_header(header);

    for (pos, mut step) in file.steps.into_iter().enumerate() {
        validate_and_canonicalize_step(&mut step, pos, &vars, &format_where_json(pos))?;
        sink.on_step(step);
    }
    Ok(())
}

pub fn read_trace_jsonl<R: BufRead, S: TraceEventSink>(
    reader: R,
    sink: &mut S,
) -> Result<(), TraceParseError> {
    let mut header: Option<TraceHeader> = None;
    let mut header_where: Option<String> = None;
    let mut delivered_header = false;
    let mut vars: HashSet<String> = HashSet::new();
    let mut expected_index: usize = 0;

    for (zero_line_no, line) in reader.lines().enumerate() {
        let line_no = zero_line_no + 1;
        let line = line?;
        let trimmed = strip_utf8_bom(line.trim());
        if trimmed.is_empty() {
            continue;
        }

        let raw_line_prefix = line_prefix(trimmed);
        let tag: TraceJsonlTag = decode_jsonl_str(trimmed, line_no, &raw_line_prefix)?;
        match tag.ty.as_str() {
            "header" => {
                let TraceJsonlHeaderLine {
                    version,
                    module,
                    variables,
                } = decode_jsonl_str(trimmed, line_no, &raw_line_prefix)?;
                if delivered_header || header.is_some() {
                    return Err(TraceParseError::JsonlUnexpectedHeader { line_no });
                }
                let where_ = format_where_jsonl_header(line_no);
                vars = build_var_set(&variables, &where_)?;
                header = Some(TraceHeader {
                    version,
                    module,
                    variables,
                });
                header_where = Some(where_);
            }
            "step" => {
                let TraceJsonlStepLine {
                    index,
                    state,
                    action,
                } = decode_jsonl_str(trimmed, line_no, &raw_line_prefix)?;
                if !delivered_header && header.is_none() {
                    return Err(TraceParseError::JsonlMissingHeader { line_no });
                }

                if !delivered_header {
                    let hdr = header
                        .take()
                        .ok_or(TraceParseError::JsonlMissingBufferedHeader { line_no })?;
                    sink.on_header(hdr);
                    delivered_header = true;
                }

                let mut step = TraceStep {
                    index,
                    state,
                    action,
                };
                validate_and_canonicalize_step(
                    &mut step,
                    expected_index,
                    &vars,
                    &format_where_jsonl(line_no),
                )?;
                expected_index += 1;
                sink.on_step(step);
            }
            other => {
                return Err(TraceParseError::JsonlUnknownEventType {
                    line_no,
                    ty: other.to_string(),
                });
            }
        }
    }

    if !delivered_header {
        if header.is_some() {
            return Err(TraceParseError::MissingAnySteps {
                where_: header_where.unwrap_or_else(|| "jsonl header".to_string()),
            });
        }
        return Err(TraceParseError::JsonlMissingHeaderAtEof);
    }

    Ok(())
}

fn decode_jsonl_str<T: DeserializeOwned>(
    input: &str,
    line_no: usize,
    raw_line_prefix: &str,
) -> Result<T, TraceParseError> {
    let mut de = serde_json::Deserializer::from_str(input);
    match serde_path_to_error::deserialize(&mut de) {
        Ok(v) => Ok(v),
        Err(e) => {
            let path = format_json_path(e.path());
            let source = e.into_inner();
            Err(TraceParseError::JsonlDecode {
                line_no,
                path,
                column: source.column(),
                source,
                raw_line_prefix: raw_line_prefix.to_string(),
            })
        }
    }
}

fn build_var_set(variables: &[String], where_: &str) -> Result<HashSet<String>, TraceParseError> {
    let mut vars: HashSet<String> = HashSet::with_capacity(variables.len());
    for v in variables {
        if !vars.insert(v.clone()) {
            return Err(TraceParseError::DuplicateVariable {
                where_: where_.to_string(),
                var: v.clone(),
            });
        }
    }
    Ok(vars)
}

fn validate_and_canonicalize_step(
    step: &mut TraceStep,
    expected_index: usize,
    vars: &HashSet<String>,
    where_: &str,
) -> Result<(), TraceParseError> {
    let got = step.index.unwrap_or(expected_index);
    if got != expected_index {
        return Err(TraceParseError::StepIndexMismatch {
            where_: where_.to_string(),
            expected: expected_index,
            got,
        });
    }
    step.index = Some(got);

    if got == 0 && step.action.is_some() {
        return Err(TraceParseError::ActionOnInitialStep {
            where_: where_.to_string(),
        });
    }

    for k in step.state.keys() {
        if !vars.contains(k) {
            return Err(TraceParseError::UnknownVariable {
                where_: where_.to_string(),
                var: k.clone(),
            });
        }
    }

    Ok(())
}

fn line_prefix(line: &str) -> String {
    const LIMIT: usize = 200;
    if line.len() <= LIMIT {
        return line.to_string();
    }
    let mut end = LIMIT;
    while end > 0 && !line.is_char_boundary(end) {
        end -= 1;
    }
    format!("{}...", &line[..end])
}

fn format_where_jsonl(line_no: usize) -> String {
    format!("jsonl line {}", line_no)
}

fn format_where_jsonl_header(line_no: usize) -> String {
    format!("jsonl header line {}", line_no)
}

fn format_where_json(step_index: usize) -> String {
    format!("json steps[{}]", step_index)
}

fn strip_utf8_bom_bytes<R: BufRead>(r: &mut R) -> Result<(), io::Error> {
    const BOM: &[u8] = &[0xEF, 0xBB, 0xBF];
    let buf = r.fill_buf()?;
    if buf.starts_with(BOM) {
        r.consume(BOM.len());
    }
    Ok(())
}

fn strip_utf8_bom(s: &str) -> &str {
    s.strip_prefix('\u{feff}').unwrap_or(s)
}
