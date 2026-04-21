// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 trace view` -- counterexample trace viewer with variable diffs.
//!
//! Reads a JSON output file produced by `tla2 check --output json` and displays
//! counterexample traces in a rich format with variable diffs between states.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use anyhow::{Context, Result};
use serde::Serialize;
use tla_check::{CounterexampleInfo, JsonOutput, JsonValue, StateInfo};

use crate::cli_schema::TraceViewOutputFormat;
use crate::cmd_explain::format_json_value;

/// Run the trace view command.
pub(crate) fn cmd_trace_view(
    trace_file: &Path,
    format: TraceViewOutputFormat,
    filter_vars: &[String],
    step: Option<usize>,
    show_diff: bool,
    show_unchanged: bool,
) -> Result<()> {
    let json_content = std::fs::read_to_string(trace_file)
        .with_context(|| format!("Failed to read trace file: {}", trace_file.display()))?;

    let output: JsonOutput = serde_json::from_str(&json_content)
        .with_context(|| format!("Failed to parse JSON from: {}", trace_file.display()))?;

    let counterexample = output.counterexample.as_ref();
    if counterexample.is_none() || counterexample.is_some_and(|c| c.states.is_empty()) {
        println!("No counterexample trace found in the output file.");
        println!();
        println!("Status: {}", output.result.status);
        if let Some(msg) = &output.result.error_message {
            println!("Message: {msg}");
        }
        return Ok(());
    }

    let ce = counterexample.expect("checked above");
    let steps = build_view_steps(ce, filter_vars)?;

    // Collect all variable names across all steps for the table format.
    let all_vars = collect_all_variable_names(&steps, filter_vars);

    match format {
        TraceViewOutputFormat::Human => {
            if let Some(step_idx) = step {
                print_single_step_human(&steps, step_idx, show_diff, show_unchanged)?;
            } else {
                print_all_steps_human(&output, &steps, show_diff, show_unchanged);
            }
        }
        TraceViewOutputFormat::Json => {
            let json_out = build_json_view(&output, &steps, step);
            println!(
                "{}",
                serde_json::to_string_pretty(&json_out)
                    .context("Failed to serialize trace view to JSON")?
            );
        }
        TraceViewOutputFormat::Table => {
            if let Some(step_idx) = step {
                print_single_step_table(&steps, &all_vars, step_idx)?;
            } else {
                print_table(&steps, &all_vars);
            }
        }
    }

    Ok(())
}

/// A single step in the trace view.
struct ViewStep {
    index: usize,
    action_name: String,
    action_type: String,
    /// Variable values at this step (filtered if --filter was given).
    variables: BTreeMap<String, JsonValue>,
    /// Variables that changed from the previous step.
    changed: BTreeMap<String, (JsonValue, JsonValue)>,
    is_stuttering: bool,
}

/// Build view steps from the counterexample, applying variable filtering.
fn build_view_steps(ce: &CounterexampleInfo, filter_vars: &[String]) -> Result<Vec<ViewStep>> {
    let filter: BTreeSet<&str> = filter_vars.iter().map(|s| s.as_str()).collect();
    let mut steps = Vec::with_capacity(ce.states.len());

    for (i, state) in ce.states.iter().enumerate() {
        let variables: BTreeMap<String, JsonValue> = state
            .variables
            .iter()
            .filter(|(k, _)| filter.is_empty() || filter.contains(k.as_str()))
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect();

        let changed = if i > 0 {
            compute_changes(&ce.states[i - 1], state, &filter)
        } else {
            BTreeMap::new()
        };

        let is_stuttering = i > 0 && changed.is_empty();

        steps.push(ViewStep {
            index: state.index,
            action_name: state.action.name.clone(),
            action_type: state.action.action_type.clone(),
            variables,
            changed,
            is_stuttering,
        });
    }

    Ok(steps)
}

/// Compute changed variables between two states, respecting the filter.
fn compute_changes(
    prev: &StateInfo,
    curr: &StateInfo,
    filter: &BTreeSet<&str>,
) -> BTreeMap<String, (JsonValue, JsonValue)> {
    // Use the built-in diff if available.
    if let Some(diff) = &curr.diff_from_previous {
        return diff
            .changed
            .iter()
            .filter(|(k, _)| filter.is_empty() || filter.contains(k.as_str()))
            .map(|(k, c)| (k.clone(), (c.from.clone(), c.to.clone())))
            .collect();
    }

    let mut changes = BTreeMap::new();
    for (name, curr_val) in &curr.variables {
        if !filter.is_empty() && !filter.contains(name.as_str()) {
            continue;
        }
        match prev.variables.get(name) {
            Some(prev_val) if prev_val != curr_val => {
                changes.insert(name.clone(), (prev_val.clone(), curr_val.clone()));
            }
            None => {
                changes.insert(name.clone(), (JsonValue::Undefined, curr_val.clone()));
            }
            _ => {}
        }
    }
    for (name, prev_val) in &prev.variables {
        if !filter.is_empty() && !filter.contains(name.as_str()) {
            continue;
        }
        if !curr.variables.contains_key(name) {
            changes.insert(name.clone(), (prev_val.clone(), JsonValue::Undefined));
        }
    }
    changes
}

/// Collect all variable names across all steps (sorted).
fn collect_all_variable_names(steps: &[ViewStep], filter_vars: &[String]) -> Vec<String> {
    if !filter_vars.is_empty() {
        return filter_vars.to_vec();
    }
    let mut vars: BTreeSet<String> = BTreeSet::new();
    for step in steps {
        for k in step.variables.keys() {
            vars.insert(k.clone());
        }
    }
    vars.into_iter().collect()
}

// ---------------------------------------------------------------------------
// Human output format
// ---------------------------------------------------------------------------

fn print_all_steps_human(
    output: &JsonOutput,
    steps: &[ViewStep],
    show_diff: bool,
    show_unchanged: bool,
) {
    // Header
    if let Some(vp) = &output.result.violated_property {
        println!("Violated {}: {}", vp.prop_type, vp.name);
        if let Some(loc) = &vp.location {
            println!("  at {}:{}:{}", loc.file, loc.line, loc.column);
        }
        println!();
    }

    // Collect unique action names.
    let mut action_set: BTreeSet<&str> = BTreeSet::new();
    for s in steps {
        if s.action_type != "initial" {
            action_set.insert(&s.action_name);
        }
    }

    for s in steps {
        print_step_human(s, show_diff, show_unchanged);
    }

    // Summary line
    println!(
        "--- Summary: {} steps, {} variables, {} unique actions ---",
        steps.len(),
        steps
            .first()
            .map(|s| s.variables.len())
            .unwrap_or(0),
        action_set.len(),
    );
}

fn print_single_step_human(
    steps: &[ViewStep],
    step_idx: usize,
    show_diff: bool,
    show_unchanged: bool,
) -> Result<()> {
    let s = steps
        .iter()
        .find(|s| s.index == step_idx)
        .with_context(|| {
            format!(
                "Step {} not found (trace has steps {}..={})",
                step_idx,
                steps.first().map(|s| s.index).unwrap_or(0),
                steps.last().map(|s| s.index).unwrap_or(0),
            )
        })?;
    print_step_human(s, show_diff, show_unchanged);
    Ok(())
}

fn print_step_human(step: &ViewStep, show_diff: bool, show_unchanged: bool) {
    // Step header
    let label = if step.action_type == "initial" {
        format!("State {}: <<Initial predicate>>", step.index)
    } else if step.is_stuttering {
        format!(
            "State {}: {} (stuttering - no changes)",
            step.index, step.action_name
        )
    } else {
        format!("State {}: {}", step.index, step.action_name)
    };
    println!("--- {label} ---");

    if step.action_type == "initial" || !show_diff {
        // Show all variables
        for (name, value) in &step.variables {
            let marker = if step.changed.contains_key(name) {
                "*"
            } else {
                " "
            };
            println!(" {marker} /\\ {name} = {}", format_json_value(value));
        }
    } else {
        // Diff mode: show changed variables first, then optionally unchanged
        if step.changed.is_empty() {
            println!("  (no changes)");
        } else {
            for (name, (from, to)) in &step.changed {
                println!(
                    " *  {name}: {} -> {}",
                    format_json_value(from),
                    format_json_value(to),
                );
            }
        }
        if show_unchanged {
            for (name, value) in &step.variables {
                if !step.changed.contains_key(name) {
                    println!("    /\\ {name} = {}", format_json_value(value));
                }
            }
        }
    }
    println!();
}

// ---------------------------------------------------------------------------
// Table output format
// ---------------------------------------------------------------------------

fn print_table(steps: &[ViewStep], all_vars: &[String]) {
    if steps.is_empty() || all_vars.is_empty() {
        println!("(empty trace)");
        return;
    }

    // Build column data: first column is "Step", then one column per variable.
    let mut columns: Vec<Vec<String>> = Vec::with_capacity(1 + all_vars.len());

    // Step column
    let mut step_col = vec!["Step".to_string()];
    for s in steps {
        step_col.push(format!("{}", s.index));
    }
    columns.push(step_col);

    // Variable columns
    for var in all_vars {
        let mut col = vec![var.clone()];
        for s in steps {
            let val = s
                .variables
                .get(var)
                .map(format_json_value)
                .unwrap_or_else(|| "-".to_string());
            col.push(val);
        }
        columns.push(col);
    }

    // Compute column widths
    let widths: Vec<usize> = columns
        .iter()
        .map(|col| col.iter().map(|cell| cell.len()).max().unwrap_or(0))
        .collect();

    // Print header
    let header: Vec<String> = columns
        .iter()
        .zip(widths.iter())
        .map(|(col, w)| format!("{:>width$}", col[0], width = *w))
        .collect();
    println!("{}", header.join(" | "));

    // Separator
    let sep: Vec<String> = widths.iter().map(|w| "-".repeat(*w)).collect();
    println!("{}", sep.join("-+-"));

    // Data rows
    for row_idx in 1..columns[0].len() {
        let row: Vec<String> = columns
            .iter()
            .zip(widths.iter())
            .map(|(col, w)| format!("{:>width$}", col[row_idx], width = *w))
            .collect();
        println!("{}", row.join(" | "));
    }
}

fn print_single_step_table(
    steps: &[ViewStep],
    all_vars: &[String],
    step_idx: usize,
) -> Result<()> {
    let s = steps
        .iter()
        .find(|s| s.index == step_idx)
        .with_context(|| format!("Step {step_idx} not found in trace"))?;

    let max_name_len = all_vars.iter().map(|v| v.len()).max().unwrap_or(0);
    println!("Step {}: {}", s.index, s.action_name);
    for var in all_vars {
        let val = s
            .variables
            .get(var)
            .map(format_json_value)
            .unwrap_or_else(|| "-".to_string());
        let marker = if s.changed.contains_key(var) {
            "*"
        } else {
            " "
        };
        println!(
            " {marker} {:>width$} = {}",
            var,
            val,
            width = max_name_len
        );
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// JSON output format
// ---------------------------------------------------------------------------

#[derive(Debug, Serialize)]
struct JsonTraceView {
    version: String,
    trace_length: usize,
    variables: Vec<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    violation: Option<JsonViolation>,
    steps: Vec<JsonViewStep>,
    summary: JsonSummary,
}

#[derive(Debug, Serialize)]
struct JsonViolation {
    name: String,
    #[serde(rename = "type")]
    prop_type: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    expression: Option<String>,
}

#[derive(Debug, Serialize)]
struct JsonViewStep {
    index: usize,
    action: String,
    action_type: String,
    is_stuttering: bool,
    variables: BTreeMap<String, serde_json::Value>,
    #[serde(skip_serializing_if = "BTreeMap::is_empty")]
    changed: BTreeMap<String, JsonViewChange>,
}

#[derive(Debug, Serialize)]
struct JsonViewChange {
    from: serde_json::Value,
    to: serde_json::Value,
}

#[derive(Debug, Serialize)]
struct JsonSummary {
    total_steps: usize,
    total_variables: usize,
    unique_actions: Vec<String>,
}

fn build_json_view(
    output: &JsonOutput,
    steps: &[ViewStep],
    step_filter: Option<usize>,
) -> JsonTraceView {
    let violation = output
        .result
        .violated_property
        .as_ref()
        .map(|vp| JsonViolation {
            name: vp.name.clone(),
            prop_type: vp.prop_type.clone(),
            expression: vp.expression.clone(),
        });

    let all_vars: BTreeSet<String> = steps
        .iter()
        .flat_map(|s| s.variables.keys().cloned())
        .collect();

    let mut action_set: BTreeSet<String> = BTreeSet::new();
    for s in steps {
        if s.action_type != "initial" {
            action_set.insert(s.action_name.clone());
        }
    }

    let filtered_steps: Vec<&ViewStep> = match step_filter {
        Some(idx) => steps.iter().filter(|s| s.index == idx).collect(),
        None => steps.iter().collect(),
    };

    let json_steps: Vec<JsonViewStep> = filtered_steps
        .iter()
        .map(|s| {
            let variables: BTreeMap<String, serde_json::Value> = s
                .variables
                .iter()
                .map(|(k, v)| (k.clone(), json_value_to_serde(v)))
                .collect();
            let changed: BTreeMap<String, JsonViewChange> = s
                .changed
                .iter()
                .map(|(k, (from, to))| {
                    (
                        k.clone(),
                        JsonViewChange {
                            from: json_value_to_serde(from),
                            to: json_value_to_serde(to),
                        },
                    )
                })
                .collect();
            JsonViewStep {
                index: s.index,
                action: s.action_name.clone(),
                action_type: s.action_type.clone(),
                is_stuttering: s.is_stuttering,
                variables,
                changed,
            }
        })
        .collect();

    JsonTraceView {
        version: "1.0".to_string(),
        trace_length: steps.len(),
        variables: all_vars.into_iter().collect(),
        violation,
        steps: json_steps,
        summary: JsonSummary {
            total_steps: steps.len(),
            total_variables: steps
                .first()
                .map(|s| s.variables.len())
                .unwrap_or(0),
            unique_actions: action_set.into_iter().collect(),
        },
    }
}

/// Convert our `JsonValue` to `serde_json::Value` for output.
fn json_value_to_serde(value: &JsonValue) -> serde_json::Value {
    match value {
        JsonValue::Bool(b) => serde_json::Value::Bool(*b),
        JsonValue::Int(n) => serde_json::json!(n),
        JsonValue::BigInt(s) => serde_json::Value::String(s.clone()),
        JsonValue::String(s) => serde_json::Value::String(s.clone()),
        JsonValue::ModelValue(s) => serde_json::Value::String(s.clone()),
        JsonValue::Undefined => serde_json::Value::Null,
        JsonValue::Set(elems) => {
            serde_json::Value::Array(elems.iter().map(json_value_to_serde).collect())
        }
        JsonValue::Seq(elems) => {
            serde_json::Value::Array(elems.iter().map(json_value_to_serde).collect())
        }
        JsonValue::Tuple(elems) => {
            serde_json::Value::Array(elems.iter().map(json_value_to_serde).collect())
        }
        JsonValue::Record(fields) => {
            let map: serde_json::Map<String, serde_json::Value> = fields
                .iter()
                .map(|(k, v)| (k.clone(), json_value_to_serde(v)))
                .collect();
            serde_json::Value::Object(map)
        }
        JsonValue::Function { mapping, .. } => {
            let entries: Vec<serde_json::Value> = mapping
                .iter()
                .map(|(k, v)| {
                    serde_json::json!({
                        "key": json_value_to_serde(k),
                        "value": json_value_to_serde(v),
                    })
                })
                .collect();
            serde_json::Value::Array(entries)
        }
        JsonValue::Interval { lo, hi } => {
            serde_json::json!({"lo": lo, "hi": hi})
        }
        _ => serde_json::Value::String(format!("{value:?}")),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_test_json_output() -> JsonOutput {
        let json_str = r#"{
            "version": "1.3",
            "tool": "tla2",
            "timestamp": "2026-03-30T00:00:00Z",
            "input": {
                "spec_file": "Spec.tla",
                "module": "Spec",
                "workers": 1
            },
            "specification": {
                "invariants": ["TypeOK", "Safety"],
                "properties": [],
                "constants": {},
                "variables": ["x", "y"]
            },
            "soundness": {
                "mode": "sound",
                "features_used": [],
                "deviations": [],
                "assumptions": []
            },
            "completeness": "exhaustive",
            "result": {
                "status": "error",
                "error_type": "invariant_violation",
                "error_code": "TLC_INVARIANT_VIOLATION",
                "error_message": "Invariant Safety is violated.",
                "violated_property": {
                    "name": "Safety",
                    "type": "invariant"
                }
            },
            "counterexample": {
                "length": 3,
                "states": [
                    {
                        "index": 1,
                        "action": { "name": "Initial predicate", "type": "initial" },
                        "variables": {
                            "x": { "type": "int", "value": 0 },
                            "y": { "type": "int", "value": 0 }
                        }
                    },
                    {
                        "index": 2,
                        "action": { "name": "Increment", "type": "next" },
                        "variables": {
                            "x": { "type": "int", "value": 1 },
                            "y": { "type": "int", "value": 0 }
                        }
                    },
                    {
                        "index": 3,
                        "action": { "name": "Increment", "type": "next" },
                        "variables": {
                            "x": { "type": "int", "value": 2 },
                            "y": { "type": "int", "value": 0 }
                        }
                    }
                ]
            },
            "statistics": {
                "states_found": 10,
                "states_initial": 1,
                "transitions": 9,
                "time_seconds": 0.01
            },
            "diagnostics": {
                "warnings": [],
                "info": []
            }
        }"#;
        serde_json::from_str(json_str).expect("test JSON should parse")
    }

    #[test]
    fn test_view_build_steps_computes_diffs() {
        let output = make_test_json_output();
        let ce = output.counterexample.as_ref().unwrap();
        let steps = build_view_steps(ce, &[]).unwrap();

        assert_eq!(steps.len(), 3);
        assert!(steps[0].changed.is_empty());
        assert_eq!(steps[0].action_type, "initial");

        assert_eq!(steps[1].changed.len(), 1);
        assert!(steps[1].changed.contains_key("x"));

        assert_eq!(steps[2].changed.len(), 1);
        assert!(steps[2].changed.contains_key("x"));
    }

    #[test]
    fn test_view_filter_vars() {
        let output = make_test_json_output();
        let ce = output.counterexample.as_ref().unwrap();
        let steps = build_view_steps(ce, &["x".to_string()]).unwrap();

        // Only 'x' should be in variables
        for s in &steps {
            assert!(s.variables.contains_key("x"));
            assert!(!s.variables.contains_key("y"));
        }
    }

    #[test]
    fn test_view_json_output_has_summary() {
        let output = make_test_json_output();
        let ce = output.counterexample.as_ref().unwrap();
        let steps = build_view_steps(ce, &[]).unwrap();
        let json_out = build_json_view(&output, &steps, None);

        assert_eq!(json_out.trace_length, 3);
        assert_eq!(json_out.summary.total_steps, 3);
        assert_eq!(json_out.summary.total_variables, 2);
        assert_eq!(json_out.summary.unique_actions, vec!["Increment"]);
        assert!(json_out.violation.is_some());
    }

    #[test]
    fn test_view_step_filter() {
        let output = make_test_json_output();
        let ce = output.counterexample.as_ref().unwrap();
        let steps = build_view_steps(ce, &[]).unwrap();
        let json_out = build_json_view(&output, &steps, Some(2));

        assert_eq!(json_out.steps.len(), 1);
        assert_eq!(json_out.steps[0].index, 2);
    }

    #[test]
    fn test_view_collect_all_variable_names() {
        let output = make_test_json_output();
        let ce = output.counterexample.as_ref().unwrap();
        let steps = build_view_steps(ce, &[]).unwrap();
        let vars = collect_all_variable_names(&steps, &[]);

        assert_eq!(vars, vec!["x", "y"]);
    }
}
