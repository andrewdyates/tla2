// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 explain` — counterexample trace explanation from saved JSON output.
//!
//! Reads a JSON output file produced by `tla2 check --output json` and generates
//! a human-readable step-by-step explanation of the counterexample trace:
//!
//! - For each step, shows which variables changed and their new values
//! - Highlights the invariant violation at the final state
//! - Shows which sub-expression of the invariant failed (when `--spec` is given)
//! - Supports `--verbose` for full state dumps at each step
//! - Supports `--diff` mode showing only variable changes between steps
//! - Supports `--format human|json` output

use std::collections::HashMap;

use anyhow::{Context, Result};
use serde::Serialize;
use tla_check::{CounterexampleInfo, JsonOutput, JsonValue, StateInfo};

/// Output format for the explain command.
#[derive(Clone, Copy, Debug)]
pub(crate) enum ExplainFormat {
    Human,
    Json,
}

/// Configuration for the explain command.
#[allow(dead_code)]
pub(crate) struct ExplainConfig {
    pub trace_file: std::path::PathBuf,
    pub spec_file: Option<std::path::PathBuf>,
    pub config_file: Option<std::path::PathBuf>,
    pub invariant: Option<String>,
    pub diff_mode: bool,
    pub verbose: bool,
    pub format: ExplainFormat,
}

/// Run the explain command.
pub(crate) fn cmd_explain(config: ExplainConfig) -> Result<()> {
    let json_content = std::fs::read_to_string(&config.trace_file)
        .with_context(|| format!("Failed to read trace file: {}", config.trace_file.display()))?;

    let output: JsonOutput = serde_json::from_str(&json_content)
        .with_context(|| format!("Failed to parse JSON from: {}", config.trace_file.display()))?;

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

    // Build the explanation.
    let explanation = build_explanation(ce)?;

    // Optionally extract invariant conjuncts from the spec.
    let invariant_analysis = if config.spec_file.is_some() {
        analyze_invariant_structure(&output, &config)?
    } else {
        None
    };

    match config.format {
        ExplainFormat::Human => {
            print_human_explanation(&output, &explanation, invariant_analysis.as_ref(), &config);
        }
        ExplainFormat::Json => {
            let json_explanation =
                build_json_explanation(&output, &explanation, invariant_analysis.as_ref());
            println!(
                "{}",
                serde_json::to_string_pretty(&json_explanation)
                    .context("Failed to serialize explanation to JSON")?
            );
        }
    }

    Ok(())
}

/// A single step in the explained trace.
struct ExplainedStepInfo {
    index: usize,
    action_name: String,
    action_type: String,
    variables: HashMap<String, JsonValue>,
    changes: Vec<VariableChangeInfo>,
    is_stuttering: bool,
}

/// Information about a single variable change.
struct VariableChangeInfo {
    name: String,
    from: JsonValue,
    to: JsonValue,
}

/// Information about invariant sub-expression structure.
struct InvariantAnalysis {
    invariant_name: String,
    conjuncts: Vec<String>,
}

/// Build step-by-step explanation from the counterexample.
fn build_explanation(ce: &CounterexampleInfo) -> Result<Vec<ExplainedStepInfo>> {
    let mut steps = Vec::with_capacity(ce.states.len());

    for (i, state) in ce.states.iter().enumerate() {
        let changes = if i > 0 {
            compute_variable_changes(&ce.states[i - 1], state)
        } else {
            Vec::new()
        };

        let is_stuttering = i > 0 && changes.is_empty();

        steps.push(ExplainedStepInfo {
            index: state.index,
            action_name: state.action.name.clone(),
            action_type: state.action.action_type.clone(),
            variables: state.variables.clone(),
            changes,
            is_stuttering,
        });
    }

    Ok(steps)
}

/// Compute which variables changed between two consecutive states.
fn compute_variable_changes(prev: &StateInfo, curr: &StateInfo) -> Vec<VariableChangeInfo> {
    // If the JSON already has diff_from_previous, use it.
    if let Some(diff) = &curr.diff_from_previous {
        let mut changes: Vec<VariableChangeInfo> = diff
            .changed
            .iter()
            .map(|(name, change)| VariableChangeInfo {
                name: name.clone(),
                from: change.from.clone(),
                to: change.to.clone(),
            })
            .collect();
        changes.sort_by(|a, b| a.name.cmp(&b.name));
        return changes;
    }

    // Otherwise compute manually.
    let mut changes = Vec::new();
    for (name, curr_val) in &curr.variables {
        match prev.variables.get(name) {
            Some(prev_val) if prev_val != curr_val => {
                changes.push(VariableChangeInfo {
                    name: name.clone(),
                    from: prev_val.clone(),
                    to: curr_val.clone(),
                });
            }
            None => {
                changes.push(VariableChangeInfo {
                    name: name.clone(),
                    from: JsonValue::Undefined,
                    to: curr_val.clone(),
                });
            }
            _ => {}
        }
    }

    // Check for removed variables.
    for (name, prev_val) in &prev.variables {
        if !curr.variables.contains_key(name) {
            changes.push(VariableChangeInfo {
                name: name.clone(),
                from: prev_val.clone(),
                to: JsonValue::Undefined,
            });
        }
    }

    // Sort by name for deterministic output.
    changes.sort_by(|a, b| a.name.cmp(&b.name));
    changes
}

/// Analyze the invariant structure by extracting conjuncts from the spec.
///
/// This parses the TLA+ spec file, finds the invariant operator, and extracts
/// its conjunct sub-expressions so users can identify which part failed.
fn analyze_invariant_structure(
    output: &JsonOutput,
    config: &ExplainConfig,
) -> Result<Option<InvariantAnalysis>> {
    let spec_file = match &config.spec_file {
        Some(f) => f,
        None => return Ok(None),
    };

    // Determine the invariant name.
    let inv_name = config
        .invariant
        .clone()
        .or_else(|| {
            output
                .result
                .violated_property
                .as_ref()
                .map(|vp| vp.name.clone())
        })
        .or_else(|| output.specification.invariants.first().cloned());

    let Some(inv_name) = inv_name else {
        return Ok(None);
    };

    // Parse the spec to find the invariant definition.
    let source = std::fs::read_to_string(spec_file)
        .with_context(|| format!("Failed to read spec file: {}", spec_file.display()))?;

    let tree = tla_core::parse_to_syntax_tree(&source);
    let lower_result = tla_core::lower(tla_core::FileId(0), &tree);
    if !lower_result.errors.is_empty() {
        // Cannot analyze, but that is not fatal for the explain command.
        return Ok(None);
    }

    let module = match &lower_result.module {
        Some(m) => m,
        None => return Ok(None),
    };

    // Find the invariant operator and extract conjuncts.
    let conjuncts = extract_conjuncts_from_module(module, &inv_name);

    if conjuncts.is_empty() {
        return Ok(None);
    }

    Ok(Some(InvariantAnalysis {
        invariant_name: inv_name,
        conjuncts,
    }))
}

/// Find an operator definition in a module and extract conjunct expressions.
///
/// If the operator body is `A /\ B /\ C`, returns pretty-printed `["A", "B", "C"]`.
/// Otherwise returns the full body as a single expression.
fn extract_conjuncts_from_module(
    module: &tla_core::ast::Module,
    operator_name: &str,
) -> Vec<String> {
    for unit in &module.units {
        if let tla_core::ast::Unit::Operator(def) = &unit.node {
            if def.name.node == operator_name {
                return extract_conjuncts_from_expr(&def.body.node);
            }
        }
    }
    Vec::new()
}

/// Recursively extract conjuncts from an expression.
///
/// `Expr::And(lhs, rhs)` represents `A /\ B` in the TLA+ AST.
fn extract_conjuncts_from_expr(expr: &tla_core::ast::Expr) -> Vec<String> {
    match expr {
        tla_core::ast::Expr::And(lhs, rhs) => {
            let mut result = extract_conjuncts_from_expr(&lhs.node);
            result.extend(extract_conjuncts_from_expr(&rhs.node));
            result
        }
        other => {
            vec![tla_core::pretty_expr(other)]
        }
    }
}

/// Print human-readable explanation.
fn print_human_explanation(
    output: &JsonOutput,
    steps: &[ExplainedStepInfo],
    invariant_analysis: Option<&InvariantAnalysis>,
    config: &ExplainConfig,
) {
    // Header
    println!("=== Counterexample Trace Explanation ===");
    println!();

    if let Some(vp) = &output.result.violated_property {
        println!("Violated {}: {}", vp.prop_type, vp.name);
        if let Some(expr) = &vp.expression {
            println!("Expression: {expr}");
        }
        if let Some(loc) = &vp.location {
            println!("Location: {}:{}:{}", loc.file, loc.line, loc.column);
        }
        println!();
    } else if let Some(msg) = &output.result.error_message {
        println!("Error: {msg}");
        println!();
    }

    println!(
        "Trace length: {} step{}",
        steps.len(),
        if steps.len() == 1 { "" } else { "s" }
    );
    println!();

    for step in steps {
        print_step_human(step, config);
    }

    // Invariant sub-expression analysis
    if let Some(analysis) = invariant_analysis {
        println!(
            "=== Invariant Sub-Expression Analysis: {} ===",
            analysis.invariant_name
        );
        println!();
        println!(
            "The following conjuncts compose the invariant. \
             Check each against the final state:"
        );
        println!();
        for (i, conjunct) in analysis.conjuncts.iter().enumerate() {
            println!("  {}. {}", i + 1, conjunct);
        }
        println!();
    }
}

/// Print a single step in human-readable format.
fn print_step_human(step: &ExplainedStepInfo, config: &ExplainConfig) {
    let step_label = if step.action_type == "initial" {
        format!("State {}: Initial predicate", step.index)
    } else if step.is_stuttering {
        format!(
            "State {}: {} (stuttering - no changes)",
            step.index, step.action_name
        )
    } else {
        format!("State {}: {}", step.index, step.action_name)
    };

    println!("--- {} ---", step_label);

    if step.action_type == "initial" || config.verbose {
        // Show all variables
        print_variables(&step.variables);
    } else if config.diff_mode {
        // Show only changes
        if step.changes.is_empty() {
            println!("  (no changes)");
        } else {
            for change in &step.changes {
                println!(
                    "  {} = {} -> {}",
                    change.name,
                    format_json_value(&change.from),
                    format_json_value(&change.to),
                );
            }
        }
    } else {
        // Default: show changes summary, then all variables
        if !step.changes.is_empty() {
            println!("  Changes:");
            for change in &step.changes {
                println!(
                    "    {} : {} -> {}",
                    change.name,
                    format_json_value(&change.from),
                    format_json_value(&change.to),
                );
            }
        }
        print_variables(&step.variables);
    }

    println!();
}

/// Print all variables in a state.
fn print_variables(variables: &HashMap<String, JsonValue>) {
    let mut sorted: Vec<_> = variables.iter().collect();
    sorted.sort_by_key(|(k, _)| k.as_str());
    for (name, value) in &sorted {
        println!("  /\\ {} = {}", name, format_json_value(value));
    }
}

/// Format a `JsonValue` for human-readable display using TLA+ notation.
pub(crate) fn format_json_value(value: &JsonValue) -> String {
    match value {
        JsonValue::Bool(b) => {
            if *b {
                "TRUE".to_string()
            } else {
                "FALSE".to_string()
            }
        }
        JsonValue::Int(n) => format!("{n}"),
        JsonValue::BigInt(s) => s.clone(),
        JsonValue::String(s) => format!("\"{s}\""),
        JsonValue::ModelValue(s) => s.clone(),
        JsonValue::Undefined => "<undefined>".to_string(),
        JsonValue::Set(elems) => {
            let items: Vec<String> = elems.iter().map(format_json_value).collect();
            format!("{{{}}}", items.join(", "))
        }
        JsonValue::Seq(elems) => {
            let items: Vec<String> = elems.iter().map(format_json_value).collect();
            format!("<<{}>>", items.join(", "))
        }
        JsonValue::Tuple(elems) => {
            let items: Vec<String> = elems.iter().map(format_json_value).collect();
            format!("<<{}>>", items.join(", "))
        }
        JsonValue::Record(fields) => {
            let mut sorted: Vec<_> = fields.iter().collect();
            sorted.sort_by_key(|(k, _)| k.as_str());
            let items: Vec<String> = sorted
                .iter()
                .map(|(k, v)| format!("{k} |-> {}", format_json_value(v)))
                .collect();
            format!("[{}]", items.join(", "))
        }
        JsonValue::Function { mapping, .. } => {
            let items: Vec<String> = mapping
                .iter()
                .map(|(k, v)| format!("{} |-> {}", format_json_value(k), format_json_value(v)))
                .collect();
            format!("({})", items.join(" @@ "))
        }
        JsonValue::Interval { lo, hi } => format!("{lo}..{hi}"),
        _ => format!("{value:?}"),
    }
}

// --- JSON output types ---

#[derive(Debug, Serialize)]
struct JsonExplanation {
    version: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    violation: Option<ViolationSummary>,
    trace_length: usize,
    steps: Vec<JsonStepInfo>,
    #[serde(skip_serializing_if = "Option::is_none")]
    invariant_analysis: Option<JsonInvariantAnalysis>,
}

#[derive(Debug, Serialize)]
struct ViolationSummary {
    name: String,
    #[serde(rename = "type")]
    prop_type: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    expression: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    message: Option<String>,
}

#[derive(Debug, Serialize)]
struct JsonStepInfo {
    index: usize,
    action: String,
    action_type: String,
    is_stuttering: bool,
    changes: Vec<JsonChangeInfo>,
    variables: HashMap<String, serde_json::Value>,
}

#[derive(Debug, Serialize)]
struct JsonChangeInfo {
    variable: String,
    from: serde_json::Value,
    to: serde_json::Value,
}

#[derive(Debug, Serialize)]
struct JsonInvariantAnalysis {
    invariant_name: String,
    conjuncts: Vec<String>,
}

fn build_json_explanation(
    output: &JsonOutput,
    steps: &[ExplainedStepInfo],
    invariant_analysis: Option<&InvariantAnalysis>,
) -> JsonExplanation {
    let violation = output
        .result
        .violated_property
        .as_ref()
        .map(|vp| ViolationSummary {
            name: vp.name.clone(),
            prop_type: vp.prop_type.clone(),
            expression: vp.expression.clone(),
            message: output.result.error_message.clone(),
        });

    let json_steps: Vec<JsonStepInfo> = steps
        .iter()
        .map(|s| {
            let changes: Vec<JsonChangeInfo> = s
                .changes
                .iter()
                .map(|c| JsonChangeInfo {
                    variable: c.name.clone(),
                    from: json_value_to_serde(&c.from),
                    to: json_value_to_serde(&c.to),
                })
                .collect();

            let variables: HashMap<String, serde_json::Value> = s
                .variables
                .iter()
                .map(|(k, v)| (k.clone(), json_value_to_serde(v)))
                .collect();

            JsonStepInfo {
                index: s.index,
                action: s.action_name.clone(),
                action_type: s.action_type.clone(),
                is_stuttering: s.is_stuttering,
                changes,
                variables,
            }
        })
        .collect();

    let json_invariant = invariant_analysis.map(|ia| JsonInvariantAnalysis {
        invariant_name: ia.invariant_name.clone(),
        conjuncts: ia.conjuncts.clone(),
    });

    JsonExplanation {
        version: "1.0".to_string(),
        violation,
        trace_length: steps.len(),
        steps: json_steps,
        invariant_analysis: json_invariant,
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
    fn test_explain_build_explanation_computes_diffs() {
        let output = make_test_json_output();
        let ce = output.counterexample.as_ref().unwrap();

        let steps = build_explanation(ce).unwrap();
        assert_eq!(steps.len(), 3);

        // Step 0: initial, no changes
        assert!(steps[0].changes.is_empty());
        assert_eq!(steps[0].action_type, "initial");

        // Step 1: x changed from 0 to 1
        assert_eq!(steps[1].changes.len(), 1);
        assert_eq!(steps[1].changes[0].name, "x");
        assert_eq!(steps[1].changes[0].from, JsonValue::Int(0));
        assert_eq!(steps[1].changes[0].to, JsonValue::Int(1));

        // Step 2: x changed from 1 to 2
        assert_eq!(steps[2].changes.len(), 1);
        assert_eq!(steps[2].changes[0].name, "x");
    }

    #[test]
    fn test_explain_format_json_value_displays_tla_syntax() {
        assert_eq!(format_json_value(&JsonValue::Bool(true)), "TRUE");
        assert_eq!(format_json_value(&JsonValue::Bool(false)), "FALSE");
        assert_eq!(format_json_value(&JsonValue::Int(42)), "42");
        assert_eq!(
            format_json_value(&JsonValue::String("hello".into())),
            "\"hello\""
        );
        assert_eq!(
            format_json_value(&JsonValue::ModelValue("m1".into())),
            "m1"
        );
        assert_eq!(format_json_value(&JsonValue::Undefined), "<undefined>");

        let set = JsonValue::Set(vec![JsonValue::Int(1), JsonValue::Int(2)]);
        assert_eq!(format_json_value(&set), "{1, 2}");

        let seq = JsonValue::Seq(vec![JsonValue::Int(1), JsonValue::Int(2)]);
        assert_eq!(format_json_value(&seq), "<<1, 2>>");
    }

    #[test]
    fn test_explain_json_output_format() {
        let output = make_test_json_output();
        let ce = output.counterexample.as_ref().unwrap();

        let steps = build_explanation(ce).unwrap();
        let json_out = build_json_explanation(&output, &steps, None);

        assert_eq!(json_out.trace_length, 3);
        assert!(json_out.violation.is_some());
        let violation = json_out.violation.unwrap();
        assert_eq!(violation.name, "Safety");
        assert_eq!(violation.prop_type, "invariant");
        assert_eq!(json_out.steps.len(), 3);
        assert!(json_out.steps[0].changes.is_empty());
        assert_eq!(json_out.steps[1].changes.len(), 1);
        assert_eq!(json_out.steps[1].changes[0].variable, "x");
    }
}
