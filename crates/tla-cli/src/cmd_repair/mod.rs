// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 repair` -- counterexample trace analysis with fix suggestions.
//!
//! Reads a JSON output file produced by `tla2 check --output json`, parses the
//! counterexample trace, and analyzes the final state transition that caused the
//! invariant violation. Produces actionable repair suggestions:
//!
//! - Which variables changed in the violating step
//! - What values would satisfy the invariant (by reverting individual changes)
//! - Which action (Next disjunct) was taken
//! - Minimal state change to restore the invariant
//! - Invariant conjunct decomposition (when `--spec` is given)

use std::collections::HashMap;
use std::path::PathBuf;

use anyhow::{Context, Result};
use serde::Serialize;
use tla_check::{CounterexampleInfo, JsonOutput, JsonValue, StateInfo};

// ---------------------------------------------------------------------------
// Public interface
// ---------------------------------------------------------------------------

/// Output format for the repair command.
#[derive(Clone, Copy, Debug)]
pub(crate) enum RepairFormat {
    Human,
    Json,
}

/// Configuration for the repair command (populated from CLI args).
#[allow(dead_code)]
pub(crate) struct RepairConfig {
    pub trace_file: PathBuf,
    pub spec_file: Option<PathBuf>,
    pub config_file: Option<PathBuf>,
    pub invariant: Option<String>,
    pub max_suggestions: usize,
    pub format: RepairFormat,
}

/// Entry point for `tla2 repair`.
pub(crate) fn cmd_repair(config: RepairConfig) -> Result<()> {
    // 1. Read and parse the JSON trace file.
    let json_content = std::fs::read_to_string(&config.trace_file)
        .with_context(|| format!("Failed to read trace file: {}", config.trace_file.display()))?;

    let output: JsonOutput = serde_json::from_str(&json_content)
        .with_context(|| format!("Failed to parse JSON from: {}", config.trace_file.display()))?;

    // 2. Validate: need a counterexample trace.
    let counterexample = match output.counterexample.as_ref() {
        Some(ce) if !ce.states.is_empty() => ce,
        _ => {
            println!("No counterexample trace found in the output file.");
            println!();
            println!("Status: {}", output.result.status);
            if let Some(msg) = &output.result.error_message {
                println!("Message: {msg}");
            }
            println!();
            println!("The repair command requires a counterexample trace.");
            println!("Run: tla2 check --output json <spec.tla> to generate one.");
            return Ok(());
        }
    };

    // 3. Build the repair analysis.
    let analysis = build_repair_analysis(&output, counterexample, &config)?;

    // 4. Emit output.
    match config.format {
        RepairFormat::Human => print_human_repair(&analysis),
        RepairFormat::Json => {
            let json = serde_json::to_string_pretty(&analysis)
                .context("Failed to serialize repair analysis to JSON")?;
            println!("{json}");
        }
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Core analysis types
// ---------------------------------------------------------------------------

/// Complete repair analysis result.
#[derive(Debug, Serialize)]
struct RepairAnalysis {
    /// Length of the counterexample trace.
    trace_length: usize,
    /// 1-based index of the violating step (last step in the trace).
    violating_step: usize,
    /// Name of the violated invariant (if known).
    #[serde(skip_serializing_if = "Option::is_none")]
    violated_invariant: Option<String>,
    /// Error message from the model checker.
    #[serde(skip_serializing_if = "Option::is_none")]
    error_message: Option<String>,
    /// Action that was active during the violating step.
    #[serde(skip_serializing_if = "Option::is_none")]
    violating_action: Option<String>,
    /// Variables that changed in the violating step.
    changed_variables: Vec<VariableChange>,
    /// Variables that did NOT change in the violating step.
    unchanged_variables: Vec<UnchangedVariable>,
    /// Repair suggestions ordered by likelihood of usefulness.
    suggestions: Vec<RepairSuggestion>,
    /// Invariant conjunct decomposition (if --spec was provided).
    #[serde(skip_serializing_if = "Option::is_none")]
    invariant_conjuncts: Option<Vec<String>>,
    /// Next disjunct decomposition (if --spec was provided).
    #[serde(skip_serializing_if = "Option::is_none")]
    next_disjuncts: Option<Vec<String>>,
}

/// A variable that changed in the violating step.
#[derive(Debug, Serialize)]
struct VariableChange {
    name: String,
    #[serde(serialize_with = "serialize_json_value")]
    from: JsonValue,
    #[serde(serialize_with = "serialize_json_value")]
    to: JsonValue,
    /// Human-readable description of the change.
    description: String,
}

/// A variable that was unchanged in the violating step.
#[derive(Debug, Serialize)]
struct UnchangedVariable {
    name: String,
    #[serde(serialize_with = "serialize_json_value")]
    value: JsonValue,
}

/// A single repair suggestion.
#[derive(Debug, Serialize)]
struct RepairSuggestion {
    /// Unique identifier for the suggestion (1-based).
    id: usize,
    /// Category of the suggestion.
    category: SuggestionCategory,
    /// One-line summary.
    summary: String,
    /// Detailed explanation.
    detail: String,
    /// Confidence level (high, medium, low).
    confidence: Confidence,
}

/// Category of repair suggestion.
#[derive(Debug, Clone, Copy, Serialize)]
#[serde(rename_all = "snake_case")]
enum SuggestionCategory {
    /// Revert a variable change.
    RevertVariable,
    /// Constrain the action's guard.
    ConstrainGuard,
    /// Strengthen the action's effect.
    StrengthenEffect,
    /// General invariant analysis.
    InvariantStructure,
    /// Action identification.
    ActionAnalysis,
}

/// Confidence level for a suggestion.
#[derive(Debug, Clone, Copy, Serialize)]
#[serde(rename_all = "snake_case")]
enum Confidence {
    High,
    Medium,
    Low,
}

// ---------------------------------------------------------------------------
// Analysis builder
// ---------------------------------------------------------------------------

/// Build the full repair analysis from the counterexample trace.
fn build_repair_analysis(
    output: &JsonOutput,
    ce: &CounterexampleInfo,
    config: &RepairConfig,
) -> Result<RepairAnalysis> {
    let trace_length = ce.states.len();
    let violating_step = if trace_length > 0 {
        ce.states.last().map(|s| s.index).unwrap_or(trace_length)
    } else {
        0
    };

    // Identify the violated invariant.
    let violated_invariant = config
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

    // Compute variable changes for the final transition.
    let (changed_variables, unchanged_variables) = if trace_length >= 2 {
        let prev = &ce.states[trace_length - 2];
        let curr = &ce.states[trace_length - 1];
        compute_changes(prev, curr)
    } else if trace_length == 1 {
        // Single-state trace: violation in the initial state.
        let state = &ce.states[0];
        let unchanged: Vec<UnchangedVariable> = sorted_var_names(&state.variables)
            .into_iter()
            .map(|name| UnchangedVariable {
                value: state.variables[&name].clone(),
                name,
            })
            .collect();
        (Vec::new(), unchanged)
    } else {
        (Vec::new(), Vec::new())
    };

    // Identify the violating action.
    let violating_action = if trace_length >= 2 {
        let last = &ce.states[trace_length - 1];
        if last.action.action_type == "initial" {
            None
        } else {
            Some(last.action.name.clone())
        }
    } else {
        None
    };

    // Optional: parse spec for invariant conjuncts and Next disjuncts.
    let (invariant_conjuncts, next_disjuncts) =
        analyze_spec_structure(output, config, violated_invariant.as_deref())?;

    // Generate repair suggestions.
    let suggestions = generate_suggestions(
        &changed_variables,
        &unchanged_variables,
        violating_action.as_deref(),
        invariant_conjuncts.as_deref(),
        next_disjuncts.as_deref(),
        trace_length,
        config.max_suggestions,
    );

    Ok(RepairAnalysis {
        trace_length,
        violating_step,
        violated_invariant,
        error_message: output.result.error_message.clone(),
        violating_action,
        changed_variables,
        unchanged_variables,
        suggestions,
        invariant_conjuncts: invariant_conjuncts.map(|v| v.to_vec()),
        next_disjuncts: next_disjuncts.map(|v| v.to_vec()),
    })
}

/// Compute changed and unchanged variables between two states.
fn compute_changes(
    prev: &StateInfo,
    curr: &StateInfo,
) -> (Vec<VariableChange>, Vec<UnchangedVariable>) {
    let mut changed = Vec::new();
    let mut unchanged = Vec::new();

    // If the JSON already has diff_from_previous, use it.
    if let Some(diff) = &curr.diff_from_previous {
        for (name, change) in &diff.changed {
            changed.push(VariableChange {
                description: describe_change(&change.from, &change.to),
                name: name.clone(),
                from: change.from.clone(),
                to: change.to.clone(),
            });
        }
        // Unchanged = all variables NOT in the diff.
        for name in sorted_var_names(&curr.variables) {
            if !diff.changed.contains_key(&name) {
                unchanged.push(UnchangedVariable {
                    value: curr.variables[&name].clone(),
                    name,
                });
            }
        }
        changed.sort_by(|a, b| a.name.cmp(&b.name));
        return (changed, unchanged);
    }

    // Otherwise compute manually.
    for name in sorted_var_names(&curr.variables) {
        let curr_val = &curr.variables[&name];
        match prev.variables.get(&name) {
            Some(prev_val) if prev_val != curr_val => {
                changed.push(VariableChange {
                    description: describe_change(prev_val, curr_val),
                    name,
                    from: prev_val.clone(),
                    to: curr_val.clone(),
                });
            }
            Some(_) => {
                unchanged.push(UnchangedVariable {
                    value: curr_val.clone(),
                    name,
                });
            }
            None => {
                changed.push(VariableChange {
                    description: "newly introduced variable".to_string(),
                    name,
                    from: JsonValue::Undefined,
                    to: curr_val.clone(),
                });
            }
        }
    }

    // Variables removed in the current state.
    for name in sorted_var_names(&prev.variables) {
        if !curr.variables.contains_key(&name) {
            let from = prev.variables[&name].clone();
            changed.push(VariableChange {
                description: "variable removed".to_string(),
                name,
                from,
                to: JsonValue::Undefined,
            });
        }
    }

    (changed, unchanged)
}

/// Produce a human-readable description of how a value changed.
fn describe_change(from: &JsonValue, to: &JsonValue) -> String {
    match (from, to) {
        (JsonValue::Int(a), JsonValue::Int(b)) => {
            let delta = b - a;
            if delta > 0 {
                format!("incremented by {delta} ({a} -> {b})")
            } else {
                format!("decremented by {} ({a} -> {b})", -delta)
            }
        }
        (JsonValue::Bool(a), JsonValue::Bool(b)) => {
            format!("toggled from {} to {}", bool_str(*a), bool_str(*b))
        }
        (JsonValue::Set(a), JsonValue::Set(b)) => {
            let a_len = a.len();
            let b_len = b.len();
            if b_len > a_len {
                format!(
                    "set grew from {} to {} element{}",
                    a_len,
                    b_len,
                    if b_len == 1 { "" } else { "s" }
                )
            } else if b_len < a_len {
                format!(
                    "set shrank from {} to {} element{}",
                    a_len,
                    b_len,
                    if b_len == 1 { "" } else { "s" }
                )
            } else {
                "set elements changed (same cardinality)".to_string()
            }
        }
        (JsonValue::Seq(a), JsonValue::Seq(b)) => {
            let a_len = a.len();
            let b_len = b.len();
            if b_len > a_len {
                format!("sequence grew from length {} to {}", a_len, b_len)
            } else if b_len < a_len {
                format!("sequence shrank from length {} to {}", a_len, b_len)
            } else {
                "sequence elements changed (same length)".to_string()
            }
        }
        (JsonValue::Record(_), JsonValue::Record(_)) => "record fields changed".to_string(),
        (JsonValue::Function { .. }, JsonValue::Function { .. }) => {
            "function mapping changed".to_string()
        }
        (JsonValue::String(a), JsonValue::String(b)) => {
            format!("string changed from \"{a}\" to \"{b}\"")
        }
        (JsonValue::ModelValue(a), JsonValue::ModelValue(b)) => {
            format!("model value changed from {a} to {b}")
        }
        _ => {
            format!(
                "changed from {} to {}",
                format_json_value(from),
                format_json_value(to)
            )
        }
    }
}

fn bool_str(b: bool) -> &'static str {
    if b {
        "TRUE"
    } else {
        "FALSE"
    }
}

/// Return variable names from a variables map, sorted alphabetically.
fn sorted_var_names(variables: &HashMap<String, JsonValue>) -> Vec<String> {
    let mut names: Vec<String> = variables.keys().cloned().collect();
    names.sort();
    names
}

// ---------------------------------------------------------------------------
// Spec structure analysis (optional, when --spec is provided)
// ---------------------------------------------------------------------------

/// Analyze the TLA+ spec to extract invariant conjuncts and Next disjuncts.
///
/// Returns `(invariant_conjuncts, next_disjuncts)`.
fn analyze_spec_structure(
    output: &JsonOutput,
    config: &RepairConfig,
    violated_invariant: Option<&str>,
) -> Result<(Option<Vec<String>>, Option<Vec<String>>)> {
    let spec_file = match &config.spec_file {
        Some(f) => f,
        None => return Ok((None, None)),
    };

    let source = std::fs::read_to_string(spec_file)
        .with_context(|| format!("Failed to read spec file: {}", spec_file.display()))?;

    let tree = tla_core::parse_to_syntax_tree(&source);
    let lower_result = tla_core::lower(tla_core::FileId(0), &tree);
    if !lower_result.errors.is_empty() {
        // Cannot analyze, but that is not fatal for the repair command.
        return Ok((None, None));
    }

    let module = match &lower_result.module {
        Some(m) => m,
        None => return Ok((None, None)),
    };

    // Extract invariant conjuncts.
    let inv_name = violated_invariant
        .map(String::from)
        .or_else(|| output.specification.invariants.first().cloned());

    let invariant_conjuncts = inv_name
        .as_deref()
        .map(|name| extract_expressions_from_operator(module, name, ExprKind::Conjuncts))
        .filter(|v| !v.is_empty());

    // Extract Next disjuncts.
    let next_name = output.specification.next.as_deref().or(Some("Next"));

    let next_disjuncts = next_name
        .map(|name| extract_expressions_from_operator(module, name, ExprKind::Disjuncts))
        .filter(|v| !v.is_empty());

    Ok((invariant_conjuncts, next_disjuncts))
}

/// What kind of sub-expressions to extract.
enum ExprKind {
    Conjuncts,
    Disjuncts,
}

/// Find an operator in the module and extract its conjunct or disjunct sub-expressions.
fn extract_expressions_from_operator(
    module: &tla_core::ast::Module,
    operator_name: &str,
    kind: ExprKind,
) -> Vec<String> {
    for unit in &module.units {
        if let tla_core::ast::Unit::Operator(def) = &unit.node {
            if def.name.node == operator_name {
                return match kind {
                    ExprKind::Conjuncts => extract_conjuncts(&def.body.node),
                    ExprKind::Disjuncts => extract_disjuncts(&def.body.node),
                };
            }
        }
    }
    Vec::new()
}

/// Recursively extract conjuncts from `A /\ B /\ C`.
fn extract_conjuncts(expr: &tla_core::ast::Expr) -> Vec<String> {
    match expr {
        tla_core::ast::Expr::And(lhs, rhs) => {
            let mut result = extract_conjuncts(&lhs.node);
            result.extend(extract_conjuncts(&rhs.node));
            result
        }
        other => vec![tla_core::pretty_expr(other)],
    }
}

/// Recursively extract disjuncts from `A \/ B \/ C`.
fn extract_disjuncts(expr: &tla_core::ast::Expr) -> Vec<String> {
    match expr {
        tla_core::ast::Expr::Or(lhs, rhs) => {
            let mut result = extract_disjuncts(&lhs.node);
            result.extend(extract_disjuncts(&rhs.node));
            result
        }
        other => vec![tla_core::pretty_expr(other)],
    }
}

// ---------------------------------------------------------------------------
// Suggestion generation
// ---------------------------------------------------------------------------

/// Generate repair suggestions based on the analysis.
fn generate_suggestions(
    changed: &[VariableChange],
    _unchanged: &[UnchangedVariable],
    violating_action: Option<&str>,
    invariant_conjuncts: Option<&[String]>,
    next_disjuncts: Option<&[String]>,
    trace_length: usize,
    max_suggestions: usize,
) -> Vec<RepairSuggestion> {
    let mut suggestions = Vec::new();
    let mut id = 1;

    // Suggestion: single-state violation (initial state).
    if trace_length <= 1 && changed.is_empty() {
        suggestions.push(RepairSuggestion {
            id,
            category: SuggestionCategory::InvariantStructure,
            summary: "Invariant violated in the initial state (Init)".to_string(),
            detail: "The invariant does not hold for at least one initial state. \
                     Check the Init predicate to ensure it establishes the invariant. \
                     Either strengthen Init to exclude the violating state or weaken \
                     the invariant to accept it."
                .to_string(),
            confidence: Confidence::High,
        });
        id += 1;
    }

    // Suggestion: revert each changed variable.
    for var in changed {
        if id > max_suggestions {
            break;
        }
        suggestions.push(RepairSuggestion {
            id,
            category: SuggestionCategory::RevertVariable,
            summary: format!(
                "Revert '{}': keep value at {} instead of {}",
                var.name,
                format_json_value(&var.from),
                format_json_value(&var.to),
            ),
            detail: format!(
                "Variable '{}' changed from {} to {} in the violating step. \
                 If the invariant held in the previous state, reverting this change \
                 (keeping {} = {}) may restore the invariant. Consider adding a guard \
                 to the action that prevents this transition when the invariant would \
                 be violated.",
                var.name,
                format_json_value(&var.from),
                format_json_value(&var.to),
                var.name,
                format_json_value(&var.from),
            ),
            confidence: if changed.len() == 1 {
                Confidence::High
            } else {
                Confidence::Medium
            },
        });
        id += 1;
    }

    // Suggestion: constrain the violating action's guard.
    if let Some(action) = violating_action {
        if id <= max_suggestions {
            let guard_detail = if changed.len() == 1 {
                format!(
                    "Action '{}' changed '{}' in a way that violated the invariant. \
                     Add a precondition to '{}' that checks the invariant would still \
                     hold after the update. For example, add a conjunct to the action's \
                     guard: {action} == ... /\\ <new_guard> /\\ ...",
                    action, changed[0].name, action,
                )
            } else {
                let var_list: Vec<&str> = changed.iter().map(|v| v.name.as_str()).collect();
                format!(
                    "Action '{}' changed variables [{}] in a way that violated the \
                     invariant. Add a precondition that prevents this combination of \
                     changes. Consider strengthening the guard of '{}' to exclude \
                     states where these updates would break the invariant.",
                    action,
                    var_list.join(", "),
                    action,
                )
            };
            suggestions.push(RepairSuggestion {
                id,
                category: SuggestionCategory::ConstrainGuard,
                summary: format!("Add guard to action '{action}' to prevent this transition"),
                detail: guard_detail,
                confidence: Confidence::High,
            });
            id += 1;
        }
    }

    // Suggestion: strengthen the effect (constrain the primed variables).
    if !changed.is_empty() {
        if let Some(action) = violating_action {
            if id <= max_suggestions {
                suggestions.push(RepairSuggestion {
                    id,
                    category: SuggestionCategory::StrengthenEffect,
                    summary: format!("Constrain the effect of action '{action}'"),
                    detail: format!(
                        "Instead of adding a guard, you can constrain what values the \
                         primed variables can take. For example, if '{}' is assigned a \
                         value that violates the invariant, constrain the assignment to \
                         only produce invariant-preserving values. This is sometimes \
                         more natural than a guard when the action must remain enabled.",
                        changed
                            .iter()
                            .map(|v| format!("{}'", v.name))
                            .collect::<Vec<_>>()
                            .join(", "),
                    ),
                    confidence: Confidence::Medium,
                });
                id += 1;
            }
        }
    }

    // Suggestion: invariant conjunct analysis.
    if let Some(conjuncts) = invariant_conjuncts {
        if id <= max_suggestions && conjuncts.len() > 1 {
            let conjunct_list = conjuncts
                .iter()
                .enumerate()
                .map(|(i, c)| format!("  {}. {}", i + 1, c))
                .collect::<Vec<_>>()
                .join("\n");
            suggestions.push(RepairSuggestion {
                id,
                category: SuggestionCategory::InvariantStructure,
                summary: format!(
                    "Invariant has {} conjuncts -- identify which one fails",
                    conjuncts.len()
                ),
                detail: format!(
                    "The invariant is a conjunction of {} sub-expressions. Evaluate \
                     each against the violating state to identify which conjunct(s) \
                     fail:\n{}\n\nFocus the repair on the failing conjunct(s).",
                    conjuncts.len(),
                    conjunct_list,
                ),
                confidence: Confidence::Medium,
            });
            id += 1;
        }
    }

    // Suggestion: identify which Next disjunct was active.
    if let Some(disjuncts) = next_disjuncts {
        if id <= max_suggestions && disjuncts.len() > 1 {
            let disjunct_display = if let Some(action) = violating_action {
                format!(
                    "The violating action was '{}'. The Next operator has {} \
                     disjuncts. The repair should target the disjunct corresponding \
                     to '{}'.",
                    action,
                    disjuncts.len(),
                    action,
                )
            } else {
                let disjunct_list = disjuncts
                    .iter()
                    .enumerate()
                    .map(|(i, d)| format!("  {}. {}", i + 1, d))
                    .collect::<Vec<_>>()
                    .join("\n");
                format!(
                    "The Next operator has {} disjuncts:\n{}\n\nIdentify which \
                     disjunct was active in the violating step to target the repair.",
                    disjuncts.len(),
                    disjunct_list,
                )
            };
            suggestions.push(RepairSuggestion {
                id,
                category: SuggestionCategory::ActionAnalysis,
                summary: format!(
                    "Next has {} disjuncts -- target the responsible action",
                    disjuncts.len()
                ),
                detail: disjunct_display,
                confidence: Confidence::Low,
            });
            // id += 1; // not needed, last usage
        }
    }

    suggestions.truncate(max_suggestions);
    suggestions
}

// ---------------------------------------------------------------------------
// Human-readable output
// ---------------------------------------------------------------------------

/// Print the repair analysis in human-readable format.
fn print_human_repair(analysis: &RepairAnalysis) {
    println!("=== Repair Analysis ===");
    println!();

    // Summary
    if let Some(inv) = &analysis.violated_invariant {
        println!("Violated invariant: {inv}");
    }
    if let Some(msg) = &analysis.error_message {
        println!("Error: {msg}");
    }
    println!(
        "Trace length: {} state{}",
        analysis.trace_length,
        plural(analysis.trace_length)
    );
    println!("Violating step: {}", analysis.violating_step);
    if let Some(action) = &analysis.violating_action {
        println!("Violating action: {action}");
    }
    println!();

    // Changed variables
    if analysis.changed_variables.is_empty() {
        if analysis.trace_length <= 1 {
            println!("--- Initial State Violation ---");
            println!("The invariant was violated in the initial state (no transitions taken).");
            println!();
            if !analysis.unchanged_variables.is_empty() {
                println!("State variables:");
                for var in &analysis.unchanged_variables {
                    println!("  /\\ {} = {}", var.name, format_json_value(&var.value));
                }
                println!();
            }
        } else {
            println!("--- Stuttering Step ---");
            println!("No variables changed in the violating step (stuttering transition).");
            println!();
        }
    } else {
        println!(
            "--- Variables Changed in Violating Step ({}) ---",
            analysis.changed_variables.len()
        );
        println!();
        for var in &analysis.changed_variables {
            println!(
                "  {} : {} -> {}",
                var.name,
                format_json_value(&var.from),
                format_json_value(&var.to),
            );
            println!("         ({})", var.description);
        }
        println!();

        if !analysis.unchanged_variables.is_empty() {
            println!(
                "--- Unchanged Variables ({}) ---",
                analysis.unchanged_variables.len()
            );
            for var in &analysis.unchanged_variables {
                println!("  /\\ {} = {}", var.name, format_json_value(&var.value));
            }
            println!();
        }
    }

    // Invariant conjuncts
    if let Some(conjuncts) = &analysis.invariant_conjuncts {
        println!("--- Invariant Conjuncts ---");
        println!();
        for (i, conjunct) in conjuncts.iter().enumerate() {
            println!("  {}. {}", i + 1, conjunct);
        }
        println!();
    }

    // Next disjuncts
    if let Some(disjuncts) = &analysis.next_disjuncts {
        println!("--- Next Disjuncts ---");
        println!();
        for (i, disjunct) in disjuncts.iter().enumerate() {
            println!("  {}. {}", i + 1, disjunct);
        }
        println!();
    }

    // Suggestions
    if analysis.suggestions.is_empty() {
        println!("No repair suggestions available.");
    } else {
        println!(
            "=== Repair Suggestions ({}) ===",
            analysis.suggestions.len()
        );
        println!();
        for suggestion in &analysis.suggestions {
            let confidence_tag = match suggestion.confidence {
                Confidence::High => "[HIGH]",
                Confidence::Medium => "[MEDIUM]",
                Confidence::Low => "[LOW]",
            };
            println!(
                "{}. {} {}",
                suggestion.id, confidence_tag, suggestion.summary
            );
            println!();
            // Indent the detail text.
            for line in suggestion.detail.lines() {
                println!("   {line}");
            }
            println!();
        }
    }
}

fn plural(n: usize) -> &'static str {
    if n == 1 {
        ""
    } else {
        "s"
    }
}

// ---------------------------------------------------------------------------
// Value formatting
// ---------------------------------------------------------------------------

/// Format a `JsonValue` for human-readable display using TLA+ notation.
fn format_json_value(value: &JsonValue) -> String {
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

// ---------------------------------------------------------------------------
// Serde helpers
// ---------------------------------------------------------------------------

/// Serialize a `JsonValue` to a serde_json::Value for JSON output.
fn serialize_json_value<S>(value: &JsonValue, serializer: S) -> std::result::Result<S::Ok, S::Error>
where
    S: serde::Serializer,
{
    let serde_val = json_value_to_serde(value);
    serde_val.serialize(serializer)
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

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use tla_check::JsonOutput;

    fn make_test_json_output() -> JsonOutput {
        let json_str = r#"{
            "version": "1.3",
            "tool": "tla2",
            "timestamp": "2026-03-30T00:00:00Z",
            "input": {
                "spec_file": "Counter.tla",
                "module": "Counter",
                "workers": 1
            },
            "specification": {
                "invariants": ["Safety"],
                "properties": [],
                "constants": {},
                "variables": ["count", "limit"]
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
                            "count": { "type": "int", "value": 0 },
                            "limit": { "type": "int", "value": 3 }
                        }
                    },
                    {
                        "index": 2,
                        "action": { "name": "Increment", "type": "next" },
                        "variables": {
                            "count": { "type": "int", "value": 2 },
                            "limit": { "type": "int", "value": 3 }
                        }
                    },
                    {
                        "index": 3,
                        "action": { "name": "Increment", "type": "next" },
                        "variables": {
                            "count": { "type": "int", "value": 4 },
                            "limit": { "type": "int", "value": 3 }
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
    fn test_repair_analysis_identifies_changed_variables() {
        let output = make_test_json_output();
        let ce = output.counterexample.as_ref().unwrap();
        let config = RepairConfig {
            trace_file: PathBuf::from("test.json"),
            spec_file: None,
            config_file: None,
            invariant: None,
            max_suggestions: 5,
            format: RepairFormat::Human,
        };
        let analysis = build_repair_analysis(&output, ce, &config).unwrap();

        assert_eq!(analysis.trace_length, 3);
        assert_eq!(analysis.violating_step, 3);
        assert_eq!(analysis.violated_invariant.as_deref(), Some("Safety"));
        assert_eq!(analysis.violating_action.as_deref(), Some("Increment"));

        // Only `count` changed in the last step (2 -> 4), `limit` stayed at 3.
        assert_eq!(analysis.changed_variables.len(), 1);
        assert_eq!(analysis.changed_variables[0].name, "count");
        assert_eq!(analysis.changed_variables[0].from, JsonValue::Int(2));
        assert_eq!(analysis.changed_variables[0].to, JsonValue::Int(4));

        assert_eq!(analysis.unchanged_variables.len(), 1);
        assert_eq!(analysis.unchanged_variables[0].name, "limit");
    }

    #[test]
    fn test_repair_suggestions_generated() {
        let output = make_test_json_output();
        let ce = output.counterexample.as_ref().unwrap();
        let config = RepairConfig {
            trace_file: PathBuf::from("test.json"),
            spec_file: None,
            config_file: None,
            invariant: None,
            max_suggestions: 5,
            format: RepairFormat::Human,
        };
        let analysis = build_repair_analysis(&output, ce, &config).unwrap();

        assert!(!analysis.suggestions.is_empty());
        // First suggestion should be a revert of the changed variable.
        assert!(matches!(
            analysis.suggestions[0].category,
            SuggestionCategory::RevertVariable
        ));
        assert!(analysis.suggestions[0].summary.contains("count"));

        // There should be a ConstrainGuard suggestion for the Increment action.
        let has_guard_suggestion = analysis
            .suggestions
            .iter()
            .any(|s| matches!(s.category, SuggestionCategory::ConstrainGuard));
        assert!(has_guard_suggestion);
    }

    #[test]
    fn test_repair_max_suggestions_respected() {
        let output = make_test_json_output();
        let ce = output.counterexample.as_ref().unwrap();
        let config = RepairConfig {
            trace_file: PathBuf::from("test.json"),
            spec_file: None,
            config_file: None,
            invariant: None,
            max_suggestions: 2,
            format: RepairFormat::Human,
        };
        let analysis = build_repair_analysis(&output, ce, &config).unwrap();
        assert!(analysis.suggestions.len() <= 2);
    }

    #[test]
    fn test_describe_change_int() {
        assert_eq!(
            describe_change(&JsonValue::Int(2), &JsonValue::Int(5)),
            "incremented by 3 (2 -> 5)"
        );
        assert_eq!(
            describe_change(&JsonValue::Int(5), &JsonValue::Int(2)),
            "decremented by 3 (5 -> 2)"
        );
    }

    #[test]
    fn test_describe_change_bool() {
        assert_eq!(
            describe_change(&JsonValue::Bool(true), &JsonValue::Bool(false)),
            "toggled from TRUE to FALSE"
        );
    }

    #[test]
    fn test_describe_change_set() {
        let small = JsonValue::Set(vec![JsonValue::Int(1)]);
        let big = JsonValue::Set(vec![
            JsonValue::Int(1),
            JsonValue::Int(2),
            JsonValue::Int(3),
        ]);
        assert_eq!(
            describe_change(&small, &big),
            "set grew from 1 to 3 elements"
        );
        assert_eq!(
            describe_change(&big, &small),
            "set shrank from 3 to 1 element"
        );
    }

    #[test]
    fn test_json_output_serialization() {
        let output = make_test_json_output();
        let ce = output.counterexample.as_ref().unwrap();
        let config = RepairConfig {
            trace_file: PathBuf::from("test.json"),
            spec_file: None,
            config_file: None,
            invariant: None,
            max_suggestions: 5,
            format: RepairFormat::Json,
        };
        let analysis = build_repair_analysis(&output, ce, &config).unwrap();
        let json = serde_json::to_string_pretty(&analysis).unwrap();
        assert!(json.contains("\"trace_length\": 3"));
        assert!(json.contains("\"violating_step\": 3"));
        assert!(json.contains("\"count\""));
    }

    #[test]
    fn test_single_state_violation() {
        let json_str = r#"{
            "version": "1.3",
            "tool": "tla2",
            "timestamp": "2026-03-30T00:00:00Z",
            "input": {
                "spec_file": "Bad.tla",
                "module": "Bad",
                "workers": 1
            },
            "specification": {
                "invariants": ["TypeOK"],
                "properties": [],
                "constants": {},
                "variables": ["x"]
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
                "error_message": "Invariant TypeOK is violated.",
                "violated_property": {
                    "name": "TypeOK",
                    "type": "invariant"
                }
            },
            "counterexample": {
                "length": 1,
                "states": [
                    {
                        "index": 1,
                        "action": { "name": "Initial predicate", "type": "initial" },
                        "variables": {
                            "x": { "type": "int", "value": -1 }
                        }
                    }
                ]
            },
            "statistics": {
                "states_found": 1,
                "states_initial": 1,
                "transitions": 0,
                "time_seconds": 0.001
            },
            "diagnostics": {
                "warnings": [],
                "info": []
            }
        }"#;
        let output: JsonOutput = serde_json::from_str(json_str).unwrap();
        let ce = output.counterexample.as_ref().unwrap();
        let config = RepairConfig {
            trace_file: PathBuf::from("test.json"),
            spec_file: None,
            config_file: None,
            invariant: None,
            max_suggestions: 5,
            format: RepairFormat::Human,
        };
        let analysis = build_repair_analysis(&output, ce, &config).unwrap();
        assert_eq!(analysis.trace_length, 1);
        assert!(analysis.changed_variables.is_empty());
        assert_eq!(analysis.unchanged_variables.len(), 1);
        assert!(analysis
            .suggestions
            .iter()
            .any(|s| matches!(s.category, SuggestionCategory::InvariantStructure)));
    }
}
