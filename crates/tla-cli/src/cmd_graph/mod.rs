// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 graph` -- state transition graph visualization from saved JSON output.
//!
//! Reads a JSON output file produced by `tla2 check --output json` and builds
//! a state transition graph from the counterexample trace:
//!
//! - Each state is a node (labeled with step number and key variable values)
//! - Each transition is an edge (labeled with action name if available)
//! - Error/violating states highlighted in red
//! - Initial state highlighted in green
//!
//! Output formats:
//! - **DOT** (default): Graphviz DOT with proper node shapes, colors, edge labels
//! - **Mermaid**: Mermaid.js flowchart syntax for GitHub markdown rendering
//! - **JSON**: Node/edge adjacency list for programmatic consumption

use std::collections::HashMap;
use std::path::Path;

use anyhow::{Context, Result};
use serde::Serialize;
use tla_check::{JsonOutput, JsonValue};

use crate::cmd_explain::format_json_value;

/// Output format for the graph command.
#[derive(Clone, Copy, Debug)]
pub(crate) enum GraphOutputFormat {
    Dot,
    Mermaid,
    Json,
}

/// Run the graph command.
pub(crate) fn cmd_graph(
    trace_file: &Path,
    format: GraphOutputFormat,
    max_states: usize,
    highlight_error: bool,
    cluster_by_action: bool,
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
    let graph = build_graph(ce, &output, max_states, highlight_error);

    match format {
        GraphOutputFormat::Dot => {
            println!("{}", render_dot(&graph, cluster_by_action));
        }
        GraphOutputFormat::Mermaid => {
            println!("{}", render_mermaid(&graph, cluster_by_action));
        }
        GraphOutputFormat::Json => {
            let json_graph = build_json_graph(&graph);
            println!(
                "{}",
                serde_json::to_string_pretty(&json_graph)
                    .context("Failed to serialize graph to JSON")?
            );
        }
    }

    Ok(())
}

/// A node in the state transition graph.
struct GraphNode {
    /// Step index (1-based, from the trace).
    index: usize,
    /// Compact label: variable=value pairs.
    label: String,
    /// Action that produced this state.
    action_name: String,
    /// Whether this is the initial state.
    is_initial: bool,
    /// Whether this is an error/violating state.
    is_error: bool,
    /// Whether this is a truncation placeholder.
    is_truncated: bool,
}

/// An edge in the state transition graph.
struct GraphEdge {
    from_index: usize,
    to_index: usize,
    action_label: String,
}

/// The complete graph structure.
struct Graph {
    nodes: Vec<GraphNode>,
    edges: Vec<GraphEdge>,
    total_states: usize,
    truncated: bool,
}

/// Build a graph from the counterexample trace.
fn build_graph(
    ce: &tla_check::CounterexampleInfo,
    output: &JsonOutput,
    max_states: usize,
    highlight_error: bool,
) -> Graph {
    let total_states = ce.states.len();
    let effective_limit = if max_states == 0 {
        total_states
    } else {
        max_states
    };
    let truncated = total_states > effective_limit;
    let states_to_render = total_states.min(effective_limit);

    let has_error = output.result.status == "error";

    let mut nodes = Vec::with_capacity(states_to_render + usize::from(truncated));
    let mut edges = Vec::with_capacity(states_to_render.saturating_sub(1));

    for (i, state) in ce.states.iter().take(states_to_render).enumerate() {
        let is_initial = state.action.action_type == "initial";
        let is_last = i == total_states - 1;
        let is_error = highlight_error && has_error && is_last && i < states_to_render;

        let label = build_compact_label(&state.variables);

        nodes.push(GraphNode {
            index: state.index,
            label,
            action_name: state.action.name.clone(),
            is_initial,
            is_error,
            is_truncated: false,
        });

        if i > 0 {
            edges.push(GraphEdge {
                from_index: ce.states[i - 1].index,
                to_index: state.index,
                action_label: state.action.name.clone(),
            });
        }
    }

    if truncated {
        let remaining = total_states - states_to_render;
        nodes.push(GraphNode {
            index: 0,
            label: format!(
                "... {remaining} more state{}",
                if remaining == 1 { "" } else { "s" }
            ),
            action_name: String::new(),
            is_initial: false,
            is_error: false,
            is_truncated: true,
        });
        if let Some(last_rendered) = ce.states.get(states_to_render - 1) {
            edges.push(GraphEdge {
                from_index: last_rendered.index,
                to_index: 0,
                action_label: "...".to_string(),
            });
        }
    }

    Graph {
        nodes,
        edges,
        total_states,
        truncated,
    }
}

/// Build a compact label from variable=value pairs.
///
/// Truncates long values to keep the label readable.
fn build_compact_label(variables: &HashMap<String, JsonValue>) -> String {
    let mut sorted: Vec<_> = variables.iter().collect();
    sorted.sort_by_key(|(k, _)| k.as_str());

    let mut parts = Vec::with_capacity(sorted.len());
    for (name, value) in &sorted {
        let formatted = format_json_value(value);
        let truncated = truncate_value(&formatted, 40);
        parts.push(format!("{name}={truncated}"));
    }
    parts.join("\\n")
}

/// Truncate a value string to at most `max_len` characters.
fn truncate_value(s: &str, max_len: usize) -> String {
    if s.len() <= max_len {
        s.to_string()
    } else {
        format!("{}...", &s[..max_len.saturating_sub(3)])
    }
}

// ---------------------------------------------------------------------------
// DOT output
// ---------------------------------------------------------------------------

/// Render the graph as Graphviz DOT.
fn render_dot(graph: &Graph, cluster_by_action: bool) -> String {
    let mut out = String::with_capacity(1024);
    out.push_str("digraph trace {\n");
    out.push_str("    rankdir=TB;\n");
    out.push_str("    node [shape=box, style=filled, fontname=\"Courier\", fontsize=10];\n");
    out.push_str("    edge [fontname=\"Helvetica\", fontsize=9];\n");
    out.push('\n');

    if cluster_by_action {
        render_dot_clustered(graph, &mut out);
    } else {
        render_dot_flat(graph, &mut out);
    }

    // Edges
    out.push('\n');
    for edge in &graph.edges {
        let from_id = node_id(edge.from_index);
        let to_id = node_id(edge.to_index);
        let label = escape_dot(&edge.action_label);
        out.push_str(&format!("    {from_id} -> {to_id} [label=\"{label}\"];\n"));
    }

    if graph.truncated {
        out.push_str(&format!(
            "\n    // Total states in trace: {}, showing first {}\n",
            graph.total_states,
            graph.nodes.len() - 1 // exclude the truncation placeholder
        ));
    }

    out.push_str("}\n");
    out
}

/// Render nodes without clustering.
fn render_dot_flat(graph: &Graph, out: &mut String) {
    for node in &graph.nodes {
        render_dot_node(node, out);
    }
}

/// Render nodes clustered by action name.
fn render_dot_clustered(graph: &Graph, out: &mut String) {
    // Group non-truncated nodes by action.
    let mut action_groups: HashMap<&str, Vec<&GraphNode>> = HashMap::new();
    let mut truncated_nodes = Vec::new();
    for node in &graph.nodes {
        if node.is_truncated {
            truncated_nodes.push(node);
        } else {
            action_groups
                .entry(&node.action_name)
                .or_default()
                .push(node);
        }
    }

    let mut sorted_actions: Vec<_> = action_groups.keys().copied().collect();
    sorted_actions.sort();

    for (i, action) in sorted_actions.iter().enumerate() {
        let nodes = &action_groups[action];
        let label = escape_dot(action);
        out.push_str(&format!("    subgraph cluster_{i} {{\n"));
        out.push_str(&format!("        label=\"{label}\";\n"));
        out.push_str("        style=dashed;\n");
        out.push_str("        color=grey;\n");
        for node in nodes {
            out.push_str("    ");
            render_dot_node(node, out);
        }
        out.push_str("    }\n\n");
    }

    for node in truncated_nodes {
        render_dot_node(node, out);
    }
}

/// Render a single DOT node definition.
fn render_dot_node(node: &GraphNode, out: &mut String) {
    let id = node_id(node.index);
    let label = if node.is_truncated {
        escape_dot(&node.label)
    } else {
        let step_label = format!("Step {}", node.index);
        format!("{}\\n{}", escape_dot(&step_label), escape_dot(&node.label))
    };

    let (fillcolor, fontcolor) = if node.is_truncated {
        ("\"#f0f0f0\"", "\"#666666\"")
    } else if node.is_error {
        ("\"#ffcccc\"", "\"#cc0000\"")
    } else if node.is_initial {
        ("\"#ccffcc\"", "\"#006600\"")
    } else {
        ("\"#e8e8ff\"", "\"#000000\"")
    };

    let shape = if node.is_truncated { "ellipse" } else { "box" };

    out.push_str(&format!(
        "    {id} [label=\"{label}\", fillcolor={fillcolor}, fontcolor={fontcolor}, shape={shape}];\n"
    ));
}

/// Generate a DOT-safe node identifier from the state index.
fn node_id(index: usize) -> String {
    if index == 0 {
        "truncated".to_string()
    } else {
        format!("s{index}")
    }
}

/// Escape special characters for DOT label strings.
fn escape_dot(s: &str) -> String {
    s.replace('\\', "\\\\")
        .replace('"', "\\\"")
        .replace('\n', "\\n")
}

// ---------------------------------------------------------------------------
// Mermaid output
// ---------------------------------------------------------------------------

/// Render the graph as Mermaid.js flowchart syntax.
fn render_mermaid(graph: &Graph, cluster_by_action: bool) -> String {
    let mut out = String::with_capacity(1024);
    out.push_str("flowchart TD\n");

    if cluster_by_action {
        render_mermaid_clustered(graph, &mut out);
    } else {
        render_mermaid_flat(graph, &mut out);
    }

    // Edges
    out.push('\n');
    for edge in &graph.edges {
        let from_id = mermaid_node_id(edge.from_index);
        let to_id = mermaid_node_id(edge.to_index);
        let label = escape_mermaid(&edge.action_label);
        out.push_str(&format!("    {from_id} -->|{label}| {to_id}\n"));
    }

    // Styling
    out.push('\n');
    for node in &graph.nodes {
        let id = mermaid_node_id(node.index);
        if node.is_truncated {
            out.push_str(&format!(
                "    style {id} fill:#f0f0f0,color:#666666,stroke-dasharray: 5 5\n"
            ));
        } else if node.is_error {
            out.push_str(&format!(
                "    style {id} fill:#ffcccc,color:#cc0000,stroke:#cc0000\n"
            ));
        } else if node.is_initial {
            out.push_str(&format!(
                "    style {id} fill:#ccffcc,color:#006600,stroke:#006600\n"
            ));
        }
    }

    if graph.truncated {
        out.push_str(&format!(
            "\n    %% Total states in trace: {}, showing first {}\n",
            graph.total_states,
            graph.nodes.len() - 1
        ));
    }

    out
}

/// Render Mermaid nodes without clustering.
fn render_mermaid_flat(graph: &Graph, out: &mut String) {
    for node in &graph.nodes {
        render_mermaid_node(node, out);
    }
}

/// Render Mermaid nodes clustered by action name.
fn render_mermaid_clustered(graph: &Graph, out: &mut String) {
    let mut action_groups: HashMap<&str, Vec<&GraphNode>> = HashMap::new();
    let mut truncated_nodes = Vec::new();
    for node in &graph.nodes {
        if node.is_truncated {
            truncated_nodes.push(node);
        } else {
            action_groups
                .entry(&node.action_name)
                .or_default()
                .push(node);
        }
    }

    let mut sorted_actions: Vec<_> = action_groups.keys().copied().collect();
    sorted_actions.sort();

    for action in &sorted_actions {
        let nodes = &action_groups[action];
        let label = escape_mermaid(action);
        out.push_str(&format!(
            "    subgraph sub_{} [\"{label}\"]\n",
            sanitize_mermaid_id(action)
        ));
        for node in nodes {
            out.push_str("    ");
            render_mermaid_node(node, out);
        }
        out.push_str("    end\n\n");
    }

    for node in truncated_nodes {
        render_mermaid_node(node, out);
    }
}

/// Render a single Mermaid node definition.
fn render_mermaid_node(node: &GraphNode, out: &mut String) {
    let id = mermaid_node_id(node.index);
    if node.is_truncated {
        let label = escape_mermaid(&node.label);
        out.push_str(&format!("    {id}((\"{label}\"))\n"));
    } else {
        // Use <br/> for line breaks inside Mermaid labels.
        let label_with_breaks = node.label.replace("\\n", "<br/>");
        let label = escape_mermaid(&format!("Step {}<br/>{}", node.index, label_with_breaks));
        out.push_str(&format!("    {id}[\"{label}\"]\n"));
    }
}

/// Generate a Mermaid-safe node identifier.
fn mermaid_node_id(index: usize) -> String {
    if index == 0 {
        "truncated".to_string()
    } else {
        format!("s{index}")
    }
}

/// Sanitize a string for use as a Mermaid subgraph ID.
fn sanitize_mermaid_id(s: &str) -> String {
    s.chars()
        .map(|c| {
            if c.is_alphanumeric() || c == '_' {
                c
            } else {
                '_'
            }
        })
        .collect()
}

/// Escape special characters for Mermaid labels.
fn escape_mermaid(s: &str) -> String {
    s.replace('"', "&quot;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
}

// ---------------------------------------------------------------------------
// JSON output
// ---------------------------------------------------------------------------

#[derive(Debug, Serialize)]
struct JsonGraph {
    version: String,
    total_states: usize,
    rendered_states: usize,
    truncated: bool,
    nodes: Vec<JsonGraphNode>,
    edges: Vec<JsonGraphEdge>,
}

#[derive(Debug, Serialize)]
struct JsonGraphNode {
    id: String,
    index: usize,
    label: String,
    action: String,
    is_initial: bool,
    is_error: bool,
    is_truncated: bool,
}

#[derive(Debug, Serialize)]
struct JsonGraphEdge {
    from: String,
    to: String,
    action: String,
}

fn build_json_graph(graph: &Graph) -> JsonGraph {
    let nodes = graph
        .nodes
        .iter()
        .map(|n| JsonGraphNode {
            id: node_id(n.index),
            index: n.index,
            label: n.label.replace("\\n", "\n"),
            action: n.action_name.clone(),
            is_initial: n.is_initial,
            is_error: n.is_error,
            is_truncated: n.is_truncated,
        })
        .collect();

    let edges = graph
        .edges
        .iter()
        .map(|e| JsonGraphEdge {
            from: node_id(e.from_index),
            to: node_id(e.to_index),
            action: e.action_label.clone(),
        })
        .collect();

    let rendered_states = graph.nodes.iter().filter(|n| !n.is_truncated).count();

    JsonGraph {
        version: "1.0".to_string(),
        total_states: graph.total_states,
        rendered_states,
        truncated: graph.truncated,
        nodes,
        edges,
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

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
    fn test_graph_builds_correct_node_count() {
        let output = make_test_json_output();
        let ce = output.counterexample.as_ref().unwrap();
        let graph = build_graph(ce, &output, 50, true);

        assert_eq!(graph.nodes.len(), 3);
        assert_eq!(graph.edges.len(), 2);
        assert!(!graph.truncated);
        assert_eq!(graph.total_states, 3);
    }

    #[test]
    fn test_graph_initial_and_error_flags() {
        let output = make_test_json_output();
        let ce = output.counterexample.as_ref().unwrap();
        let graph = build_graph(ce, &output, 50, true);

        assert!(graph.nodes[0].is_initial);
        assert!(!graph.nodes[0].is_error);
        assert!(!graph.nodes[1].is_initial);
        assert!(!graph.nodes[1].is_error);
        assert!(!graph.nodes[2].is_initial);
        assert!(graph.nodes[2].is_error);
    }

    #[test]
    fn test_graph_truncation() {
        let output = make_test_json_output();
        let ce = output.counterexample.as_ref().unwrap();
        let graph = build_graph(ce, &output, 2, true);

        // 2 rendered states + 1 truncation placeholder
        assert_eq!(graph.nodes.len(), 3);
        assert!(graph.truncated);
        assert!(graph.nodes[2].is_truncated);
        assert!(graph.nodes[2].label.contains("1 more state"));
    }

    #[test]
    fn test_graph_highlight_error_disabled() {
        let output = make_test_json_output();
        let ce = output.counterexample.as_ref().unwrap();
        let graph = build_graph(ce, &output, 50, false);

        // With highlight_error=false, no node should be marked as error.
        assert!(graph.nodes.iter().all(|n| !n.is_error));
    }

    #[test]
    fn test_graph_dot_output_contains_digraph() {
        let output = make_test_json_output();
        let ce = output.counterexample.as_ref().unwrap();
        let graph = build_graph(ce, &output, 50, true);

        let dot = render_dot(&graph, false);
        assert!(dot.starts_with("digraph trace {"));
        assert!(dot.contains("s1"));
        assert!(dot.contains("s2"));
        assert!(dot.contains("s3"));
        assert!(dot.contains("#ccffcc")); // initial state green
        assert!(dot.contains("#ffcccc")); // error state red
        assert!(dot.contains("Increment")); // edge label
    }

    #[test]
    fn test_graph_dot_clustered_output() {
        let output = make_test_json_output();
        let ce = output.counterexample.as_ref().unwrap();
        let graph = build_graph(ce, &output, 50, true);

        let dot = render_dot(&graph, true);
        assert!(dot.contains("subgraph cluster_"));
        assert!(dot.contains("Initial predicate"));
        assert!(dot.contains("Increment"));
    }

    #[test]
    fn test_graph_mermaid_output_contains_flowchart() {
        let output = make_test_json_output();
        let ce = output.counterexample.as_ref().unwrap();
        let graph = build_graph(ce, &output, 50, true);

        let mermaid = render_mermaid(&graph, false);
        assert!(mermaid.starts_with("flowchart TD"));
        assert!(mermaid.contains("s1"));
        assert!(mermaid.contains("s2"));
        assert!(mermaid.contains("s3"));
        assert!(mermaid.contains("-->|Increment|"));
        assert!(mermaid.contains("fill:#ccffcc")); // initial
        assert!(mermaid.contains("fill:#ffcccc")); // error
    }

    #[test]
    fn test_graph_json_output_structure() {
        let output = make_test_json_output();
        let ce = output.counterexample.as_ref().unwrap();
        let graph = build_graph(ce, &output, 50, true);

        let json_graph = build_json_graph(&graph);
        assert_eq!(json_graph.total_states, 3);
        assert_eq!(json_graph.rendered_states, 3);
        assert!(!json_graph.truncated);
        assert_eq!(json_graph.nodes.len(), 3);
        assert_eq!(json_graph.edges.len(), 2);

        assert!(json_graph.nodes[0].is_initial);
        assert!(json_graph.nodes[2].is_error);
        assert_eq!(json_graph.edges[0].from, "s1");
        assert_eq!(json_graph.edges[0].to, "s2");
        assert_eq!(json_graph.edges[0].action, "Increment");
    }

    #[test]
    fn test_graph_truncate_value_short() {
        assert_eq!(truncate_value("hello", 40), "hello");
    }

    #[test]
    fn test_graph_truncate_value_long() {
        let long_str = "a".repeat(50);
        let result = truncate_value(&long_str, 40);
        assert!(result.ends_with("..."));
        assert!(result.len() <= 40);
    }

    #[test]
    fn test_graph_escape_dot() {
        assert_eq!(escape_dot("hello\"world"), "hello\\\"world");
        assert_eq!(escape_dot("line\nnew"), "line\\nnew");
    }

    #[test]
    fn test_graph_escape_mermaid() {
        assert_eq!(escape_mermaid("a<b>c"), "a&lt;b&gt;c");
        assert_eq!(escape_mermaid("a\"b"), "a&quot;b");
    }
}
