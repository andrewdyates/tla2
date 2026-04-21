// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! GraphViz DOT format export for counterexample traces.

use crate::Trace;
use std::fmt::Write;

/// Convert a trace to GraphViz DOT format for visualization.
///
/// The DOT output creates a directed graph where:
/// - Each state is a node with variable values shown
/// - Each transition is an edge labeled with "Next" or "Init"
/// - For liveness violations, the cycle portion is highlighted
///
/// # Arguments
///
/// * `trace` - The counterexample trace to convert
/// * `loop_start` - Optional index where a liveness cycle begins
///
/// # Example output
///
/// ```dot
/// digraph trace {
///   rankdir=TB;
///   node [shape=record, fontname="Courier"];
///
///   s0 [label="State 1|x = 0\\ly = 0"];
///   s1 [label="State 2|x = 1\\ly = 0"];
///
///   s0 -> s1 [label="Next"];
/// }
/// ```
pub fn trace_to_dot(trace: &Trace, loop_start: Option<usize>) -> String {
    let mut dot = String::new();
    dot.push_str("digraph trace {\n");
    dot.push_str("  rankdir=TB;\n");
    dot.push_str("  node [shape=record, fontname=\"Courier\"];\n");
    dot.push_str("  edge [fontname=\"Helvetica\", fontsize=10];\n");
    dot.push('\n');

    // Generate nodes for each state
    for (i, state) in trace.states.iter().enumerate() {
        let state_num = i + 1;
        let fp = format!("{:08x}", state.fingerprint().0 & 0xFFFFFFFF);

        // Build variable list with proper escaping for DOT records
        let vars: Vec<String> = state
            .vars()
            .map(|(name, value)| {
                let value_str = format!("{}", value);
                // Escape special characters for DOT record labels
                let escaped = value_str
                    .replace('\\', "\\\\")
                    .replace('"', "\\\"")
                    .replace('{', "\\{")
                    .replace('}', "\\}")
                    .replace('|', "\\|")
                    .replace('<', "\\<")
                    .replace('>', "\\>");
                format!("{} = {}", name, escaped)
            })
            .collect();
        let vars_label = vars.join("\\l") + "\\l"; // Left-align each line

        // Determine node style based on position
        let style = if i == 0 {
            // Initial state: green border
            ", style=bold, color=green"
        } else if i == trace.states.len() - 1 && loop_start.is_none() {
            // Final state (error state): red border
            ", style=bold, color=red"
        } else if loop_start.is_some_and(|ls| i >= ls) {
            // Part of liveness cycle: blue border
            ", style=bold, color=blue"
        } else {
            ""
        };

        let _ = writeln!(
            dot,
            "  s{} [label=\"State {} ({})\\n|{}\"{}];",
            i, state_num, fp, vars_label, style
        );
    }

    dot.push('\n');

    // Generate edges between consecutive states
    for i in 0..trace.states.len().saturating_sub(1) {
        let edge_label = if i == 0 { "Init" } else { "Next" };

        // Determine edge style
        let style = if let Some(ls) = loop_start {
            if i >= ls {
                // Cycle edge: blue, bold
                ", style=bold, color=blue"
            } else {
                ""
            }
        } else {
            ""
        };

        let _ = writeln!(
            dot,
            "  s{} -> s{} [label=\"{}\"{}];",
            i,
            i + 1,
            edge_label,
            style
        );
    }

    // For liveness cycles, add back-edge to show the loop
    if let Some(ls) = loop_start {
        if trace.states.len() > ls {
            let last_idx = trace.states.len() - 1;
            let _ = writeln!(
                dot,
                "  s{} -> s{} [label=\"cycle\", style=dashed, color=blue, constraint=false];",
                last_idx, ls
            );
        }
    }

    dot.push_str("}\n");
    dot
}

/// Convert a combined liveness trace (prefix + cycle) to DOT format.
///
/// This is a convenience function for liveness violations where
/// the prefix and cycle are provided separately.
pub fn liveness_trace_to_dot(prefix: &Trace, cycle: &Trace) -> String {
    // Combine prefix and cycle into single trace
    let mut combined = prefix.clone();
    for state in &cycle.states {
        combined.states.push(state.clone());
    }
    trace_to_dot(&combined, Some(prefix.states.len()))
}
