// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Output formatters for dependency graph analysis.
//!
//! Supports three output formats:
//! - Tree: indented text tree showing the dependency hierarchy
//! - DOT: Graphviz DOT format for graph visualization
//! - JSON: structured data for tooling integration

use std::collections::BTreeSet;

use serde::Serialize;

use super::graph::{DepGraph, RootKind};

// ---------------------------------------------------------------------------
// Tree output
// ---------------------------------------------------------------------------

/// Emit a human-readable tree view of the dependency graph.
pub(crate) fn emit_tree(graph: &DepGraph, show_unused: bool, modules_only: bool) {
    println!("Module: {}", graph.module_name);

    // EXTENDS
    for (mod_name, extends) in &graph.extends {
        if mod_name == &graph.module_name {
            println!("  EXTENDS: {}", extends.join(", "));
        } else {
            println!("  {} EXTENDS: {}", mod_name, extends.join(", "));
        }
    }

    // INSTANCE
    for (mod_name, instances) in &graph.instances {
        for inst in instances {
            let prefix = if mod_name == &graph.module_name {
                String::new()
            } else {
                format!("{} ", mod_name)
            };
            let local_tag = if inst.is_local { "LOCAL " } else { "" };
            println!("  {}{}INSTANCE {}", prefix, local_tag, inst.target_module);
        }
    }

    if modules_only {
        println!();
        let mut all_modules: BTreeSet<&str> = BTreeSet::new();
        all_modules.insert(&graph.module_name);
        for extends in graph.extends.values() {
            for e in extends {
                all_modules.insert(e);
            }
        }
        for instances in graph.instances.values() {
            for inst in instances {
                all_modules.insert(&inst.target_module);
            }
        }
        println!("  Modules referenced: {}", all_modules.len());
        for m in &all_modules {
            println!("    {}", m);
        }
        return;
    }

    // Variables
    if !graph.variables.is_empty() {
        println!();
        println!("  Variables: {}", graph.variables.join(", "));
    }

    // Roots with their call trees
    if !graph.roots.is_empty() {
        println!();
        for root in &graph.roots {
            let kind_label = match root.kind {
                RootKind::Init => "init",
                RootKind::Next => "next",
                RootKind::Invariant => "invariant",
                RootKind::Property => "property",
            };
            println!("  {} ({})", root.name, kind_label);
            print_call_tree(graph, &root.name, "    ", &mut BTreeSet::new());
        }
    }

    // Variable usage summary
    if !graph.var_reads.is_empty() || !graph.var_writes.is_empty() {
        println!();
        println!("  Variable usage:");
        let mut all_ops: BTreeSet<&str> = BTreeSet::new();
        for op in graph.var_reads.keys() {
            all_ops.insert(op);
        }
        for op in graph.var_writes.keys() {
            all_ops.insert(op);
        }
        for op in &all_ops {
            let reads = graph
                .var_reads
                .get(*op)
                .map(|s| {
                    s.iter()
                        .map(|v| v.as_str())
                        .collect::<Vec<_>>()
                        .join(", ")
                })
                .unwrap_or_default();
            let writes = graph
                .var_writes
                .get(*op)
                .map(|s| {
                    s.iter()
                        .map(|v| format!("{}'", v))
                        .collect::<Vec<_>>()
                        .join(", ")
                })
                .unwrap_or_default();

            let mut usage_parts = Vec::new();
            if !reads.is_empty() {
                usage_parts.push(format!("reads: {}", reads));
            }
            if !writes.is_empty() {
                usage_parts.push(format!("writes: {}", writes));
            }
            if !usage_parts.is_empty() {
                println!("    {} -- {}", op, usage_parts.join("; "));
            }
        }
    }

    // Unreachable operators
    if show_unused {
        let unreachable = graph.unreachable_operators();
        if !unreachable.is_empty() {
            println!();
            println!("  Unreachable operators:");
            for (name, info) in &unreachable {
                let line = info.line_number(&graph.source);
                let line_info = if line > 0 {
                    format!(" (line {})", line)
                } else {
                    String::new()
                };
                println!("    {}{}", name, line_info);
            }
        }
    }

    // Cycles
    if !graph.cycles.is_empty() {
        println!();
        println!("  Circular dependencies:");
        for cycle in &graph.cycles {
            println!("    {} -> {}", cycle.join(" -> "), cycle[0]);
        }
    }
}

/// Print a call tree rooted at the given operator, with indentation.
fn print_call_tree(
    graph: &DepGraph,
    op: &str,
    indent: &str,
    visited: &mut BTreeSet<String>,
) {
    if let Some(callees) = graph.call_edges.get(op) {
        let callees_vec: Vec<&String> = callees.iter().collect();
        for (i, callee) in callees_vec.iter().enumerate() {
            let is_last = i == callees_vec.len() - 1;
            let connector = if is_last { "└── " } else { "├── " };
            let continuation = if is_last { "    " } else { "│   " };

            let module_suffix = graph
                .operators
                .get(callee.as_str())
                .filter(|info| info.module != graph.module_name)
                .map(|info| format!(" ({})", info.module))
                .unwrap_or_default();

            if visited.contains(*callee) {
                println!("{}{}{}{} [...]", indent, connector, callee, module_suffix);
            } else {
                println!("{}{}{}{}", indent, connector, callee, module_suffix);
                visited.insert((*callee).clone());
                let child_indent = format!("{}{}", indent, continuation);
                print_call_tree(graph, callee, &child_indent, visited);
                visited.remove(*callee);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// DOT output
// ---------------------------------------------------------------------------

/// Emit Graphviz DOT format.
pub(crate) fn emit_dot(graph: &DepGraph, modules_only: bool) {
    println!("digraph deps {{");
    println!("  rankdir=LR;");
    println!("  node [fontname=\"Helvetica\", fontsize=10];");
    println!("  edge [fontname=\"Helvetica\", fontsize=9];");
    println!();

    if modules_only {
        emit_dot_modules_only(graph);
    } else {
        emit_dot_full(graph);
    }

    println!("}}");
}

fn emit_dot_modules_only(graph: &DepGraph) {
    let mut all_modules: BTreeSet<&str> = BTreeSet::new();
    all_modules.insert(&graph.module_name);
    for extends in graph.extends.values() {
        for e in extends {
            all_modules.insert(e);
        }
    }
    for instances in graph.instances.values() {
        for inst in instances {
            all_modules.insert(&inst.target_module);
        }
    }

    for m in &all_modules {
        let shape = if *m == graph.module_name {
            "box, style=bold"
        } else if tla_core::is_stdlib_module(m) {
            "ellipse, style=dashed"
        } else {
            "box"
        };
        println!("  \"{}\" [shape={}, label=\"{}\"];", m, shape, m);
    }
    println!();

    // EXTENDS edges (dashed)
    for (mod_name, extends) in &graph.extends {
        for ext in extends {
            println!(
                "  \"{}\" -> \"{}\" [style=dashed, label=\"EXTENDS\"];",
                mod_name, ext
            );
        }
    }

    // INSTANCE edges (dashed, blue)
    for (mod_name, instances) in &graph.instances {
        for inst in instances {
            println!(
                "  \"{}\" -> \"{}\" [style=dashed, color=blue, label=\"INSTANCE\"];",
                mod_name, inst.target_module
            );
        }
    }
}

fn emit_dot_full(graph: &DepGraph) {
    let root_names: BTreeSet<&str> = graph.roots.iter().map(|r| r.name.as_str()).collect();

    // Group operators by module into subgraph clusters.
    let mut by_module: std::collections::BTreeMap<&str, Vec<&str>> =
        std::collections::BTreeMap::new();
    for (name, info) in &graph.operators {
        by_module.entry(&info.module).or_default().push(name);
    }

    for (mod_name, ops) in &by_module {
        println!(
            "  subgraph cluster_{} {{",
            mod_name.replace(|c: char| !c.is_alphanumeric(), "_")
        );
        println!("    label=\"{}\";", mod_name);
        println!("    style=rounded;");
        println!("    color=gray60;");
        println!();

        for op in ops {
            let is_root = root_names.contains(op);
            let info = &graph.operators[*op];

            let shape = if info.contains_prime { "box" } else { "ellipse" };
            let fill = if is_root {
                ", style=filled, fillcolor=lightblue"
            } else if !graph.reachable.contains(*op) {
                ", style=filled, fillcolor=lightyellow"
            } else {
                ""
            };

            let label = if info.arity > 0 {
                format!("{}({})", op, info.arity)
            } else {
                (*op).to_string()
            };

            println!(
                "    \"{}\" [shape={}{}, label=\"{}\"];",
                op, shape, fill, label
            );
        }
        println!("  }}");
        println!();
    }

    // EXTENDS edges
    for (mod_name, extends) in &graph.extends {
        for ext in extends {
            println!(
                "  \"{}\" -> \"{}\" [style=dashed, label=\"EXTENDS\"];",
                mod_name, ext
            );
        }
    }

    // INSTANCE edges
    for (mod_name, instances) in &graph.instances {
        for inst in instances {
            println!(
                "  \"{}\" -> \"{}\" [style=dashed, color=blue, label=\"INSTANCE\"];",
                mod_name, inst.target_module
            );
        }
    }

    // Call edges
    for (caller, callees) in &graph.call_edges {
        for callee in callees {
            if graph.operators.contains_key(caller)
                && graph.operators.contains_key(callee.as_str())
            {
                println!("  \"{}\" -> \"{}\";", caller, callee);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// JSON output
// ---------------------------------------------------------------------------

#[derive(Serialize)]
struct JsonOutput {
    modules: Vec<JsonModule>,
    operators: Vec<JsonOperator>,
    edges: Vec<JsonEdge>,
    roots: Vec<JsonRoot>,
    variables: Vec<String>,
    unreachable: Vec<String>,
    cycles: Vec<Vec<String>>,
}

#[derive(Serialize)]
struct JsonModule {
    name: String,
    extends: Vec<String>,
    instances: Vec<String>,
}

#[derive(Serialize)]
struct JsonOperator {
    name: String,
    module: String,
    arity: usize,
    local: bool,
    line: usize,
    contains_prime: bool,
    is_recursive: bool,
    reachable: bool,
    reads: Vec<String>,
    writes: Vec<String>,
}

#[derive(Serialize)]
struct JsonEdge {
    from: String,
    to: String,
    kind: String,
}

#[derive(Serialize)]
struct JsonRoot {
    name: String,
    kind: String,
}

/// Emit structured JSON output.
pub(crate) fn emit_json(graph: &DepGraph, show_unused: bool, modules_only: bool) {
    // Build module list.
    let mut modules: Vec<JsonModule> = Vec::new();
    let mut seen_modules: BTreeSet<&str> = BTreeSet::new();
    seen_modules.insert(&graph.module_name);

    modules.push(JsonModule {
        name: graph.module_name.clone(),
        extends: graph
            .extends
            .get(&graph.module_name)
            .cloned()
            .unwrap_or_default(),
        instances: graph
            .instances
            .get(&graph.module_name)
            .map(|insts| insts.iter().map(|i| i.target_module.clone()).collect())
            .unwrap_or_default(),
    });

    for mod_name in graph.extends.keys().chain(graph.instances.keys()) {
        if !seen_modules.contains(mod_name.as_str()) {
            seen_modules.insert(mod_name);
            modules.push(JsonModule {
                name: mod_name.clone(),
                extends: graph.extends.get(mod_name).cloned().unwrap_or_default(),
                instances: graph
                    .instances
                    .get(mod_name)
                    .map(|insts| insts.iter().map(|i| i.target_module.clone()).collect())
                    .unwrap_or_default(),
            });
        }
    }

    if modules_only {
        let output = serde_json::json!({
            "modules": modules,
        });
        println!(
            "{}",
            serde_json::to_string_pretty(&output).expect("invariant: serialization succeeds")
        );
        return;
    }

    // Build operator list.
    let operators: Vec<JsonOperator> = graph
        .operators
        .iter()
        .map(|(name, info)| JsonOperator {
            name: name.clone(),
            module: info.module.clone(),
            arity: info.arity,
            local: info.local,
            line: info.line_number(&graph.source),
            contains_prime: info.contains_prime,
            is_recursive: info.is_recursive,
            reachable: graph.reachable.contains(name),
            reads: graph
                .var_reads
                .get(name)
                .map(|s| s.iter().cloned().collect())
                .unwrap_or_default(),
            writes: graph
                .var_writes
                .get(name)
                .map(|s| s.iter().cloned().collect())
                .unwrap_or_default(),
        })
        .collect();

    // Build edge list.
    let mut edges: Vec<JsonEdge> = Vec::new();

    for (mod_name, extends) in &graph.extends {
        for ext in extends {
            edges.push(JsonEdge {
                from: mod_name.clone(),
                to: ext.clone(),
                kind: "extends".to_string(),
            });
        }
    }
    for (mod_name, instances) in &graph.instances {
        for inst in instances {
            edges.push(JsonEdge {
                from: mod_name.clone(),
                to: inst.target_module.clone(),
                kind: "instance".to_string(),
            });
        }
    }

    for (caller, callees) in &graph.call_edges {
        for callee in callees {
            if graph.operators.contains_key(callee.as_str()) {
                edges.push(JsonEdge {
                    from: caller.clone(),
                    to: callee.clone(),
                    kind: "call".to_string(),
                });
            }
        }
    }

    let roots: Vec<JsonRoot> = graph
        .roots
        .iter()
        .map(|r| JsonRoot {
            name: r.name.clone(),
            kind: r.kind.to_string(),
        })
        .collect();

    let unreachable: Vec<String> = if show_unused {
        graph
            .unreachable_operators()
            .iter()
            .map(|(name, _)| (*name).to_string())
            .collect()
    } else {
        Vec::new()
    };

    let output = JsonOutput {
        modules,
        operators,
        edges,
        roots,
        variables: graph.variables.clone(),
        unreachable,
        cycles: graph.cycles.clone(),
    };

    println!(
        "{}",
        serde_json::to_string_pretty(&output).expect("invariant: serialization succeeds")
    );
}
