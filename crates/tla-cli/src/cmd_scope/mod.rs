// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 scope` -- scope and dependency graph analysis for TLA+ specifications.
//!
//! Parses a TLA+ spec and produces a detailed scope analysis:
//! - Which operators reference which other operators
//! - Which operators read which state variables
//! - Which operators use which constants
//! - Dead operators (not reachable from Init/Next/invariants)
//!
//! Output formats: Human (tree-style), JSON, DOT (Graphviz).

use std::collections::{BTreeMap, BTreeSet, HashSet, VecDeque};
use std::path::Path;

use anyhow::{bail, Context, Result};
use serde::Serialize;

use tla_core::ast::{Expr, Module, Unit};
use tla_core::{parse, lower_main_module, FileId, SyntaxNode};

use crate::helpers::read_source;

// ---------------------------------------------------------------------------
// Output format enum
// ---------------------------------------------------------------------------

/// Output format for the scope command.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) enum ScopeOutputFormat {
    /// Human-readable tree (default).
    #[default]
    Human,
    /// Structured JSON.
    Json,
    /// Graphviz DOT.
    Dot,
}

// ---------------------------------------------------------------------------
// Internal scope graph
// ---------------------------------------------------------------------------

/// A node in the scope graph representing a single operator.
#[derive(Debug, Clone)]
struct ScopeEntry {
    /// Module the operator belongs to.
    module: String,
    /// Number of parameters.
    arity: usize,
    /// Whether the operator is LOCAL.
    local: bool,
    /// Byte offset in source (for line-number computation).
    byte_offset: u32,
    /// True if body contains primed variables.
    contains_prime: bool,
    /// True if declared RECURSIVE.
    is_recursive: bool,
}

impl ScopeEntry {
    /// Compute 1-indexed line number from byte offset.
    fn line_number(&self, source: &str) -> usize {
        let off = self.byte_offset as usize;
        if off == 0 || off > source.len() {
            return 0;
        }
        source[..off].chars().filter(|&c| c == '\n').count() + 1
    }
}

/// Complete scope analysis for a TLA+ specification.
struct ScopeGraph {
    /// Module name of the primary spec.
    module_name: String,
    /// All operators indexed by name.
    operators: BTreeMap<String, ScopeEntry>,
    /// Operator-to-operator call edges.
    calls: BTreeMap<String, BTreeSet<String>>,
    /// Operator-to-variable read edges.
    var_reads: BTreeMap<String, BTreeSet<String>>,
    /// Operator-to-variable write edges (primed references).
    var_writes: BTreeMap<String, BTreeSet<String>>,
    /// Operator-to-constant usage edges.
    const_uses: BTreeMap<String, BTreeSet<String>>,
    /// All declared variables.
    variables: Vec<String>,
    /// All declared constants.
    constants: Vec<String>,
    /// Root operator names (Init/Next/invariants).
    roots: Vec<String>,
    /// Operators reachable from any root.
    reachable: BTreeSet<String>,
    /// Source text (for line-number lookups).
    source: String,
}

impl ScopeGraph {
    /// Build the scope graph from a parsed and lowered module.
    fn build(module: &Module, source: &str) -> Self {
        let module_name = module.name.node.clone();
        let mut graph = Self {
            module_name: module_name.clone(),
            operators: BTreeMap::new(),
            calls: BTreeMap::new(),
            var_reads: BTreeMap::new(),
            var_writes: BTreeMap::new(),
            const_uses: BTreeMap::new(),
            variables: Vec::new(),
            constants: Vec::new(),
            roots: Vec::new(),
            reachable: BTreeSet::new(),
            source: source.to_string(),
        };

        // Collect declarations from module units.
        for unit in &module.units {
            match &unit.node {
                Unit::Variable(vars) => {
                    for v in vars {
                        graph.variables.push(v.node.clone());
                    }
                }
                Unit::Constant(consts) => {
                    for c in consts {
                        graph.constants.push(c.name.node.clone());
                    }
                }
                Unit::Operator(op_def) => {
                    let name = op_def.name.node.clone();
                    graph.operators.insert(
                        name,
                        ScopeEntry {
                            module: module_name.clone(),
                            arity: op_def.params.len(),
                            local: op_def.local,
                            byte_offset: op_def.name.span.start,
                            contains_prime: op_def.contains_prime,
                            is_recursive: op_def.is_recursive,
                        },
                    );
                }
                Unit::Recursive(_)
                | Unit::Instance(_)
                | Unit::Assume(_)
                | Unit::Theorem(_)
                | Unit::Separator => {}
            }
        }

        // Walk operator bodies.
        let var_set: HashSet<&str> = graph.variables.iter().map(|s| s.as_str()).collect();
        let const_set: HashSet<&str> = graph.constants.iter().map(|s| s.as_str()).collect();

        for unit in &module.units {
            if let Unit::Operator(op_def) = &unit.node {
                let op_name = op_def.name.node.clone();
                let param_names: HashSet<String> =
                    op_def.params.iter().map(|p| p.name.node.clone()).collect();

                let mut collector = ScopeCollector {
                    calls: BTreeSet::new(),
                    var_reads: BTreeSet::new(),
                    var_writes: BTreeSet::new(),
                    const_uses: BTreeSet::new(),
                    variables: &var_set,
                    constants: &const_set,
                    params: &param_names,
                    in_prime: false,
                    bound_names: Vec::new(),
                };
                collector.visit_expr(&op_def.body.node);

                if !collector.calls.is_empty() {
                    graph.calls.insert(op_name.clone(), collector.calls);
                }
                if !collector.var_reads.is_empty() {
                    graph.var_reads.insert(op_name.clone(), collector.var_reads);
                }
                if !collector.var_writes.is_empty() {
                    graph.var_writes.insert(op_name.clone(), collector.var_writes);
                }
                if !collector.const_uses.is_empty() {
                    graph.const_uses.insert(op_name, collector.const_uses);
                }
            }
        }

        // Determine roots: convention names Init/Next, plus any operator whose
        // name ends with "Inv" or "Invariant" or "TypeOK" (common patterns).
        for name in graph.operators.keys() {
            if name == "Init"
                || name == "Next"
                || name == "Spec"
                || name == "TypeOK"
                || name.ends_with("Inv")
                || name.ends_with("Invariant")
            {
                graph.roots.push(name.clone());
            }
        }

        // Compute reachability from roots.
        graph.compute_reachability();

        graph
    }

    /// BFS reachability from root operators.
    fn compute_reachability(&mut self) {
        let mut queue: VecDeque<String> = VecDeque::new();
        for root in &self.roots {
            if self.reachable.insert(root.clone()) {
                queue.push_back(root.clone());
            }
        }
        while let Some(current) = queue.pop_front() {
            if let Some(callees) = self.calls.get(&current) {
                for callee in callees {
                    if self.reachable.insert(callee.clone()) {
                        queue.push_back(callee.clone());
                    }
                }
            }
        }
    }

    /// Return operators that are not reachable from any root.
    fn dead_operators(&self) -> Vec<&str> {
        self.operators
            .keys()
            .filter(|name| {
                !self.reachable.contains(*name)
                    && !tla_core::is_stdlib_module(
                        self.operators.get(*name).map_or("", |e| &e.module),
                    )
            })
            .map(|s| s.as_str())
            .collect()
    }
}

// ---------------------------------------------------------------------------
// Expression visitor
// ---------------------------------------------------------------------------

/// Walks an expression tree collecting scope references.
struct ScopeCollector<'a> {
    calls: BTreeSet<String>,
    var_reads: BTreeSet<String>,
    var_writes: BTreeSet<String>,
    const_uses: BTreeSet<String>,
    variables: &'a HashSet<&'a str>,
    constants: &'a HashSet<&'a str>,
    params: &'a HashSet<String>,
    in_prime: bool,
    bound_names: Vec<HashSet<String>>,
}

impl<'a> ScopeCollector<'a> {
    fn is_bound(&self, name: &str) -> bool {
        self.bound_names.iter().any(|scope| scope.contains(name))
    }

    fn push_scope(&mut self, names: &[String]) {
        self.bound_names.push(names.iter().cloned().collect());
    }

    fn pop_scope(&mut self) {
        self.bound_names.pop();
    }

    fn visit_expr(&mut self, expr: &Expr) {
        match expr {
            Expr::Ident(name, _) => {
                if self.is_bound(name) || self.params.contains(name) {
                    return;
                }
                if self.variables.contains(name.as_str()) {
                    if self.in_prime {
                        self.var_writes.insert(name.clone());
                    } else {
                        self.var_reads.insert(name.clone());
                    }
                } else if self.constants.contains(name.as_str()) {
                    self.const_uses.insert(name.clone());
                } else {
                    self.calls.insert(name.clone());
                }
            }
            Expr::StateVar(name, _, _) => {
                if self.in_prime {
                    self.var_writes.insert(name.clone());
                } else {
                    self.var_reads.insert(name.clone());
                }
            }
            Expr::Apply(op_expr, args) => {
                self.visit_expr(&op_expr.node);
                for arg in args {
                    self.visit_expr(&arg.node);
                }
            }
            Expr::ModuleRef(target, op_name, args) => {
                let qualified = format!("{}!{}", target.name(), op_name);
                self.calls.insert(qualified);
                self.calls.insert(op_name.clone());
                for arg in args {
                    self.visit_expr(&arg.node);
                }
            }
            Expr::OpRef(name) => {
                self.calls.insert(name.clone());
            }
            Expr::Prime(inner) => {
                let was = self.in_prime;
                self.in_prime = true;
                self.visit_expr(&inner.node);
                self.in_prime = was;
            }
            // Binary operators.
            Expr::And(a, b)
            | Expr::Or(a, b)
            | Expr::Implies(a, b)
            | Expr::Equiv(a, b)
            | Expr::Eq(a, b)
            | Expr::Neq(a, b)
            | Expr::Lt(a, b)
            | Expr::Gt(a, b)
            | Expr::Leq(a, b)
            | Expr::Geq(a, b)
            | Expr::In(a, b)
            | Expr::NotIn(a, b)
            | Expr::Subseteq(a, b)
            | Expr::Union(a, b)
            | Expr::Intersect(a, b)
            | Expr::SetMinus(a, b)
            | Expr::FuncSet(a, b)
            | Expr::Add(a, b)
            | Expr::Sub(a, b)
            | Expr::Mul(a, b)
            | Expr::Div(a, b)
            | Expr::IntDiv(a, b)
            | Expr::Mod(a, b)
            | Expr::Pow(a, b)
            | Expr::Range(a, b)
            | Expr::LeadsTo(a, b) => {
                self.visit_expr(&a.node);
                self.visit_expr(&b.node);
            }
            // Unary operators.
            Expr::Not(inner)
            | Expr::Neg(inner)
            | Expr::Powerset(inner)
            | Expr::BigUnion(inner)
            | Expr::Domain(inner)
            | Expr::Always(inner)
            | Expr::Eventually(inner)
            | Expr::Enabled(inner)
            | Expr::Unchanged(inner) => {
                self.visit_expr(&inner.node);
            }
            Expr::WeakFair(vars, action) | Expr::StrongFair(vars, action) => {
                self.visit_expr(&vars.node);
                self.visit_expr(&action.node);
            }
            Expr::If(cond, then_e, else_e) => {
                self.visit_expr(&cond.node);
                self.visit_expr(&then_e.node);
                self.visit_expr(&else_e.node);
            }
            Expr::Case(arms, other) => {
                for arm in arms {
                    self.visit_expr(&arm.guard.node);
                    self.visit_expr(&arm.body.node);
                }
                if let Some(other) = other {
                    self.visit_expr(&other.node);
                }
            }
            Expr::Let(defs, body) => {
                let names: Vec<String> = defs.iter().map(|d| d.name.node.clone()).collect();
                for def in defs {
                    self.visit_expr(&def.body.node);
                }
                self.push_scope(&names);
                self.visit_expr(&body.node);
                self.pop_scope();
            }
            Expr::Forall(bounds, body) | Expr::Exists(bounds, body) => {
                let mut names = Vec::new();
                for bv in bounds {
                    names.push(bv.name.node.clone());
                    if let Some(ref domain) = bv.domain {
                        self.visit_expr(&domain.node);
                    }
                }
                self.push_scope(&names);
                self.visit_expr(&body.node);
                self.pop_scope();
            }
            Expr::Choose(bv, body) => {
                if let Some(ref domain) = bv.domain {
                    self.visit_expr(&domain.node);
                }
                self.push_scope(&[bv.name.node.clone()]);
                self.visit_expr(&body.node);
                self.pop_scope();
            }
            Expr::SetEnum(elems) | Expr::Tuple(elems) | Expr::Times(elems) => {
                for e in elems {
                    self.visit_expr(&e.node);
                }
            }
            Expr::SetBuilder(body, bounds) => {
                let mut names = Vec::new();
                for bv in bounds {
                    names.push(bv.name.node.clone());
                    if let Some(ref domain) = bv.domain {
                        self.visit_expr(&domain.node);
                    }
                }
                self.push_scope(&names);
                self.visit_expr(&body.node);
                self.pop_scope();
            }
            Expr::SetFilter(bv, body) => {
                if let Some(ref domain) = bv.domain {
                    self.visit_expr(&domain.node);
                }
                self.push_scope(&[bv.name.node.clone()]);
                self.visit_expr(&body.node);
                self.pop_scope();
            }
            Expr::FuncDef(bounds, body) => {
                let mut names = Vec::new();
                for bv in bounds {
                    names.push(bv.name.node.clone());
                    if let Some(ref domain) = bv.domain {
                        self.visit_expr(&domain.node);
                    }
                }
                self.push_scope(&names);
                self.visit_expr(&body.node);
                self.pop_scope();
            }
            Expr::FuncApply(f, arg) => {
                self.visit_expr(&f.node);
                self.visit_expr(&arg.node);
            }
            Expr::Except(base, specs) => {
                self.visit_expr(&base.node);
                for spec in specs {
                    for path_elem in &spec.path {
                        if let tla_core::ast::ExceptPathElement::Index(idx) = path_elem {
                            self.visit_expr(&idx.node);
                        }
                    }
                    self.visit_expr(&spec.value.node);
                }
            }
            Expr::Record(fields) | Expr::RecordSet(fields) => {
                for (_, val) in fields {
                    self.visit_expr(&val.node);
                }
            }
            Expr::RecordAccess(base, _) => {
                self.visit_expr(&base.node);
            }
            Expr::Lambda(params, body) => {
                let names: Vec<String> = params.iter().map(|p| p.node.clone()).collect();
                self.push_scope(&names);
                self.visit_expr(&body.node);
                self.pop_scope();
            }
            Expr::Label(label) => {
                self.visit_expr(&label.body.node);
            }
            Expr::SubstIn(_, body) => {
                self.visit_expr(&body.node);
            }
            Expr::InstanceExpr(_, _) => {}
            Expr::Bool(_) | Expr::Int(_) | Expr::String(_) => {}
        }
    }
}

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Run the scope analysis command.
pub(crate) fn cmd_scope(file: &Path, format: ScopeOutputFormat) -> Result<()> {
    let source = read_source(file)?;
    let parse_result = parse(&source);
    if !parse_result.errors.is_empty() {
        let file_path = file.display().to_string();
        for err in &parse_result.errors {
            let diagnostic = tla_core::parse_error_diagnostic(
                &file_path,
                &err.message,
                err.start,
                err.end,
            );
            diagnostic.eprint(&file_path, &source);
        }
        bail!("parse failed with {} error(s)", parse_result.errors.len());
    }
    let tree = SyntaxNode::new_root(parse_result.green_node);

    let hint_name = file
        .file_stem()
        .and_then(|s| s.to_str())
        .filter(|s| !s.is_empty());
    let result = lower_main_module(FileId(0), &tree, hint_name);
    if !result.errors.is_empty() {
        let file_path = file.display().to_string();
        for err in &result.errors {
            let diagnostic =
                tla_core::lower_error_diagnostic(&file_path, &err.message, err.span);
            diagnostic.eprint(&file_path, &source);
        }
        bail!("lower failed with {} error(s)", result.errors.len());
    }
    let module = result.module.context("lower produced no module")?;

    let graph = ScopeGraph::build(&module, &source);

    match format {
        ScopeOutputFormat::Human => emit_human(&graph),
        ScopeOutputFormat::Json => emit_json(&graph),
        ScopeOutputFormat::Dot => emit_dot(&graph),
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Human-readable (tree) output
// ---------------------------------------------------------------------------

fn emit_human(graph: &ScopeGraph) {
    println!("Scope analysis: {}", graph.module_name);
    println!();

    // Variables
    if !graph.variables.is_empty() {
        println!("Variables: {}", graph.variables.join(", "));
    }

    // Constants
    if !graph.constants.is_empty() {
        println!("Constants: {}", graph.constants.join(", "));
    }

    // Roots
    if !graph.roots.is_empty() {
        println!();
        println!("Roots: {}", graph.roots.join(", "));
    }

    // Operator details
    println!();
    println!("Operators ({}):", graph.operators.len());
    for (name, entry) in &graph.operators {
        let line = entry.line_number(&graph.source);
        let line_str = if line > 0 {
            format!(":{}", line)
        } else {
            String::new()
        };
        let mut tags = Vec::new();
        if entry.local {
            tags.push("LOCAL");
        }
        if entry.is_recursive {
            tags.push("RECURSIVE");
        }
        if entry.contains_prime {
            tags.push("priming");
        }
        if !graph.reachable.contains(name) {
            tags.push("DEAD");
        }
        let tag_str = if tags.is_empty() {
            String::new()
        } else {
            format!(" [{}]", tags.join(", "))
        };
        let arity_str = if entry.arity > 0 {
            format!("({})", entry.arity)
        } else {
            String::new()
        };

        println!("  {}{}{}{}", name, arity_str, line_str, tag_str);

        // Calls
        if let Some(callees) = graph.calls.get(name) {
            let filtered: Vec<&str> = callees
                .iter()
                .filter(|c| graph.operators.contains_key(c.as_str()))
                .map(|c| c.as_str())
                .collect();
            if !filtered.is_empty() {
                print_tree_items("calls", &filtered);
            }
        }

        // Variable reads
        if let Some(reads) = graph.var_reads.get(name) {
            let items: Vec<&str> = reads.iter().map(|s| s.as_str()).collect();
            print_tree_items("reads", &items);
        }

        // Variable writes
        if let Some(writes) = graph.var_writes.get(name) {
            let items: Vec<&str> = writes.iter().map(|s| s.as_str()).collect();
            print_tree_items("writes", &items);
        }

        // Constant uses
        if let Some(consts) = graph.const_uses.get(name) {
            let items: Vec<&str> = consts.iter().map(|s| s.as_str()).collect();
            print_tree_items("constants", &items);
        }
    }

    // Dead code summary
    let dead = graph.dead_operators();
    if !dead.is_empty() {
        println!();
        println!("Dead operators ({}):", dead.len());
        for d in &dead {
            let line = graph
                .operators
                .get(*d)
                .map(|e| e.line_number(&graph.source))
                .unwrap_or(0);
            if line > 0 {
                println!("  {} (line {})", d, line);
            } else {
                println!("  {}", d);
            }
        }
    }
}

/// Print a tree-style indented sub-list for an operator attribute.
fn print_tree_items(label: &str, items: &[&str]) {
    if items.len() == 1 {
        println!("    {} {}", label, items[0]);
    } else {
        println!("    {} {}", label, items.join(", "));
    }
}

// ---------------------------------------------------------------------------
// JSON output
// ---------------------------------------------------------------------------

#[derive(Serialize)]
struct JsonScopeOutput {
    module: String,
    variables: Vec<String>,
    constants: Vec<String>,
    roots: Vec<String>,
    operators: Vec<JsonScopeOperator>,
    dead_operators: Vec<String>,
}

#[derive(Serialize)]
struct JsonScopeOperator {
    name: String,
    arity: usize,
    line: usize,
    local: bool,
    recursive: bool,
    contains_prime: bool,
    reachable: bool,
    calls: Vec<String>,
    reads_variables: Vec<String>,
    writes_variables: Vec<String>,
    uses_constants: Vec<String>,
}

fn emit_json(graph: &ScopeGraph) {
    let operators: Vec<JsonScopeOperator> = graph
        .operators
        .iter()
        .map(|(name, entry)| {
            JsonScopeOperator {
                name: name.clone(),
                arity: entry.arity,
                line: entry.line_number(&graph.source),
                local: entry.local,
                recursive: entry.is_recursive,
                contains_prime: entry.contains_prime,
                reachable: graph.reachable.contains(name),
                calls: graph
                    .calls
                    .get(name)
                    .map(|s| s.iter().cloned().collect())
                    .unwrap_or_default(),
                reads_variables: graph
                    .var_reads
                    .get(name)
                    .map(|s| s.iter().cloned().collect())
                    .unwrap_or_default(),
                writes_variables: graph
                    .var_writes
                    .get(name)
                    .map(|s| s.iter().cloned().collect())
                    .unwrap_or_default(),
                uses_constants: graph
                    .const_uses
                    .get(name)
                    .map(|s| s.iter().cloned().collect())
                    .unwrap_or_default(),
            }
        })
        .collect();

    let dead = graph.dead_operators().iter().map(|s| s.to_string()).collect();

    let output = JsonScopeOutput {
        module: graph.module_name.clone(),
        variables: graph.variables.clone(),
        constants: graph.constants.clone(),
        roots: graph.roots.clone(),
        operators,
        dead_operators: dead,
    };

    println!(
        "{}",
        serde_json::to_string_pretty(&output).expect("invariant: serialization succeeds")
    );
}

// ---------------------------------------------------------------------------
// DOT (Graphviz) output
// ---------------------------------------------------------------------------

fn emit_dot(graph: &ScopeGraph) {
    println!("digraph scope {{");
    println!("  rankdir=LR;");
    println!("  node [fontname=\"Helvetica\", fontsize=10];");
    println!("  edge [fontname=\"Helvetica\", fontsize=9];");
    println!();

    let root_set: BTreeSet<&str> = graph.roots.iter().map(|s| s.as_str()).collect();
    let dead_set: BTreeSet<&str> = graph.dead_operators().into_iter().collect();

    // Variable nodes (distinct shape).
    if !graph.variables.is_empty() {
        println!("  // Variables");
        for v in &graph.variables {
            println!(
                "  \"var:{}\" [shape=diamond, style=filled, fillcolor=lightgreen, label=\"{}\"];",
                v, v
            );
        }
        println!();
    }

    // Constant nodes (distinct shape).
    if !graph.constants.is_empty() {
        println!("  // Constants");
        for c in &graph.constants {
            println!(
                "  \"const:{}\" [shape=hexagon, style=filled, fillcolor=lightyellow, label=\"{}\"];",
                c, c
            );
        }
        println!();
    }

    // Operator nodes.
    println!("  // Operators");
    for (name, entry) in &graph.operators {
        let shape = if entry.contains_prime { "box" } else { "ellipse" };
        let fill = if root_set.contains(name.as_str()) {
            ", style=filled, fillcolor=lightblue"
        } else if dead_set.contains(name.as_str()) {
            ", style=filled, fillcolor=mistyrose"
        } else {
            ""
        };
        let label = if entry.arity > 0 {
            format!("{}({})", name, entry.arity)
        } else {
            name.clone()
        };
        println!("  \"op:{}\" [shape={}{}, label=\"{}\"];", name, shape, fill, label);
    }
    println!();

    // Call edges (solid black).
    println!("  // Call edges");
    for (caller, callees) in &graph.calls {
        for callee in callees {
            if graph.operators.contains_key(callee.as_str()) {
                println!("  \"op:{}\" -> \"op:{}\";", caller, callee);
            }
        }
    }

    // Variable-read edges (green, dashed).
    println!();
    println!("  // Variable reads");
    for (op, vars) in &graph.var_reads {
        for v in vars {
            println!(
                "  \"op:{}\" -> \"var:{}\" [style=dashed, color=green, label=\"reads\"];",
                op, v
            );
        }
    }

    // Variable-write edges (red, dashed).
    println!();
    println!("  // Variable writes");
    for (op, vars) in &graph.var_writes {
        for v in vars {
            println!(
                "  \"op:{}\" -> \"var:{}\" [style=dashed, color=red, label=\"writes\"];",
                op, v
            );
        }
    }

    // Constant-use edges (orange, dotted).
    println!();
    println!("  // Constant uses");
    for (op, consts) in &graph.const_uses {
        for c in consts {
            println!(
                "  \"op:{}\" -> \"const:{}\" [style=dotted, color=orange, label=\"uses\"];",
                op, c
            );
        }
    }

    println!("}}");
}

// ---------------------------------------------------------------------------
// Unit tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    /// Parse a TLA+ source string and build a ScopeGraph.
    fn scope_from_source(source: &str) -> ScopeGraph {
        let parse_result = parse(source);
        assert!(
            parse_result.errors.is_empty(),
            "parse errors: {:?}",
            parse_result.errors
        );
        let tree = SyntaxNode::new_root(parse_result.green_node);
        let result = lower_main_module(FileId(0), &tree, Some("Test"));
        assert!(
            result.errors.is_empty(),
            "lower errors: {:?}",
            result.errors
        );
        let module = result.module.expect("module should be present");
        ScopeGraph::build(&module, source)
    }

    #[test]
    fn test_basic_operator_detection() {
        let source = r#"
---- MODULE Test ----
VARIABLE x

Init == x = 0
Next == x' = x + 1
====
"#;
        let graph = scope_from_source(source);
        assert_eq!(graph.module_name, "Test");
        assert!(graph.operators.contains_key("Init"));
        assert!(graph.operators.contains_key("Next"));
        assert_eq!(graph.variables, vec!["x".to_string()]);
    }

    #[test]
    fn test_variable_reads_and_writes() {
        let source = r#"
---- MODULE Test ----
VARIABLE x, y

Init == x = 0 /\ y = 1
Next == x' = y /\ y' = x
====
"#;
        let graph = scope_from_source(source);

        // Init reads x and y (via Eq comparisons).
        let init_reads = graph.var_reads.get("Init");
        assert!(init_reads.is_some(), "Init should have var_reads");
        let init_reads = init_reads.unwrap();
        assert!(init_reads.contains("x"), "Init should read x");
        assert!(init_reads.contains("y"), "Init should read y");

        // Next writes x' and y'.
        let next_writes = graph.var_writes.get("Next");
        assert!(next_writes.is_some(), "Next should have var_writes");
        let next_writes = next_writes.unwrap();
        assert!(next_writes.contains("x"), "Next should write x");
        assert!(next_writes.contains("y"), "Next should write y");

        // Next reads x and y (RHS of assignments).
        let next_reads = graph.var_reads.get("Next");
        assert!(next_reads.is_some(), "Next should have var_reads");
        let next_reads = next_reads.unwrap();
        assert!(next_reads.contains("x"), "Next should read x");
        assert!(next_reads.contains("y"), "Next should read y");
    }

    #[test]
    fn test_constant_usage() {
        let source = r#"
---- MODULE Test ----
CONSTANT N
VARIABLE x

Init == x = N
Next == x' = x + 1
====
"#;
        let graph = scope_from_source(source);
        assert_eq!(graph.constants, vec!["N".to_string()]);

        let init_consts = graph.const_uses.get("Init");
        assert!(init_consts.is_some(), "Init should use constants");
        assert!(init_consts.unwrap().contains("N"));
    }

    #[test]
    fn test_operator_call_edges() {
        let source = r#"
---- MODULE Test ----
VARIABLE x

Helper(v) == v + 1
Init == x = 0
Next == x' = Helper(x)
====
"#;
        let graph = scope_from_source(source);

        let next_calls = graph.calls.get("Next");
        assert!(next_calls.is_some(), "Next should have call edges");
        assert!(
            next_calls.unwrap().contains("Helper"),
            "Next should call Helper"
        );
    }

    #[test]
    fn test_dead_code_detection() {
        let source = r#"
---- MODULE Test ----
VARIABLE x

Init == x = 0
Next == x' = x + 1
Unused == x + 42
====
"#;
        let graph = scope_from_source(source);

        let dead = graph.dead_operators();
        assert!(dead.contains(&"Unused"), "Unused should be dead: {:?}", dead);
        assert!(!dead.contains(&"Init"), "Init should not be dead");
        assert!(!dead.contains(&"Next"), "Next should not be dead");
    }

    #[test]
    fn test_reachability_transitive() {
        let source = r#"
---- MODULE Test ----
VARIABLE x

Deep == 42
Middle == Deep
Init == x = Middle
Next == x' = x
====
"#;
        let graph = scope_from_source(source);

        assert!(graph.reachable.contains("Init"));
        assert!(graph.reachable.contains("Middle"));
        assert!(graph.reachable.contains("Deep"));
        assert!(graph.reachable.contains("Next"));
    }

    #[test]
    fn test_bound_variable_scoping() {
        let source = r#"
---- MODULE Test ----
VARIABLE x

Init == x = 0
Next == \E v \in {1, 2, 3} : x' = v
====
"#;
        let graph = scope_from_source(source);

        // `v` is bound by \E, so should NOT appear in calls.
        let next_calls = graph.calls.get("Next").cloned().unwrap_or_default();
        assert!(
            !next_calls.contains("v"),
            "bound variable v should not be in calls: {:?}",
            next_calls
        );
    }

    #[test]
    fn test_scope_output_format_default() {
        assert_eq!(ScopeOutputFormat::default(), ScopeOutputFormat::Human);
    }

    #[test]
    fn test_line_number_computation() {
        let source = "line1\nline2\nline3\n";
        let entry = ScopeEntry {
            module: "M".to_string(),
            arity: 0,
            local: false,
            byte_offset: 6, // start of "line2"
            contains_prime: false,
            is_recursive: false,
        };
        assert_eq!(entry.line_number(source), 2);
    }

    #[test]
    fn test_line_number_zero_offset() {
        let entry = ScopeEntry {
            module: "M".to_string(),
            arity: 0,
            local: false,
            byte_offset: 0,
            contains_prime: false,
            is_recursive: false,
        };
        assert_eq!(entry.line_number("any source"), 0);
    }

    #[test]
    fn test_empty_module() {
        let source = r#"
---- MODULE Empty ----
====
"#;
        let graph = scope_from_source(source);
        assert_eq!(graph.module_name, "Empty");
        assert!(graph.operators.is_empty());
        assert!(graph.variables.is_empty());
        assert!(graph.constants.is_empty());
        assert!(graph.roots.is_empty());
        assert!(graph.dead_operators().is_empty());
    }

    #[test]
    fn test_local_operator_detected() {
        let source = r#"
---- MODULE Test ----
VARIABLE x

LOCAL Helper == 42
Init == x = Helper
Next == x' = x
====
"#;
        let graph = scope_from_source(source);
        let helper = graph.operators.get("Helper").expect("Helper should exist");
        assert!(helper.local, "Helper should be marked LOCAL");
    }

    #[test]
    fn test_multiple_constants() {
        let source = r#"
---- MODULE Test ----
CONSTANT A, B, C
VARIABLE x

Init == x = A
Next == x' = IF x = A THEN B ELSE C
====
"#;
        let graph = scope_from_source(source);
        assert_eq!(graph.constants.len(), 3);
        assert!(graph.constants.contains(&"A".to_string()));
        assert!(graph.constants.contains(&"B".to_string()));
        assert!(graph.constants.contains(&"C".to_string()));

        let next_consts = graph.const_uses.get("Next").expect("Next should use constants");
        assert!(next_consts.contains("A"));
        assert!(next_consts.contains("B"));
        assert!(next_consts.contains("C"));
    }

    #[test]
    fn test_json_output_structure() {
        let source = r#"
---- MODULE Test ----
CONSTANT N
VARIABLE x

Init == x = N
Next == x' = x + 1
====
"#;
        let graph = scope_from_source(source);

        // Build the JSON output struct and verify its fields.
        let operators: Vec<JsonScopeOperator> = graph
            .operators
            .iter()
            .map(|(name, entry)| JsonScopeOperator {
                name: name.clone(),
                arity: entry.arity,
                line: entry.line_number(&graph.source),
                local: entry.local,
                recursive: entry.is_recursive,
                contains_prime: entry.contains_prime,
                reachable: graph.reachable.contains(name),
                calls: graph
                    .calls
                    .get(name)
                    .map(|s| s.iter().cloned().collect())
                    .unwrap_or_default(),
                reads_variables: graph
                    .var_reads
                    .get(name)
                    .map(|s| s.iter().cloned().collect())
                    .unwrap_or_default(),
                writes_variables: graph
                    .var_writes
                    .get(name)
                    .map(|s| s.iter().cloned().collect())
                    .unwrap_or_default(),
                uses_constants: graph
                    .const_uses
                    .get(name)
                    .map(|s| s.iter().cloned().collect())
                    .unwrap_or_default(),
            })
            .collect();

        let output = JsonScopeOutput {
            module: graph.module_name.clone(),
            variables: graph.variables.clone(),
            constants: graph.constants.clone(),
            roots: graph.roots.clone(),
            operators,
            dead_operators: graph.dead_operators().iter().map(|s| s.to_string()).collect(),
        };

        let json_str = serde_json::to_string_pretty(&output);
        assert!(json_str.is_ok(), "JSON serialization should succeed");
        let json_str = json_str.unwrap();
        assert!(json_str.contains("\"module\": \"Test\""));
        assert!(json_str.contains("\"N\""));
        assert!(json_str.contains("\"Init\""));
        assert!(json_str.contains("\"Next\""));
    }
}
