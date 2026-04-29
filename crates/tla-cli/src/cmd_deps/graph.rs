// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Dependency graph construction and analysis.
//!
//! Walks the TLA+ AST to build operator call graphs, variable usage maps,
//! reachability from roots (Init/Next/invariants), and cycle detection.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};

use tla_core::ast::{Expr, Module, Unit};

/// Complete dependency analysis result for a TLA+ spec.
pub(crate) struct DepGraph {
    /// Primary module name.
    pub(crate) module_name: String,
    /// EXTENDS relationships: module -> [extended modules].
    pub(crate) extends: BTreeMap<String, Vec<String>>,
    /// INSTANCE relationships: module -> [(instance_name, target_module)].
    pub(crate) instances: BTreeMap<String, Vec<InstanceInfo>>,
    /// All operators by qualified name (module.op or just op for main module).
    pub(crate) operators: BTreeMap<String, OperatorInfo>,
    /// Call edges: caller -> [callees].
    pub(crate) call_edges: BTreeMap<String, BTreeSet<String>>,
    /// Variable reads per operator: op -> [variables read].
    pub(crate) var_reads: BTreeMap<String, BTreeSet<String>>,
    /// Variable writes per operator: op -> [variables written (primed)].
    pub(crate) var_writes: BTreeMap<String, BTreeSet<String>>,
    /// Root operators (Init, Next, invariants, properties).
    pub(crate) roots: Vec<RootInfo>,
    /// Operators reachable from any root.
    pub(crate) reachable: BTreeSet<String>,
    /// Detected cycles (excluding RECURSIVE self-calls).
    pub(crate) cycles: Vec<Vec<String>>,
    /// All declared variables.
    pub(crate) variables: Vec<String>,
    /// Set of operator names declared RECURSIVE.
    pub(crate) recursive_ops: BTreeSet<String>,
    /// Source text for the main module (used for byte-offset-to-line conversion).
    pub(crate) source: String,
}

/// Information about an INSTANCE declaration.
pub(crate) struct InstanceInfo {
    pub(crate) target_module: String,
    pub(crate) is_local: bool,
}

/// Metadata about an operator.
pub(crate) struct OperatorInfo {
    /// The module this operator belongs to.
    pub(crate) module: String,
    /// Number of parameters.
    pub(crate) arity: usize,
    /// Whether the operator is LOCAL.
    pub(crate) local: bool,
    /// Byte offset of the operator name in the source file.
    pub(crate) byte_offset: u32,
    /// Whether the operator has primed variables in its body.
    pub(crate) contains_prime: bool,
    /// Whether the operator was declared RECURSIVE.
    pub(crate) is_recursive: bool,
}

impl OperatorInfo {
    /// Compute the 1-indexed line number from a byte offset and source text.
    pub(crate) fn line_number(&self, source: &str) -> usize {
        let offset = self.byte_offset as usize;
        if offset == 0 || offset > source.len() {
            return 0;
        }
        source[..offset].chars().filter(|&c| c == '\n').count() + 1
    }
}

/// A root entry point for model checking.
pub(crate) struct RootInfo {
    pub(crate) name: String,
    pub(crate) kind: RootKind,
}

/// The kind of root operator.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum RootKind {
    Init,
    Next,
    Invariant,
    Property,
}

impl std::fmt::Display for RootKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RootKind::Init => write!(f, "init"),
            RootKind::Next => write!(f, "next"),
            RootKind::Invariant => write!(f, "invariant"),
            RootKind::Property => write!(f, "property"),
        }
    }
}

impl DepGraph {
    /// Build a dependency graph from a parsed+lowered module.
    pub(crate) fn build(
        module: &Module,
        loaded_modules: &[&Module],
        config: Option<&tla_check::Config>,
        source: &str,
    ) -> Self {
        let module_name = module.name.node.clone();
        let mut graph = Self {
            module_name: module_name.clone(),
            extends: BTreeMap::new(),
            instances: BTreeMap::new(),
            operators: BTreeMap::new(),
            call_edges: BTreeMap::new(),
            var_reads: BTreeMap::new(),
            var_writes: BTreeMap::new(),
            roots: Vec::new(),
            reachable: BTreeSet::new(),
            cycles: Vec::new(),
            variables: Vec::new(),
            recursive_ops: BTreeSet::new(),
            source: source.to_string(),
        };

        // Collect EXTENDS.
        if !module.extends.is_empty() {
            let ext_names: Vec<String> = module.extends.iter().map(|e| e.node.clone()).collect();
            graph.extends.insert(module_name.clone(), ext_names);
        }

        // Collect variables, operators, instances from the main module.
        graph.collect_module_info(&module_name, module);

        // Collect info from loaded (EXTENDS/INSTANCE) modules.
        for loaded_mod in loaded_modules {
            let ext_mod_name = &loaded_mod.name.node;
            if !loaded_mod.extends.is_empty() {
                let ext_names: Vec<String> =
                    loaded_mod.extends.iter().map(|e| e.node.clone()).collect();
                graph
                    .extends
                    .entry(ext_mod_name.clone())
                    .or_insert(ext_names);
            }
            graph.collect_module_info(ext_mod_name, loaded_mod);
        }

        // Walk operator bodies to build call edges and variable usage.
        graph.analyze_operator_bodies(module);
        for loaded_mod in loaded_modules {
            graph.analyze_operator_bodies(loaded_mod);
        }

        // Determine roots from config.
        if let Some(cfg) = config {
            if let Some(ref init) = cfg.init {
                graph.roots.push(RootInfo {
                    name: init.clone(),
                    kind: RootKind::Init,
                });
            }
            if let Some(ref next) = cfg.next {
                graph.roots.push(RootInfo {
                    name: next.clone(),
                    kind: RootKind::Next,
                });
            }
            for inv in &cfg.invariants {
                graph.roots.push(RootInfo {
                    name: inv.clone(),
                    kind: RootKind::Invariant,
                });
            }
            for prop in &cfg.properties {
                graph.roots.push(RootInfo {
                    name: prop.clone(),
                    kind: RootKind::Property,
                });
            }
        }

        // If no config, try convention names Init/Next.
        if graph.roots.is_empty() {
            if graph.operators.contains_key("Init") {
                graph.roots.push(RootInfo {
                    name: "Init".to_string(),
                    kind: RootKind::Init,
                });
            }
            if graph.operators.contains_key("Next") {
                graph.roots.push(RootInfo {
                    name: "Next".to_string(),
                    kind: RootKind::Next,
                });
            }
        }

        // Compute reachability from roots.
        graph.compute_reachability();

        // Detect cycles.
        graph.detect_cycles();

        graph
    }

    /// Collect variables, operators, and instances from a module.
    fn collect_module_info(&mut self, mod_name: &str, module: &Module) {
        for unit in &module.units {
            match &unit.node {
                Unit::Variable(vars) => {
                    for v in vars {
                        self.variables.push(v.node.clone());
                    }
                }
                Unit::Operator(op_def) => {
                    let op_name = op_def.name.node.clone();
                    self.operators.insert(
                        op_name.clone(),
                        OperatorInfo {
                            module: mod_name.to_string(),
                            arity: op_def.params.len(),
                            local: op_def.local,
                            byte_offset: op_def.name.span.start,
                            contains_prime: op_def.contains_prime,
                            is_recursive: op_def.is_recursive,
                        },
                    );
                    if op_def.is_recursive {
                        self.recursive_ops.insert(op_name);
                    }
                }
                Unit::Instance(inst) => {
                    let instances = self.instances.entry(mod_name.to_string()).or_default();
                    instances.push(InstanceInfo {
                        target_module: inst.module.node.clone(),
                        is_local: inst.local,
                    });
                }
                Unit::Recursive(decls) => {
                    for decl in decls {
                        self.recursive_ops.insert(decl.name.node.clone());
                    }
                }
                Unit::Constant(_) | Unit::Assume(_) | Unit::Theorem(_) | Unit::Separator => {}
            }
        }
    }

    /// Walk all operator bodies to find call edges and variable references.
    fn analyze_operator_bodies(&mut self, module: &Module) {
        let var_set: HashSet<&str> = self.variables.iter().map(|s| s.as_str()).collect();

        for unit in &module.units {
            if let Unit::Operator(op_def) = &unit.node {
                let op_name = op_def.name.node.clone();
                let param_names: HashSet<String> =
                    op_def.params.iter().map(|p| p.name.node.clone()).collect();

                let mut collector = ExprCollector {
                    calls: BTreeSet::new(),
                    var_reads: BTreeSet::new(),
                    var_writes: BTreeSet::new(),
                    variables: &var_set,
                    params: &param_names,
                    in_prime: false,
                    bound_names: Vec::new(),
                };
                collector.visit_expr(&op_def.body.node);

                if !collector.calls.is_empty() {
                    self.call_edges.insert(op_name.clone(), collector.calls);
                }
                if !collector.var_reads.is_empty() {
                    self.var_reads.insert(op_name.clone(), collector.var_reads);
                }
                if !collector.var_writes.is_empty() {
                    self.var_writes
                        .insert(op_name.clone(), collector.var_writes);
                }
            }
        }
    }

    /// Compute the set of operators reachable from any root.
    fn compute_reachability(&mut self) {
        let mut queue: VecDeque<String> = VecDeque::new();
        for root in &self.roots {
            if !self.reachable.contains(&root.name) {
                self.reachable.insert(root.name.clone());
                queue.push_back(root.name.clone());
            }
        }

        while let Some(current) = queue.pop_front() {
            if let Some(callees) = self.call_edges.get(&current) {
                for callee in callees {
                    if !self.reachable.contains(callee) {
                        self.reachable.insert(callee.clone());
                        queue.push_back(callee.clone());
                    }
                }
            }
        }
    }

    /// Detect non-trivial cycles in the call graph (excluding RECURSIVE self-calls).
    fn detect_cycles(&mut self) {
        let all_ops: Vec<String> = self.call_edges.keys().cloned().collect();
        let mut color: HashMap<String, u8> = HashMap::new(); // 0=white, 1=gray, 2=black
        let mut path: Vec<String> = Vec::new();
        let mut cycles: Vec<Vec<String>> = Vec::new();

        for op in &all_ops {
            if color.get(op).copied().unwrap_or(0) == 0 {
                self.dfs_cycle(op, &mut color, &mut path, &mut cycles);
            }
        }

        self.cycles = cycles;
    }

    /// DFS helper for cycle detection.
    fn dfs_cycle(
        &self,
        node: &str,
        color: &mut HashMap<String, u8>,
        path: &mut Vec<String>,
        cycles: &mut Vec<Vec<String>>,
    ) {
        color.insert(node.to_string(), 1); // gray
        path.push(node.to_string());

        if let Some(callees) = self.call_edges.get(node) {
            for callee in callees {
                // Skip RECURSIVE self-calls.
                if callee == node && self.recursive_ops.contains(node) {
                    continue;
                }

                match color.get(callee).copied().unwrap_or(0) {
                    0 => {
                        self.dfs_cycle(callee, color, path, cycles);
                    }
                    1 => {
                        // Gray: found a cycle.
                        if let Some(start) = path.iter().position(|n| n == callee) {
                            let cycle: Vec<String> = path[start..].to_vec();
                            if cycle.len() > 1 || !self.recursive_ops.contains(callee) {
                                cycles.push(cycle);
                            }
                        }
                    }
                    _ => {} // black: already processed
                }
            }
        }

        path.pop();
        color.insert(node.to_string(), 2); // black
    }

    /// Get unreachable operators (defined but not reachable from any root).
    pub(crate) fn unreachable_operators(&self) -> Vec<(&str, &OperatorInfo)> {
        self.operators
            .iter()
            .filter(|(name, info)| {
                // Skip standard library operators.
                if tla_core::is_stdlib_module(&info.module) {
                    return false;
                }
                !self.reachable.contains(*name)
            })
            .map(|(name, info)| (name.as_str(), info))
            .collect()
    }
}

/// Expression walker that collects operator calls and variable references.
struct ExprCollector<'a> {
    calls: BTreeSet<String>,
    var_reads: BTreeSet<String>,
    var_writes: BTreeSet<String>,
    variables: &'a HashSet<&'a str>,
    params: &'a HashSet<String>,
    in_prime: bool,
    bound_names: Vec<HashSet<String>>,
}

impl<'a> ExprCollector<'a> {
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
                } else {
                    // Could be an operator reference.
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
                let was_in_prime = self.in_prime;
                self.in_prime = true;
                self.visit_expr(&inner.node);
                self.in_prime = was_in_prime;
            }
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
                let let_names: Vec<String> = defs.iter().map(|d| d.name.node.clone()).collect();
                for def in defs {
                    self.visit_expr(&def.body.node);
                }
                self.push_scope(&let_names);
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
