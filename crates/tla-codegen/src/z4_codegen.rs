// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! TLA+ to Rust code generator targeting z4 SAT solver specifications.
//!
//! Generates standalone Rust modules from TLA+ specs (e.g., `BCP.tla`,
//! `CDCL.tla`, `PDR.tla`) with:
//! - A state struct from `VARIABLES`
//! - `init()` and `next()` functions from `Init`/`Next` operators
//! - Invariant check functions
//! - Kani verification harnesses (`#[kani::proof]`)
//!
//! Type mapping: `Int -> i64`, `Bool -> bool`, `Set -> HashSet`, `Sequence -> Vec`,
//! `Function -> HashMap`, `String -> String`.

use std::collections::{HashMap, HashSet};
use std::fmt::Write;

use tla_core::ast::{Expr, Module, OperatorDef, Unit};

fn emit_floor_int_div(lhs: String, rhs: String) -> String {
    format!(
        "({{ let __a = {lhs}; let __b = {rhs}; let __q = __a / __b; if (__a ^ __b) < 0 && __a % __b != 0 {{ __q - 1 }} else {{ __q }} }})"
    )
}

fn emit_floor_int_mod(lhs: String, rhs: String) -> String {
    // TLA+ % requires positive divisor (b > 0) per TLC semantics.
    // Euclidean mod: let r = a % b; if r < 0 { r + b } else { r }
    format!(
        "({{ let __a = {lhs}; let __b = {rhs}; let __r = __a % __b; if __r < 0 {{ __r + __b }} else {{ __r }} }})"
    )
}

/// Error type for z4 code generation failures.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub enum Z4CodegenError {
    /// The module has no VARIABLE declarations.
    #[error("module has no VARIABLE declarations")]
    NoVariables,

    /// A required operator (Init or Next) is missing.
    #[error("missing required operator: {0}")]
    MissingOperator(String),

    /// An expression could not be translated to Rust.
    #[error("unsupported expression: {0}")]
    UnsupportedExpr(String),
}

/// Configuration for z4 code generation.
#[derive(Debug, Clone)]
pub struct Z4CodegenOptions {
    /// Whether to emit a `#[kani::proof]` harness.
    pub emit_kani_harness: bool,
    /// Maximum BFS depth for the Kani bounded-exploration harness.
    pub kani_unwind: usize,
}

impl Default for Z4CodegenOptions {
    fn default() -> Self {
        Self {
            emit_kani_harness: true,
            kani_unwind: 5,
        }
    }
}

/// Generate a standalone Rust module from a TLA+ module.
///
/// The generated code is self-contained (uses only `std`) and includes:
/// - `State` struct with one field per TLA+ `VARIABLE`
/// - `init() -> Vec<State>` from the `Init` operator
/// - `next(state: &State) -> Vec<State>` from the `Next` operator
/// - One `check_<name>(state: &State) -> bool` per invariant
/// - Optionally, Kani verification harnesses
#[must_use]
pub fn generate_rust_module(module: &Module) -> String {
    generate_rust_module_with_options(module, &Z4CodegenOptions::default())
}

/// Generate a standalone Rust module with explicit options.
#[must_use]
pub fn generate_rust_module_with_options(module: &Module, options: &Z4CodegenOptions) -> String {
    let mut gen = Z4CodeGenerator::new(module);
    gen.generate(options)
}

struct Z4CodeGenerator<'a> {
    module: &'a Module,
    out: String,
    variables: Vec<String>,
    var_set: HashSet<String>,
    _constants: Vec<String>,
    operators: HashMap<String, &'a OperatorDef>,
    invariants: Vec<&'a OperatorDef>,
}

impl<'a> Z4CodeGenerator<'a> {
    fn new(module: &'a Module) -> Self {
        let mut variables = Vec::new();
        let mut var_set = HashSet::new();
        let mut constants = Vec::new();
        let mut operators = HashMap::new();
        let mut invariants = Vec::new();

        for unit in &module.units {
            match &unit.node {
                Unit::Variable(vars) => {
                    for v in vars {
                        variables.push(v.node.clone());
                        var_set.insert(v.node.clone());
                    }
                }
                Unit::Constant(consts) => {
                    for c in consts {
                        constants.push(c.name.node.clone());
                    }
                }
                Unit::Operator(op) => {
                    operators.insert(op.name.node.clone(), op);
                    let name = op.name.node.as_str();
                    if (name.starts_with("Inv") || name.ends_with("Invariant") || name == "TypeOK")
                        && !op.contains_prime
                        && op.params.is_empty()
                    {
                        invariants.push(op);
                    }
                }
                _ => {}
            }
        }

        Self {
            module,
            out: String::with_capacity(4096),
            variables,
            var_set,
            _constants: constants,
            operators,
            invariants,
        }
    }

    fn generate(&mut self, options: &Z4CodegenOptions) -> String {
        self.emit_header();
        self.emit_imports();
        self.emit_state_struct();
        self.emit_init();
        self.emit_next();
        self.emit_invariants();
        if options.emit_kani_harness {
            self.emit_kani_harness(options.kani_unwind);
        }
        self.out.clone()
    }

    fn emit_header(&mut self) {
        let _ = writeln!(
            self.out,
            "//! Generated from TLA+ module: {}",
            self.module.name.node
        );
        let _ = writeln!(self.out, "//!");
        let _ = writeln!(self.out, "//! Auto-generated by tla-codegen z4_codegen.");
        let _ = writeln!(self.out, "//! Do not edit manually.");
        let _ = writeln!(self.out);
        let _ = writeln!(self.out, "#![allow(unused, clippy::all)]");
        let _ = writeln!(self.out);
    }

    fn emit_imports(&mut self) {
        let _ = writeln!(self.out, "use std::collections::{{HashMap, HashSet}};");
        let _ = writeln!(self.out);
    }

    fn emit_state_struct(&mut self) {
        let _ = writeln!(
            self.out,
            "/// State variables for {}",
            self.module.name.node
        );
        let _ = writeln!(self.out, "#[derive(Debug, Clone, PartialEq, Eq, Hash)]");
        let _ = writeln!(self.out, "pub struct State {{");
        for var in &self.variables {
            let rust_name = to_snake(var);
            let rust_type = self.infer_var_type(var);
            let _ = writeln!(self.out, "    pub {rust_name}: {rust_type},");
        }
        let _ = writeln!(self.out, "}}");
        let _ = writeln!(self.out);
    }

    fn infer_var_type(&self, var_name: &str) -> String {
        if let Some(init_op) = self.operators.get("Init") {
            if let Some(ty) = infer_type_from_init_conjuncts(&init_op.body.node, var_name) {
                return ty;
            }
        }
        if let Some(type_ok) = self.operators.get("TypeOK") {
            if let Some(ty) = infer_type_from_typeinv(&type_ok.body.node, var_name) {
                return ty;
            }
        }
        "i64".to_string()
    }

    fn emit_init(&mut self) {
        let _ = writeln!(self.out, "/// Initial states from Init operator.");
        let _ = writeln!(self.out, "pub fn init() -> Vec<State> {{");
        if let Some(init_op) = self.operators.get("Init") {
            self.emit_init_body(&init_op.body.node);
        } else {
            let _ = writeln!(self.out, "    vec![]");
        }
        let _ = writeln!(self.out, "}}");
        let _ = writeln!(self.out);
    }

    fn emit_init_body(&mut self, expr: &Expr) {
        let conjuncts = collect_conjuncts(expr);
        let mut assignments: HashMap<String, String> = HashMap::new();
        for c in &conjuncts {
            if let Expr::Eq(lhs, rhs) = c {
                if let Expr::Ident(name, _) = &lhs.node {
                    if self.var_set.contains(name) {
                        let rust_val = self.expr_to_rust(&rhs.node, false);
                        assignments.insert(name.clone(), rust_val);
                    }
                }
            }
        }
        let _ = writeln!(self.out, "    vec![State {{");
        for var in &self.variables {
            let rust_name = to_snake(var);
            let val = assignments
                .get(var)
                .cloned()
                .unwrap_or_else(|| "Default::default()".to_string());
            let _ = writeln!(self.out, "        {rust_name}: {val},");
        }
        let _ = writeln!(self.out, "    }}]");
    }

    fn emit_next(&mut self) {
        let _ = writeln!(self.out, "/// Successor states from Next operator.");
        let _ = writeln!(self.out, "pub fn next(state: &State) -> Vec<State> {{");
        if let Some(next_op) = self.operators.get("Next") {
            self.emit_next_body(&next_op.body.node);
        } else {
            let _ = writeln!(self.out, "    let _ = state;");
            let _ = writeln!(self.out, "    vec![]");
        }
        let _ = writeln!(self.out, "}}");
        let _ = writeln!(self.out);
    }

    fn emit_next_body(&mut self, expr: &Expr) {
        let disjuncts = collect_disjuncts(expr);
        let _ = writeln!(self.out, "    let mut successors = Vec::new();");
        for action in &disjuncts {
            self.emit_action(action);
        }
        let _ = writeln!(self.out, "    successors");
    }

    fn emit_action(&mut self, expr: &Expr) {
        let conjuncts = collect_conjuncts(expr);
        let mut guards = Vec::new();
        let mut primed_assigns: HashMap<String, String> = HashMap::new();
        let mut unchanged_vars: HashSet<String> = HashSet::new();

        for c in &conjuncts {
            match c {
                Expr::Eq(lhs, rhs) => {
                    if let Expr::Prime(inner) = &lhs.node {
                        if let Expr::Ident(name, _) = &inner.node {
                            if self.var_set.contains(name) {
                                let rust_val = self.expr_to_rust(&rhs.node, true);
                                primed_assigns.insert(name.clone(), rust_val);
                                continue;
                            }
                        }
                    }
                    guards.push(self.expr_to_rust(c, true));
                }
                Expr::Unchanged(inner) => {
                    self.collect_unchanged_vars(&inner.node, &mut unchanged_vars);
                }
                _ => {
                    guards.push(self.expr_to_rust(c, true));
                }
            }
        }

        let _ = writeln!(self.out, "    {{");
        if !guards.is_empty() {
            let guard_str = guards.join(" && ");
            let _ = writeln!(self.out, "        if {guard_str} {{");
        }
        let indent = if guards.is_empty() {
            "        "
        } else {
            "            "
        };
        let _ = writeln!(self.out, "{indent}let next = State {{");
        for var in &self.variables {
            let rust_name = to_snake(var);
            if let Some(val) = primed_assigns.get(var) {
                let _ = writeln!(self.out, "{indent}    {rust_name}: {val},");
            } else {
                let _ = writeln!(
                    self.out,
                    "{indent}    {rust_name}: state.{rust_name}.clone(),"
                );
            }
        }
        let _ = writeln!(self.out, "{indent}}};");
        let _ = writeln!(self.out, "{indent}successors.push(next);");
        if !guards.is_empty() {
            let _ = writeln!(self.out, "        }}");
        }
        let _ = writeln!(self.out, "    }}");
    }

    fn collect_unchanged_vars(&self, expr: &Expr, out: &mut HashSet<String>) {
        match expr {
            Expr::Ident(name, _) if self.var_set.contains(name) => {
                out.insert(name.clone());
            }
            Expr::Tuple(elems) => {
                for e in elems {
                    self.collect_unchanged_vars(&e.node, out);
                }
            }
            _ => {}
        }
    }

    fn emit_invariants(&mut self) {
        for inv in &self.invariants.clone() {
            let fn_name = to_snake(&inv.name.node);
            let _ = writeln!(self.out, "/// Invariant: {}", inv.name.node);
            let _ = writeln!(self.out, "pub fn check_{fn_name}(state: &State) -> bool {{");
            let body_rust = self.expr_to_rust(&inv.body.node, true);
            let _ = writeln!(self.out, "    {body_rust}");
            let _ = writeln!(self.out, "}}");
            let _ = writeln!(self.out);
        }
    }

    fn emit_kani_harness(&mut self, unwind: usize) {
        let _ = writeln!(self.out, "#[cfg(kani)]");
        let _ = writeln!(self.out, "mod kani_proofs {{");
        let _ = writeln!(self.out, "    use super::*;");
        let _ = writeln!(self.out);
        let _ = writeln!(self.out, "    #[kani::proof]");
        let _ = writeln!(self.out, "    fn init_satisfies_invariants() {{");
        let _ = writeln!(self.out, "        let states = init();");
        let _ = writeln!(self.out, "        for state in &states {{");
        for inv in &self.invariants {
            let fn_name = to_snake(&inv.name.node);
            let _ = writeln!(
                self.out,
                "            kani::assert(check_{fn_name}(state), \"{} violated in init\");",
                inv.name.node
            );
        }
        let _ = writeln!(self.out, "        }}");
        let _ = writeln!(self.out, "    }}");
        let _ = writeln!(self.out);
        let _ = writeln!(self.out, "    #[kani::proof]");
        let _ = writeln!(self.out, "    #[kani::unwind({unwind})]");
        let _ = writeln!(self.out, "    fn next_preserves_invariants() {{");
        let _ = writeln!(self.out, "        let init_states = init();");
        let _ = writeln!(self.out, "        if init_states.is_empty() {{ return; }}");
        let _ = writeln!(self.out, "        let idx: usize = kani::any();");
        let _ = writeln!(self.out, "        kani::assume(idx < init_states.len());");
        let _ = writeln!(self.out, "        let state = &init_states[idx];");
        for inv in &self.invariants {
            let fn_name = to_snake(&inv.name.node);
            let _ = writeln!(self.out, "        kani::assume(check_{fn_name}(state));");
        }
        let _ = writeln!(self.out, "        let next_states = next(state);");
        let _ = writeln!(self.out, "        for ns in &next_states {{");
        for inv in &self.invariants {
            let fn_name = to_snake(&inv.name.node);
            let _ = writeln!(
                self.out,
                "            kani::assert(check_{fn_name}(ns), \"{} violated after step\");",
                inv.name.node
            );
        }
        let _ = writeln!(self.out, "        }}");
        let _ = writeln!(self.out, "    }}");
        let _ = writeln!(self.out, "}}");
    }

    fn expr_to_rust(&self, expr: &Expr, prefix_state: bool) -> String {
        match expr {
            Expr::Bool(b) => b.to_string(),
            Expr::Int(n) => format!("{n}_i64"),
            Expr::String(s) => format!("{s:?}.to_string()"),
            Expr::Ident(name, _) => {
                if self.var_set.contains(name) && prefix_state {
                    format!("state.{}", to_snake(name))
                } else {
                    match name.as_str() {
                        "TRUE" => "true".to_string(),
                        "FALSE" => "false".to_string(),
                        "BOOLEAN" => {
                            "vec![true, false].into_iter().collect::<HashSet<bool>>()".to_string()
                        }
                        _ => to_snake(name),
                    }
                }
            }
            Expr::Prime(inner) => {
                if let Expr::Ident(name, _) = &inner.node {
                    format!("{}_next", to_snake(name))
                } else {
                    format!(
                        "/* unsupported prime: */ {}",
                        self.expr_to_rust(&inner.node, prefix_state)
                    )
                }
            }
            Expr::And(a, b) => format!(
                "({} && {})",
                self.expr_to_rust(&a.node, prefix_state),
                self.expr_to_rust(&b.node, prefix_state)
            ),
            Expr::Or(a, b) => format!(
                "({} || {})",
                self.expr_to_rust(&a.node, prefix_state),
                self.expr_to_rust(&b.node, prefix_state)
            ),
            Expr::Not(a) => format!("!{}", self.expr_to_rust(&a.node, prefix_state)),
            Expr::Implies(a, b) => format!(
                "(!{} || {})",
                self.expr_to_rust(&a.node, prefix_state),
                self.expr_to_rust(&b.node, prefix_state)
            ),
            Expr::Equiv(a, b) => format!(
                "({} == {})",
                self.expr_to_rust(&a.node, prefix_state),
                self.expr_to_rust(&b.node, prefix_state)
            ),
            Expr::Eq(a, b) => format!(
                "({} == {})",
                self.expr_to_rust(&a.node, prefix_state),
                self.expr_to_rust(&b.node, prefix_state)
            ),
            Expr::Neq(a, b) => format!(
                "({} != {})",
                self.expr_to_rust(&a.node, prefix_state),
                self.expr_to_rust(&b.node, prefix_state)
            ),
            Expr::Lt(a, b) => format!(
                "({} < {})",
                self.expr_to_rust(&a.node, prefix_state),
                self.expr_to_rust(&b.node, prefix_state)
            ),
            Expr::Leq(a, b) => format!(
                "({} <= {})",
                self.expr_to_rust(&a.node, prefix_state),
                self.expr_to_rust(&b.node, prefix_state)
            ),
            Expr::Gt(a, b) => format!(
                "({} > {})",
                self.expr_to_rust(&a.node, prefix_state),
                self.expr_to_rust(&b.node, prefix_state)
            ),
            Expr::Geq(a, b) => format!(
                "({} >= {})",
                self.expr_to_rust(&a.node, prefix_state),
                self.expr_to_rust(&b.node, prefix_state)
            ),
            Expr::Add(a, b) => format!(
                "({} + {})",
                self.expr_to_rust(&a.node, prefix_state),
                self.expr_to_rust(&b.node, prefix_state)
            ),
            Expr::Sub(a, b) => format!(
                "({} - {})",
                self.expr_to_rust(&a.node, prefix_state),
                self.expr_to_rust(&b.node, prefix_state)
            ),
            Expr::Mul(a, b) => format!(
                "({} * {})",
                self.expr_to_rust(&a.node, prefix_state),
                self.expr_to_rust(&b.node, prefix_state)
            ),
            Expr::Div(a, b) => format!(
                "({} / {})",
                self.expr_to_rust(&a.node, prefix_state),
                self.expr_to_rust(&b.node, prefix_state)
            ),
            Expr::IntDiv(a, b) => emit_floor_int_div(
                self.expr_to_rust(&a.node, prefix_state),
                self.expr_to_rust(&b.node, prefix_state),
            ),
            Expr::Mod(a, b) => emit_floor_int_mod(
                self.expr_to_rust(&a.node, prefix_state),
                self.expr_to_rust(&b.node, prefix_state),
            ),
            Expr::Neg(a) => format!("(-{})", self.expr_to_rust(&a.node, prefix_state)),
            Expr::Pow(a, b) => format!(
                "{}.pow({} as u32)",
                self.expr_to_rust(&a.node, prefix_state),
                self.expr_to_rust(&b.node, prefix_state)
            ),
            Expr::In(elem, set) => {
                if let Expr::Range(lo, hi) = &set.node {
                    let e = self.expr_to_rust(&elem.node, prefix_state);
                    let l = self.expr_to_rust(&lo.node, prefix_state);
                    let h = self.expr_to_rust(&hi.node, prefix_state);
                    format!("({e} >= {l} && {e} <= {h})")
                } else {
                    format!(
                        "{}.contains(&{})",
                        self.expr_to_rust(&set.node, prefix_state),
                        self.expr_to_rust(&elem.node, prefix_state)
                    )
                }
            }
            Expr::NotIn(elem, set) => format!(
                "!{}.contains(&{})",
                self.expr_to_rust(&set.node, prefix_state),
                self.expr_to_rust(&elem.node, prefix_state)
            ),
            Expr::Subseteq(a, b) => format!(
                "{}.is_subset(&{})",
                self.expr_to_rust(&a.node, prefix_state),
                self.expr_to_rust(&b.node, prefix_state)
            ),
            Expr::Union(a, b) => format!(
                "{}.union(&{}).cloned().collect::<HashSet<_>>()",
                self.expr_to_rust(&a.node, prefix_state),
                self.expr_to_rust(&b.node, prefix_state)
            ),
            Expr::Intersect(a, b) => format!(
                "{}.intersection(&{}).cloned().collect::<HashSet<_>>()",
                self.expr_to_rust(&a.node, prefix_state),
                self.expr_to_rust(&b.node, prefix_state)
            ),
            Expr::SetMinus(a, b) => format!(
                "{}.difference(&{}).cloned().collect::<HashSet<_>>()",
                self.expr_to_rust(&a.node, prefix_state),
                self.expr_to_rust(&b.node, prefix_state)
            ),
            Expr::SetEnum(elems) => {
                if elems.is_empty() {
                    "HashSet::new()".to_string()
                } else {
                    let strs: Vec<_> = elems
                        .iter()
                        .map(|e| self.expr_to_rust(&e.node, prefix_state))
                        .collect();
                    format!(
                        "vec![{}].into_iter().collect::<HashSet<_>>()",
                        strs.join(", ")
                    )
                }
            }
            Expr::Range(a, b) => format!(
                "({}..={}).collect::<HashSet<_>>()",
                self.expr_to_rust(&a.node, prefix_state),
                self.expr_to_rust(&b.node, prefix_state)
            ),
            Expr::Tuple(elems) => {
                let strs: Vec<_> = elems
                    .iter()
                    .map(|e| self.expr_to_rust(&e.node, prefix_state))
                    .collect();
                format!("({})", strs.join(", "))
            }
            Expr::FuncApply(func, arg) => format!(
                "{}[{} as usize]",
                self.expr_to_rust(&func.node, prefix_state),
                self.expr_to_rust(&arg.node, prefix_state)
            ),
            Expr::FuncDef(bounds, body) => {
                if bounds.len() == 1 {
                    let bound = &bounds[0];
                    let var_name = to_snake(&bound.name.node);
                    let domain = bound
                        .domain
                        .as_ref()
                        .map(|d| self.expr_to_rust(&d.node, prefix_state))
                        .unwrap_or_else(|| "/* unknown domain */".to_string());
                    let body_str = self.expr_to_rust(&body.node, prefix_state);
                    format!("{domain}.iter().map(|&{var_name}| ({var_name}, {body_str})).collect::<HashMap<_, _>>()")
                } else {
                    "/* unsupported multi-bound FuncDef */".to_string()
                }
            }
            Expr::Record(fields) => {
                let field_strs: Vec<_> = fields
                    .iter()
                    .map(|(k, v)| {
                        format!(
                            "(\"{}\".to_string(), {})",
                            k.node,
                            self.expr_to_rust(&v.node, prefix_state)
                        )
                    })
                    .collect();
                format!(
                    "vec![{}].into_iter().collect::<HashMap<String, _>>()",
                    field_strs.join(", ")
                )
            }
            Expr::RecordAccess(rec, field) => format!(
                "{}[\"{}\"]",
                self.expr_to_rust(&rec.node, prefix_state),
                field.name.node
            ),
            Expr::Except(base, specs) => {
                let base_str = self.expr_to_rust(&base.node, prefix_state);
                let mut result = format!("{{ let mut __ex = {base_str}.clone(); ");
                for spec in specs {
                    if let Some(tla_core::ast::ExceptPathElement::Index(idx)) = spec.path.first() {
                        let key = self.expr_to_rust(&idx.node, prefix_state);
                        let val = self.expr_to_rust(&spec.value.node, prefix_state);
                        result.push_str(&format!("__ex.insert({key}, {val}); "));
                    }
                }
                result.push_str("__ex }");
                result
            }
            Expr::Forall(bounds, body) => {
                self.emit_quantifier_expr("all", bounds, body, prefix_state)
            }
            Expr::Exists(bounds, body) => {
                self.emit_quantifier_expr("any", bounds, body, prefix_state)
            }
            Expr::Choose(bound, pred) => {
                let var_name = to_snake(&bound.name.node);
                let domain = bound
                    .domain
                    .as_ref()
                    .map(|d| self.expr_to_rust(&d.node, prefix_state))
                    .unwrap_or_else(|| "/* unknown domain */".to_string());
                let body_str = self.expr_to_rust(&pred.node, prefix_state);
                format!("*{domain}.iter().find(|&&{var_name}| {body_str}).expect(\"CHOOSE: no matching element\")")
            }
            Expr::SetBuilder(body, bounds) => {
                if bounds.len() == 1 {
                    let bound = &bounds[0];
                    let var_name = to_snake(&bound.name.node);
                    let domain = bound
                        .domain
                        .as_ref()
                        .map(|d| self.expr_to_rust(&d.node, prefix_state))
                        .unwrap_or_else(|| "/* unknown domain */".to_string());
                    let body_str = self.expr_to_rust(&body.node, prefix_state);
                    format!("{domain}.iter().map(|&{var_name}| {body_str}).collect::<HashSet<_>>()")
                } else {
                    "/* unsupported multi-bound SetBuilder */".to_string()
                }
            }
            Expr::SetFilter(bound, pred) => {
                let var_name = to_snake(&bound.name.node);
                let domain = bound
                    .domain
                    .as_ref()
                    .map(|d| self.expr_to_rust(&d.node, prefix_state))
                    .unwrap_or_else(|| "/* unknown domain */".to_string());
                let body_str = self.expr_to_rust(&pred.node, prefix_state);
                format!("{domain}.iter().filter(|&&{var_name}| {body_str}).cloned().collect::<HashSet<_>>()")
            }
            Expr::If(cond, then_e, else_e) => format!(
                "if {} {{ {} }} else {{ {} }}",
                self.expr_to_rust(&cond.node, prefix_state),
                self.expr_to_rust(&then_e.node, prefix_state),
                self.expr_to_rust(&else_e.node, prefix_state)
            ),
            Expr::Let(defs, body) => {
                let mut result = "{\n".to_string();
                for def in defs {
                    let name = to_snake(&def.name.node);
                    let val = self.expr_to_rust(&def.body.node, prefix_state);
                    if def.params.is_empty() {
                        result.push_str(&format!("    let {name} = {val};\n"));
                    } else {
                        let params: Vec<_> = def
                            .params
                            .iter()
                            .map(|p| format!("{}: _", to_snake(&p.name.node)))
                            .collect();
                        result.push_str(&format!(
                            "    let {name} = |{}| {val};\n",
                            params.join(", ")
                        ));
                    }
                }
                let body_str = self.expr_to_rust(&body.node, prefix_state);
                result.push_str(&format!("    {body_str}\n}}"));
                result
            }
            Expr::Case(arms, other) => {
                let mut result = String::new();
                for (i, arm) in arms.iter().enumerate() {
                    let cond = self.expr_to_rust(&arm.guard.node, prefix_state);
                    let body = self.expr_to_rust(&arm.body.node, prefix_state);
                    if i == 0 {
                        result.push_str(&format!("if {cond} {{ {body} }}"));
                    } else {
                        result.push_str(&format!(" else if {cond} {{ {body} }}"));
                    }
                }
                if let Some(default) = other {
                    let d = self.expr_to_rust(&default.node, prefix_state);
                    result.push_str(&format!(" else {{ {d} }}"));
                } else {
                    result.push_str(" else { panic!(\"CASE: no matching arm\") }");
                }
                result
            }
            Expr::Apply(op_expr, args) => {
                if let Expr::Ident(name, _) = &op_expr.node {
                    self.translate_apply(name, args, prefix_state)
                } else {
                    let op_str = self.expr_to_rust(&op_expr.node, prefix_state);
                    let arg_strs: Vec<_> = args
                        .iter()
                        .map(|a| self.expr_to_rust(&a.node, prefix_state))
                        .collect();
                    format!("{op_str}({})", arg_strs.join(", "))
                }
            }
            Expr::Unchanged(_) => "true".to_string(),
            Expr::Label(label) => self.expr_to_rust(&label.body.node, prefix_state),
            Expr::Domain(f) => format!(
                "{}.keys().cloned().collect::<HashSet<_>>()",
                self.expr_to_rust(&f.node, prefix_state)
            ),
            _ => format!("/* unsupported: {:?} */", std::mem::discriminant(expr)),
        }
    }

    fn emit_quantifier_expr(
        &self,
        method: &str,
        bounds: &[tla_core::ast::BoundVar],
        body: &tla_core::span::Spanned<Expr>,
        prefix_state: bool,
    ) -> String {
        if bounds.len() == 1 {
            let bound = &bounds[0];
            let var_name = to_snake(&bound.name.node);
            let domain = bound
                .domain
                .as_ref()
                .map(|d| self.expr_to_rust(&d.node, prefix_state))
                .unwrap_or_else(|| "/* unknown domain */".to_string());
            let body_str = self.expr_to_rust(&body.node, prefix_state);
            format!("{domain}.iter().{method}(|&{var_name}| {body_str})")
        } else {
            let mut result = String::new();
            let mut var_names = Vec::new();
            let mut domains = Vec::new();
            for bound in bounds {
                var_names.push(to_snake(&bound.name.node));
                domains.push(
                    bound
                        .domain
                        .as_ref()
                        .map(|d| self.expr_to_rust(&d.node, prefix_state))
                        .unwrap_or_else(|| "/* unknown domain */".to_string()),
                );
            }
            let body_str = self.expr_to_rust(&body.node, prefix_state);
            for i in 0..var_names.len() {
                result.push_str(&format!(
                    "{}.iter().{method}(|&{}| ",
                    domains[i], var_names[i]
                ));
            }
            result.push_str(&body_str);
            for _ in 0..var_names.len() {
                result.push(')');
            }
            result
        }
    }

    fn translate_apply(
        &self,
        name: &str,
        args: &[tla_core::span::Spanned<Expr>],
        prefix_state: bool,
    ) -> String {
        match name {
            "Append" if args.len() == 2 => {
                let seq = self.expr_to_rust(&args[0].node, prefix_state);
                let elem = self.expr_to_rust(&args[1].node, prefix_state);
                format!("{{ let mut __s = {seq}.clone(); __s.push({elem}); __s }}")
            }
            "Len" if args.len() == 1 => format!(
                "{}.len() as i64",
                self.expr_to_rust(&args[0].node, prefix_state)
            ),
            "Head" if args.len() == 1 => format!(
                "{}[0].clone()",
                self.expr_to_rust(&args[0].node, prefix_state)
            ),
            "Tail" if args.len() == 1 => format!(
                "{}[1..].to_vec()",
                self.expr_to_rust(&args[0].node, prefix_state)
            ),
            "SubSeq" if args.len() == 3 => {
                let seq = self.expr_to_rust(&args[0].node, prefix_state);
                let lo = self.expr_to_rust(&args[1].node, prefix_state);
                let hi = self.expr_to_rust(&args[2].node, prefix_state);
                format!("{seq}[({lo} as usize - 1)..({hi} as usize)].to_vec()")
            }
            "Cardinality" if args.len() == 1 => format!(
                "{}.len() as i64",
                self.expr_to_rust(&args[0].node, prefix_state)
            ),
            "IsFiniteSet" if args.len() == 1 => {
                let _ = self.expr_to_rust(&args[0].node, prefix_state);
                "true".to_string()
            }
            _ => {
                if let Some(op_def) = self.operators.get(name) {
                    if op_def.params.is_empty() && args.is_empty() {
                        self.expr_to_rust(&op_def.body.node, prefix_state)
                    } else {
                        let fn_name = to_snake(name);
                        let arg_strs: Vec<_> = args
                            .iter()
                            .map(|a| self.expr_to_rust(&a.node, prefix_state))
                            .collect();
                        format!("{fn_name}({})", arg_strs.join(", "))
                    }
                } else {
                    let fn_name = to_snake(name);
                    let arg_strs: Vec<_> = args
                        .iter()
                        .map(|a| self.expr_to_rust(&a.node, prefix_state))
                        .collect();
                    format!("{fn_name}({})", arg_strs.join(", "))
                }
            }
        }
    }
}

fn to_snake(s: &str) -> String {
    let mut result = String::new();
    for (i, c) in s.chars().enumerate() {
        if c.is_uppercase() && i > 0 {
            result.push('_');
        }
        result.push(c.to_ascii_lowercase());
    }
    result
}

fn collect_conjuncts(expr: &Expr) -> Vec<&Expr> {
    let mut out = Vec::new();
    collect_conjuncts_rec(expr, &mut out);
    out
}
fn collect_conjuncts_rec<'a>(expr: &'a Expr, out: &mut Vec<&'a Expr>) {
    match expr {
        Expr::And(a, b) => {
            collect_conjuncts_rec(&a.node, out);
            collect_conjuncts_rec(&b.node, out);
        }
        Expr::Label(label) => collect_conjuncts_rec(&label.body.node, out),
        _ => out.push(expr),
    }
}

fn collect_disjuncts(expr: &Expr) -> Vec<&Expr> {
    let mut out = Vec::new();
    collect_disjuncts_rec(expr, &mut out);
    out
}
fn collect_disjuncts_rec<'a>(expr: &'a Expr, out: &mut Vec<&'a Expr>) {
    match expr {
        Expr::Or(a, b) => {
            collect_disjuncts_rec(&a.node, out);
            collect_disjuncts_rec(&b.node, out);
        }
        Expr::Label(label) => collect_disjuncts_rec(&label.body.node, out),
        _ => out.push(expr),
    }
}

fn infer_type_from_init_conjuncts(expr: &Expr, var_name: &str) -> Option<String> {
    for c in collect_conjuncts(expr) {
        if let Expr::Eq(lhs, rhs) = c {
            if let Expr::Ident(name, _) = &lhs.node {
                if name == var_name {
                    return Some(infer_type_from_expr(&rhs.node));
                }
            }
        }
        if let Expr::In(elem, set) = c {
            if let Expr::Ident(name, _) = &elem.node {
                if name == var_name {
                    return infer_element_type_from_set(&set.node);
                }
            }
        }
    }
    None
}

fn infer_type_from_typeinv(expr: &Expr, var_name: &str) -> Option<String> {
    for c in collect_conjuncts(expr) {
        if let Expr::In(elem, set) = c {
            if let Expr::Ident(name, _) = &elem.node {
                if name == var_name {
                    return infer_element_type_from_set(&set.node);
                }
            }
        }
    }
    None
}

fn infer_type_from_expr(expr: &Expr) -> String {
    match expr {
        Expr::Bool(_) => "bool".to_string(),
        Expr::Int(_) => "i64".to_string(),
        Expr::String(_) => "String".to_string(),
        Expr::SetEnum(elems) => {
            if let Some(first) = elems.first() {
                format!("HashSet<{}>", infer_type_from_expr(&first.node))
            } else {
                "HashSet<i64>".to_string()
            }
        }
        Expr::SetBuilder(_, _) | Expr::SetFilter(_, _) | Expr::Range(_, _) => {
            "HashSet<i64>".to_string()
        }
        Expr::Tuple(elems) => {
            let types: Vec<_> = elems
                .iter()
                .map(|e| infer_type_from_expr(&e.node))
                .collect();
            format!("({})", types.join(", "))
        }
        Expr::FuncDef(bounds, body) => {
            let key_ty = bounds
                .first()
                .and_then(|b| {
                    b.domain
                        .as_ref()
                        .and_then(|d| infer_element_type_from_set(&d.node))
                })
                .unwrap_or_else(|| "i64".to_string());
            let val_ty = infer_type_from_expr(&body.node);
            format!("HashMap<{key_ty}, {val_ty}>")
        }
        _ => "i64".to_string(),
    }
}

fn infer_element_type_from_set(expr: &Expr) -> Option<String> {
    match expr {
        Expr::SetEnum(elems) => elems
            .first()
            .map(|first| infer_type_from_expr(&first.node))
            .or(Some("i64".to_string())),
        Expr::Range(_, _) => Some("i64".to_string()),
        Expr::Ident(name, _) => match name.as_str() {
            "BOOLEAN" => Some("bool".to_string()),
            "Nat" | "Int" => Some("i64".to_string()),
            "STRING" => Some("String".to_string()),
            _ => None,
        },
        Expr::FuncSet(domain, range) => {
            let k = infer_element_type_from_set(&domain.node).unwrap_or("i64".to_string());
            let v = infer_element_type_from_set(&range.node).unwrap_or("i64".to_string());
            Some(format!("HashMap<{k}, {v}>"))
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tla_core::ast::{Module, OperatorDef, Unit};
    use tla_core::name_intern::NameId;
    use tla_core::span::{FileId, Span, Spanned};

    fn span() -> Span {
        Span::new(FileId(0), 0, 0)
    }
    fn s<T>(node: T) -> Spanned<T> {
        Spanned::new(node, span())
    }

    fn floor_intdiv_expr(lhs: i64, rhs: i64) -> String {
        format!(
            "({{ let __a = {lhs}_i64; let __b = {rhs}_i64; let __q = __a / __b; if (__a ^ __b) < 0 && __a % __b != 0 {{ __q - 1 }} else {{ __q }} }})"
        )
    }

    fn make_counter_module() -> Module {
        let init_body = Expr::Eq(
            Box::new(s(Expr::Ident("count".to_string(), NameId::INVALID))),
            Box::new(s(Expr::Int(0.into()))),
        );
        let next_body = Expr::Eq(
            Box::new(s(Expr::Prime(Box::new(s(Expr::Ident(
                "count".to_string(),
                NameId::INVALID,
            )))))),
            Box::new(s(Expr::Add(
                Box::new(s(Expr::Ident("count".to_string(), NameId::INVALID))),
                Box::new(s(Expr::Int(1.into()))),
            ))),
        );
        let inv_body = Expr::Geq(
            Box::new(s(Expr::Ident("count".to_string(), NameId::INVALID))),
            Box::new(s(Expr::Int(0.into()))),
        );
        Module {
            name: s("Counter".to_string()),
            extends: vec![],
            units: vec![
                s(Unit::Variable(vec![s("count".to_string())])),
                s(Unit::Operator(OperatorDef {
                    name: s("Init".to_string()),
                    params: vec![],
                    body: s(init_body),
                    local: false,
                    contains_prime: false,
                    guards_depend_on_prime: false,
                    has_primed_param: false,
                    is_recursive: false,
                    self_call_count: 0,
                })),
                s(Unit::Operator(OperatorDef {
                    name: s("Next".to_string()),
                    params: vec![],
                    body: s(next_body),
                    local: false,
                    contains_prime: true,
                    guards_depend_on_prime: false,
                    has_primed_param: false,
                    is_recursive: false,
                    self_call_count: 0,
                })),
                s(Unit::Operator(OperatorDef {
                    name: s("InvNonNeg".to_string()),
                    params: vec![],
                    body: s(inv_body),
                    local: false,
                    contains_prime: false,
                    guards_depend_on_prime: false,
                    has_primed_param: false,
                    is_recursive: false,
                    self_call_count: 0,
                })),
            ],
            action_subscript_spans: Default::default(),
            span: span(),
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_z4_generate_counter_contains_struct() {
        let module = make_counter_module();
        let code = generate_rust_module(&module);
        assert!(
            code.contains("pub struct State"),
            "generated code should contain State struct"
        );
        assert!(
            code.contains("pub count: i64"),
            "generated code should contain count field with i64 type"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_z4_generate_counter_contains_init() {
        let module = make_counter_module();
        let code = generate_rust_module(&module);
        assert!(
            code.contains("pub fn init()"),
            "generated code should contain init function"
        );
        assert!(
            code.contains("count: 0_i64"),
            "init should assign count to 0"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_z4_generate_counter_contains_next() {
        let module = make_counter_module();
        let code = generate_rust_module(&module);
        assert!(
            code.contains("pub fn next("),
            "generated code should contain next function"
        );
        assert!(
            code.contains("state.count"),
            "next should reference state.count"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_z4_generate_counter_contains_invariant() {
        let module = make_counter_module();
        let code = generate_rust_module(&module);
        assert!(
            code.contains("pub fn check_inv_non_neg("),
            "generated code should contain invariant check function"
        );
        assert!(
            code.contains("state.count >= 0_i64"),
            "invariant should check count >= 0"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_z4_generate_counter_contains_kani_harness() {
        let module = make_counter_module();
        let code = generate_rust_module(&module);
        assert!(
            code.contains("#[kani::proof]"),
            "generated code should contain Kani proof attribute"
        );
        assert!(
            code.contains("init_satisfies_invariants"),
            "generated code should contain init invariant proof"
        );
        assert!(
            code.contains("next_preserves_invariants"),
            "generated code should contain preservation proof"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_z4_generate_no_kani_when_disabled() {
        let module = make_counter_module();
        let options = Z4CodegenOptions {
            emit_kani_harness: false,
            ..Default::default()
        };
        let code = generate_rust_module_with_options(&module, &options);
        assert!(
            !code.contains("#[kani::proof]"),
            "should not contain Kani harness when disabled"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_z4_generate_imports() {
        let module = make_counter_module();
        let code = generate_rust_module(&module);
        assert!(
            code.contains("use std::collections::{HashMap, HashSet}"),
            "generated code should import HashMap and HashSet"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_z4_type_inference_bool_variable() {
        let init_body = Expr::Eq(
            Box::new(s(Expr::Ident("flag".to_string(), NameId::INVALID))),
            Box::new(s(Expr::Bool(true))),
        );
        let module = Module {
            name: s("BoolTest".to_string()),
            extends: vec![],
            units: vec![
                s(Unit::Variable(vec![s("flag".to_string())])),
                s(Unit::Operator(OperatorDef {
                    name: s("Init".to_string()),
                    params: vec![],
                    body: s(init_body),
                    local: false,
                    contains_prime: false,
                    guards_depend_on_prime: false,
                    has_primed_param: false,
                    is_recursive: false,
                    self_call_count: 0,
                })),
            ],
            action_subscript_spans: Default::default(),
            span: span(),
        };
        let code = generate_rust_module(&module);
        assert!(
            code.contains("pub flag: bool"),
            "flag should be inferred as bool, got:\n{code}"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_z4_type_inference_set_variable() {
        let init_body = Expr::Eq(
            Box::new(s(Expr::Ident("items".to_string(), NameId::INVALID))),
            Box::new(s(Expr::SetEnum(vec![
                s(Expr::Int(1.into())),
                s(Expr::Int(2.into())),
                s(Expr::Int(3.into())),
            ]))),
        );
        let module = Module {
            name: s("SetTest".to_string()),
            extends: vec![],
            units: vec![
                s(Unit::Variable(vec![s("items".to_string())])),
                s(Unit::Operator(OperatorDef {
                    name: s("Init".to_string()),
                    params: vec![],
                    body: s(init_body),
                    local: false,
                    contains_prime: false,
                    guards_depend_on_prime: false,
                    has_primed_param: false,
                    is_recursive: false,
                    self_call_count: 0,
                })),
            ],
            action_subscript_spans: Default::default(),
            span: span(),
        };
        let code = generate_rust_module(&module);
        assert!(
            code.contains("pub items: HashSet<i64>"),
            "items should be inferred as HashSet<i64>, got:\n{code}"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_z4_collect_conjuncts() {
        let expr = Expr::And(
            Box::new(s(Expr::Bool(true))),
            Box::new(s(Expr::And(
                Box::new(s(Expr::Bool(false))),
                Box::new(s(Expr::Int(42.into()))),
            ))),
        );
        assert_eq!(
            collect_conjuncts(&expr).len(),
            3,
            "should flatten nested And into 3 conjuncts"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_z4_collect_disjuncts() {
        let expr = Expr::Or(
            Box::new(s(Expr::Bool(true))),
            Box::new(s(Expr::Bool(false))),
        );
        assert_eq!(
            collect_disjuncts(&expr).len(),
            2,
            "should flatten Or into 2 disjuncts"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_z4_to_snake() {
        assert_eq!(to_snake("NumVars"), "num_vars");
        assert_eq!(to_snake("assignment"), "assignment");
        assert_eq!(to_snake("TrailConsistent"), "trail_consistent");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_z4_expr_to_rust_intdiv_negative_dividend() {
        let module = make_counter_module();
        let generator = Z4CodeGenerator::new(&module);
        let expr = Expr::IntDiv(
            Box::new(s(Expr::Int((-7).into()))),
            Box::new(s(Expr::Int(2.into()))),
        );

        assert_eq!(
            generator.expr_to_rust(&expr, false),
            floor_intdiv_expr(-7, 2)
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_z4_expr_to_rust_intdiv_negative_divisor() {
        let module = make_counter_module();
        let generator = Z4CodeGenerator::new(&module);
        let expr = Expr::IntDiv(
            Box::new(s(Expr::Int(7.into()))),
            Box::new(s(Expr::Int((-2).into()))),
        );

        assert_eq!(
            generator.expr_to_rust(&expr, false),
            floor_intdiv_expr(7, -2)
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_z4_expr_to_rust_intdiv_both_negative() {
        let module = make_counter_module();
        let generator = Z4CodeGenerator::new(&module);
        let expr = Expr::IntDiv(
            Box::new(s(Expr::Int((-7).into()))),
            Box::new(s(Expr::Int((-2).into()))),
        );

        assert_eq!(
            generator.expr_to_rust(&expr, false),
            floor_intdiv_expr(-7, -2)
        );
    }

    fn floor_intmod_expr(lhs: i64, rhs: i64) -> String {
        format!(
            "({{ let __a = {lhs}_i64; let __b = {rhs}_i64; let __r = __a % __b; if __r < 0 {{ __r + __b }} else {{ __r }} }})"
        )
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_z4_expr_to_rust_mod_negative_dividend() {
        let module = make_counter_module();
        let generator = Z4CodeGenerator::new(&module);
        let expr = Expr::Mod(
            Box::new(s(Expr::Int((-7).into()))),
            Box::new(s(Expr::Int(3.into()))),
        );

        // TLA+ (-7) % 3 = 2 (Euclidean mod)
        assert_eq!(
            generator.expr_to_rust(&expr, false),
            floor_intmod_expr(-7, 3)
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_z4_expr_to_rust_mod_positive_both() {
        let module = make_counter_module();
        let generator = Z4CodeGenerator::new(&module);
        let expr = Expr::Mod(
            Box::new(s(Expr::Int(7.into()))),
            Box::new(s(Expr::Int(3.into()))),
        );

        // TLA+ 7 % 3 = 1
        assert_eq!(
            generator.expr_to_rust(&expr, false),
            floor_intmod_expr(7, 3)
        );
    }
}
