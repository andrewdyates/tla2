// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `tla2 inline` -- inline INSTANCE modules into a self-contained TLA+ spec.
//!
//! Parses a TLA+ specification, identifies all `INSTANCE` declarations (both
//! standalone and named), resolves the referenced module files, and produces a
//! single combined spec with no INSTANCE dependencies. Standard library modules
//! (Naturals, Integers, Sequences, etc.) are left as EXTENDS and not inlined.
//!
//! Useful for:
//! - Distributing specs without multi-file dependencies
//! - Simplifying specs for tools that lack multi-module support
//! - Understanding what a spec actually defines after expansion

use std::collections::{BTreeSet, HashMap};
use std::io::Write as _;
use std::path::Path;

use anyhow::{bail, Context, Result};
use tla_core::ast::{
    BoundVar, CaseArm, ExceptPathElement, ExceptSpec, Expr, ExprLabel, InstanceDecl, Module,
    OperatorDef, Substitution, Unit,
};
use tla_core::{
    is_stdlib_module, lower_main_module, pretty_module, FileId, ModuleLoader,
    Spanned,
};

use crate::helpers::{parse_or_report, read_source};

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Inline INSTANCE dependencies into a self-contained TLA+ specification.
///
/// - `file`: path to the main .tla file
/// - `output`: optional output path (None = stdout)
/// - `keep_comments`: if true, inserts comment markers showing inlined origins
pub(crate) fn cmd_inline(
    file: &Path,
    output: Option<&Path>,
    keep_comments: bool,
) -> Result<()> {
    let source = read_source(file)?;
    let tree = parse_or_report(file, &source)?;

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

    // Load all dependencies via ModuleLoader.
    let mut loader = ModuleLoader::new(file);
    loader.seed_from_syntax_tree(&tree, file);
    let _ = loader.load_extends(&module);
    let _ = loader.load_instances(&module);

    // Perform inlining.
    let mut ctx = InlineCtx::new(&loader, keep_comments);
    let inlined = ctx.inline_module(&module);

    // Emit output.
    let output_text = pretty_module(&inlined);

    match output {
        Some(path) => {
            std::fs::write(path, &output_text)
                .with_context(|| format!("write {}", path.display()))?;
            eprintln!("wrote inlined spec to {}", path.display());
        }
        None => {
            let stdout = std::io::stdout();
            let mut handle = stdout.lock();
            handle
                .write_all(output_text.as_bytes())
                .context("write to stdout")?;
        }
    }

    // Report summary.
    report_summary(&ctx);

    Ok(())
}

/// Print a summary of which modules were inlined and which were not.
fn report_summary(ctx: &InlineCtx<'_>) {
    if !ctx.inlined_modules.is_empty() {
        let names: Vec<&str> = ctx.inlined_modules.iter().map(|s| s.as_str()).collect();
        eprintln!("inlined {} module(s): {}", names.len(), names.join(", "));
    }
    if !ctx.skipped_modules.is_empty() {
        let entries: Vec<String> = ctx
            .skipped_modules
            .iter()
            .map(|(name, reason)| format!("{name} ({reason})"))
            .collect();
        eprintln!("skipped {} module(s): {}", entries.len(), entries.join(", "));
    }
}

// ---------------------------------------------------------------------------
// Inlining context
// ---------------------------------------------------------------------------

/// Tracks state during the inlining process.
struct InlineCtx<'a> {
    loader: &'a ModuleLoader,
    keep_comments: bool,
    /// Modules successfully inlined (in order of first encounter).
    inlined_modules: Vec<String>,
    /// Modules skipped with reason (stdlib, not found, etc.).
    skipped_modules: Vec<(String, String)>,
    /// Set of module names already processed (to avoid duplicates).
    visited: BTreeSet<String>,
}

impl<'a> InlineCtx<'a> {
    fn new(loader: &'a ModuleLoader, keep_comments: bool) -> Self {
        Self {
            loader,
            keep_comments,
            inlined_modules: Vec::new(),
            skipped_modules: Vec::new(),
            visited: BTreeSet::new(),
        }
    }

    /// Inline all INSTANCE declarations in the given module, returning a new
    /// self-contained Module.
    fn inline_module(&mut self, module: &Module) -> Module {
        let mut new_units: Vec<Spanned<Unit>> = Vec::new();

        for unit in &module.units {
            match &unit.node {
                Unit::Instance(inst) => {
                    self.inline_instance_decl(inst, &mut new_units);
                }
                Unit::Operator(def) => {
                    match &def.body.node {
                        Expr::InstanceExpr(mod_name, subs) => {
                            // Named instance: Op == INSTANCE M WITH ...
                            self.inline_named_instance(def, mod_name, subs, &mut new_units);
                        }
                        _ => {
                            // Regular operator -- keep as-is.
                            new_units.push(unit.clone());
                        }
                    }
                }
                _ => {
                    // Variables, constants, recursive, assume, theorem, separator --
                    // keep unchanged.
                    new_units.push(unit.clone());
                }
            }
        }

        Module {
            name: module.name.clone(),
            extends: module.extends.clone(),
            units: new_units,
            action_subscript_spans: module.action_subscript_spans.clone(),
            span: module.span,
        }
    }

    /// Inline a standalone `INSTANCE M WITH ...` declaration.
    ///
    /// Replaces the INSTANCE unit with the operators, variables, and constants
    /// from the target module (with substitutions applied to operator bodies).
    fn inline_instance_decl(
        &mut self,
        inst: &InstanceDecl,
        out: &mut Vec<Spanned<Unit>>,
    ) {
        let mod_name = &inst.module.node;

        if is_stdlib_module(mod_name) {
            self.record_skip(mod_name, "stdlib");
            // Keep stdlib INSTANCE as-is -- the model checker handles it.
            out.push(Spanned::dummy(Unit::Instance(inst.clone())));
            return;
        }

        let Some(loaded) = self.loader.get(mod_name) else {
            self.record_skip(mod_name, "not found");
            out.push(Spanned::dummy(Unit::Instance(inst.clone())));
            return;
        };

        if !self.visited.insert(mod_name.clone()) {
            // Already inlined this module -- skip to avoid duplicates.
            return;
        }

        self.inlined_modules.push(mod_name.clone());
        let target = &loaded.module;
        let subs = build_substitution_map(&inst.substitutions);

        if self.keep_comments {
            out.push(Spanned::dummy(Unit::Separator));
            let comment_text = format!("Inlined from INSTANCE {mod_name}");
            let assume = tla_core::ast::AssumeDecl {
                name: None,
                expr: Spanned::dummy(Expr::String(comment_text)),
            };
            out.push(Spanned::dummy(Unit::Assume(assume)));
            out.push(Spanned::dummy(Unit::Separator));
        }

        self.emit_module_units(target, &subs, inst.local, out);
    }

    /// Inline a named instance `Op == INSTANCE M WITH ...`.
    ///
    /// Replaces the single operator with prefixed operators from the target
    /// module: `Op_Foo == <body with substitutions>`.
    fn inline_named_instance(
        &mut self,
        def: &OperatorDef,
        mod_name: &str,
        subs: &[Substitution],
        out: &mut Vec<Spanned<Unit>>,
    ) {
        let prefix = &def.name.node;

        if is_stdlib_module(mod_name) {
            self.record_skip(mod_name, "stdlib (named)");
            out.push(Spanned::dummy(Unit::Operator(def.clone())));
            return;
        }

        let Some(loaded) = self.loader.get(mod_name) else {
            self.record_skip(mod_name, "not found (named)");
            out.push(Spanned::dummy(Unit::Operator(def.clone())));
            return;
        };

        // Record that we inlined something from this module.
        if !self.inlined_modules.contains(&mod_name.to_string()) {
            self.inlined_modules.push(mod_name.to_string());
        }

        let target = &loaded.module;
        let sub_map = build_substitution_map(subs);

        if self.keep_comments {
            out.push(Spanned::dummy(Unit::Separator));
            let comment_text = format!("Inlined from {prefix} == INSTANCE {mod_name}");
            let assume = tla_core::ast::AssumeDecl {
                name: None,
                expr: Spanned::dummy(Expr::String(comment_text)),
            };
            out.push(Spanned::dummy(Unit::Assume(assume)));
            out.push(Spanned::dummy(Unit::Separator));
        }

        // Emit operators with prefixed names.
        for unit in &target.units {
            if let Unit::Operator(op) = &unit.node {
                let prefixed_name = format!("{prefix}_{}", op.name.node);
                let new_body = apply_substitutions(&op.body.node, &sub_map);
                let new_op = OperatorDef {
                    name: Spanned::dummy(prefixed_name),
                    params: op.params.clone(),
                    body: Spanned::dummy(new_body),
                    local: def.local || op.local,
                    contains_prime: op.contains_prime,
                    guards_depend_on_prime: op.guards_depend_on_prime,
                    has_primed_param: op.has_primed_param,
                    is_recursive: op.is_recursive,
                    self_call_count: op.self_call_count,
                };
                out.push(Spanned::dummy(Unit::Operator(new_op)));
            }
        }
    }

    /// Emit the units from a module with substitutions applied.
    fn emit_module_units(
        &mut self,
        target: &Module,
        subs: &HashMap<String, Expr>,
        local: bool,
        out: &mut Vec<Spanned<Unit>>,
    ) {
        for unit in &target.units {
            match &unit.node {
                Unit::Variable(vars) => {
                    let remaining: Vec<Spanned<String>> = vars
                        .iter()
                        .filter(|v| !subs.contains_key(&v.node))
                        .cloned()
                        .collect();
                    if !remaining.is_empty() {
                        out.push(Spanned::dummy(Unit::Variable(remaining)));
                    }
                }
                Unit::Constant(consts) => {
                    let remaining: Vec<_> = consts
                        .iter()
                        .filter(|c| !subs.contains_key(&c.name.node))
                        .cloned()
                        .collect();
                    if !remaining.is_empty() {
                        out.push(Spanned::dummy(Unit::Constant(remaining)));
                    }
                }
                Unit::Operator(op) => {
                    let new_body = apply_substitutions(&op.body.node, subs);
                    let new_op = OperatorDef {
                        name: op.name.clone(),
                        params: op.params.clone(),
                        body: Spanned::dummy(new_body),
                        local: local || op.local,
                        contains_prime: op.contains_prime,
                        guards_depend_on_prime: op.guards_depend_on_prime,
                        has_primed_param: op.has_primed_param,
                        is_recursive: op.is_recursive,
                        self_call_count: op.self_call_count,
                    };
                    out.push(Spanned::dummy(Unit::Operator(new_op)));
                }
                Unit::Recursive(decls) => {
                    out.push(Spanned::dummy(Unit::Recursive(decls.clone())));
                }
                Unit::Assume(assume) => {
                    out.push(Spanned::dummy(Unit::Assume(assume.clone())));
                }
                Unit::Theorem(thm) => {
                    out.push(Spanned::dummy(Unit::Theorem(thm.clone())));
                }
                Unit::Instance(nested_inst) => {
                    self.inline_instance_decl(nested_inst, out);
                }
                Unit::Separator => {
                    out.push(Spanned::dummy(Unit::Separator));
                }
            }
        }
    }

    fn record_skip(&mut self, name: &str, reason: &str) {
        if !self.skipped_modules.iter().any(|(n, _)| n == name) {
            self.skipped_modules
                .push((name.to_string(), reason.to_string()));
        }
    }
}

// ---------------------------------------------------------------------------
// Substitution engine
// ---------------------------------------------------------------------------

/// Build a lookup map from substitution name -> replacement expression.
fn build_substitution_map(subs: &[Substitution]) -> HashMap<String, Expr> {
    subs.iter()
        .map(|s| (s.from.node.clone(), s.to.node.clone()))
        .collect()
}

/// Substitute into a binary expression.
macro_rules! binary {
    ($variant:ident, $a:expr, $b:expr, $subs:expr) => {{
        let new_a = apply_substitutions(&$a.node, $subs);
        let new_b = apply_substitutions(&$b.node, $subs);
        Expr::$variant(
            Box::new(Spanned::dummy(new_a)),
            Box::new(Spanned::dummy(new_b)),
        )
    }};
}

/// Substitute into a unary expression.
macro_rules! unary {
    ($variant:ident, $a:expr, $subs:expr) => {{
        let new_a = apply_substitutions(&$a.node, $subs);
        Expr::$variant(Box::new(Spanned::dummy(new_a)))
    }};
}

/// Apply substitutions to an expression tree, replacing `Ident` references
/// that match substitution keys with their replacement expressions.
///
/// This is a structural substitution over the AST -- it replaces identifiers
/// whose name matches a key in the substitution map. For full capture-avoiding
/// substitution, the evaluator handles it at runtime; this structural walk is
/// sufficient for the INSTANCE WITH inlining use case.
fn apply_substitutions(expr: &Expr, subs: &HashMap<String, Expr>) -> Expr {
    if subs.is_empty() {
        return expr.clone();
    }

    match expr {
        Expr::Ident(name, id) => {
            if let Some(replacement) = subs.get(name.as_str()) {
                replacement.clone()
            } else {
                Expr::Ident(name.clone(), *id)
            }
        }
        Expr::StateVar(name, id, idx) => {
            if let Some(replacement) = subs.get(name.as_str()) {
                Expr::Prime(Box::new(Spanned::dummy(replacement.clone())))
            } else {
                Expr::StateVar(name.clone(), *id, *idx)
            }
        }

        // Binary operators.
        Expr::And(a, b) => binary!(And, a, b, subs),
        Expr::Or(a, b) => binary!(Or, a, b, subs),
        Expr::Implies(a, b) => binary!(Implies, a, b, subs),
        Expr::Equiv(a, b) => binary!(Equiv, a, b, subs),
        Expr::In(a, b) => binary!(In, a, b, subs),
        Expr::NotIn(a, b) => binary!(NotIn, a, b, subs),
        Expr::Subseteq(a, b) => binary!(Subseteq, a, b, subs),
        Expr::Union(a, b) => binary!(Union, a, b, subs),
        Expr::Intersect(a, b) => binary!(Intersect, a, b, subs),
        Expr::SetMinus(a, b) => binary!(SetMinus, a, b, subs),
        Expr::FuncSet(a, b) => binary!(FuncSet, a, b, subs),
        Expr::LeadsTo(a, b) => binary!(LeadsTo, a, b, subs),
        Expr::WeakFair(a, b) => binary!(WeakFair, a, b, subs),
        Expr::StrongFair(a, b) => binary!(StrongFair, a, b, subs),
        Expr::Eq(a, b) => binary!(Eq, a, b, subs),
        Expr::Neq(a, b) => binary!(Neq, a, b, subs),
        Expr::Lt(a, b) => binary!(Lt, a, b, subs),
        Expr::Leq(a, b) => binary!(Leq, a, b, subs),
        Expr::Gt(a, b) => binary!(Gt, a, b, subs),
        Expr::Geq(a, b) => binary!(Geq, a, b, subs),
        Expr::Add(a, b) => binary!(Add, a, b, subs),
        Expr::Sub(a, b) => binary!(Sub, a, b, subs),
        Expr::Mul(a, b) => binary!(Mul, a, b, subs),
        Expr::Div(a, b) => binary!(Div, a, b, subs),
        Expr::IntDiv(a, b) => binary!(IntDiv, a, b, subs),
        Expr::Mod(a, b) => binary!(Mod, a, b, subs),
        Expr::Pow(a, b) => binary!(Pow, a, b, subs),
        Expr::Range(a, b) => binary!(Range, a, b, subs),

        // Unary operators.
        Expr::Not(a) => unary!(Not, a, subs),
        Expr::Powerset(a) => unary!(Powerset, a, subs),
        Expr::BigUnion(a) => unary!(BigUnion, a, subs),
        Expr::Domain(a) => unary!(Domain, a, subs),
        Expr::Prime(a) => unary!(Prime, a, subs),
        Expr::Always(a) => unary!(Always, a, subs),
        Expr::Eventually(a) => unary!(Eventually, a, subs),
        Expr::Enabled(a) => unary!(Enabled, a, subs),
        Expr::Unchanged(a) => unary!(Unchanged, a, subs),
        Expr::Neg(a) => unary!(Neg, a, subs),
        Expr::RecordAccess(a, field) => {
            let new_a = apply_substitutions(&a.node, subs);
            Expr::RecordAccess(Box::new(Spanned::dummy(new_a)), field.clone())
        }

        // Quantifiers.
        Expr::Forall(bounds, body) => {
            let new_bounds = subst_bound_vars(bounds, subs);
            let new_body = apply_substitutions(&body.node, subs);
            Expr::Forall(new_bounds, Box::new(Spanned::dummy(new_body)))
        }
        Expr::Exists(bounds, body) => {
            let new_bounds = subst_bound_vars(bounds, subs);
            let new_body = apply_substitutions(&body.node, subs);
            Expr::Exists(new_bounds, Box::new(Spanned::dummy(new_body)))
        }
        Expr::Choose(bound, body) => {
            let new_bound = subst_bound_var(bound, subs);
            let new_body = apply_substitutions(&body.node, subs);
            Expr::Choose(new_bound, Box::new(Spanned::dummy(new_body)))
        }

        // Collections.
        Expr::SetEnum(elems) => Expr::SetEnum(subst_vec(elems, subs)),
        Expr::Tuple(elems) => Expr::Tuple(subst_vec(elems, subs)),
        Expr::Times(elems) => Expr::Times(subst_vec(elems, subs)),
        Expr::SetBuilder(expr, bounds) => {
            let new_expr = apply_substitutions(&expr.node, subs);
            Expr::SetBuilder(Box::new(Spanned::dummy(new_expr)), subst_bound_vars(bounds, subs))
        }
        Expr::SetFilter(bound, pred) => {
            let new_bound = subst_bound_var(bound, subs);
            let new_pred = apply_substitutions(&pred.node, subs);
            Expr::SetFilter(new_bound, Box::new(Spanned::dummy(new_pred)))
        }

        // Functions.
        Expr::FuncDef(bounds, body) => {
            let new_body = apply_substitutions(&body.node, subs);
            Expr::FuncDef(subst_bound_vars(bounds, subs), Box::new(Spanned::dummy(new_body)))
        }
        Expr::FuncApply(f, arg) => {
            let new_f = apply_substitutions(&f.node, subs);
            let new_arg = apply_substitutions(&arg.node, subs);
            Expr::FuncApply(
                Box::new(Spanned::dummy(new_f)),
                Box::new(Spanned::dummy(new_arg)),
            )
        }
        Expr::Except(f, specs) => {
            let new_f = apply_substitutions(&f.node, subs);
            let new_specs: Vec<ExceptSpec> = specs
                .iter()
                .map(|spec| {
                    let new_path: Vec<ExceptPathElement> = spec
                        .path
                        .iter()
                        .map(|p| match p {
                            ExceptPathElement::Index(idx) => ExceptPathElement::Index(
                                Spanned::dummy(apply_substitutions(&idx.node, subs)),
                            ),
                            ExceptPathElement::Field(f) => ExceptPathElement::Field(f.clone()),
                        })
                        .collect();
                    ExceptSpec {
                        path: new_path,
                        value: Spanned::dummy(apply_substitutions(&spec.value.node, subs)),
                    }
                })
                .collect();
            Expr::Except(Box::new(Spanned::dummy(new_f)), new_specs)
        }

        // Records.
        Expr::Record(fields) => {
            let new_fields: Vec<(Spanned<String>, Spanned<Expr>)> = fields
                .iter()
                .map(|(name, expr)| {
                    (name.clone(), Spanned::dummy(apply_substitutions(&expr.node, subs)))
                })
                .collect();
            Expr::Record(new_fields)
        }
        Expr::RecordSet(fields) => {
            let new_fields: Vec<(Spanned<String>, Spanned<Expr>)> = fields
                .iter()
                .map(|(name, expr)| {
                    (name.clone(), Spanned::dummy(apply_substitutions(&expr.node, subs)))
                })
                .collect();
            Expr::RecordSet(new_fields)
        }

        // Control flow.
        Expr::If(c, t, e) => Expr::If(
            Box::new(Spanned::dummy(apply_substitutions(&c.node, subs))),
            Box::new(Spanned::dummy(apply_substitutions(&t.node, subs))),
            Box::new(Spanned::dummy(apply_substitutions(&e.node, subs))),
        ),
        Expr::Case(arms, other) => {
            let new_arms: Vec<CaseArm> = arms
                .iter()
                .map(|arm| CaseArm {
                    guard: Spanned::dummy(apply_substitutions(&arm.guard.node, subs)),
                    body: Spanned::dummy(apply_substitutions(&arm.body.node, subs)),
                })
                .collect();
            let new_other = other
                .as_ref()
                .map(|o| Box::new(Spanned::dummy(apply_substitutions(&o.node, subs))));
            Expr::Case(new_arms, new_other)
        }
        Expr::Let(defs, body) => {
            let new_defs: Vec<OperatorDef> = defs
                .iter()
                .map(|d| OperatorDef {
                    name: d.name.clone(),
                    params: d.params.clone(),
                    body: Spanned::dummy(apply_substitutions(&d.body.node, subs)),
                    local: d.local,
                    contains_prime: d.contains_prime,
                    guards_depend_on_prime: d.guards_depend_on_prime,
                    has_primed_param: d.has_primed_param,
                    is_recursive: d.is_recursive,
                    self_call_count: d.self_call_count,
                })
                .collect();
            Expr::Let(new_defs, Box::new(Spanned::dummy(apply_substitutions(&body.node, subs))))
        }

        // Apply (function/operator application).
        Expr::Apply(op, args) => {
            Expr::Apply(
                Box::new(Spanned::dummy(apply_substitutions(&op.node, subs))),
                subst_vec(args, subs),
            )
        }
        Expr::ModuleRef(module, name, args) => {
            Expr::ModuleRef(module.clone(), name.clone(), subst_vec(args, subs))
        }

        // SubstIn -- nested substitution block.
        Expr::SubstIn(inner_subs, body) => {
            let new_inner: Vec<Substitution> = inner_subs
                .iter()
                .map(|s| Substitution {
                    from: s.from.clone(),
                    to: Spanned::dummy(apply_substitutions(&s.to.node, subs)),
                })
                .collect();
            Expr::SubstIn(
                new_inner,
                Box::new(Spanned::dummy(apply_substitutions(&body.node, subs))),
            )
        }

        // InstanceExpr -- nested inline instance within an expression.
        Expr::InstanceExpr(mod_name, inner_subs) => {
            let new_subs: Vec<Substitution> = inner_subs
                .iter()
                .map(|s| Substitution {
                    from: s.from.clone(),
                    to: Spanned::dummy(apply_substitutions(&s.to.node, subs)),
                })
                .collect();
            Expr::InstanceExpr(mod_name.clone(), new_subs)
        }

        // Lambda.
        Expr::Lambda(params, body) => {
            Expr::Lambda(
                params.clone(),
                Box::new(Spanned::dummy(apply_substitutions(&body.node, subs))),
            )
        }

        // Label.
        Expr::Label(label) => Expr::Label(ExprLabel {
            name: label.name.clone(),
            body: Box::new(Spanned::dummy(apply_substitutions(&label.body.node, subs))),
        }),

        // Leaf nodes -- no substitution needed.
        Expr::Bool(_) | Expr::Int(_) | Expr::String(_) | Expr::OpRef(_) => expr.clone(),
    }
}

// ---------------------------------------------------------------------------
// Bound variable / vector substitution helpers
// ---------------------------------------------------------------------------

fn subst_vec(elems: &[Spanned<Expr>], subs: &HashMap<String, Expr>) -> Vec<Spanned<Expr>> {
    elems
        .iter()
        .map(|e| Spanned::dummy(apply_substitutions(&e.node, subs)))
        .collect()
}

fn subst_bound_var(bound: &BoundVar, subs: &HashMap<String, Expr>) -> BoundVar {
    BoundVar {
        name: bound.name.clone(),
        domain: bound
            .domain
            .as_ref()
            .map(|d| Box::new(Spanned::dummy(apply_substitutions(&d.node, subs)))),
        pattern: bound.pattern.clone(),
    }
}

fn subst_bound_vars(bounds: &[BoundVar], subs: &HashMap<String, Expr>) -> Vec<BoundVar> {
    bounds.iter().map(|b| subst_bound_var(b, subs)).collect()
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use tla_core::ast::BoundVar;
    use tla_core::name_intern::NameId;
    use tla_core::pretty_expr;
    use tla_core::Spanned;

    /// Helper to create an Ident expression with an invalid NameId (for tests).
    fn ident(name: &str) -> Expr {
        Expr::Ident(name.to_string(), NameId::INVALID)
    }

    #[test]
    fn test_build_substitution_map_empty() {
        let subs: Vec<Substitution> = Vec::new();
        let map = build_substitution_map(&subs);
        assert!(map.is_empty());
    }

    #[test]
    fn test_build_substitution_map_single() {
        let subs = vec![Substitution {
            from: Spanned::dummy("x".to_string()),
            to: Spanned::dummy(Expr::Int(42.into())),
        }];
        let map = build_substitution_map(&subs);
        assert_eq!(map.len(), 1);
        assert!(map.contains_key("x"));
    }

    #[test]
    fn test_apply_substitutions_ident_match() {
        let mut subs = HashMap::new();
        subs.insert("x".to_string(), Expr::Int(99.into()));

        let expr = ident("x");
        let result = apply_substitutions(&expr, &subs);
        assert_eq!(pretty_expr(&result), "99");
    }

    #[test]
    fn test_apply_substitutions_ident_no_match() {
        let mut subs = HashMap::new();
        subs.insert("x".to_string(), Expr::Int(99.into()));

        let expr = ident("y");
        let result = apply_substitutions(&expr, &subs);
        assert_eq!(pretty_expr(&result), "y");
    }

    #[test]
    fn test_apply_substitutions_binary() {
        let mut subs = HashMap::new();
        subs.insert("N".to_string(), Expr::Int(5.into()));

        let expr = Expr::Range(
            Box::new(Spanned::dummy(Expr::Int(1.into()))),
            Box::new(Spanned::dummy(ident("N"))),
        );
        let result = apply_substitutions(&expr, &subs);
        assert_eq!(pretty_expr(&result), "1 .. 5");
    }

    #[test]
    fn test_apply_substitutions_empty_map() {
        let subs = HashMap::new();
        let expr = Expr::And(
            Box::new(Spanned::dummy(Expr::Bool(true))),
            Box::new(Spanned::dummy(Expr::Bool(false))),
        );
        let result = apply_substitutions(&expr, &subs);
        assert_eq!(pretty_expr(&result), pretty_expr(&expr));
    }

    #[test]
    fn test_apply_substitutions_nested() {
        let mut subs = HashMap::new();
        subs.insert("a".to_string(), Expr::Int(1.into()));
        subs.insert("b".to_string(), Expr::Int(2.into()));

        let expr = Expr::Add(
            Box::new(Spanned::dummy(ident("a"))),
            Box::new(Spanned::dummy(Expr::Mul(
                Box::new(Spanned::dummy(ident("b"))),
                Box::new(Spanned::dummy(Expr::Int(3.into()))),
            ))),
        );
        let result = apply_substitutions(&expr, &subs);
        assert_eq!(pretty_expr(&result), "1 + 2 * 3");
    }

    #[test]
    fn test_apply_substitutions_if_then_else() {
        let mut subs = HashMap::new();
        subs.insert("flag".to_string(), Expr::Bool(true));

        let expr = Expr::If(
            Box::new(Spanned::dummy(ident("flag"))),
            Box::new(Spanned::dummy(Expr::Int(1.into()))),
            Box::new(Spanned::dummy(Expr::Int(0.into()))),
        );
        let result = apply_substitutions(&expr, &subs);
        assert_eq!(pretty_expr(&result), "IF TRUE THEN 1 ELSE 0");
    }

    #[test]
    fn test_apply_substitutions_set_enum() {
        let mut subs = HashMap::new();
        subs.insert("x".to_string(), Expr::String("hello".to_string()));

        let expr = Expr::SetEnum(vec![
            Spanned::dummy(ident("x")),
            Spanned::dummy(Expr::Int(2.into())),
        ]);
        let result = apply_substitutions(&expr, &subs);
        assert_eq!(pretty_expr(&result), "{\"hello\", 2}");
    }

    #[test]
    fn test_apply_substitutions_quantifier() {
        let mut subs = HashMap::new();
        subs.insert(
            "S".to_string(),
            Expr::SetEnum(vec![
                Spanned::dummy(Expr::Int(1.into())),
                Spanned::dummy(Expr::Int(2.into())),
            ]),
        );

        let bound = BoundVar {
            name: Spanned::dummy("x".to_string()),
            domain: Some(Box::new(Spanned::dummy(ident("S")))),
            pattern: None,
        };
        let body = Expr::Gt(
            Box::new(Spanned::dummy(ident("x"))),
            Box::new(Spanned::dummy(Expr::Int(0.into()))),
        );
        let expr = Expr::Forall(vec![bound], Box::new(Spanned::dummy(body)));
        let result = apply_substitutions(&expr, &subs);
        let text = pretty_expr(&result);
        assert!(text.contains("{1, 2}"), "expected substituted set in: {text}");
    }

    #[test]
    fn test_apply_substitutions_leaf_unchanged() {
        let subs = HashMap::new();
        for leaf in [
            Expr::Bool(true),
            Expr::Int(42.into()),
            Expr::String("hi".to_string()),
        ] {
            let original = pretty_expr(&leaf);
            let result = apply_substitutions(&leaf, &subs);
            assert_eq!(pretty_expr(&result), original);
        }
    }

    #[test]
    fn test_is_stdlib_module_known() {
        assert!(is_stdlib_module("Naturals"));
        assert!(is_stdlib_module("Integers"));
        assert!(is_stdlib_module("Sequences"));
        assert!(is_stdlib_module("FiniteSets"));
        assert!(is_stdlib_module("TLC"));
        assert!(!is_stdlib_module("MyCustomModule"));
    }

    #[test]
    fn test_inline_ctx_record_skip_dedup() {
        let loader = ModuleLoader::with_base_dir(std::path::PathBuf::from("/tmp"));
        let mut ctx = InlineCtx::new(&loader, false);
        ctx.record_skip("Foo", "not found");
        ctx.record_skip("Foo", "not found");
        ctx.record_skip("Bar", "stdlib");
        assert_eq!(ctx.skipped_modules.len(), 2);
    }

    #[test]
    fn test_subst_vec_applies_to_all_elements() {
        let mut subs = HashMap::new();
        subs.insert("a".to_string(), Expr::Int(10.into()));

        let elems = vec![
            Spanned::dummy(ident("a")),
            Spanned::dummy(ident("b")),
            Spanned::dummy(Expr::Int(3.into())),
        ];
        let result = subst_vec(&elems, &subs);
        assert_eq!(result.len(), 3);
        assert_eq!(pretty_expr(&result[0].node), "10");
        assert_eq!(pretty_expr(&result[1].node), "b");
        assert_eq!(pretty_expr(&result[2].node), "3");
    }

    #[test]
    fn test_subst_bound_var_domain() {
        let mut subs = HashMap::new();
        subs.insert("S".to_string(), Expr::Int(42.into()));

        let bound = BoundVar {
            name: Spanned::dummy("x".to_string()),
            domain: Some(Box::new(Spanned::dummy(ident("S")))),
            pattern: None,
        };
        let result = subst_bound_var(&bound, &subs);
        let domain_expr = result.domain.expect("should have domain");
        assert_eq!(pretty_expr(&domain_expr.node), "42");
    }

    #[test]
    fn test_subst_bound_var_no_domain() {
        let subs = HashMap::new();
        let bound = BoundVar {
            name: Spanned::dummy("x".to_string()),
            domain: None,
            pattern: None,
        };
        let result = subst_bound_var(&bound, &subs);
        assert!(result.domain.is_none());
    }
}
