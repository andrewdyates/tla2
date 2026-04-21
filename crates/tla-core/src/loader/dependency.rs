// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! EXTENDS and INSTANCE dependency resolution.
//!
//! Recursive loading of module dependencies via EXTENDS and INSTANCE
//! declarations, with deduplication and deterministic ordering.

use std::collections::HashSet;

use super::error::LoadError;
use super::ModuleLoader;
use crate::ast::{Expr, Module, Unit};
use crate::stdlib::is_stdlib_module;

fn push_unique(loaded: &mut Vec<String>, seen: &mut HashSet<String>, name: &str) -> bool {
    if !seen.insert(name.to_string()) {
        return false;
    }
    loaded.push(name.to_string());
    true
}

fn collect_instance_expr_modules_in_order(
    expr: &Expr,
    seen: &mut HashSet<String>,
    out: &mut Vec<String>,
) {
    match expr {
        Expr::InstanceExpr(module_name, subs) => {
            if seen.insert(module_name.clone()) {
                out.push(module_name.clone());
            }
            for sub in subs {
                collect_instance_expr_modules_in_order(&sub.to.node, seen, out);
            }
        }

        Expr::Bool(_)
        | Expr::Int(_)
        | Expr::String(_)
        | Expr::Ident(_, _)
        | Expr::StateVar(_, _, _)
        | Expr::OpRef(_) => {}

        Expr::Apply(op, args) => {
            collect_instance_expr_modules_in_order(&op.node, seen, out);
            for arg in args {
                collect_instance_expr_modules_in_order(&arg.node, seen, out);
            }
        }
        Expr::ModuleRef(_, _, args) => {
            for arg in args {
                collect_instance_expr_modules_in_order(&arg.node, seen, out);
            }
        }
        Expr::Lambda(_params, body) => {
            collect_instance_expr_modules_in_order(&body.node, seen, out);
        }
        Expr::Label(label) => {
            collect_instance_expr_modules_in_order(&label.body.node, seen, out);
        }

        Expr::And(a, b)
        | Expr::Or(a, b)
        | Expr::Implies(a, b)
        | Expr::Equiv(a, b)
        | Expr::In(a, b)
        | Expr::NotIn(a, b)
        | Expr::Subseteq(a, b)
        | Expr::Union(a, b)
        | Expr::Intersect(a, b)
        | Expr::SetMinus(a, b)
        | Expr::FuncSet(a, b)
        | Expr::LeadsTo(a, b)
        | Expr::WeakFair(a, b)
        | Expr::StrongFair(a, b)
        | Expr::Eq(a, b)
        | Expr::Neq(a, b)
        | Expr::Lt(a, b)
        | Expr::Leq(a, b)
        | Expr::Gt(a, b)
        | Expr::Geq(a, b)
        | Expr::Add(a, b)
        | Expr::Sub(a, b)
        | Expr::Mul(a, b)
        | Expr::Div(a, b)
        | Expr::IntDiv(a, b)
        | Expr::Mod(a, b)
        | Expr::Pow(a, b)
        | Expr::Range(a, b) => {
            collect_instance_expr_modules_in_order(&a.node, seen, out);
            collect_instance_expr_modules_in_order(&b.node, seen, out);
        }

        Expr::Not(a)
        | Expr::Powerset(a)
        | Expr::BigUnion(a)
        | Expr::Domain(a)
        | Expr::Prime(a)
        | Expr::Always(a)
        | Expr::Eventually(a)
        | Expr::Enabled(a)
        | Expr::Unchanged(a)
        | Expr::Neg(a)
        | Expr::RecordAccess(a, _) => {
            collect_instance_expr_modules_in_order(&a.node, seen, out);
        }

        Expr::Forall(bounds, body) | Expr::Exists(bounds, body) => {
            for b in bounds {
                if let Some(domain) = &b.domain {
                    collect_instance_expr_modules_in_order(&domain.node, seen, out);
                }
            }
            collect_instance_expr_modules_in_order(&body.node, seen, out);
        }
        Expr::Choose(bound, body) => {
            if let Some(domain) = &bound.domain {
                collect_instance_expr_modules_in_order(&domain.node, seen, out);
            }
            collect_instance_expr_modules_in_order(&body.node, seen, out);
        }

        Expr::SetEnum(elems) | Expr::Tuple(elems) | Expr::Times(elems) => {
            for e in elems {
                collect_instance_expr_modules_in_order(&e.node, seen, out);
            }
        }
        Expr::SetBuilder(expr, bounds) => {
            collect_instance_expr_modules_in_order(&expr.node, seen, out);
            for b in bounds {
                if let Some(domain) = &b.domain {
                    collect_instance_expr_modules_in_order(&domain.node, seen, out);
                }
            }
        }
        Expr::SetFilter(bound, pred) => {
            if let Some(domain) = &bound.domain {
                collect_instance_expr_modules_in_order(&domain.node, seen, out);
            }
            collect_instance_expr_modules_in_order(&pred.node, seen, out);
        }

        Expr::FuncDef(bounds, body) => {
            for b in bounds {
                if let Some(domain) = &b.domain {
                    collect_instance_expr_modules_in_order(&domain.node, seen, out);
                }
            }
            collect_instance_expr_modules_in_order(&body.node, seen, out);
        }
        Expr::FuncApply(f, arg) => {
            collect_instance_expr_modules_in_order(&f.node, seen, out);
            collect_instance_expr_modules_in_order(&arg.node, seen, out);
        }
        Expr::Except(f, specs) => {
            collect_instance_expr_modules_in_order(&f.node, seen, out);
            for spec in specs {
                for p in &spec.path {
                    if let crate::ast::ExceptPathElement::Index(idx) = p {
                        collect_instance_expr_modules_in_order(&idx.node, seen, out);
                    }
                }
                collect_instance_expr_modules_in_order(&spec.value.node, seen, out);
            }
        }

        Expr::Record(fields) | Expr::RecordSet(fields) => {
            for (_name, expr) in fields {
                collect_instance_expr_modules_in_order(&expr.node, seen, out);
            }
        }

        Expr::If(c, t, e) => {
            collect_instance_expr_modules_in_order(&c.node, seen, out);
            collect_instance_expr_modules_in_order(&t.node, seen, out);
            collect_instance_expr_modules_in_order(&e.node, seen, out);
        }
        Expr::Case(arms, other) => {
            for arm in arms {
                collect_instance_expr_modules_in_order(&arm.guard.node, seen, out);
                collect_instance_expr_modules_in_order(&arm.body.node, seen, out);
            }
            if let Some(other) = other {
                collect_instance_expr_modules_in_order(&other.node, seen, out);
            }
        }
        Expr::Let(defs, body) => {
            for d in defs {
                collect_instance_expr_modules_in_order(&d.body.node, seen, out);
            }
            collect_instance_expr_modules_in_order(&body.node, seen, out);
        }
        Expr::SubstIn(subs, body) => {
            for s in subs {
                collect_instance_expr_modules_in_order(&s.to.node, seen, out);
            }
            collect_instance_expr_modules_in_order(&body.node, seen, out);
        }
    }
}

fn load_and_expand(
    loader: &mut ModuleLoader,
    module_name: &str,
    loaded: &mut Vec<String>,
    loaded_seen: &mut HashSet<String>,
) -> Result<(), LoadError> {
    let loaded_this = match loader.load(module_name) {
        Ok(_) => true,
        Err(LoadError::NotFound { .. }) if is_stdlib_module(module_name) => false,
        Err(e) => return Err(e),
    };
    if !loaded_this {
        return Ok(());
    }

    // If we've already processed this module, avoid re-expanding dependencies. This keeps
    // `loaded` free of duplicates and reduces repeated recursion.
    if !push_unique(loaded, loaded_seen, module_name) {
        return Ok(());
    }

    let sub_module = loader.cache.get(module_name).map(|m| m.module.clone());
    if let Some(sub_mod) = sub_module {
        for name in loader.load_extends(&sub_mod)? {
            push_unique(loaded, loaded_seen, &name);
        }
        for name in loader.load_instances(&sub_mod)? {
            push_unique(loaded, loaded_seen, &name);
        }
    }

    Ok(())
}

impl ModuleLoader {
    /// Load all modules that a module extends (non-stdlib only)
    ///
    /// This recursively loads all extended modules and their instanced modules.
    /// Extended modules may define named instances (e.g., C == INSTANCE Consensus)
    /// which need to be loaded for proper operator resolution.
    ///
    /// Returns a deduplicated list of module names in deterministic discovery order
    /// (depth-first traversal of EXTENDS, then INSTANCE dependencies).
    pub fn load_extends(&mut self, module: &Module) -> Result<Vec<String>, LoadError> {
        let mut visited = HashSet::new();
        visited.insert(module.name.node.clone());
        self.load_extends_inner(module, &mut visited)
    }

    /// Inner recursive helper with a `visited` set to prevent infinite recursion
    /// on circular EXTENDS chains (e.g., A EXTENDS B, B EXTENDS A).
    fn load_extends_inner(
        &mut self,
        module: &Module,
        visited: &mut HashSet<String>,
    ) -> Result<Vec<String>, LoadError> {
        let mut loaded = Vec::new();
        let mut loaded_seen: HashSet<String> = HashSet::new();

        for ext in &module.extends {
            let name = &ext.node;
            let loaded_this = match self.load(name) {
                Ok(_) => true,
                Err(LoadError::NotFound { .. }) if is_stdlib_module(name) => false,
                Err(e) => return Err(e),
            };

            // Always record stdlib module names even when no .tla file exists.
            // These names populate `extended_module_names` in the EvalCtx, which
            // gates builtin operator overrides (e.g., Functions → FoldFunction,
            // SequencesExt → FoldSeq, FiniteSetsExt → FoldSet). Without this,
            // specs like Huang that EXTENDS Functions get the slow TLA-defined
            // FoldFunction instead of the Rust builtin. Part of #2944.
            push_unique(&mut loaded, &mut loaded_seen, name);

            if !loaded_this {
                continue;
            }

            // Skip already-visited modules to prevent circular EXTENDS recursion
            if !visited.insert(name.clone()) {
                continue;
            }

            // Clone to avoid borrow issues
            let sub_module = self.cache.get(name).map(|m| m.module.clone());
            if let Some(sub_mod) = sub_module {
                // Recursively load extended modules
                let sub_extends = self.load_extends_inner(&sub_mod, visited)?;
                for name in sub_extends {
                    push_unique(&mut loaded, &mut loaded_seen, &name);
                }
                // Also load instanced modules from extended modules
                // This is needed for cases like: Main EXTENDS Voting, Voting has C == INSTANCE Consensus
                let sub_instances = self.load_instances(&sub_mod)?;
                for name in sub_instances {
                    push_unique(&mut loaded, &mut loaded_seen, &name);
                }
            }
        }

        Ok(loaded)
    }

    /// Load all modules that a module instances (non-stdlib only).
    ///
    /// This recursively loads all instanced modules and their dependencies.
    /// Unlike EXTENDS, INSTANCE modules may have substitutions (WITH clauses),
    /// which are handled at evaluation time.
    pub fn load_instances(&mut self, module: &Module) -> Result<Vec<String>, LoadError> {
        let mut loaded = Vec::new();
        let mut loaded_seen: HashSet<String> = HashSet::new();

        for unit in &module.units {
            // Handle standalone INSTANCE declarations
            if let Unit::Instance(inst) = &unit.node {
                load_and_expand(self, &inst.module.node, &mut loaded, &mut loaded_seen)?;

                // INSTANCE ... WITH substitutions can contain nested INSTANCE expressions (e.g. via
                // LET-bound instance operators). Discover and load them in deterministic traversal
                // order.
                let mut nested_seen = HashSet::new();
                let mut nested_order = Vec::new();
                for sub in &inst.substitutions {
                    collect_instance_expr_modules_in_order(
                        &sub.to.node,
                        &mut nested_seen,
                        &mut nested_order,
                    );
                }
                for module_name in nested_order {
                    load_and_expand(self, &module_name, &mut loaded, &mut loaded_seen)?;
                }
            }

            // Handle named instances: InChan == INSTANCE Channel WITH ...
            // These are operators whose body is InstanceExpr
            if let Unit::Operator(def) = &unit.node {
                if let Expr::InstanceExpr(module_name, subs) = &def.body.node {
                    load_and_expand(self, module_name, &mut loaded, &mut loaded_seen)?;

                    // Avoid double-scanning the root INSTANCE module (handled above); only scan
                    // substitutions for nested INSTANCE expressions.
                    let mut nested_seen = HashSet::new();
                    let mut nested_order = Vec::new();
                    for sub in subs {
                        collect_instance_expr_modules_in_order(
                            &sub.to.node,
                            &mut nested_seen,
                            &mut nested_order,
                        );
                    }
                    for module_name in nested_order {
                        load_and_expand(self, &module_name, &mut loaded, &mut loaded_seen)?;
                    }
                }
            }

            // Handle nested named instances inside operator bodies (e.g. LET G == INSTANCE Graphs IN ...).
            //
            // TLC/SANY allow INSTANCE expressions anywhere an operator definition can appear, not just
            // as a top-level `Op == INSTANCE M ...` declaration. We need to load these instanced
            // modules so that module references like `G!Transpose` can be evaluated.
            if let Unit::Operator(def) = &unit.node {
                // Named instances (`Op == INSTANCE M ...`) are handled above; skip here to avoid
                // double-loading the root module.
                if matches!(&def.body.node, Expr::InstanceExpr(..)) {
                    continue;
                }

                // Discover nested INSTANCE expressions in a deterministic order (source/AST
                // traversal order). This matters for reproducible module loading and stable
                // downstream diagnostics.
                let mut nested_seen = HashSet::new();
                let mut nested_order = Vec::new();
                collect_instance_expr_modules_in_order(
                    &def.body.node,
                    &mut nested_seen,
                    &mut nested_order,
                );

                for module_name in nested_order {
                    load_and_expand(self, &module_name, &mut loaded, &mut loaded_seen)?;
                }
            }
        }

        Ok(loaded)
    }
}
