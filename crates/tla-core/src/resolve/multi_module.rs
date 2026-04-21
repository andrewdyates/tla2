// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Multi-module resolution: EXTENDS, INSTANCE, and module-level orchestration.

use super::context::ResolveCtx;
use super::types::{ResolveOptions, ScopeKind, SymbolKind};
use super::walker::{resolve_expr, resolve_instance, resolve_operator_def, resolve_theorem};
use super::ResolveResult;
use crate::ast::{Module, Unit};
use crate::span::Span;

/// Resolve names in a module
pub(crate) fn resolve_module(module: &Module) -> ResolveCtx {
    resolve_module_with_options(module, ResolveOptions::default())
}

/// Resolve names in a module, optionally including proof scripts.
pub(crate) fn resolve_module_with_options(module: &Module, options: ResolveOptions) -> ResolveCtx {
    let mut ctx = ResolveCtx::new();
    ctx.push_scope(ScopeKind::Module);

    // Inject standard library symbols based on EXTENDS declarations
    let extends: Vec<&str> = module.extends.iter().map(|s| s.node.as_str()).collect();
    crate::stdlib::inject_stdlib(&mut ctx, &extends);

    // First pass: collect all top-level definitions
    collect_top_level_defs(&mut ctx, module);

    // Second pass: resolve references in bodies
    resolve_unit_bodies(&mut ctx, module, options);

    ctx.pop_scope();
    ctx
}

/// Resolve a module with extended modules pre-loaded.
///
/// The `extended_modules` should be the already-loaded modules that this
/// module extends (non-stdlib). Their symbols will be injected into the
/// resolution context before resolving the main module.
pub fn resolve_with_extends(module: &Module, extended_modules: &[&Module]) -> ResolveResult {
    resolve_with_extends_and_instances(module, extended_modules, &[])
}

/// Resolve a module with extended modules and standalone INSTANCE modules pre-loaded.
///
/// `INSTANCE Foo` (without naming the instance as an operator) introduces `Foo`'s public operator
/// definitions into the unqualified name lookup scope, but does not introduce its constants or
/// variables as new names.
pub fn resolve_with_extends_and_instances(
    module: &Module,
    extended_modules: &[&Module],
    instanced_modules: &[&Module],
) -> ResolveResult {
    resolve_with_extends_and_instances_with_options(
        module,
        extended_modules,
        instanced_modules,
        ResolveOptions::default(),
    )
}

pub fn resolve_with_extends_and_instances_with_options(
    module: &Module,
    extended_modules: &[&Module],
    instanced_modules: &[&Module],
    options: ResolveOptions,
) -> ResolveResult {
    let mut ctx = ResolveCtx::new();
    ctx.push_scope(ScopeKind::Module);

    // First inject stdlib symbols.
    //
    // We need transitive stdlib visibility (if Echo EXTENDS TLC, then a module that EXTENDS Echo
    // should see PrintT), but must avoid injecting synthetic stubs for stdlib-named modules that
    // were actually loaded from source (e.g., TLAPS.tla in tlaplus-examples), or we'll create
    // duplicate-definition errors.
    use std::collections::HashSet;

    let loaded_names: HashSet<&str> = extended_modules
        .iter()
        .chain(instanced_modules.iter())
        .map(|m| m.name.node.as_str())
        .collect();

    let mut stdlib_extends: Vec<&str> = Vec::new();
    for ext in &module.extends {
        let name = ext.node.as_str();
        if crate::stdlib::is_stdlib_module(name) && !loaded_names.contains(name) {
            stdlib_extends.push(name);
        }
    }
    for ext_mod in extended_modules {
        for ext in &ext_mod.extends {
            let name = ext.node.as_str();
            if crate::stdlib::is_stdlib_module(name) && !loaded_names.contains(name) {
                stdlib_extends.push(name);
            }
        }
    }
    for inst_mod in instanced_modules {
        for ext in &inst_mod.extends {
            let name = ext.node.as_str();
            if crate::stdlib::is_stdlib_module(name) && !loaded_names.contains(name) {
                stdlib_extends.push(name);
            }
        }
    }

    crate::stdlib::inject_stdlib(&mut ctx, &stdlib_extends);

    // Then inject symbols from extended user modules
    let mut injected: HashSet<&str> = HashSet::new();
    for ext_mod in extended_modules {
        if !injected.insert(ext_mod.name.node.as_str()) {
            continue;
        }
        inject_module_symbols(&mut ctx, ext_mod);
    }
    for inst_mod in instanced_modules {
        if !injected.insert(inst_mod.name.node.as_str()) {
            continue;
        }
        inject_module_operator_symbols(&mut ctx, inst_mod);
    }

    // First pass: collect all top-level definitions
    collect_top_level_defs(&mut ctx, module);

    // Second pass: resolve references in bodies
    resolve_unit_bodies(&mut ctx, module, options);

    ctx.pop_scope();

    ResolveResult {
        symbols: ctx.all_symbols,
        references: ctx.references,
        errors: ctx.errors,
    }
}

/// Inject all public symbols from a module into a resolution context.
///
/// This is used for EXTENDS: all non-LOCAL definitions from the extended
/// module become available in the extending module.
pub(crate) fn inject_module_symbols(ctx: &mut ResolveCtx, module: &Module) {
    let span = Span::dummy(); // Use dummy span for imported symbols

    // Inject variables
    for unit in &module.units {
        match &unit.node {
            Unit::Variable(vars) => {
                for var in vars {
                    ctx.define(&var.node, SymbolKind::Variable, span, 0, false);
                }
            }
            Unit::Constant(consts) => {
                for c in consts {
                    let arity = c.arity.unwrap_or(0);
                    ctx.define(&c.name.node, SymbolKind::Constant, span, arity, false);
                }
            }
            Unit::Operator(op) => {
                // Skip LOCAL operators
                if !op.local {
                    ctx.define_imported_operator(&op.name.node, span, op.params.len());
                }
            }
            Unit::Theorem(thm) => {
                if let Some(name) = &thm.name {
                    ctx.define_imported_operator(&name.node, span, 0);
                }
            }
            Unit::Assume(assume) => {
                if let Some(name) = &assume.name {
                    ctx.define_imported_operator(&name.node, span, 0);
                }
            }
            // `RECURSIVE` is a forward declaration within a module, not a public definition.
            // Only actual (non-LOCAL) operator definitions are imported via EXTENDS.
            Unit::Recursive(_) => {}
            Unit::Instance(_) | Unit::Separator => {}
        }
    }
}

fn inject_module_operator_symbols(ctx: &mut ResolveCtx, module: &Module) {
    let span = Span::dummy(); // Use dummy span for imported symbols

    for unit in &module.units {
        match &unit.node {
            Unit::Operator(op) => {
                // Skip LOCAL operators
                if op.local {
                    continue;
                }
                ctx.define_imported_operator(&op.name.node, span, op.params.len());
            }
            Unit::Theorem(thm) => {
                if let Some(name) = &thm.name {
                    ctx.define_imported_operator(&name.node, span, 0);
                }
            }
            Unit::Assume(assume) => {
                if let Some(name) = &assume.name {
                    ctx.define_imported_operator(&name.node, span, 0);
                }
            }
            Unit::Variable(_)
            | Unit::Constant(_)
            | Unit::Recursive(_)
            | Unit::Instance(_)
            | Unit::Separator => {}
        }
    }
}

/// First pass: collect all top-level definitions from a module.
fn collect_top_level_defs(ctx: &mut ResolveCtx, module: &Module) {
    for unit in &module.units {
        match &unit.node {
            Unit::Variable(vars) => {
                for var in vars {
                    ctx.define(&var.node, SymbolKind::Variable, var.span, 0, false);
                }
            }
            Unit::Constant(consts) => {
                for c in consts {
                    let arity = c.arity.unwrap_or(0);
                    ctx.define(
                        &c.name.node,
                        SymbolKind::Constant,
                        c.name.span,
                        arity,
                        false,
                    );
                }
            }
            // `RECURSIVE` is a forward declaration; avoid defining it separately to prevent
            // spurious duplicate-definition errors when the operator body appears later.
            Unit::Recursive(_) => {}
            Unit::Operator(op) => {
                ctx.define(
                    &op.name.node,
                    SymbolKind::Operator,
                    op.name.span,
                    op.params.len(),
                    op.local,
                );
            }
            Unit::Instance(inst) => {
                ctx.define(
                    &inst.module.node,
                    SymbolKind::Module,
                    inst.module.span,
                    0,
                    inst.local,
                );
            }
            Unit::Theorem(thm) => {
                if let Some(name) = &thm.name {
                    ctx.define(&name.node, SymbolKind::Operator, name.span, 0, false);
                }
            }
            Unit::Assume(assume) => {
                if let Some(name) = &assume.name {
                    // TLAPS-style named assumptions (ASSUME Name == expr) introduce a name that
                    // can be referenced later (e.g., in BY clauses). Treat them like 0-arity
                    // operators for name resolution.
                    ctx.define(&name.node, SymbolKind::Operator, name.span, 0, false);
                }
            }
            Unit::Separator => {}
        }
    }
}

/// Second pass: resolve references in unit bodies.
fn resolve_unit_bodies(ctx: &mut ResolveCtx, module: &Module, options: ResolveOptions) {
    for unit in &module.units {
        match &unit.node {
            Unit::Operator(op) => {
                resolve_operator_def(ctx, op);
            }
            Unit::Assume(assume) => {
                resolve_expr(ctx, &assume.expr);
            }
            Unit::Theorem(thm) => {
                resolve_theorem(ctx, thm, options);
            }
            Unit::Instance(inst) => {
                resolve_instance(ctx, inst);
            }
            Unit::Variable(_) | Unit::Constant(_) | Unit::Recursive(_) | Unit::Separator => {}
        }
    }
}
