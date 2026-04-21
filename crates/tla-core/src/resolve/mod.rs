// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Name resolution and scope analysis for TLA+
//!
//! This module performs semantic analysis on the AST:
//! - Resolves identifier references to their definitions
//! - Tracks scope (module, LET, quantifier, function definition)
//! - Reports undefined references and duplicate definitions
//! - Builds a symbol table for downstream use
//!
//! # TLA+ Scoping Rules
//!
//! TLA+ has several scoping constructs:
//! - **Module scope**: VARIABLE, CONSTANT, operator definitions
//! - **LET scope**: Local definitions in LET...IN
//! - **Quantifier scope**: Bound variables in \A, \E, CHOOSE
//! - **Function scope**: Parameters in [x \in S |-> ...]
//! - **Set scope**: Variables in {e : x \in S} and {x \in S : P}
//! - **Lambda scope**: Parameters in LAMBDA x, y : body
//!
//! Inner scopes shadow outer scopes. EXTENDS brings external definitions
//! into module scope. INSTANCE creates parameterized imports.

mod context;
mod error;
mod multi_module;
mod types;
mod walker;

#[cfg(test)]
mod tests;

// Re-export public types
pub(crate) use context::ResolveCtx;
pub use error::{ResolveError, ResolveErrorKind};
pub use multi_module::{
    resolve_with_extends, resolve_with_extends_and_instances,
    resolve_with_extends_and_instances_with_options,
};
// resolve_module and resolve_module_with_options return ResolveCtx (internal type);
// external callers should use resolve() or resolve_with_options() which return ResolveResult.
pub(crate) use multi_module::{resolve_module, resolve_module_with_options};
pub use types::{ResolveOptions, Symbol, SymbolKind};

use crate::ast::Module;

/// Result of name resolution
#[derive(Debug)]
pub struct ResolveResult {
    /// All defined symbols
    pub symbols: Vec<Symbol>,
    /// All references (use_span -> def_span)
    pub references: Vec<(crate::span::Span, crate::span::Span)>,
    /// Resolution errors
    pub errors: Vec<ResolveError>,
}

impl ResolveResult {
    /// Check if resolution succeeded
    pub fn is_ok(&self) -> bool {
        self.errors.is_empty()
    }
}

/// Resolve a module and return the result
pub fn resolve(module: &Module) -> ResolveResult {
    let ctx = resolve_module(module);
    ResolveResult {
        symbols: ctx.all_symbols,
        references: ctx.references,
        errors: ctx.errors,
    }
}

/// Resolve a module with options and return the result
pub fn resolve_with_options(module: &Module, options: ResolveOptions) -> ResolveResult {
    let ctx = resolve_module_with_options(module, options);
    ResolveResult {
        symbols: ctx.all_symbols,
        references: ctx.references,
        errors: ctx.errors,
    }
}
