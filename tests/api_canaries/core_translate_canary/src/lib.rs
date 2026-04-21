// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// API compatibility canary for tla-core (Part of #1325).
// This crate exercises stable public API paths from tla-core.
// Compile failure here means a public API contract was broken.
//
// Contract surface: parsing, lowering, resolution, AST types,
// name interning, substitution, and translation dispatch.

// Canary crates intentionally import symbols to verify they exist.
// The imports ARE the test — "unused" is expected.
#![allow(unused_imports, dead_code)]

// --- Parsing pipeline (via crate root re-exports) ---
use tla_core::LowerResult;
use tla_core::{ParseResult, SyntaxNode};
use tla_core::{ResolveOptions, ResolveResult};

// --- AST types ---
use tla_core::ast::{Expr, Module, OperatorDef, Unit};

// --- Source location (via crate root re-exports) ---
use tla_core::{FileId, Span, Spanned};

// --- Name interning (via crate root re-exports) ---
use tla_core::NameId;

// --- Error handling (via crate root re-exports) ---
use tla_core::Error as CoreError;

// --- Translation dispatch (via crate root re-exports) ---
use tla_core::TranslateExpr;

// --- Substitution (via crate root re-exports) ---
use tla_core::BoundNameStack;

// --- Visitor/fold (via crate root re-exports) ---
use tla_core::ExprFold;
use tla_core::ExprVisitor;

// --- Module loader (via crate root re-exports) ---
use tla_core::ModuleLoader;

// --- Diagnostics (via crate root re-exports) ---
use tla_core::{Diagnostic, Severity};

/// Exercise the parse → lower → resolve pipeline types.
/// This function is never called; it only needs to compile.
fn canary_parse_pipeline(source: &str) {
    // parse is re-exported at crate root; parser module is pub(crate).
    let _parse_result: ParseResult = tla_core::parse(source);
    let file_id = FileId(0);
    let _ = Span {
        file: file_id,
        start: 0,
        end: 0,
    };
}

/// Exercise AST type construction contracts.
fn canary_ast_types(module: &Module) {
    let _: &Spanned<String> = &module.name;
    let _: &[Spanned<Unit>] = &module.units;
}

/// Exercise name interning contracts.
/// Note: resolve_name was narrowed to pub(crate) in #2646 — it has zero external callers.
/// The public API for name interning is via the crate-root re-exports.
fn canary_name_intern() {
    let _id: NameId = tla_core::intern_name("x");
    let _count: usize = tla_core::interned_name_count();
}

/// Exercise resolve options contract.
fn canary_resolve_options() {
    let _opts = ResolveOptions::default();
}

// Ensure trait objects are constructible (trait is object-safe or at least importable).
fn canary_traits() {
    fn _takes_visitor<V: ExprVisitor>(_v: V) {}
    fn _takes_fold<F: ExprFold>(_f: F) {}
}

// Type-assert re-exports exist at crate root.
fn canary_root_reexports() {
    // parser module is pub(crate); parse is accessible via crate root re-export.
    let _: fn(&str) -> ParseResult = tla_core::parse;
}
