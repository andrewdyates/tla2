// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! tla-core: Core TLA+ parser, AST, and semantic analysis
//!
//! This crate provides the foundation for all TLA2 tools:
//! - Lexer and parser for TLA+ source code
//! - CST→AST lowering (`lower`)
//! - Abstract syntax tree (AST) with source spans
//! - Semantic analysis: name resolution, scope checking (`resolve`)
//! - Identifier interning (`name_intern`)
//! - Standard library operator definitions (`stdlib`)
//! - Module system support: EXTENDS, INSTANCE (`loader`)
//! - Diagnostics and error reporting (`diagnostic`)
//! - Pretty-printing (`pretty`)
//! - Expression substitution (`subst`)
//!
//! # Architecture
//!
//! ```text
//! TLA+ Source
//!      │
//!      ▼
//! ┌─────────┐    ┌─────────┐    ┌─────────┐    ┌─────────┐
//! │  Lexer  │───▶│ Parser  │───▶│   AST   │───▶│Resolver │
//! │ (logos) │    │(rowan)  │    │         │    │         │
//! └─────────┘    └─────────┘    └─────────┘    └─────────┘
//! ```

pub(crate) mod debug_env;

pub mod ast;
pub(crate) mod diagnostic;
pub(crate) mod error;
pub(crate) mod expr_visitors;
pub(crate) mod fnv;
pub(crate) mod fold;
pub mod kani_types;
pub(crate) mod loader;
pub(crate) mod lower;
pub mod name_intern;
pub(crate) mod pretty;
pub mod quint;
pub(crate) mod resolve;
pub mod span;
pub(crate) mod stdlib;
pub(crate) mod subst;
pub(crate) mod syntax;
pub(crate) mod translate;
pub(crate) mod var_index;
pub(crate) mod visit;

// Shared type aliases used across the checker/evaluator/value stack.
// Defined here so downstream crates (tla-value, tla-eval) can reference them
// without depending on tla-check.

/// Operator definition storage.
/// Arc-wrapped for O(1) cloning during state enumeration.
/// See tla-check#209: expression tree cloning was a major performance bottleneck.
pub type OpEnv = kani_types::HashMap<String, std::sync::Arc<ast::OperatorDef>>;

// Re-exports
pub use error::{Error, Result};
pub use span::{FileId, Span, Spanned};

// Syntax re-exports
pub use syntax::{
    parse, parse_multi_module, parse_to_syntax_tree, MultiModuleParseResult, ParseError,
    ParseResult, ParsedModule,
};
pub use syntax::{SyntaxElement, SyntaxKind, SyntaxNode, SyntaxToken, TlaLanguage};

// Lower re-exports
pub use lower::{
    compute_contains_prime, compute_guards_depend_on_prime, compute_has_primed_param,
    compute_is_recursive, lower, lower_main_module, lower_single_expr, operator_has_primed_param,
    LowerError, LowerResult,
};

// Pretty-print re-exports
pub use pretty::{pretty_expr, pretty_module};
// Formatter re-exports (width-aware TLA+ formatting)
pub use pretty::{
    format_expr, format_module, format_module_with_config, FormatConfig, TlaFormatter,
};

// Resolve re-exports
pub use resolve::{
    resolve, resolve_with_extends, resolve_with_extends_and_instances,
    resolve_with_extends_and_instances_with_options, resolve_with_options, ResolveError,
    ResolveErrorKind, ResolveOptions, ResolveResult, Symbol, SymbolKind,
};

// Loader re-exports
pub use loader::{LoadError, LoadedModule, ModuleLoader};

// Diagnostic re-exports
pub use diagnostic::{
    lower_error_diagnostic, parse_error_diagnostic, Diagnostic, DiagnosticLabel, DiagnosticSpan,
    LabelColor, Severity,
};

// Name interning re-exports
pub use name_intern::{
    clear_global_name_interner, freeze_interner, intern_name, interned_name_count, lookup_name_id,
    resolve_name_id, resolve_name_id_string_fp64, NameId,
};

// Substitution re-exports
pub use subst::{free_vars, inlining_is_capture_safe, substitution_would_capture, BoundNameStack};

// Fold re-exports
pub use fold::{ExprFold, SpanPolicy, SubstituteAt, SubstituteExpr};

// FNV hash re-exports
pub use fnv::{FNV_OFFSET, FNV_PRIME};

// Debug environment re-exports
// Only env_flag_is_set remains public — the tla_debug_flag! macro references
// $crate::env_flag_is_set, so it must be accessible from downstream crates.
// The other three helpers (env_flag_eq, env_opt_usize, env_usize_or) have been
// localized into tla-check, their sole non-tla-core consumer (Part of #3039).
pub use debug_env::env_flag_is_set;

// Stable public translate surface. Downstream callers should import these from
// `tla_core::{...}`; the internal `tla_core::translate::*` module path is not
// part of the external API contract.
pub use translate::{dispatch_translate_bool, dispatch_translate_int, TranslateExpr};

// Visit re-exports
pub use visit::{single_bound_var_names, walk_expr, walk_spanned_expr, ExprVisitor, VisitorOutput};

// Variable indexing re-exports
pub use var_index::{VarIndex, VarRegistry};

// Stdlib re-exports
pub use stdlib::{get_module_operators, is_stdlib_module, STDLIB_MODULES};

// Expression visitor re-exports
pub use expr_visitors::{
    apply_substitutions_v, arg_has_name_in_set_v, collect_bound_names_v, collect_conjuncts_v,
    expr_contains_any_prime_v, expr_contains_at_v, expr_contains_enabled_v, expr_contains_exists_v,
    expr_contains_ident_v, expr_contains_operator_application_v,
    expr_contains_prime_not_assignment_v, expr_contains_prime_v, expr_contains_primed_param_v,
    expr_contains_temporal_v, expr_has_any_prime_legacy_v, expr_has_free_var_in_set_v,
    expr_mentions_name_spanned_v, expr_mentions_name_v, expr_references_any_free_name_v,
    expr_references_state_vars_v, get_primed_var_refs_v, is_guard_expression_v,
    is_simple_prime_var,
};
