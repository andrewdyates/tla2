// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Semantic analysis for LSP diagnostics.
//!
//! This module performs lightweight static analysis on the resolved AST to
//! produce diagnostics beyond parse/lower/resolve errors:
//!
//! - **Unused declarations**: CONSTANT/VARIABLE names that are declared but
//!   never referenced in any operator body.
//! - **Resolve error classification**: Distinguishes truly undefined names
//!   (Error) from names that may come from unloaded modules (Warning).

use std::collections::HashSet;

use tla_core::{
    ast::{Module, Unit},
    ResolveErrorKind, ResolveResult, Span, SymbolKind,
};

/// A semantic diagnostic produced by analysis.
#[derive(Debug, Clone)]
pub(crate) struct SemanticDiagnostic {
    /// Location of the issue
    pub(crate) span: Span,
    /// Human-readable message
    pub(crate) message: String,
    /// Severity category
    pub(crate) kind: SemanticDiagnosticKind,
}

/// Severity categories for semantic diagnostics.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SemanticDiagnosticKind {
    /// Truly undefined name (not from a known extended module)
    UndefinedName,
    /// Duplicate definition in same scope
    DuplicateDefinition,
    /// Arity mismatch in operator application
    ArityMismatch,
    /// Kind mismatch (variable used as operator, etc.)
    KindMismatch,
    /// Possibly undefined (might come from unloaded module)
    PossiblyUndefined,
    /// Declared CONSTANT/VARIABLE never referenced
    UnusedDeclaration,
}

/// Run semantic analysis on a resolved module.
///
/// Returns diagnostics for issues found beyond basic parse/lower/resolve errors.
pub(crate) fn analyze_module(module: &Module, resolve: &ResolveResult) -> Vec<SemanticDiagnostic> {
    let mut diagnostics = Vec::new();

    // Classify resolve errors
    classify_resolve_errors(module, resolve, &mut diagnostics);

    // Detect unused declarations
    detect_unused_declarations(module, resolve, &mut diagnostics);

    diagnostics
}

/// Classify resolve errors into appropriate severity levels.
///
/// Names that might come from EXTENDS'd modules we haven't loaded are
/// downgraded to "possibly undefined" (Warning). Names that cannot possibly
/// be from an external module are promoted to Error severity.
fn classify_resolve_errors(
    module: &Module,
    resolve: &ResolveResult,
    out: &mut Vec<SemanticDiagnostic>,
) {
    let has_extends = !module.extends.is_empty();
    let has_instance = module
        .units
        .iter()
        .any(|u| matches!(u.node, Unit::Instance(_)));
    let may_have_external = has_extends || has_instance;

    for err in &resolve.errors {
        let (kind, message) = match &err.kind {
            ResolveErrorKind::Undefined { name } => {
                if may_have_external {
                    (
                        SemanticDiagnosticKind::PossiblyUndefined,
                        format!(
                            "Undefined identifier `{name}` (may be provided by an extended module)"
                        ),
                    )
                } else {
                    (
                        SemanticDiagnosticKind::UndefinedName,
                        format!("Undefined identifier `{name}`"),
                    )
                }
            }
            ResolveErrorKind::Duplicate { name, .. } => (
                SemanticDiagnosticKind::DuplicateDefinition,
                format!("Duplicate definition of `{name}`"),
            ),
            ResolveErrorKind::ImportedOperatorArityConflict {
                name,
                first_arity,
                second_arity,
                ..
            } => (
                SemanticDiagnosticKind::ArityMismatch,
                format!(
                    "Conflicting definitions of operator `{name}` (arity {first_arity} vs {second_arity})"
                ),
            ),
            ResolveErrorKind::ArityMismatch {
                name,
                expected,
                got,
            } => (
                SemanticDiagnosticKind::ArityMismatch,
                format!("Operator `{name}` expects {expected} arguments, got {got}"),
            ),
            ResolveErrorKind::KindMismatch {
                name,
                expected,
                got,
            } => (
                SemanticDiagnosticKind::KindMismatch,
                format!("`{name}` is a {got:?}, expected {expected:?}"),
            ),
            // ResolveErrorKind is #[non_exhaustive]; handle future variants
            _ => (
                SemanticDiagnosticKind::UndefinedName,
                err.to_string(),
            ),
        };

        out.push(SemanticDiagnostic {
            span: err.span,
            message,
            kind,
        });
    }
}

/// Detect CONSTANT/VARIABLE declarations that are never referenced.
///
/// This is reported as a Hint-level diagnostic. Unused constants are common
/// in model-checking contexts (where the .cfg file provides values), so
/// this should be informational rather than alarming.
fn detect_unused_declarations(
    _module: &Module,
    resolve: &ResolveResult,
    out: &mut Vec<SemanticDiagnostic>,
) {
    // Collect all def_spans that are referenced at least once
    let referenced_defs: HashSet<Span> = resolve
        .references
        .iter()
        .map(|(_use_span, def_span)| *def_span)
        .collect();

    // Check each module-level VARIABLE and CONSTANT declaration.
    // Skip built-in symbols (BOOLEAN, Nat, etc.) which have Span::dummy().
    let dummy = Span::dummy();
    for sym in &resolve.symbols {
        match sym.kind {
            SymbolKind::Variable | SymbolKind::Constant => {
                if sym.def_span == dummy {
                    continue; // Built-in/stdlib symbol, not user-declared
                }
                if !referenced_defs.contains(&sym.def_span) {
                    let kind_str = match sym.kind {
                        SymbolKind::Variable => "VARIABLE",
                        SymbolKind::Constant => "CONSTANT",
                        _ => unreachable!(),
                    };
                    out.push(SemanticDiagnostic {
                        span: sym.def_span,
                        message: format!(
                            "{kind_str} `{}` is declared but never referenced in this module",
                            sym.name
                        ),
                        kind: SemanticDiagnosticKind::UnusedDeclaration,
                    });
                }
            }
            // Operators, bound vars, etc. are not flagged as unused
            _ => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tla_core::{lower, parse, resolve, FileId, SyntaxNode};

    fn analyze_source(
        source: &str,
    ) -> (
        Option<Module>,
        Option<ResolveResult>,
        Vec<SemanticDiagnostic>,
    ) {
        let parse_result = parse(source);
        if !parse_result.errors.is_empty() {
            return (None, None, Vec::new());
        }
        let tree = SyntaxNode::new_root(parse_result.green_node);
        let lower_result = lower(FileId(0), &tree);
        if let Some(module) = lower_result.module {
            let resolve_result = resolve(&module);
            let diags = analyze_module(&module, &resolve_result);
            (Some(module), Some(resolve_result), diags)
        } else {
            (None, None, Vec::new())
        }
    }

    #[test]
    fn test_unused_variable_detected() {
        let source = r#"
---- MODULE Unused ----
VARIABLE x, y
Init == x = 0
====
"#;
        let (_, _, diags) = analyze_source(source);
        let unused: Vec<_> = diags
            .iter()
            .filter(|d| d.kind == SemanticDiagnosticKind::UnusedDeclaration)
            .collect();
        assert_eq!(
            unused.len(),
            1,
            "expected 1 unused declaration, got {}: {:?}",
            unused.len(),
            unused.iter().map(|d| &d.message).collect::<Vec<_>>()
        );
        assert!(
            unused[0].message.contains("y"),
            "expected unused diagnostic for `y`, got: {}",
            unused[0].message
        );
    }

    #[test]
    fn test_no_unused_when_all_referenced() {
        let source = r#"
---- MODULE AllUsed ----
VARIABLE x
CONSTANT N
Init == x = N
====
"#;
        let (_, _, diags) = analyze_source(source);
        let unused: Vec<_> = diags
            .iter()
            .filter(|d| d.kind == SemanticDiagnosticKind::UnusedDeclaration)
            .collect();
        assert!(
            unused.is_empty(),
            "expected no unused declarations, got: {:?}",
            unused.iter().map(|d| &d.message).collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_undefined_without_extends_is_error() {
        let source = r#"
---- MODULE NoExtends ----
VARIABLE x
Init == x = Bogus
====
"#;
        let (_, _, diags) = analyze_source(source);
        let undefined: Vec<_> = diags
            .iter()
            .filter(|d| d.kind == SemanticDiagnosticKind::UndefinedName)
            .collect();
        assert!(
            !undefined.is_empty(),
            "expected undefined name diagnostic for `Bogus`"
        );
    }

    #[test]
    fn test_undefined_with_extends_is_possibly_undefined() {
        let source = r#"
---- MODULE WithExtends ----
EXTENDS Naturals
VARIABLE x
Init == x = Bogus
====
"#;
        let (_, _, diags) = analyze_source(source);
        let possibly: Vec<_> = diags
            .iter()
            .filter(|d| d.kind == SemanticDiagnosticKind::PossiblyUndefined)
            .collect();
        assert!(
            !possibly.is_empty(),
            "expected possibly-undefined diagnostic for `Bogus` when EXTENDS present"
        );
        // Should NOT have a hard UndefinedName error
        let hard: Vec<_> = diags
            .iter()
            .filter(|d| d.kind == SemanticDiagnosticKind::UndefinedName)
            .collect();
        assert!(
            hard.is_empty(),
            "should not produce hard UndefinedName with EXTENDS, got: {:?}",
            hard.iter().map(|d| &d.message).collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_unused_constant_detected() {
        let source = r#"
---- MODULE UnusedConst ----
CONSTANT A, B
VARIABLE x
Init == x = A
====
"#;
        let (_, _, diags) = analyze_source(source);
        let unused: Vec<_> = diags
            .iter()
            .filter(|d| d.kind == SemanticDiagnosticKind::UnusedDeclaration)
            .collect();
        assert_eq!(
            unused.len(),
            1,
            "expected 1 unused constant (B), got {}: {:?}",
            unused.len(),
            unused.iter().map(|d| &d.message).collect::<Vec<_>>()
        );
        assert!(
            unused[0].message.contains("B"),
            "expected unused diagnostic for `B`, got: {}",
            unused[0].message
        );
    }
}
