// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use tla_core::{
    ast::{Module, Unit},
    ResolveResult, Span, Symbol, SymbolKind as TlaSymbolKind,
};
use tower_lsp::lsp_types::*;

use crate::position::span_to_range;

/// Construct a `DocumentSymbol` with the deprecated field suppressed in one place.
#[allow(deprecated)]
fn mk_document_symbol(
    name: String,
    detail: Option<String>,
    kind: SymbolKind,
    range: Range,
    selection_range: Range,
) -> DocumentSymbol {
    DocumentSymbol {
        name,
        detail,
        kind,
        tags: None,
        deprecated: None,
        range,
        selection_range,
        children: None,
    }
}

/// Construct a `SymbolInformation` with the deprecated field suppressed in one place.
#[allow(deprecated)]
pub(crate) fn mk_symbol_information(
    name: String,
    kind: SymbolKind,
    location: Location,
    container_name: Option<String>,
) -> SymbolInformation {
    SymbolInformation {
        name,
        kind,
        tags: None,
        deprecated: None,
        location,
        container_name,
    }
}

/// Get document symbols from a module
pub(crate) fn get_document_symbols(module: &Module, source: &str) -> Vec<DocumentSymbol> {
    let mut symbols = Vec::new();
    for unit in &module.units {
        collect_unit_symbols(&unit.node, unit.span, source, &mut symbols);
    }
    symbols
}

/// Convert a single AST unit into document symbols.
fn collect_unit_symbols(
    node: &Unit,
    unit_span: tla_core::Span,
    source: &str,
    out: &mut Vec<DocumentSymbol>,
) {
    match node {
        Unit::Variable(vars) => {
            for var in vars {
                out.push(mk_document_symbol(
                    var.node.clone(),
                    Some("VARIABLE".to_string()),
                    SymbolKind::VARIABLE,
                    span_to_range(source, var.span),
                    span_to_range(source, var.span),
                ));
            }
        }
        Unit::Constant(consts) => {
            for c in consts {
                let detail = if let Some(arity) = c.arity {
                    format!("CONSTANT (arity {})", arity)
                } else {
                    "CONSTANT".to_string()
                };
                out.push(mk_document_symbol(
                    c.name.node.clone(),
                    Some(detail),
                    SymbolKind::CONSTANT,
                    span_to_range(source, c.name.span),
                    span_to_range(source, c.name.span),
                ));
            }
        }
        Unit::Recursive(decls) => {
            for r in decls {
                let detail = format!("RECURSIVE (arity {})", r.arity);
                out.push(mk_document_symbol(
                    r.name.node.clone(),
                    Some(detail),
                    SymbolKind::FUNCTION,
                    span_to_range(source, r.name.span),
                    span_to_range(source, r.name.span),
                ));
            }
        }
        Unit::Operator(op) => {
            let kind = if op.params.is_empty() {
                SymbolKind::CONSTANT
            } else {
                SymbolKind::FUNCTION
            };
            let detail = if op.params.is_empty() {
                None
            } else {
                Some(format!(
                    "({})",
                    op.params
                        .iter()
                        .map(|p| p.name.node.as_str())
                        .collect::<Vec<_>>()
                        .join(", ")
                ))
            };
            out.push(mk_document_symbol(
                op.name.node.clone(),
                detail,
                kind,
                span_to_range(source, unit_span),
                span_to_range(source, op.name.span),
            ));
        }
        Unit::Theorem(thm) => {
            if let Some(name) = &thm.name {
                out.push(mk_document_symbol(
                    name.node.clone(),
                    Some("THEOREM".to_string()),
                    SymbolKind::CLASS,
                    span_to_range(source, unit_span),
                    span_to_range(source, name.span),
                ));
            }
        }
        Unit::Instance(inst) => {
            out.push(mk_document_symbol(
                format!("INSTANCE {}", inst.module.node),
                None,
                SymbolKind::MODULE,
                span_to_range(source, unit_span),
                span_to_range(source, inst.module.span),
            ));
        }
        Unit::Assume(_) => {
            out.push(mk_document_symbol(
                "ASSUME".to_string(),
                None,
                SymbolKind::BOOLEAN,
                span_to_range(source, unit_span),
                span_to_range(source, unit_span),
            ));
        }
        Unit::Separator => {}
    }
}

/// Find the symbol at a position
pub(crate) fn find_symbol_at_position(resolve: &ResolveResult, offset: u32) -> Option<Span> {
    // Check references first (more specific)
    for (use_span, def_span) in &resolve.references {
        if offset >= use_span.start && offset <= use_span.end {
            return Some(*def_span);
        }
    }
    None
}

/// Find all references to a definition
pub(crate) fn find_references_to_def(resolve: &ResolveResult, def_span: Span) -> Vec<Span> {
    resolve
        .references
        .iter()
        .filter(|(_, d)| *d == def_span)
        .map(|(u, _)| *u)
        .collect()
}

/// Find definition span at position (either definition itself or reference)
pub(crate) fn find_definition_span_at_position(
    resolve: &ResolveResult,
    offset: u32,
) -> Option<Span> {
    // Check if cursor is on a reference
    for (use_span, def_span) in &resolve.references {
        if offset >= use_span.start && offset <= use_span.end {
            return Some(*def_span);
        }
    }
    // Check if cursor is on a definition
    for sym in &resolve.symbols {
        if offset >= sym.def_span.start && offset <= sym.def_span.end {
            return Some(sym.def_span);
        }
    }
    None
}

/// Get hover info for a symbol
pub(crate) fn get_hover_info(resolve: &ResolveResult, offset: u32) -> Option<String> {
    // Check if on a definition
    for sym in &resolve.symbols {
        if offset >= sym.def_span.start && offset <= sym.def_span.end {
            return Some(format_symbol_info(sym));
        }
    }
    // Check if on a reference
    for (use_span, def_span) in &resolve.references {
        if offset >= use_span.start && offset <= use_span.end {
            // Find the symbol
            for sym in &resolve.symbols {
                if sym.def_span == *def_span {
                    return Some(format_symbol_info(sym));
                }
            }
        }
    }
    None
}

fn format_symbol_info(sym: &Symbol) -> String {
    let kind_str = match sym.kind {
        TlaSymbolKind::Variable => "VARIABLE",
        TlaSymbolKind::Constant => "CONSTANT",
        TlaSymbolKind::Operator => "OPERATOR",
        TlaSymbolKind::BoundVar => "bound variable",
        TlaSymbolKind::OpParam => "parameter",
        TlaSymbolKind::Module => "MODULE",
    };
    let local_str = if sym.local { "LOCAL " } else { "" };
    if sym.arity > 0 {
        format!(
            "{}{} {} (arity {})",
            local_str, kind_str, sym.name, sym.arity
        )
    } else {
        format!("{}{} {}", local_str, kind_str, sym.name)
    }
}
