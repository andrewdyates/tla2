// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! LSP diagnostic generation.
//!
//! Converts internal error/warning/hint representations into LSP `Diagnostic`
//! structs and publishes them to the client. Diagnostics are categorized:
//!
//! | Source           | Severity    | Code prefix |
//! |------------------|-------------|-------------|
//! | Parse errors     | Error       | `E1xxx`     |
//! | Lower errors     | Error       | `E2xxx`     |
//! | Undefined name   | Error/Warn  | `E3xxx`     |
//! | Arity mismatch   | Warning     | `W3xxx`     |
//! | Unused decl      | Hint        | `H4xxx`     |

use tower_lsp::lsp_types::*;

use crate::analysis::SemanticDiagnosticKind;
use crate::backend::TlaBackend;
use crate::position::{offset_to_position, span_to_range};

/// Diagnostic code constants.
///
/// These follow a convention where the first digit indicates the pipeline stage
/// and the letter indicates severity: E=Error, W=Warning, H=Hint, I=Info.
mod codes {
    pub(super) const PARSE_ERROR: &str = "E1001";
    pub(super) const LOWER_ERROR: &str = "E2001";
    pub(super) const UNDEFINED_NAME: &str = "E3001";
    pub(super) const DUPLICATE_DEF: &str = "E3002";
    pub(super) const ARITY_MISMATCH: &str = "W3003";
    pub(super) const KIND_MISMATCH: &str = "W3004";
    pub(super) const POSSIBLY_UNDEFINED: &str = "W3005";
    pub(super) const UNUSED_DECLARATION: &str = "H4001";
}

impl TlaBackend {
    /// Publish diagnostics for a document.
    ///
    /// Collects diagnostics from all analysis stages (parse, lower, resolve,
    /// semantic) and sends them to the client in a single batch. The document
    /// version is included so the client can discard stale diagnostics when
    /// the user edits faster than analysis completes.
    pub(crate) async fn publish_diagnostics(&self, uri: &Url) {
        let (diagnostics, version) = if let Some(doc) = self.documents.get(uri) {
            let mut diags = Vec::new();

            // Stage 1: Parse errors (always Error severity)
            for err in &doc.parse_errors {
                diags.push(Diagnostic {
                    range: Range::new(
                        offset_to_position(&doc.source, err.start),
                        offset_to_position(&doc.source, err.end),
                    ),
                    severity: Some(DiagnosticSeverity::ERROR),
                    code: Some(NumberOrString::String(codes::PARSE_ERROR.to_string())),
                    source: Some("tla2-parser".to_string()),
                    message: err.message.clone(),
                    ..Default::default()
                });
            }

            // Stage 2: Lower errors (always Error severity)
            for err in &doc.lower_errors {
                diags.push(Diagnostic {
                    range: span_to_range(&doc.source, err.span),
                    severity: Some(DiagnosticSeverity::ERROR),
                    code: Some(NumberOrString::String(codes::LOWER_ERROR.to_string())),
                    source: Some("tla2-lower".to_string()),
                    message: err.message.clone(),
                    ..Default::default()
                });
            }

            // Stage 3+4: Semantic diagnostics (classified resolve errors + analysis)
            for diag in &doc.semantic_diagnostics {
                let (severity, code) = match diag.kind {
                    SemanticDiagnosticKind::UndefinedName => {
                        (DiagnosticSeverity::ERROR, codes::UNDEFINED_NAME)
                    }
                    SemanticDiagnosticKind::DuplicateDefinition => {
                        (DiagnosticSeverity::ERROR, codes::DUPLICATE_DEF)
                    }
                    SemanticDiagnosticKind::ArityMismatch => {
                        (DiagnosticSeverity::WARNING, codes::ARITY_MISMATCH)
                    }
                    SemanticDiagnosticKind::KindMismatch => {
                        (DiagnosticSeverity::WARNING, codes::KIND_MISMATCH)
                    }
                    SemanticDiagnosticKind::PossiblyUndefined => {
                        (DiagnosticSeverity::WARNING, codes::POSSIBLY_UNDEFINED)
                    }
                    SemanticDiagnosticKind::UnusedDeclaration => {
                        (DiagnosticSeverity::HINT, codes::UNUSED_DECLARATION)
                    }
                };

                diags.push(Diagnostic {
                    range: span_to_range(&doc.source, diag.span),
                    severity: Some(severity),
                    code: Some(NumberOrString::String(code.to_string())),
                    source: Some("tla2-analysis".to_string()),
                    message: diag.message.clone(),
                    tags: diagnostic_tags(diag.kind),
                    ..Default::default()
                });
            }

            (diags, Some(doc.version))
        } else {
            (Vec::new(), None)
        };

        self.client
            .publish_diagnostics(uri.clone(), diagnostics, version)
            .await;
    }
}

/// Compute LSP diagnostic tags for a given semantic diagnostic kind.
///
/// - Unused declarations get the `Unnecessary` tag, which editors typically
///   render as faded/dimmed text.
fn diagnostic_tags(kind: SemanticDiagnosticKind) -> Option<Vec<DiagnosticTag>> {
    match kind {
        SemanticDiagnosticKind::UnusedDeclaration => Some(vec![DiagnosticTag::UNNECESSARY]),
        _ => None,
    }
}
