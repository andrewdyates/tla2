// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use tla_core::{ast::Module, lower, parse, resolve, FileId, ResolveResult, SyntaxNode};

use crate::analysis::{self, SemanticDiagnostic};

/// Document state stored for each open file
#[derive(Debug)]
pub(crate) struct DocumentState {
    /// Source text
    pub(crate) source: String,
    /// Document version (incremented on each change for incremental diagnostics)
    pub(crate) version: i32,
    /// Lowered AST (if parse succeeded)
    pub(crate) module: Option<Module>,
    /// Resolution result (if lowering succeeded)
    pub(crate) resolve: Option<ResolveResult>,
    /// Parse errors
    pub(crate) parse_errors: Vec<tla_core::ParseError>,
    /// Lower errors
    pub(crate) lower_errors: Vec<tla_core::LowerError>,
    /// Semantic diagnostics from deeper analysis
    pub(crate) semantic_diagnostics: Vec<SemanticDiagnostic>,
}

impl DocumentState {
    #[cfg(test)]
    pub(crate) fn new(source: String) -> Self {
        Self {
            source,
            version: 0,
            module: None,
            resolve: None,
            parse_errors: Vec::new(),
            lower_errors: Vec::new(),
            semantic_diagnostics: Vec::new(),
        }
    }

    /// Create a new document state with a version number.
    pub(crate) fn with_version(source: String, version: i32) -> Self {
        Self {
            source,
            version,
            module: None,
            resolve: None,
            parse_errors: Vec::new(),
            lower_errors: Vec::new(),
            semantic_diagnostics: Vec::new(),
        }
    }

    /// Parse and analyze the document.
    ///
    /// This runs the full pipeline: parse -> lower -> resolve -> semantic analysis.
    /// On each `didChange` notification, the document is re-analyzed from scratch
    /// (full sync mode). The version is used for diagnostic publishing so the
    /// client can discard stale diagnostics.
    pub(crate) fn analyze(&mut self) {
        // Reset analysis state
        self.semantic_diagnostics.clear();

        // Parse
        let parse_result = parse(&self.source);
        self.parse_errors = parse_result.errors.clone();

        if !parse_result.errors.is_empty() {
            self.module = None;
            self.resolve = None;
            return;
        }

        // Lower
        let tree = SyntaxNode::new_root(parse_result.green_node);
        let lower_result = lower(FileId(0), &tree);
        self.lower_errors = lower_result.errors.clone();

        if let Some(module) = lower_result.module {
            // Resolve
            let resolve_result = resolve(&module);

            // Run semantic analysis (unused declarations, error classification, etc.)
            self.semantic_diagnostics = analysis::analyze_module(&module, &resolve_result);

            self.resolve = Some(resolve_result);
            self.module = Some(module);
        } else {
            self.module = None;
            self.resolve = None;
        }
    }
}
