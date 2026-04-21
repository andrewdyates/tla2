// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use tla_core::ast::Unit;
use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;
use tower_lsp::LanguageServer;

use crate::backend::TlaBackend;
use crate::document::DocumentState;
use crate::{completions, position, symbols};

#[tower_lsp::async_trait]
impl LanguageServer for TlaBackend {
    async fn initialize(&self, _: InitializeParams) -> Result<InitializeResult> {
        Ok(InitializeResult {
            capabilities: ServerCapabilities {
                text_document_sync: Some(TextDocumentSyncCapability::Kind(
                    TextDocumentSyncKind::FULL,
                )),
                document_symbol_provider: Some(OneOf::Left(true)),
                definition_provider: Some(OneOf::Left(true)),
                references_provider: Some(OneOf::Left(true)),
                hover_provider: Some(HoverProviderCapability::Simple(true)),
                completion_provider: Some(CompletionOptions {
                    trigger_characters: Some(vec![
                        "\\".to_string(), // For \A, \E, etc.
                        ".".to_string(),  // For module.operator
                        "_".to_string(),  // For WF_, SF_
                    ]),
                    resolve_provider: Some(false),
                    ..Default::default()
                }),
                workspace_symbol_provider: Some(OneOf::Left(true)),
                ..Default::default()
            },
            server_info: Some(ServerInfo {
                name: "tla2-lsp".to_string(),
                version: Some(env!("CARGO_PKG_VERSION").to_string()),
            }),
        })
    }

    async fn initialized(&self, _: InitializedParams) {
        tracing::info!("TLA2 Language Server initialized");
    }

    async fn shutdown(&self) -> Result<()> {
        Ok(())
    }

    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        let uri = params.text_document.uri;
        let version = params.text_document.version;
        let mut doc = DocumentState::with_version(params.text_document.text, version);
        doc.analyze();
        self.documents.insert(uri.clone(), doc);
        self.publish_diagnostics(&uri).await;
    }

    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        let uri = params.text_document.uri;
        let version = params.text_document.version;
        if let Some(change) = params.content_changes.into_iter().last() {
            let mut doc = DocumentState::with_version(change.text, version);
            doc.analyze();
            self.documents.insert(uri.clone(), doc);
            self.publish_diagnostics(&uri).await;
        }
    }

    async fn did_close(&self, params: DidCloseTextDocumentParams) {
        self.documents.remove(&params.text_document.uri);
    }

    async fn document_symbol(
        &self,
        params: DocumentSymbolParams,
    ) -> Result<Option<DocumentSymbolResponse>> {
        let uri = &params.text_document.uri;
        if let Some(doc) = self.documents.get(uri) {
            if let Some(module) = &doc.module {
                let syms = symbols::get_document_symbols(module, &doc.source);
                return Ok(Some(DocumentSymbolResponse::Nested(syms)));
            }
        }
        Ok(None)
    }

    async fn goto_definition(
        &self,
        params: GotoDefinitionParams,
    ) -> Result<Option<GotoDefinitionResponse>> {
        let uri = &params.text_document_position_params.text_document.uri;
        let pos = params.text_document_position_params.position;

        if let Some(doc) = self.documents.get(uri) {
            if let Some(resolve) = &doc.resolve {
                let offset = position::position_to_offset(&doc.source, pos);
                if let Some(def_span) = symbols::find_symbol_at_position(resolve, offset) {
                    let range = position::span_to_range(&doc.source, def_span);
                    return Ok(Some(GotoDefinitionResponse::Scalar(Location::new(
                        uri.clone(),
                        range,
                    ))));
                }
            }
        }
        Ok(None)
    }

    async fn references(&self, params: ReferenceParams) -> Result<Option<Vec<Location>>> {
        let uri = &params.text_document_position.text_document.uri;
        let pos = params.text_document_position.position;

        if let Some(doc) = self.documents.get(uri) {
            if let Some(resolve) = &doc.resolve {
                let offset = position::position_to_offset(&doc.source, pos);
                if let Some(def_span) = symbols::find_definition_span_at_position(resolve, offset) {
                    let refs = symbols::find_references_to_def(resolve, def_span);
                    let mut locations: Vec<Location> = refs
                        .into_iter()
                        .map(|span| {
                            Location::new(uri.clone(), position::span_to_range(&doc.source, span))
                        })
                        .collect();

                    // Include definition itself if requested
                    if params.context.include_declaration {
                        locations.push(Location::new(
                            uri.clone(),
                            position::span_to_range(&doc.source, def_span),
                        ));
                    }

                    return Ok(Some(locations));
                }
            }
        }
        Ok(None)
    }

    async fn hover(&self, params: HoverParams) -> Result<Option<Hover>> {
        let uri = &params.text_document_position_params.text_document.uri;
        let pos = params.text_document_position_params.position;

        if let Some(doc) = self.documents.get(uri) {
            if let Some(resolve) = &doc.resolve {
                let offset = position::position_to_offset(&doc.source, pos);
                if let Some(info) = symbols::get_hover_info(resolve, offset) {
                    return Ok(Some(Hover {
                        contents: HoverContents::Markup(MarkupContent {
                            kind: MarkupKind::PlainText,
                            value: info,
                        }),
                        range: None,
                    }));
                }
            }
        }
        Ok(None)
    }

    async fn completion(&self, params: CompletionParams) -> Result<Option<CompletionResponse>> {
        let uri = &params.text_document_position.text_document.uri;

        let mut items = Vec::new();

        // Always provide keywords
        items.extend(completions::get_keyword_completions());

        // Always provide standard library modules (for EXTENDS)
        items.extend(completions::get_stdlib_module_completions());

        // If we have a parsed document, provide context-specific completions
        if let Some(doc) = self.documents.get(uri) {
            // Add local symbols
            if let Some(resolve) = &doc.resolve {
                items.extend(completions::get_local_symbol_completions(resolve));
            }

            // Add operators from extended modules
            if let Some(module) = &doc.module {
                items.extend(completions::get_stdlib_operator_completions(module));
            }
        }

        // Deduplicate by label
        let mut seen = std::collections::HashSet::new();
        items.retain(|item| seen.insert(item.label.clone()));

        Ok(Some(CompletionResponse::Array(items)))
    }

    async fn symbol(
        &self,
        params: WorkspaceSymbolParams,
    ) -> Result<Option<Vec<SymbolInformation>>> {
        let query = params.query.to_lowercase();
        let mut result = Vec::new();

        // Search through all open documents
        for entry in self.documents.iter() {
            let uri = entry.key().clone();
            let doc = entry.value();

            if let Some(module) = &doc.module {
                // Get symbols from module
                for unit in &module.units {
                    let (name, kind) = match &unit.node {
                        Unit::Variable(vars) => {
                            for var in vars {
                                if var.node.to_lowercase().contains(&query) {
                                    result.push(symbols::mk_symbol_information(
                                        var.node.clone(),
                                        SymbolKind::VARIABLE,
                                        Location::new(
                                            uri.clone(),
                                            position::span_to_range(&doc.source, var.span),
                                        ),
                                        Some(module.name.node.clone()),
                                    ));
                                }
                            }
                            continue;
                        }
                        Unit::Constant(consts) => {
                            for c in consts {
                                if c.name.node.to_lowercase().contains(&query) {
                                    result.push(symbols::mk_symbol_information(
                                        c.name.node.clone(),
                                        SymbolKind::CONSTANT,
                                        Location::new(
                                            uri.clone(),
                                            position::span_to_range(&doc.source, c.name.span),
                                        ),
                                        Some(module.name.node.clone()),
                                    ));
                                }
                            }
                            continue;
                        }
                        Unit::Operator(op) => (op.name.node.clone(), SymbolKind::FUNCTION),
                        Unit::Theorem(thm) => {
                            if let Some(name) = &thm.name {
                                (name.node.clone(), SymbolKind::CLASS)
                            } else {
                                continue;
                            }
                        }
                        _ => continue,
                    };

                    if name.to_lowercase().contains(&query) {
                        result.push(symbols::mk_symbol_information(
                            name,
                            kind,
                            Location::new(
                                uri.clone(),
                                position::span_to_range(&doc.source, unit.span),
                            ),
                            Some(module.name.node.clone()),
                        ));
                    }
                }
            }
        }

        Ok(Some(result))
    }
}
