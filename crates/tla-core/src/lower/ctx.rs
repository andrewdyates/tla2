// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Lowering context, error types, and utility functions.

use crate::span::{FileId, Span};
use crate::syntax::kinds::{SyntaxKind, SyntaxNode, SyntaxToken};
use std::collections::HashSet;

/// Errors that can occur during lowering
#[derive(Debug, Clone)]
pub struct LowerError {
    pub message: String,
    pub span: Span,
}

/// Context for lowering operations
pub(crate) struct LowerCtx {
    /// The file being lowered
    file_id: FileId,
    /// Collected errors
    errors: Vec<LowerError>,
    /// Recorded spans of lowered action subscript bodies for the module currently being lowered.
    action_subscript_spans: HashSet<Span>,
}

impl LowerCtx {
    /// Create a new lowering context
    pub(crate) fn new(file_id: FileId) -> Self {
        Self {
            file_id,
            errors: Vec::new(),
            action_subscript_spans: HashSet::new(),
        }
    }

    /// Record an error
    pub(crate) fn error(&mut self, message: impl Into<String>, span: Span) {
        self.errors.push(LowerError {
            message: message.into(),
            span,
        });
    }

    /// Take all collected errors
    pub(crate) fn take_errors(&mut self) -> Vec<LowerError> {
        std::mem::take(&mut self.errors)
    }

    /// Record that a lowered expression span originated from `[A]_v` / `<<A>>_v` syntax.
    pub(crate) fn record_action_subscript_span(&mut self, span: Span) {
        self.action_subscript_spans.insert(span);
    }

    /// Drain the recorded action-subscript spans for the current module.
    pub(crate) fn take_action_subscript_spans(&mut self) -> HashSet<Span> {
        std::mem::take(&mut self.action_subscript_spans)
    }

    /// Create a span from a syntax node
    pub(super) fn span(&self, node: &SyntaxNode) -> Span {
        let range = node.text_range();
        Span::new(self.file_id, range.start().into(), range.end().into())
    }

    /// Create a span from a syntax token
    pub(super) fn token_span(&self, token: &SyntaxToken) -> Span {
        let range = token.text_range();
        Span::new(self.file_id, range.start().into(), range.end().into())
    }

    /// Create a "tight" span from a syntax node, excluding trailing trivia.
    /// This walks the children recursively to find the last non-trivia token.
    pub(super) fn tight_span(&self, node: &SyntaxNode) -> Span {
        let range = node.text_range();
        let start: u32 = range.start().into();

        // Find the last non-trivia token by walking children recursively
        if let Some(end) = Self::find_last_non_trivia_end(node) {
            Span::new(self.file_id, start, end)
        } else {
            // Fallback to full range if no tokens found
            Span::new(self.file_id, start, range.end().into())
        }
    }

    pub(super) fn preserved_expr_span(&self, node: &SyntaxNode) -> Span {
        if node.kind() == SyntaxKind::SubscriptExpr {
            self.span(node)
        } else {
            self.tight_span(node)
        }
    }

    /// Recursively find the end offset of the last non-trivia token in a node
    fn find_last_non_trivia_end(node: &SyntaxNode) -> Option<u32> {
        let mut last_end: Option<u32> = None;

        for child in node.children_with_tokens() {
            match child {
                rowan::NodeOrToken::Token(token) => {
                    if !token.kind().is_trivia() {
                        last_end = Some(token.text_range().end().into());
                    }
                }
                rowan::NodeOrToken::Node(child_node) => {
                    // Recursively find in child node
                    if let Some(end) = Self::find_last_non_trivia_end(&child_node) {
                        last_end = Some(end);
                    }
                }
            }
        }

        last_end
    }
}

/// Strip surrounding quotes and unescape TLA+ string escape sequences.
/// TLA+ supports: `\\`, `\"`, `\n`, `\t`, `\r`, `\f`
/// (matches SANY's reduceString in TLAplusParser.java:659-679).
pub(super) fn unescape_tla_string(raw: &str) -> String {
    let inner = if raw.len() >= 2 {
        &raw[1..raw.len() - 1]
    } else {
        raw
    };
    let mut result = String::with_capacity(inner.len());
    let mut chars = inner.chars();
    while let Some(c) = chars.next() {
        if c == '\\' {
            match chars.next() {
                Some('\\') => result.push('\\'),
                Some('"') => result.push('"'),
                Some('n') => result.push('\n'),
                Some('t') => result.push('\t'),
                Some('r') => result.push('\r'),
                Some('f') => result.push('\x0C'),
                Some(other) => {
                    // Unknown escape: preserve as-is (matches SANY behavior)
                    result.push('\\');
                    result.push(other);
                }
                None => result.push('\\'),
            }
        } else {
            result.push(c);
        }
    }
    result
}
