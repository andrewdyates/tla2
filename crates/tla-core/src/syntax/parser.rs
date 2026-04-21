// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! TLA+ parser using rowan for lossless syntax tree
//!
//! This parser uses an event-based approach:
//! 1. Lex input into tokens
//! 2. Parse tokens into events (StartNode, FinishNode, AddToken, Error)
//! 3. Build rowan GreenNode from events
//!
//! The parser is a recursive descent parser with Pratt parsing for expressions.

use crate::syntax::kinds::{SyntaxKind, SyntaxNode};
use crate::syntax::lexer::Token;
use rowan::{GreenNode, GreenNodeBuilder};

#[path = "parser_tables.rs"]
mod parser_tables;
use parser_tables::*;

#[path = "token_syntax_map.rs"]
mod token_syntax_map;
use token_syntax_map::token_to_syntax_kind;

#[path = "parser_proof.rs"]
mod parser_proof;

#[path = "parser_expr/mod.rs"]
mod parser_expr;
#[path = "parser_expr_bracket.rs"]
mod parser_expr_bracket;
#[path = "parser_expr_junction.rs"]
mod parser_expr_junction;
#[path = "parser_expr_postfix.rs"]
mod parser_expr_postfix;
#[path = "parser_module_defs.rs"]
mod parser_module_defs;
#[path = "parser_module_root.rs"]
mod parser_module_root;

#[cfg(test)]
#[path = "parser_tests.rs"]
mod parser_tests;

#[cfg(test)]
#[path = "parser_tests_apalache.rs"]
mod parser_tests_apalache;

/// A parsed token with its text, span, and column info for layout-aware parsing
#[derive(Debug, Clone)]
struct ParsedToken {
    kind: Token,
    text: String,
    start: u32,
    /// Column number (0-indexed) for layout-aware bullet list parsing
    column: u32,
}

/// Parser events that are collected during parsing
#[derive(Debug, Clone)]
enum Event {
    /// Start a new node
    StartNode { kind: SyntaxKind },
    /// Finish the current node
    FinishNode,
    /// Add a token
    AddToken { kind: SyntaxKind, text: String },
    /// Record an error
    Error { _message: String },
}

/// Type of junction list (bullet-style And or Or)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum JunctionType {
    Conjunction, // /\
    Disjunction, // \/
}

/// Information about an active junction list
#[derive(Debug, Clone)]
struct JunctionListInfo {
    _junction_type: JunctionType,
    column: u32,
}

/// Tracks nested bullet-style conjunction/disjunction lists for layout-aware parsing.
/// Column position of `/\` and `\/` determines list membership (similar to SANY).
#[derive(Debug, Default)]
struct JunctionListContext {
    stack: Vec<JunctionListInfo>,
}

impl JunctionListContext {
    /// Start a new junction list at the given column with the given type
    fn start(&mut self, column: u32, junction_type: JunctionType) {
        self.stack.push(JunctionListInfo {
            _junction_type: junction_type,
            column,
        });
    }

    /// End the current junction list
    fn end(&mut self) {
        self.stack.pop();
    }

    /// Get the column of the current junction list, if any
    fn current_column(&self) -> Option<u32> {
        self.stack.last().map(|info| info.column)
    }
}

/// The parser state
pub(crate) struct Parser {
    tokens: Vec<ParsedToken>,
    pos: usize,
    events: Vec<Event>,
    errors: Vec<ParseError>,
    junction_context: JunctionListContext,
}

/// A parse error with location
#[derive(Debug, Clone)]
pub struct ParseError {
    pub message: String,
    pub start: u32,
    pub end: u32,
}

/// Result of parsing
pub struct ParseResult {
    pub green_node: GreenNode,
    pub errors: Vec<ParseError>,
}

impl Parser {
    /// Create a new parser for the given source
    pub fn new(source: &str) -> Self {
        let tokens: Vec<_> = lex_with_positions(source).collect();
        Self {
            tokens,
            pos: 0,
            events: Vec::new(),
            errors: Vec::new(),
            junction_context: JunctionListContext::default(),
        }
    }

    /// Parse and return the green node
    pub fn parse(mut self) -> ParseResult {
        self.parse_root();
        let errors = std::mem::take(&mut self.errors);
        let green_node = self.build_tree();
        ParseResult { green_node, errors }
    }

    /// Build the rowan tree from events
    fn build_tree(self) -> GreenNode {
        let mut builder = GreenNodeBuilder::new();
        let mut forward_parents: Vec<(usize, SyntaxKind)> = Vec::new();

        for (idx, event) in self.events.into_iter().enumerate() {
            // Check for forward parent references
            while let Some(&(fwd_idx, kind)) = forward_parents.last() {
                if fwd_idx == idx {
                    builder.start_node(kind.into());
                    forward_parents.pop();
                } else {
                    break;
                }
            }

            match event {
                Event::StartNode { kind } => {
                    builder.start_node(kind.into());
                }
                Event::FinishNode => {
                    builder.finish_node();
                }
                Event::AddToken { kind, text } => {
                    builder.token(kind.into(), &text);
                }
                Event::Error { .. } => {
                    // Errors are collected separately, add error node
                    builder.start_node(SyntaxKind::Error.into());
                    builder.finish_node();
                }
            }
        }

        builder.finish()
    }

    // === Token access ===

    /// Get the current token kind
    fn current(&self) -> Option<Token> {
        self.tokens.get(self.pos).map(|t| t.kind)
    }

    /// Get the current token text
    fn current_text(&self) -> Option<&str> {
        self.tokens.get(self.pos).map(|t| t.text.as_str())
    }

    /// Get the current token's column (for layout-aware bullet list parsing)
    fn current_column(&self) -> u32 {
        self.tokens.get(self.pos).map_or(0, |t| t.column)
    }

    /// Get the current position
    fn current_pos(&self) -> u32 {
        self.tokens.get(self.pos).map_or(0, |t| t.start)
    }

    /// Peek at the next token kind
    fn peek(&self) -> Option<Token> {
        self.peek_nth(1)
    }

    /// Peek at the Nth non-trivia token ahead (1 = next, 2 = next+1, etc.)
    fn peek_nth(&self, n: usize) -> Option<Token> {
        let mut pos = self.pos + 1;
        let mut count = 0;
        while pos < self.tokens.len() {
            let token = &self.tokens[pos];
            if !token.kind.is_trivia() {
                count += 1;
                if count == n {
                    return Some(token.kind);
                }
            }
            pos += 1;
        }
        None
    }

    /// Look back to find the previous non-trivia token.
    /// Returns None if at the start of the token stream.
    fn prev_non_trivia(&self) -> Option<Token> {
        if self.pos == 0 {
            return None;
        }
        let mut pos = self.pos - 1;
        loop {
            let token = &self.tokens[pos];
            if !token.kind.is_trivia() {
                return Some(token.kind);
            }
            if pos == 0 {
                return None;
            }
            pos -= 1;
        }
    }

    /// Check if current position looks like the start of a proof step label.
    ///
    /// Proof step labels are ambiguous with BY-clause step references because both use `<n>...`.
    /// Heuristic:
    /// - A label is `<n>` followed by an optional label token, optionally a dot, then a token that
    ///   can start a proof step body (proof keyword or expression).
    /// - Step references tend to be followed by `,`, `DEF/DEFS`, or immediately by the next
    ///   step label (`<...>`).
    fn is_step_label_start(&self) -> bool {
        if self.current() != Some(Token::Lt) {
            return false;
        }
        // Check: < NUMBER >
        let next1 = self.peek_nth(1);
        let next2 = self.peek_nth(2);
        if !matches!((next1, next2), (Some(Token::Number), Some(Token::Gt))) {
            return false;
        }
        // Check for optional label and then either dot or a token that can start a proof step body.
        let next3 = self.peek_nth(3);
        match next3 {
            Some(Token::Dot) => true,
            Some(token @ (Token::Ident | Token::Number)) => {
                let next4 = self.peek_nth(4);
                if next4 == Some(Token::Dot) {
                    return true;
                }
                // If next4 is an Ident followed by == (DefEq), this is a step REFERENCE
                // followed by an operator definition at module level, NOT a step label start.
                // e.g., in `BY <1>1\n\n1bOr2bMsgs ==`, the `<1>1` is a reference.
                if next4 == Some(Token::Ident) {
                    let next5 = self.peek_nth(5);
                    if next5 == Some(Token::DefEq) {
                        return false;
                    }
                }
                // If the token after the label can start a proof step body, treat next3 as a label.
                if next4.is_some_and(is_proof_step_body_start) {
                    return true;
                }
                // Otherwise, next3 might actually be the start of the step body (e.g., `<2> A = 0`).
                // In that case, only accept it as a step label start if it looks unlike a step ref.
                if matches!(
                    next4,
                    Some(
                        Token::Comma
                            | Token::Def
                            | Token::Defs
                            | Token::By
                            | Token::Obvious
                            | Token::Omitted
                            | Token::Proof
                            | Token::Lt
                    )
                ) {
                    return false;
                }
                is_proof_step_body_start(token)
            }
            Some(token) => is_proof_step_body_start(token),
            None => false,
        }
    }

    /// Check if we're at a parenthesized infix operator: (op)
    /// Used to distinguish `B1 (+) B2 ==` from `Op(x, y) ==`
    fn is_parenthesized_infix_op(&self) -> bool {
        if self.current() != Some(Token::LParen) {
            return false;
        }
        let next1 = self.peek_nth(1);
        let next2 = self.peek_nth(2);
        // Pattern: ( op )
        if let Some(op) = next1 {
            if is_infix_op_symbol(op) && next2 == Some(Token::RParen) {
                return true;
            }
        }
        false
    }

    /// Check if at end of file
    fn at_eof(&self) -> bool {
        self.pos >= self.tokens.len()
    }

    /// Check if current token matches
    fn at(&self, kind: Token) -> bool {
        self.current() == Some(kind)
    }

    // === Event building ===

    /// Create a checkpoint at the current position for Pratt parsing
    fn checkpoint(&self) -> usize {
        self.events.len()
    }

    /// Start a node at a previously saved checkpoint (wraps previous content)
    fn start_node_at(&mut self, checkpoint: usize, kind: SyntaxKind) {
        // Insert StartNode at the checkpoint position
        self.events.insert(checkpoint, Event::StartNode { kind });
    }

    /// Start a new node
    fn start_node(&mut self, kind: SyntaxKind) {
        self.events.push(Event::StartNode { kind });
    }

    /// Finish the current node
    fn finish_node(&mut self) {
        self.events.push(Event::FinishNode);
    }

    /// Bump the current token and advance
    fn bump(&mut self) {
        if let Some(token) = self.tokens.get(self.pos) {
            let kind = token_to_syntax_kind(token.kind);
            self.events.push(Event::AddToken {
                kind,
                text: token.text.clone(),
            });
            self.pos += 1;
        }
    }

    /// Bump and skip trivia
    fn bump_skip_trivia(&mut self) {
        self.bump();
        self.skip_trivia();
    }

    /// Advance past current token, adding it to the syntax tree for position tracking.
    /// Used for leading bullets (/\ and \/) which are syntactic sugar but must be
    /// included in the tree to maintain accurate source positions.
    fn advance_skip_trivia(&mut self) {
        // Add the current token to maintain position tracking
        self.bump();
        // Add following trivia to the tree as well
        self.skip_trivia();
    }

    /// Skip whitespace and comments, adding them to the syntax tree
    fn skip_trivia(&mut self) {
        while let Some(token) = self.tokens.get(self.pos) {
            if token.kind.is_trivia() {
                let kind = token_to_syntax_kind(token.kind);
                self.events.push(Event::AddToken {
                    kind,
                    text: token.text.clone(),
                });
                self.pos += 1;
            } else {
                break;
            }
        }
    }

    /// Skip whitespace and comments WITHOUT adding them to the syntax tree.
    /// Use this during lookahead when we might reset the position.
    fn skip_trivia_no_emit(&mut self) {
        while let Some(token) = self.tokens.get(self.pos) {
            if token.kind.is_trivia() {
                self.pos += 1;
            } else {
                break;
            }
        }
    }

    /// Expect a specific token, emit error if not found
    fn expect(&mut self, expected: Token) -> bool {
        if self.at(expected) {
            self.bump_skip_trivia();
            true
        } else {
            self.error(format!("expected {expected:?}"));
            false
        }
    }

    /// Record an error
    fn error(&mut self, message: String) {
        let start = self.current_pos();
        let end = self
            .tokens
            .get(self.pos)
            .map_or(start, |t| t.start + t.text.len() as u32);
        self.errors.push(ParseError {
            message: message.clone(),
            start,
            end,
        });
        self.events.push(Event::Error { _message: message });
    }
}

/// Compute line start offsets from source text
fn compute_line_starts(source: &str) -> Vec<usize> {
    let mut starts = vec![0]; // Line 0 starts at offset 0
    for (i, c) in source.char_indices() {
        if c == '\n' {
            starts.push(i + 1); // Next line starts after the newline
        }
    }
    starts
}

/// Get column number (0-indexed) for a byte offset given line starts
fn offset_to_column(offset: usize, line_starts: &[usize]) -> u32 {
    // Binary search to find which line this offset is on
    let line = line_starts
        .binary_search(&offset)
        .unwrap_or_else(|insert_point| insert_point.saturating_sub(1));
    let line_start = line_starts.get(line).copied().unwrap_or(0);
    (offset - line_start) as u32
}

/// Lex with position and column information for layout-aware parsing
fn lex_with_positions(source: &str) -> impl Iterator<Item = ParsedToken> + '_ {
    use logos::Logos;
    let line_starts = compute_line_starts(source);
    let lexer = Token::lexer(source);
    lexer.spanned().filter_map(move |(result, span)| {
        result.ok().map(|kind| {
            let column = offset_to_column(span.start, &line_starts);
            ParsedToken {
                kind,
                text: source[span.clone()].to_string(),
                start: span.start as u32,
                column,
            }
        })
    })
}

/// Parse TLA+ source and return a syntax tree
pub fn parse(source: &str) -> ParseResult {
    Parser::new(source).parse()
}

/// Get the syntax tree root node
pub fn parse_to_syntax_tree(source: &str) -> SyntaxNode {
    let result = parse(source);
    SyntaxNode::new_root(result.green_node)
}

/// A single module extracted from a multi-module file
#[derive(Debug)]
pub struct ParsedModule {
    /// Module name extracted from the `---- MODULE Name ----` header
    pub name: String,
    /// The syntax node for this module (rooted at SyntaxKind::Module)
    pub syntax_node: SyntaxNode,
}

/// Result of parsing a multi-module file
#[derive(Debug)]
pub struct MultiModuleParseResult {
    /// All modules found in order of appearance.
    /// The last module is the "main" module; earlier modules are dependencies
    /// available for EXTENDS/INSTANCE.
    pub modules: Vec<ParsedModule>,
    /// Parse errors from the entire file
    pub errors: Vec<ParseError>,
}

/// Parse a TLA+ source that may contain multiple `---- MODULE Name ---- ... ====` blocks.
///
/// Returns all modules found in order of appearance. The last module is considered
/// the "main" module; earlier modules are dependencies (available for EXTENDS/INSTANCE).
///
/// Single-module files work identically to [`parse`], returning exactly one module.
pub fn parse_multi_module(source: &str) -> MultiModuleParseResult {
    let result = parse(source);
    let root = SyntaxNode::new_root(result.green_node);

    let mut modules = Vec::new();
    for child in root.children() {
        if child.kind() == SyntaxKind::Module {
            if let Some(name) = extract_module_name(&child) {
                modules.push(ParsedModule {
                    name,
                    syntax_node: child,
                });
            }
        }
    }

    MultiModuleParseResult {
        modules,
        errors: result.errors,
    }
}

/// Extract the module name from a Module syntax node.
///
/// Walks the children looking for `ModuleKw` followed by `Ident`.
fn extract_module_name(module_node: &SyntaxNode) -> Option<String> {
    let mut saw_module_kw = false;
    for child in module_node.children_with_tokens() {
        if let rowan::NodeOrToken::Token(token) = child {
            if token.kind() == SyntaxKind::ModuleKw {
                saw_module_kw = true;
            } else if saw_module_kw && token.kind() == SyntaxKind::Ident {
                return Some(token.text().to_string());
            }
        }
    }
    None
}
