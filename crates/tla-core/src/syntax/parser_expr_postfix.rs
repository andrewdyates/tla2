// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Postfix operator and step reference parsing routines for the TLA+ parser.
//!
//! Handles prime (`'`), function application (`f[x]`), record access (`r.field`),
//! module references (`M!Op`), action subscripts (`[A]_v`), and step references
//! (`<N>label`). Extracted from parser_expr.rs to keep parser files under size gates.

use super::parser_tables::{is_keyword_as_field_name, is_module_ref_operator};
use super::Parser;
use crate::syntax::kinds::SyntaxKind;
use crate::syntax::lexer::Token;

impl Parser {
    /// Check if we're at a step reference pattern: <N>label
    /// This is used in proofs to reference the result of a prior step
    pub(super) fn is_step_reference(&self) -> bool {
        if self.current() != Some(Token::Lt) {
            return false;
        }
        let next1 = self.peek_nth(1);
        let next2 = self.peek_nth(2);
        // Pattern: < NUMBER > followed by optional label
        if next1 == Some(Token::Number) && next2 == Some(Token::Gt) {
            // Check what comes after >
            let next3 = self.peek_nth(3);
            // Valid step references: <1>1, <2>a, <3>, etc.
            // Must be followed by a label (Number or Ident) or end of step ref
            matches!(next3, Some(Token::Number) | Some(Token::Ident) | None)
                || !matches!(
                    next3,
                    Some(Token::Plus) | Some(Token::Minus) | Some(Token::Star) | Some(Token::Slash)
                )
        } else {
            false
        }
    }

    /// Parse a step reference: <N>label (e.g., <4>4, <2>a)
    pub(super) fn parse_step_reference(&mut self) {
        let cp = self.checkpoint();
        self.start_node(SyntaxKind::StepLabel);
        self.bump_skip_trivia(); // <
        self.bump_skip_trivia(); // number
        self.bump_skip_trivia(); // >
                                 // Optional label (number or identifier)
        if self.at(Token::Number) || self.at(Token::Ident) {
            self.bump_skip_trivia();
        }
        self.finish_node();
        self.parse_postfix(cp);
    }

    /// Parse postfix operators: prime, function application, field access
    /// checkpoint should be the position before the atom being modified
    pub(super) fn parse_postfix(&mut self, checkpoint: usize) {
        let mut current_checkpoint = checkpoint;
        loop {
            match self.current() {
                Some(Token::Prime) => {
                    // Wrap the preceding expression in a UnaryExpr
                    self.start_node_at(current_checkpoint, SyntaxKind::UnaryExpr);
                    self.bump_skip_trivia();
                    self.finish_node();
                    // Update checkpoint for chained postfix ops
                    current_checkpoint = checkpoint;
                }
                Some(Token::LBracket) => {
                    // Function application f[x] or f[x,y] (tuple index) - wrap the function expression
                    self.start_node_at(current_checkpoint, SyntaxKind::FuncApplyExpr);
                    self.bump_skip_trivia();
                    self.parse_expr();
                    // Handle tuple indexing: f[x,y,z]
                    while self.at(Token::Comma) {
                        self.bump_skip_trivia();
                        self.parse_expr();
                    }
                    self.expect(Token::RBracket);
                    self.finish_node();
                    current_checkpoint = checkpoint;
                }
                Some(Token::Dot) => {
                    // Record field access r.field - wrap the record expression
                    // TLC/SANY allows keywords as field names (e.g., bar.RECURSIVE, bar.NEW)
                    self.start_node_at(current_checkpoint, SyntaxKind::RecordAccessExpr);
                    self.bump_skip_trivia();
                    if self.at(Token::Ident) || self.current().is_some_and(is_keyword_as_field_name)
                    {
                        self.bump_skip_trivia();
                    } else {
                        self.error("expected field name".to_string());
                    }
                    self.finish_node();
                    current_checkpoint = checkpoint;
                }
                Some(Token::Bang) => {
                    // Disambiguate:
                    // - Theorem assertion: TheoremName!:
                    // - Module reference: Module!Op or Module!Op(args)
                    // - Module reference to operator symbol: R!+(a, b), R!\leq(a, b)
                    // - TLAPS-generated operator names: Op! (as part of name) applied like `Op!(x)`
                    if self.peek() == Some(Token::Colon) {
                        // Theorem assertion: Name!:
                        self.start_node_at(current_checkpoint, SyntaxKind::TheoremRefExpr);
                        self.bump_skip_trivia(); // !
                        self.bump_skip_trivia(); // :
                        self.finish_node();
                        current_checkpoint = checkpoint;
                        continue;
                    }
                    if self.peek() == Some(Token::LParen) {
                        self.start_node_at(current_checkpoint, SyntaxKind::ApplyExpr);
                        self.bump_skip_trivia(); // !
                        self.parse_arg_list();
                        self.finish_node();
                        current_checkpoint = checkpoint;
                        continue;
                    }

                    self.start_node_at(current_checkpoint, SyntaxKind::ModuleRefExpr);
                    self.bump_skip_trivia(); // !
                    if self.at(Token::Ident) {
                        self.bump_skip_trivia();
                        // Check for function application
                        if self.at(Token::LParen) {
                            self.parse_arg_list();
                        }
                    } else if self.at(Token::Number) {
                        // TLAPS sometimes generates names like `TLANext!1`.
                        self.bump_skip_trivia();
                    } else if self.current().is_some_and(is_module_ref_operator) {
                        // Module reference to operator symbol: R!+(a, b), R!\leq(a, b)
                        self.bump_skip_trivia(); // operator symbol
                                                 // Check for function application
                        if self.at(Token::LParen) {
                            self.parse_arg_list();
                        }
                    } else {
                        // Leave as-is for error recovery; do not emit a hard error here because `!`
                        // is overloaded in multiple TLA+/TLAPS syntactic contexts.
                    }
                    self.finish_node();
                    current_checkpoint = checkpoint;
                }
                Some(Token::Underscore) => {
                    // Action subscript: [A]_v or <<A>>_v or [A]_<<v1, v2>> or [A]_(expr)
                    // Subscript can be identifier, tuple, or parenthesized expression.
                    // Only valid after action brackets `[A]` or `<<A>>`, i.e., when the
                    // previous non-trivia token is `]` or `>>`. (#451)
                    let prev = self.prev_non_trivia();
                    let valid_subscript_context =
                        prev == Some(Token::RBracket) || prev == Some(Token::RAngle);
                    let next = self.peek();
                    if valid_subscript_context
                        && (next == Some(Token::Ident)
                            || next == Some(Token::LAngle)
                            || next == Some(Token::LParen))
                    {
                        self.start_node_at(current_checkpoint, SyntaxKind::SubscriptExpr);
                        self.bump_skip_trivia(); // _
                        if self.at(Token::Ident) {
                            // Allow postfix expressions in subscripts, e.g. `[A]_M!vars`.
                            // We parse `M` as an atom and then allow module references and other
                            // postfix operators to attach to it.
                            let sub_cp = self.checkpoint();
                            self.bump_skip_trivia(); // identifier
                            self.parse_postfix(sub_cp);
                        } else if self.at(Token::LAngle) {
                            self.parse_tuple(); // tuple expression
                        } else if self.at(Token::LParen) {
                            // Parenthesized subscript expression: _(expr)
                            self.start_node(SyntaxKind::ParenExpr);
                            self.bump_skip_trivia(); // (
                            self.parse_expr();
                            self.expect(Token::RParen); // )
                            self.finish_node();
                        }
                        self.finish_node();
                        current_checkpoint = checkpoint;
                    } else {
                        break;
                    }
                }
                Some(Token::Ident) => {
                    // Action subscript with underscore-prefixed identifier: [A]_vars
                    // With the lexer change, _vars is tokenized as Ident("_vars") rather than
                    // Underscore followed by Ident("vars"). We handle this by checking if the
                    // identifier starts with underscore.
                    // Only valid after action brackets `[A]` or `<<A>>`, i.e., when the
                    // previous non-trivia token is `]` or `>>`. (#451)
                    let prev = self.prev_non_trivia();
                    let valid_subscript_context =
                        prev == Some(Token::RBracket) || prev == Some(Token::RAngle);
                    let text = self.current_text();
                    if valid_subscript_context && text.is_some_and(|t| t.starts_with('_')) {
                        self.start_node_at(current_checkpoint, SyntaxKind::SubscriptExpr);
                        let sub_cp = self.checkpoint();
                        self.bump_skip_trivia(); // underscore-prefixed identifier
                        self.parse_postfix(sub_cp);
                        self.finish_node();
                        current_checkpoint = checkpoint;
                    } else {
                        break;
                    }
                }
                _ => break,
            }
        }
    }
}
