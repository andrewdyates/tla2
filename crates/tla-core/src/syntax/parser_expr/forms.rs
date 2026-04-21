// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Structured expression forms: IF/THEN/ELSE, CASE, LET/IN, set expressions,
//! tuples, and underscore-prefixed definitions.

use super::Parser;
use crate::syntax::kinds::SyntaxKind;
use crate::syntax::lexer::Token;

impl Parser {
    /// Parse IF cond THEN a ELSE b
    ///
    /// The condition can contain And/Or (e.g., `IF a /\ b THEN c ELSE d`).
    ///
    /// Layout-aware parsing handles bullet lists in THEN/ELSE branches correctly:
    /// - Bullets inside the branch (at greater column) are parsed as part of the branch
    /// - Bullets at the outer junction list's column stop the branch parsing
    pub(crate) fn parse_if(&mut self) {
        self.start_node(SyntaxKind::IfExpr);
        self.bump_skip_trivia(); // IF

        self.parse_expr(); // condition - can contain And/Or

        self.expect(Token::Then);
        self.parse_expr(); // THEN branch - layout-aware parsing handles bullets

        self.expect(Token::Else);
        self.parse_expr(); // ELSE branch - layout-aware parsing handles bullets

        self.finish_node();
    }

    /// Parse CASE arm1 [] arm2 [] OTHER -> default
    pub(crate) fn parse_case(&mut self) {
        self.start_node(SyntaxKind::CaseExpr);
        self.bump_skip_trivia(); // CASE

        // First arm (no [])
        self.start_node(SyntaxKind::CaseArm);
        self.parse_expr(); // guard
        self.expect(Token::Arrow);
        self.parse_expr(); // body
        self.finish_node();

        // Remaining arms with []
        while self.at(Token::Always) {
            // [] is lexed as Always
            self.bump_skip_trivia();

            if self.at(Token::Other) {
                // OTHER case
                self.bump_skip_trivia();
                self.expect(Token::Arrow);
                self.parse_expr();
                break;
            }

            self.start_node(SyntaxKind::CaseArm);
            self.parse_expr();
            self.expect(Token::Arrow);
            self.parse_expr();
            self.finish_node();
        }

        self.finish_node();
    }

    /// Parse LET defs IN body
    ///
    /// Standard form: `LET Op == e IN body`
    /// Apalache extension: `LET Op == e` without IN (body is implicitly the last defined name).
    /// SANY does not accept the no-IN form, but Apalache does.
    pub(crate) fn parse_let(&mut self) {
        self.start_node(SyntaxKind::LetExpr);
        self.bump_skip_trivia(); // LET

        // Definitions (can include RECURSIVE declarations)
        while !self.at(Token::In) && !self.at_eof() && !self.at(Token::ModuleEnd) {
            if self.at(Token::Recursive) {
                self.parse_recursive_decl();
            } else if self.at(Token::Ident) {
                self.parse_operator_def();
            } else if self.at(Token::Underscore) && self.peek() == Some(Token::Ident) {
                // Underscore-prefixed identifier: _name
                self.parse_underscore_prefixed_def();
            } else {
                break;
            }
        }

        if self.at(Token::In) {
            self.bump_skip_trivia(); // IN
            self.parse_expr();
        }
        // If no IN found, this is an Apalache-style LET without IN.
        // The node is closed without a body expression; the lowering
        // will treat the last definition's value as the result.

        self.finish_node();
    }

    /// Parse underscore-prefixed operator definition: _name == expr
    pub(crate) fn parse_underscore_prefixed_def(&mut self) {
        self.start_node(SyntaxKind::OperatorDef);
        self.bump_skip_trivia(); // _
        self.bump_skip_trivia(); // identifier

        // Optional parameters
        if self.at(Token::LParen) {
            self.parse_param_list();
        }

        // ==
        if self.at(Token::DefEq) || self.at(Token::TriangleEq) {
            self.bump_skip_trivia();
        } else {
            self.error("expected == in operator definition".to_string());
        }

        // Body expression
        self.parse_expr();

        self.finish_node();
    }

    /// Parse {a, b, c} or {x \in S : P} or {expr : x \in S}
    pub(crate) fn parse_set_expr(&mut self) {
        self.bump_skip_trivia(); // {

        if self.at(Token::RBrace) {
            // Empty set
            self.start_node(SyntaxKind::SetEnumExpr);
            self.bump_skip_trivia();
            self.finish_node();
            return;
        }

        // Save position for lookahead
        let checkpoint = self.pos;

        // Try to detect set filter: {x \in S : P} or {<<x, y>> \in S : P}
        // Pattern: identifier or tuple pattern followed by \in
        // NOTE: Use skip_trivia_no_emit during lookahead to avoid duplicating tokens
        if self.at(Token::Ident) {
            self.pos += 1;
            self.skip_trivia_no_emit();
            // Handle multiple identifiers: {x,y \in S : P}
            while self.at(Token::Comma) {
                self.pos += 1;
                self.skip_trivia_no_emit();
                if self.at(Token::Ident) {
                    self.pos += 1;
                    self.skip_trivia_no_emit();
                } else {
                    break;
                }
            }
            if self.at(Token::In_) {
                // This is a set filter: {x \in S : P}
                self.pos = checkpoint;
                self.start_node(SyntaxKind::SetFilterExpr);
                self.parse_bound_var();
                if self.at(Token::Colon) {
                    self.bump_skip_trivia();
                    self.parse_expr();
                    self.expect(Token::RBrace);
                    self.finish_node();
                    return;
                }
                // No colon - this must be something else, recover
                self.expect(Token::RBrace);
                self.finish_node();
                return;
            }
            self.pos = checkpoint;
        } else if self.at(Token::LAngle) {
            // Tuple pattern: {<<x, y>> \in S : P}
            // Skip over the tuple pattern to check for \in
            self.pos += 1; // <<
            self.skip_trivia_no_emit();
            // Skip tuple contents (identifiers and commas)
            let mut depth = 1;
            while depth > 0 && !self.at_eof() {
                if self.at(Token::LAngle) {
                    depth += 1;
                } else if self.at(Token::RAngle) {
                    depth -= 1;
                }
                self.pos += 1;
                self.skip_trivia_no_emit();
            }
            if self.at(Token::In_) {
                // This is a set filter with tuple pattern: {<<x, y>> \in S : P}
                self.pos = checkpoint;
                self.start_node(SyntaxKind::SetFilterExpr);
                self.parse_bound_var();
                if self.at(Token::Colon) {
                    self.bump_skip_trivia();
                    self.parse_expr();
                    self.expect(Token::RBrace);
                    self.finish_node();
                    return;
                }
                // No colon - this must be something else, recover
                self.expect(Token::RBrace);
                self.finish_node();
                return;
            }
            self.pos = checkpoint;
        }

        // Either set enumeration {a, b, c} or set map {expr : x \in S}
        // Use checkpoint to allow wrapping as SetBuilderExpr if we see :
        let expr_checkpoint = self.checkpoint();
        self.parse_expr();

        if self.at(Token::Colon) {
            // Set map/builder: {expr : x \in S}
            self.start_node_at(expr_checkpoint, SyntaxKind::SetBuilderExpr);
            self.bump_skip_trivia(); // :
            self.parse_bound_var_list();
            self.expect(Token::RBrace);
            self.finish_node();
            return;
        }

        // Set enumeration: {a, b, c}
        // Wrap from checkpoint as SetEnumExpr
        self.start_node_at(expr_checkpoint, SyntaxKind::SetEnumExpr);
        while self.at(Token::Comma) {
            self.bump_skip_trivia();
            if !self.at(Token::RBrace) {
                self.parse_expr();
            }
        }

        self.expect(Token::RBrace);
        self.finish_node();
    }

    /// Parse <<a, b, c>>
    pub(crate) fn parse_tuple(&mut self) {
        self.start_node(SyntaxKind::TupleExpr);
        self.bump_skip_trivia(); // <<

        if !self.at(Token::RAngle) {
            self.parse_expr();
            while self.at(Token::Comma) {
                self.bump_skip_trivia();
                self.parse_expr();
            }
        }

        self.expect(Token::RAngle);
        self.finish_node();
    }
}
