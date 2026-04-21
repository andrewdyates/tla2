// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Binding-oriented expression forms: quantifiers, CHOOSE, bound variables,
//! tuple patterns, and LAMBDA.

use super::Parser;
use crate::syntax::kinds::SyntaxKind;
use crate::syntax::lexer::Token;

impl Parser {
    /// Parse quantifier: \A x \in S : P or \A x : P
    pub(crate) fn parse_quantifier(&mut self) {
        self.start_node(SyntaxKind::QuantExpr);
        self.bump_skip_trivia(); // \A or \E

        self.parse_bound_var_list();

        self.expect(Token::Colon);
        self.parse_expr();

        self.finish_node();
    }

    /// Parse CHOOSE x \in S : P
    pub(crate) fn parse_choose(&mut self) {
        self.start_node(SyntaxKind::ChooseExpr);
        self.bump_skip_trivia(); // CHOOSE

        self.parse_bound_var();

        self.expect(Token::Colon);
        self.parse_expr();

        self.finish_node();
    }

    /// Parse bound variable list: x \in S, y \in T
    pub(crate) fn parse_bound_var_list(&mut self) {
        self.parse_bound_var();
        while self.at(Token::Comma) {
            self.bump_skip_trivia();
            self.parse_bound_var();
        }
    }

    /// Parse bound variable: x \in S or just x
    /// Note: multiple identifiers sharing a set (e.g. `x, y, z \in S`) are parsed as
    /// multiple BoundVar nodes where only the last one has the domain; the lowerer
    /// propagates the domain backwards.
    /// Also handles tuple patterns: <<x, y>> \in S for destructuring
    pub(crate) fn parse_bound_var(&mut self) {
        self.start_node(SyntaxKind::BoundVar);

        // Check for tuple pattern: <<x, y>> \in S
        if self.at(Token::LAngle) {
            self.parse_tuple_pattern();
        } else if self.at(Token::Ident) {
            self.bump_skip_trivia();
        }

        if self.at(Token::In_) {
            self.bump_skip_trivia();
            // Domain expression can be complex (e.g., 0 .. bound, S \cup T)
            // But must be careful not to consume :, }, ], ) which end bound var lists
            self.parse_domain_expr();
        }

        self.finish_node();
    }

    /// Parse tuple pattern: <<x, y>> for destructuring in quantifiers
    pub(crate) fn parse_tuple_pattern(&mut self) {
        self.start_node(SyntaxKind::TuplePattern);
        self.bump_skip_trivia(); // <<

        if !self.at(Token::RAngle) {
            // Parse first identifier
            if self.at(Token::Ident) {
                self.bump_skip_trivia();
            }
            // Parse remaining identifiers
            while self.at(Token::Comma) {
                self.bump_skip_trivia();
                if self.at(Token::Ident) {
                    self.bump_skip_trivia();
                }
            }
        }

        self.expect(Token::RAngle);
        self.finish_node();
    }

    /// Parse a domain expression in a bound variable context
    /// Stops at :, }, ], ), | which typically end the domain
    pub(crate) fn parse_domain_expr(&mut self) {
        self.parse_expr_bp(0);
    }

    /// Parse LAMBDA x, y : body
    pub(crate) fn parse_lambda(&mut self) {
        self.start_node(SyntaxKind::LambdaExpr);
        self.bump_skip_trivia(); // LAMBDA

        // Parameters
        if self.at(Token::Ident) {
            self.bump_skip_trivia();
            while self.at(Token::Comma) {
                self.bump_skip_trivia();
                if self.at(Token::Ident) {
                    self.bump_skip_trivia();
                }
            }
        }

        self.expect(Token::Colon);
        self.parse_expr();

        self.finish_node();
    }
}
