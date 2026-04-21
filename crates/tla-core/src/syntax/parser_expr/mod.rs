// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Expression parsing routines for the TLA+ parser.
//!
//! This file contains the core Pratt parser entry and infix loop.
//!
//! Prefix/atom dispatch is in `prefix.rs`, binding-oriented forms (quantifiers,
//! CHOOSE, LAMBDA) are in `binders.rs`, and structured expression forms (IF,
//! CASE, LET, sets, tuples) are in `forms.rs`.
//!
//! Bracket expressions, junction lists, and postfix operators are in
//! sibling modules: parser_expr_bracket, parser_expr_junction, parser_expr_postfix.

use super::parser_tables::infix_binding_power;
use super::Parser;
use crate::syntax::kinds::SyntaxKind;
use crate::syntax::lexer::Token;

mod binders;
mod forms;
mod prefix;

impl Parser {
    // === Expression parsing (Pratt parser) ===

    /// Parse an expression
    pub(crate) fn parse_expr(&mut self) {
        self.parse_expr_bp(0);
    }

    /// Parse expression with binding power (Pratt parsing)
    pub(crate) fn parse_expr_bp(&mut self, min_bp: u8) {
        self.skip_trivia();

        // Create checkpoint before parsing LHS for Pratt parsing
        let checkpoint = self.checkpoint();

        // Parse prefix/atom
        self.parse_prefix_or_atom();

        // Parse infix operators
        loop {
            self.skip_trivia();

            let Some(op) = self.current() else { break };

            // Layout-aware bullet list parsing: if we're inside a junction list
            // and see ANY operator at the same or left of the junction column, stop parsing.
            // This ensures that operators don't get parsed as infix operators
            // inside IF-THEN-ELSE branches or other nested expressions.
            //
            // Example that would fail without this fix:
            //   /\ IF TRUE THEN TRUE ELSE FALSE
            //   => FALSE
            // Without this check, "=> FALSE" would be parsed as part of the ELSE branch,
            // giving: IF TRUE THEN TRUE ELSE (FALSE => FALSE)
            // With this check, parsing stops at "=>" and the correct parse is:
            //         (IF TRUE THEN TRUE ELSE FALSE) => FALSE
            //
            // This matches SANY's isAboveCurrent() check which requires tokens to be
            // STRICTLY to the right of the junction column to continue parsing.
            if let Some(junction_column) = self.junction_context.current_column() {
                let op_column = self.current_column();
                if op_column <= junction_column {
                    break;
                }
            }

            // Special case: don't treat < as infix if it looks like a proof step label
            // Pattern: < NUMBER > [label] . (e.g., <1>., <1>1., <2>a.)
            if op == Token::Lt && self.is_step_label_start() {
                break;
            }

            // Special case: don't treat - as infix if followed by . (prefix operator definition)
            // Pattern: -. a == ... defines unary minus operator
            if op == Token::Minus && self.peek() == Some(Token::Dot) {
                break;
            }

            // Check for parenthesized infix operator: B (-) C
            if op == Token::LParen && self.is_parenthesized_infix_op() {
                // Get the inner operator to determine binding power
                let inner_op = self.peek_nth(1);
                let Some((l_bp, r_bp)) = inner_op.and_then(infix_binding_power) else {
                    break;
                };

                if l_bp < min_bp {
                    break;
                }

                // Wrap the previous expression in a BinaryExpr
                self.start_node_at(checkpoint, SyntaxKind::BinaryExpr);
                self.bump_skip_trivia(); // (
                self.bump_skip_trivia(); // operator
                self.expect(Token::RParen); // )
                self.parse_expr_bp(r_bp);
                self.finish_node();
                continue;
            }

            let Some((l_bp, r_bp)) = infix_binding_power(op) else {
                break;
            };

            if l_bp < min_bp {
                break;
            }

            // Wrap the previous expression in a BinaryExpr
            self.start_node_at(checkpoint, SyntaxKind::BinaryExpr);

            self.bump_skip_trivia(); // operator
            self.parse_expr_bp(r_bp);
            self.finish_node();
        }
    }
}
