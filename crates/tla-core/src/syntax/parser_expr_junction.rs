// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Junction list and argument list parsing routines for the TLA+ parser.
//!
//! Handles layout-aware bullet-style conjunction/disjunction lists (`/\` and `\/`)
//! and parenthesized argument lists. Extracted from parser_expr.rs to keep parser
//! files under size gates.

use super::parser_tables::infix_binding_power;
use super::{JunctionType, Parser};
use crate::syntax::kinds::SyntaxKind;
use crate::syntax::lexer::Token;

impl Parser {
    /// Parse a bullet-style conjunction or disjunction list with layout awareness.
    ///
    /// TLA+ allows "bullet-style" lists like:
    /// ```tla
    ///   /\ x = 0
    ///   /\ y = 1
    /// ```
    /// which is equivalent to `x = 0 /\ y = 1`.
    ///
    /// The key insight is that bullets at the same column form a list,
    /// while bullets at greater columns are nested inside the current expression.
    /// This is how SANY/TLC handle it, using a JunctionListContext.
    pub(super) fn parse_bullet_list(&mut self) {
        // Get the column and type of the initial bullet
        let bullet_column = self.current_column();
        let bullet_type = match self.current() {
            Some(Token::And) => JunctionType::Conjunction,
            Some(Token::Or) => JunctionType::Disjunction,
            _ => return, // Should not happen
        };

        // Start tracking this junction list
        self.junction_context.start(bullet_column, bullet_type);

        // Skip the first bullet (don't add to syntax tree)
        self.advance_skip_trivia();

        // Create a checkpoint before parsing the first expression
        let first_checkpoint = self.checkpoint();

        // Parse the first expression in the list
        // Use parse_expr_bp(0) but stop at bullets at our column level
        self.parse_bullet_list_item();

        // Now check for continuation bullets at the same column
        loop {
            self.skip_trivia();

            // Check if next token is a bullet at the same column and same type
            let next_token = self.current();
            let next_column = self.current_column();

            let is_continuation = matches!(next_token, Some(Token::And) | Some(Token::Or))
                && next_column == bullet_column
                && ((next_token == Some(Token::And) && bullet_type == JunctionType::Conjunction)
                    || (next_token == Some(Token::Or) && bullet_type == JunctionType::Disjunction));

            if !is_continuation {
                break;
            }

            // It's a continuation bullet - wrap previous expression in BinaryExpr
            self.start_node_at(first_checkpoint, SyntaxKind::BinaryExpr);

            // Add the bullet operator to the tree
            self.bump_skip_trivia();

            // Parse the next expression in the list
            self.parse_bullet_list_item();

            self.finish_node();
        }

        // End tracking this junction list
        self.junction_context.end();
    }

    /// Parse a single item within a bullet list.
    /// This parses an expression but stops at bullets at the current junction list's column.
    pub(super) fn parse_bullet_list_item(&mut self) {
        self.skip_trivia();

        // Create checkpoint for potential binary expression wrapping
        let checkpoint = self.checkpoint();

        // Parse prefix/atom
        self.parse_prefix_or_atom();

        // Parse infix operators, but stop at bullets at our junction list column
        loop {
            self.skip_trivia();

            let Some(op) = self.current() else { break };

            // Layout rule: if we encounter a token at or to the left of the current
            // junction list's bullet column, we've left the current list item.
            //
            // This matches SANY's behavior for patterns like:
            //   /\ /\ A
            //      /\ B
            //      => C
            // which should parse as (A /\ B) => C, not A /\ (B => C).
            let op_column = self.current_column();
            if let Some(junction_column) = self.junction_context.current_column() {
                if op_column <= junction_column {
                    break;
                }
            }

            // If this is And/Or, check if it's a bullet at our junction list's column
            if matches!(op, Token::And | Token::Or) {
                // If we're inside a junction list and this bullet is at or left of that column,
                // stop parsing - it's either a continuation or an outer bullet
                if let Some(junction_column) = self.junction_context.current_column() {
                    if op_column <= junction_column {
                        break;
                    }
                }
            }

            // Special case: don't treat < as infix if it looks like a proof step label
            if op == Token::Lt && self.is_step_label_start() {
                break;
            }

            // Special case: don't treat - as infix if followed by .
            if op == Token::Minus && self.peek() == Some(Token::Dot) {
                break;
            }

            // Check for parenthesized infix operator: B (-) C
            if op == Token::LParen && self.is_parenthesized_infix_op() {
                let inner_op = self.peek_nth(1);
                let Some((_, r_bp)) = inner_op.and_then(infix_binding_power) else {
                    break;
                };

                self.start_node_at(checkpoint, SyntaxKind::BinaryExpr);
                self.bump_skip_trivia(); // (
                self.bump_skip_trivia(); // operator
                self.expect(Token::RParen); // )
                self.parse_bullet_list_item_bp(r_bp);
                self.finish_node();
                continue;
            }

            let Some((_, r_bp)) = infix_binding_power(op) else {
                break;
            };

            // Wrap the previous expression in a BinaryExpr
            self.start_node_at(checkpoint, SyntaxKind::BinaryExpr);
            self.bump_skip_trivia(); // operator
            self.parse_bullet_list_item_bp(r_bp);
            self.finish_node();
        }
    }

    /// Parse expression with binding power for bullet list items.
    /// Similar to parse_expr_bp but respects junction list column boundaries.
    pub(super) fn parse_bullet_list_item_bp(&mut self, min_bp: u8) {
        self.skip_trivia();

        let checkpoint = self.checkpoint();
        self.parse_prefix_or_atom();

        loop {
            self.skip_trivia();

            let Some(op) = self.current() else { break };

            let op_column = self.current_column();
            if let Some(junction_column) = self.junction_context.current_column() {
                if op_column <= junction_column {
                    break;
                }
            }

            // If this is And/Or, check if it's a bullet at our junction list's column
            if matches!(op, Token::And | Token::Or) {
                if let Some(junction_column) = self.junction_context.current_column() {
                    if op_column <= junction_column {
                        break;
                    }
                }
            }

            if op == Token::Lt && self.is_step_label_start() {
                break;
            }

            if op == Token::Minus && self.peek() == Some(Token::Dot) {
                break;
            }

            if op == Token::LParen && self.is_parenthesized_infix_op() {
                let inner_op = self.peek_nth(1);
                let Some((inner_l_bp, r_bp)) = inner_op.and_then(infix_binding_power) else {
                    break;
                };

                if inner_l_bp < min_bp {
                    break;
                }

                self.start_node_at(checkpoint, SyntaxKind::BinaryExpr);
                self.bump_skip_trivia();
                self.bump_skip_trivia();
                self.expect(Token::RParen);
                self.parse_bullet_list_item_bp(r_bp);
                self.finish_node();
                continue;
            }

            let Some((l_bp, r_bp)) = infix_binding_power(op) else {
                break;
            };

            if l_bp < min_bp {
                break;
            }

            self.start_node_at(checkpoint, SyntaxKind::BinaryExpr);
            self.bump_skip_trivia();
            self.parse_bullet_list_item_bp(r_bp);
            self.finish_node();
        }
    }

    /// Parse argument list: (a, b, c)
    pub(super) fn parse_arg_list(&mut self) {
        self.start_node(SyntaxKind::ArgList);
        self.bump_skip_trivia(); // (

        if !self.at(Token::RParen) {
            self.parse_expr();
            while self.at(Token::Comma) {
                self.bump_skip_trivia();
                self.parse_expr();
            }
        }

        self.expect(Token::RParen);
        self.finish_node();
    }
}
