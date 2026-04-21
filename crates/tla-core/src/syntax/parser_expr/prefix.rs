// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Prefix operator and atom dispatch for expression parsing.

use super::Parser;
use crate::syntax::kinds::SyntaxKind;
use crate::syntax::lexer::Token;

impl Parser {
    /// Parse prefix operator or atom
    pub(crate) fn parse_prefix_or_atom(&mut self) {
        match self.current() {
            // Step reference in expression context: <4>4, <2>a, etc.
            Some(Token::Lt) if self.is_step_reference() => {
                self.parse_step_reference();
            }
            // Prefix operators
            Some(Token::Not) => {
                self.start_node(SyntaxKind::UnaryExpr);
                self.bump_skip_trivia();
                self.parse_prefix_or_atom();
                self.finish_node();
            }
            Some(Token::Minus) => {
                self.start_node(SyntaxKind::UnaryExpr);
                self.bump_skip_trivia();
                self.parse_prefix_or_atom();
                self.finish_node();
            }
            Some(Token::Always) => {
                self.start_node(SyntaxKind::UnaryExpr);
                self.bump_skip_trivia();
                // Action subscripts like `[][Next]_vars` require postfix parsing on the
                // operand. The subscript `_vars` follows the bracketed action `[Next]`,
                // so we need to call parse_postfix to consume it. (#465)
                let operand_cp = self.checkpoint();
                self.parse_prefix_or_atom();
                self.parse_postfix(operand_cp);
                self.finish_node();
            }
            Some(Token::Eventually) => {
                self.start_node(SyntaxKind::UnaryExpr);
                self.bump_skip_trivia();
                // Action subscripts like `<><<Action>>_vars` require postfix parsing on the
                // operand, similar to Always. (#465)
                let operand_cp = self.checkpoint();
                self.parse_prefix_or_atom();
                self.parse_postfix(operand_cp);
                self.finish_node();
            }
            Some(Token::Enabled) => {
                self.start_node(SyntaxKind::UnaryExpr);
                self.bump_skip_trivia();
                self.parse_prefix_or_atom();
                self.finish_node();
            }
            Some(Token::Unchanged) => {
                self.start_node(SyntaxKind::UnaryExpr);
                self.bump_skip_trivia();
                self.parse_prefix_or_atom();
                self.finish_node();
            }
            Some(Token::Powerset) => {
                self.start_node(SyntaxKind::UnaryExpr);
                self.bump_skip_trivia();
                self.parse_prefix_or_atom();
                self.finish_node();
            }
            Some(Token::BigUnion) => {
                self.start_node(SyntaxKind::UnaryExpr);
                self.bump_skip_trivia();
                self.parse_prefix_or_atom();
                self.finish_node();
            }
            Some(Token::Domain) => {
                self.start_node(SyntaxKind::UnaryExpr);
                self.bump_skip_trivia();
                self.parse_prefix_or_atom();
                self.finish_node();
            }
            // Quantifiers (including temporal)
            Some(Token::Forall)
            | Some(Token::Exists)
            | Some(Token::TemporalForall)
            | Some(Token::TemporalExists) => {
                self.parse_quantifier();
            }
            Some(Token::Choose) => {
                self.parse_choose();
            }
            // Control flow
            Some(Token::If) => {
                self.parse_if();
            }
            Some(Token::Case) => {
                self.parse_case();
            }
            Some(Token::Let) => {
                self.parse_let();
            }
            // Parenthesized expression
            Some(Token::LParen) => {
                let cp = self.checkpoint();
                // Check for parenthesized operator reference: (+), (-), etc.
                // These are operator values, not expressions inside parens
                if self.is_parenthesized_infix_op() {
                    self.start_node(SyntaxKind::OperatorRef);
                    self.bump_skip_trivia(); // (
                    self.bump_skip_trivia(); // operator
                    self.expect(Token::RParen); // )
                    self.finish_node();
                    self.parse_postfix(cp);
                } else {
                    self.start_node(SyntaxKind::ParenExpr);
                    self.bump_skip_trivia();
                    self.parse_expr();
                    self.expect(Token::RParen);
                    self.finish_node();
                    self.parse_postfix(cp);
                }
            }
            // Set literal or comprehension
            Some(Token::LBrace) => {
                let cp = self.checkpoint();
                self.parse_set_expr();
                self.parse_postfix(cp);
            }
            // Tuple
            Some(Token::LAngle) => {
                let cp = self.checkpoint();
                self.parse_tuple();
                self.parse_postfix(cp);
            }
            // Function/record expression
            Some(Token::LBracket) => {
                let cp = self.checkpoint();
                self.parse_bracket_expr();
                self.parse_postfix(cp);
            }
            // Lambda
            Some(Token::Lambda) => {
                self.parse_lambda();
            }
            // Literals and identifiers
            Some(Token::True) | Some(Token::False) => {
                let cp = self.checkpoint();
                self.bump_skip_trivia();
                self.parse_postfix(cp);
            }
            Some(Token::Number) => {
                let cp = self.checkpoint();
                self.bump_skip_trivia();
                self.parse_postfix(cp);
            }
            Some(Token::String) => {
                let cp = self.checkpoint();
                self.bump_skip_trivia();
                self.parse_postfix(cp);
            }
            // Underscore-prefixed identifier: _n
            Some(Token::Underscore) if self.peek() == Some(Token::Ident) => {
                let cp = self.checkpoint();
                self.bump_skip_trivia(); // _
                self.bump_skip_trivia(); // identifier
                                         // Check for function application
                if self.at(Token::LParen) {
                    self.start_node(SyntaxKind::ApplyExpr);
                    self.parse_arg_list();
                    self.finish_node();
                }
                self.parse_postfix(cp);
            }
            Some(Token::Ident) => {
                let cp = self.checkpoint();
                if self.peek() == Some(Token::ColonColon) {
                    self.start_node_at(cp, SyntaxKind::LabelExpr);
                    self.bump_skip_trivia(); // label name
                    self.bump_skip_trivia(); // ::
                    self.parse_expr();
                    self.finish_node();
                    return;
                }
                self.bump_skip_trivia();
                // Some TLAPS-generated names include a trailing `!` as part of the operator name,
                // and are then applied like a normal operator: `IInv!(i)`.
                // Disambiguate this from module references `M!Op` by looking for `!(`.
                if self.at(Token::Bang) && self.peek() == Some(Token::LParen) {
                    self.bump_skip_trivia(); // !
                    self.start_node(SyntaxKind::ApplyExpr);
                    self.parse_arg_list();
                    self.finish_node();
                    self.parse_postfix(cp);
                    return;
                }
                // Check for function application
                // BUT NOT if it's a parenthesized infix operator like (-)
                // In that case, the infix loop will handle it
                if self.at(Token::LParen) && !self.is_parenthesized_infix_op() {
                    // Use checkpoint to include the identifier in the ApplyExpr
                    self.start_node_at(cp, SyntaxKind::ApplyExpr);
                    self.parse_arg_list();
                    self.finish_node();
                }
                self.parse_postfix(cp);
            }
            Some(Token::Boolean) => {
                let cp = self.checkpoint();
                self.bump_skip_trivia();
                self.parse_postfix(cp);
            }
            // @ - used in EXCEPT expressions to refer to current value
            Some(Token::At) => {
                let cp = self.checkpoint();
                self.bump_skip_trivia();
                self.parse_postfix(cp);
            }
            // Standard library operators that take arguments via parentheses
            // These are from the Sequences and other standard modules
            Some(Token::Len)
            | Some(Token::Seq)
            | Some(Token::SubSeq)
            | Some(Token::SelectSeq)
            | Some(Token::Head)
            | Some(Token::Tail)
            | Some(Token::Append) => {
                let cp = self.checkpoint();
                self.bump_skip_trivia();
                // Check for function application
                // Use checkpoint to include the stdlib keyword in the ApplyExpr
                if self.at(Token::LParen) {
                    self.start_node_at(cp, SyntaxKind::ApplyExpr);
                    self.parse_arg_list();
                    self.finish_node();
                }
                self.parse_postfix(cp);
            }
            // Weak/Strong fairness
            Some(Token::WeakFair) | Some(Token::StrongFair) => {
                self.parse_fairness();
            }
            // And/Or at start of expression (TLA+ bullet list pattern)
            // In TLA+, you can write:
            //   /\ x = 0
            //   /\ y = 1
            // which is equivalent to: x = 0 /\ y = 1
            //
            // Layout-aware parsing: bullets at the same column form a list,
            // bullets at greater columns are nested expressions.
            Some(Token::And) | Some(Token::Or) => {
                self.parse_bullet_list();
            }
            // INSTANCE is not a general expression (TLC/SANY parity).
            //
            // We still allow `Op == INSTANCE M WITH ...` by parsing it specially in
            // `parse_operator_def`, but reject `INSTANCE` elsewhere (e.g., substitution RHS).
            Some(Token::Instance) => {
                self.error("INSTANCE is not a valid expression here".to_string());
                self.bump_skip_trivia();
            }
            // Operators as values (can be passed to higher-order operators)
            // e.g., ReduceSet(\intersect, S, base)
            // Note: Minus is handled above as prefix, but can also be an infix op value
            Some(Token::Intersect)
            | Some(Token::Union)
            | Some(Token::SetMinus)
            | Some(Token::Plus)
            | Some(Token::Star)
            | Some(Token::Slash)
            | Some(Token::Div)
            | Some(Token::Percent)
            | Some(Token::Caret)
            | Some(Token::Eq)
            | Some(Token::Neq)
            | Some(Token::Lt)
            | Some(Token::Gt)
            | Some(Token::Leq)
            | Some(Token::Geq)
            | Some(Token::Prec)
            | Some(Token::Preceq)
            | Some(Token::Succ)
            | Some(Token::Succeq)
            | Some(Token::Implies)
            | Some(Token::Equiv)
            | Some(Token::Concat)
            | Some(Token::In_)
            | Some(Token::NotIn)
            | Some(Token::Subseteq)
            | Some(Token::Subset)
            | Some(Token::Supseteq)
            | Some(Token::Supset) => {
                // Treat operator as an expression (operator reference)
                let cp = self.checkpoint();
                self.start_node(SyntaxKind::OperatorRef);
                self.bump_skip_trivia();
                self.finish_node();
                self.parse_postfix(cp);
            }
            _ => {
                // Unknown token - error recovery
                if !self.at_eof() {
                    self.error(format!("expected expression, found {:?}", self.current()));
                }
            }
        }
    }

    /// Parse WF_vars(A) or SF_vars(A)
    pub(crate) fn parse_fairness(&mut self) {
        self.start_node(SyntaxKind::BinaryExpr);
        self.bump_skip_trivia(); // WF_ or SF_

        // Subscript expression
        self.parse_prefix_or_atom();

        // Action in parentheses
        if self.at(Token::LParen) {
            self.bump_skip_trivia();
            self.parse_expr();
            self.expect(Token::RParen);
        }

        self.finish_node();
    }
}
