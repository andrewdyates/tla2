// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Declaration/operator parsing routines for the TLA+ parser.
//!
//! Extracted from parser.rs to keep parser files under size gates.

use super::parser_tables::{is_infix_op_symbol, is_stdlib_operator_name};
use super::Parser;
use crate::syntax::kinds::SyntaxKind;
use crate::syntax::lexer::Token;

impl Parser {
    pub(super) fn parse_recursive_decl(&mut self) {
        self.start_node(SyntaxKind::RecursiveDecl);
        self.bump_skip_trivia(); // RECURSIVE

        // Parse comma-separated operator signatures
        self.parse_recursive_op_signature();
        while self.at(Token::Comma) {
            self.bump_skip_trivia();
            self.parse_recursive_op_signature();
        }

        self.finish_node();
    }

    /// Parse a single recursive operator signature: Op(_, _)
    ///
    /// Accepts identifiers and standard library operator names (SelectSeq, Seq, etc.)
    /// because user code can redefine stdlib names with RECURSIVE.
    fn parse_recursive_op_signature(&mut self) {
        let is_name_token =
            self.at(Token::Ident) || self.current().is_some_and(is_stdlib_operator_name);
        if is_name_token {
            self.bump_skip_trivia();
            // Optional arity: (_, _, _)
            if self.at(Token::LParen) {
                self.bump_skip_trivia();
                while self.at(Token::Underscore) || self.at(Token::Comma) {
                    self.bump_skip_trivia();
                }
                self.expect(Token::RParen);
            }
        }
    }

    /// Parse ASSUME expr
    pub(super) fn parse_assume(&mut self) {
        self.start_node(SyntaxKind::AssumeStmt);
        self.bump_skip_trivia(); // ASSUME

        // Optional name
        if self.at(Token::Ident) && self.peek() == Some(Token::DefEq) {
            self.bump_skip_trivia(); // name
            self.bump_skip_trivia(); // ==
        }

        self.parse_expr();

        self.finish_node();
    }

    /// Parse THEOREM/LEMMA/PROPOSITION/COROLLARY
    pub(super) fn parse_theorem(&mut self) {
        self.start_node(SyntaxKind::TheoremStmt);
        self.bump_skip_trivia(); // THEOREM etc.

        // Optional name
        if self.at(Token::Ident) && self.peek() == Some(Token::DefEq) {
            self.bump_skip_trivia(); // name
            self.bump_skip_trivia(); // ==
        }

        if self.at(Token::Assume) {
            // TLAPS-style theorems/lemmas can be written as:
            //   LEMMA Foo ==
            //     ASSUME ...
            //     PROVE  ...
            self.parse_assume_prove_stmt();
        } else {
            self.parse_expr();
        }

        // Skip trivia before checking for proof start
        self.skip_trivia();

        // Optional PROOF - can start with PROOF, BY, OBVIOUS, OMITTED, or a step label (<n>)
        if self.at(Token::Proof)
            || self.at(Token::By)
            || self.at(Token::Obvious)
            || self.at(Token::Omitted)
            || self.at(Token::Lt)
        {
            self.parse_proof();
        }

        self.finish_node();
    }

    /// Parse INSTANCE Module WITH ... (as declaration)
    pub(super) fn parse_instance(&mut self) {
        self.start_node(SyntaxKind::InstanceDecl);
        self.parse_instance_body();
        self.finish_node();
    }

    /// Parse INSTANCE Module WITH ... (as expression)
    fn parse_instance_expr(&mut self) {
        self.start_node(SyntaxKind::InstanceDecl);
        self.parse_instance_body();
        self.finish_node();
    }

    /// Parse the body of an INSTANCE (shared between declaration and expression contexts)
    fn parse_instance_body(&mut self) {
        self.bump_skip_trivia(); // INSTANCE

        // Module name (can start with number like 2PCwithBTM)
        self.parse_module_name();

        // WITH substitutions
        if self.at(Token::With) {
            self.bump_skip_trivia();
            self.parse_substitution_list();
        }
    }

    /// Parse substitution list: x <- e, y <- f
    fn parse_substitution_list(&mut self) {
        self.parse_substitution();
        while self.at(Token::Comma) {
            self.bump_skip_trivia();
            self.parse_substitution();
        }
    }

    /// Parse single substitution: x <- e
    fn parse_substitution(&mut self) {
        self.start_node(SyntaxKind::Substitution);

        if self.at(Token::Ident) {
            self.bump_skip_trivia();
        }

        // <- (single token)
        self.expect(Token::LArrow);

        self.parse_expr();

        self.finish_node();
    }

    /// Parse operator definition: Op(x, y) == body
    /// Also handles:
    /// - Infix: a | b == body
    /// - Infix with parenthesized op: a (+) b == body
    /// - Function def: f[x \in S] == body
    pub(super) fn parse_operator_def(&mut self) {
        self.start_node(SyntaxKind::OperatorDef);

        // Operator name
        if self.at(Token::Ident) {
            self.bump_skip_trivia();
        }

        // Check what comes next to determine form
        match self.current() {
            // Could be parameter list OR parenthesized operator definition
            // a (+) b == body vs Op(x, y) == body
            Some(Token::LParen) => {
                // Lookahead to check if this is a parenthesized operator: (op)
                if self.is_parenthesized_infix_op() {
                    // Infix operator definition with parenthesized op: a (+) b == body
                    self.bump_skip_trivia(); // (
                    self.bump_skip_trivia(); // operator symbol
                    self.expect(Token::RParen); // )
                                                // Second operand name
                    if self.at(Token::Ident) {
                        self.bump_skip_trivia();
                    }
                } else {
                    // Standard parameter list: Op(x, y) == body
                    self.parse_param_list();
                }
            }
            // Function definition: f[x \in S] == body
            Some(Token::LBracket) => {
                self.parse_func_def_params();
            }
            // Postfix operator definition: L^+ == body, L^* == body
            // These define Kleene plus/star operators (but NOT a ^ b which is infix)
            Some(Token::Caret) => {
                // Peek ahead to see if this is postfix (^+ or ^*) or infix (^ b)
                let checkpoint = self.pos;
                self.pos += 1;
                self.skip_trivia_no_emit();
                if self.at(Token::Plus) || self.at(Token::Star) {
                    // It's a postfix operator definition
                    self.pos = checkpoint;
                    self.bump_skip_trivia(); // ^
                    self.bump_skip_trivia(); // + or *
                } else if self.at(Token::Ident) {
                    // It's an infix operator definition: a ^ b == body
                    self.pos = checkpoint;
                    self.bump_skip_trivia(); // ^
                    self.bump_skip_trivia(); // b (second operand name)
                } else {
                    self.pos = checkpoint;
                }
            }
            // Infix operator: a OP b == body (where OP is an operator symbol)
            Some(op) if is_infix_op_symbol(op) => {
                self.bump_skip_trivia(); // operator symbol
                if self.at(Token::Ident) {
                    self.bump_skip_trivia(); // second operand name
                }
            }
            _ => {
                // No parameters, just name == body
            }
        }

        // ==
        if self.at(Token::DefEq) || self.at(Token::TriangleEq) {
            self.bump_skip_trivia();
        } else {
            self.error("expected == in operator definition".to_string());
        }

        // Body expression.
        //
        // TLC/SANY treats `INSTANCE M WITH ...` as a module-level construct, not a general
        // expression. However, it is permitted as the *entire* RHS of a definition:
        //
        //   I == INSTANCE Mod WITH ...
        //
        // We parse that form here, but reject `INSTANCE` in general expression positions
        // (e.g., inside WITH substitutions).
        if self.at(Token::Instance) {
            self.parse_instance_expr();
        } else {
            self.parse_expr();
        }

        self.finish_node();
    }

    /// Parse prefix operator definition: -. a == 0 - a
    /// Pattern: <prefix-op>[.] <param> == <body>
    pub(super) fn parse_prefix_operator_def(&mut self) {
        self.start_node(SyntaxKind::OperatorDef);

        // Consume the operator symbol (e.g., -, ~, [], <>)
        self.bump_skip_trivia();

        // Check for optional dot (e.g., -. for unary minus)
        if self.at(Token::Dot) {
            self.bump_skip_trivia();
        }

        // Parse the parameter name
        if self.at(Token::Ident) {
            self.bump_skip_trivia();
        } else {
            self.error("expected parameter name in prefix operator definition".to_string());
        }

        // ==
        if self.at(Token::DefEq) || self.at(Token::TriangleEq) {
            self.bump_skip_trivia();
        } else {
            self.error("expected == in prefix operator definition".to_string());
        }

        // Body expression
        self.parse_expr();

        self.finish_node();
    }

    /// Parse operator definition for standard library tokens (Seq, Head, Tail, etc.)
    /// These tokens are keywords but in standard modules they're used as operator names
    pub(super) fn parse_stdlib_operator_def(&mut self) {
        self.start_node(SyntaxKind::OperatorDef);

        // Consume the stdlib token as the operator name
        self.bump_skip_trivia();

        // Check for parameters
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
        if self.at(Token::Instance) {
            self.parse_instance_expr();
        } else {
            self.parse_expr();
        }

        self.finish_node();
    }

    /// Parse operator definition in DEFINE context, allowing underscore-prefixed names
    /// e.g., DEFINE _m == m+1
    pub(super) fn parse_define_operator(&mut self) {
        // For underscore-prefixed names (like _m or __x), we need special handling.
        // With the lexer change, _m is now a single Ident("_m") token.
        let is_underscore_prefixed =
            self.at(Token::Ident) && self.current_text().is_some_and(|t| t.starts_with('_'));
        let is_underscore_space_ident =
            self.at(Token::Underscore) && self.peek() == Some(Token::Ident);

        if is_underscore_prefixed || is_underscore_space_ident {
            self.start_node(SyntaxKind::OperatorDef);
            if is_underscore_space_ident {
                self.bump_skip_trivia(); // _
            }
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
            if self.at(Token::Instance) {
                self.parse_instance_expr();
            } else {
                self.parse_expr();
            }

            self.finish_node();
        } else {
            // Normal identifier - use standard operator definition parser
            self.parse_operator_def();
        }
    }

    /// Parse function definition parameters: [x \in S, y \in T]
    fn parse_func_def_params(&mut self) {
        self.start_node(SyntaxKind::ArgList);
        self.bump_skip_trivia(); // [

        if !self.at(Token::RBracket) {
            self.parse_bound_var();
            while self.at(Token::Comma) {
                self.bump_skip_trivia();
                self.parse_bound_var();
            }
        }

        self.expect(Token::RBracket);
        self.finish_node();
    }

    /// Parse parameter list: (x, y, Op(_, _))
    pub(super) fn parse_param_list(&mut self) {
        self.start_node(SyntaxKind::ArgList);
        self.bump_skip_trivia(); // (

        if !self.at(Token::RParen) {
            self.parse_param();
            while self.at(Token::Comma) {
                self.bump_skip_trivia();
                self.parse_param();
            }
        }

        self.expect(Token::RParen);
        self.finish_node();
    }

    /// Parse a single parameter (possibly higher-order)
    /// Handles:
    /// - Simple: x
    /// - Underscore-prefixed: _n (for DEFINE P(_n) == ...)
    /// - Higher-order: F(_) or F(_, _)
    /// - Infix operator param: _+_ (for LET IsAbelianGroup(G, Id, _+_) == ...)
    fn parse_param(&mut self) {
        self.start_node(SyntaxKind::OperatorParam);

        if self.at(Token::Underscore) {
            self.bump_skip_trivia(); // first _
            if let Some(next) = self.current() {
                if next == Token::Ident {
                    // Underscore-prefixed identifier: _n
                    self.bump_skip_trivia();
                } else if is_infix_op_symbol(next) {
                    // Could be _op_ style infix operator parameter
                    self.bump_skip_trivia(); // operator
                    if self.at(Token::Underscore) {
                        self.bump_skip_trivia(); // second _
                    }
                }
                // Otherwise just a bare underscore placeholder
            }
        } else if self.at(Token::Ident) {
            self.bump_skip_trivia();
            // Check for arity
            if self.at(Token::LParen) {
                self.bump_skip_trivia();
                while self.at(Token::Underscore) || self.at(Token::Comma) {
                    self.bump_skip_trivia();
                }
                self.expect(Token::RParen);
            }
        }

        self.finish_node();
    }
}
