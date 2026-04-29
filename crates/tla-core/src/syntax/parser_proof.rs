// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Proof parsing methods for the TLA+ parser.
//!
//! This module contains proof-related parser methods, extracted from parser.rs
//! for code-quality gate compliance (#1261). All methods are on the `Parser`
//! struct via a separate `impl` block.

use crate::syntax::kinds::SyntaxKind;
use crate::syntax::lexer::Token;

use super::parser_tables::{can_start_expr, is_infix_op_symbol, is_proof_step_body_start};

use super::Parser;

impl Parser {
    /// Parse a proof
    pub(super) fn parse_proof(&mut self) {
        self.start_node(SyntaxKind::Proof);

        match self.current() {
            Some(Token::Obvious) => {
                self.bump_skip_trivia();
            }
            Some(Token::Omitted) => {
                self.bump_skip_trivia();
            }
            Some(Token::By) => {
                self.parse_by_clause();
            }
            Some(Token::Proof) => {
                self.bump_skip_trivia();
                // After PROOF, we can have:
                // - BY clause (leaf proof): PROOF BY ...
                // - OBVIOUS (leaf proof): PROOF OBVIOUS
                // - OMITTED (leaf proof): PROOF OMITTED
                // - Step labels (structured proof): PROOF <1>...
                match self.current() {
                    Some(Token::By) => self.parse_by_clause(),
                    Some(Token::Obvious) => {
                        self.bump_skip_trivia();
                    }
                    Some(Token::Omitted) => {
                        self.bump_skip_trivia();
                    }
                    _ => self.parse_proof_steps(),
                }
            }
            Some(Token::Lt) => {
                // Proof starts directly with step labels (no PROOF keyword)
                self.parse_proof_steps();
            }
            _ => {}
        }

        self.finish_node();
    }

    /// Parse proof steps and QED
    fn parse_proof_steps(&mut self) {
        // Parse all step labels
        self.skip_trivia();
        while self.at(Token::Lt) {
            self.parse_proof_step();
            self.skip_trivia();
        }
        // QED at the end
        if self.at(Token::Qed) {
            self.bump_skip_trivia();
            if self.at(Token::By)
                || self.at(Token::Obvious)
                || self.at(Token::Omitted)
                || self.at(Token::Lt)
            {
                self.parse_proof();
            }
        }
    }

    fn at_prove_kw(&self) -> bool {
        self.current() == Some(Token::Ident) && self.current_text() == Some("PROVE")
    }

    /// Check if current position is a proof-local definition: P(x) == ...
    /// Looks for pattern: Ident (params) == OR Ident ==
    fn is_proof_local_definition(&self) -> bool {
        if self.current() != Some(Token::Ident) {
            return false;
        }
        let mut pos = self.pos + 1;

        // Skip trivia
        while pos < self.tokens.len() && self.tokens[pos].kind.is_trivia() {
            pos += 1;
        }

        // Check for == directly (simple definition: P == ...)
        if pos < self.tokens.len() && self.tokens[pos].kind == Token::DefEq {
            return true;
        }

        // Check for (params) ==
        if pos < self.tokens.len() && self.tokens[pos].kind == Token::LParen {
            pos += 1;
            let mut depth = 1;
            while pos < self.tokens.len() && depth > 0 {
                match self.tokens[pos].kind {
                    Token::LParen => depth += 1,
                    Token::RParen => depth -= 1,
                    _ => {}
                }
                pos += 1;
            }
            // Skip trivia after )
            while pos < self.tokens.len() && self.tokens[pos].kind.is_trivia() {
                pos += 1;
            }
            // Check for ==
            if pos < self.tokens.len() && self.tokens[pos].kind == Token::DefEq {
                return true;
            }
        }

        false
    }

    /// Parse BY clause
    fn parse_by_clause(&mut self) {
        self.start_node(SyntaxKind::ByClause);
        self.bump_skip_trivia(); // BY

        // Parse hints
        self.parse_proof_hints();

        self.finish_node();
    }

    /// Parse proof hints
    pub(super) fn parse_proof_hints(&mut self) {
        // Parse proof hints (facts/lemmas, step references, DEF/DEFS, etc.).
        // Notes:
        // - DEF/DEFS can appear without comma separator: `BY PTL DEF Spec`
        // - Hints can span multiple lines until the next proof step label.
        loop {
            self.skip_trivia();

            if self.at(Token::Only) {
                // `BY ONLY ...` modifier (no comma required after ONLY)
                self.bump_skip_trivia();
                continue;
            }

            if self.at(Token::Lt) && !self.is_step_label_start() {
                // Step reference: <n>label (e.g., <1>a, <2>2) - NOT a step label start.
                self.parse_step_ref();
            } else if self.at(Token::Defs) || self.at(Token::Def) {
                self.parse_def_clause();
            } else {
                let Some(token) = self.current() else { break };
                if !can_start_expr(token) {
                    break;
                }
                self.parse_expr();
            }

            self.skip_trivia();
            if self.at(Token::Comma) {
                self.bump_skip_trivia();
                continue;
            }
            if self.at(Token::Defs) || self.at(Token::Def) {
                // DEF/DEFS can follow without comma
                continue;
            }
            break;
        }
    }

    fn parse_def_clause(&mut self) {
        self.bump_skip_trivia(); // DEF/DEFS

        // DEF/DEFS can list identifiers, operator symbols, and module refs (M!Op).
        while self.parse_def_name() {
            if self.at(Token::Comma) {
                self.bump_skip_trivia();
            } else {
                break;
            }
        }
    }

    fn parse_def_name(&mut self) -> bool {
        match self.current() {
            Some(Token::Underscore) if self.peek() == Some(Token::Ident) => {
                self.bump_skip_trivia(); // _
                self.bump_skip_trivia(); // ident
            }
            Some(Token::Ident) => {
                self.bump_skip_trivia();
                // Module reference in DEF list: M!Op
                if self.at(Token::Bang) {
                    self.bump_skip_trivia(); // !
                    if self.at(Token::Ident) {
                        self.bump_skip_trivia();
                    }
                }
            }
            Some(op) if is_infix_op_symbol(op) => {
                self.bump_skip_trivia();
            }
            Some(
                Token::Union
                | Token::Intersect
                | Token::SetMinus
                | Token::Times
                | Token::In_
                | Token::NotIn
                | Token::Subseteq
                | Token::Subset
                | Token::Supseteq
                | Token::Supset
                | Token::And
                | Token::Or
                | Token::Not
                | Token::Implies
                | Token::Equiv,
            ) => {
                self.bump_skip_trivia();
            }
            _ => {
                return false;
            }
        }

        true
    }

    /// Parse a step reference: <n>label (used in BY clauses)
    fn parse_step_ref(&mut self) {
        self.start_node(SyntaxKind::StepLabel);
        self.bump_skip_trivia(); // <
        if self.at(Token::Number) {
            self.bump_skip_trivia();
        }
        if self.at(Token::Gt) {
            self.bump_skip_trivia();
        }
        // Optional label (letter or number after >)
        if self.at(Token::Ident) || self.at(Token::Number) {
            self.bump_skip_trivia();
        }
        self.finish_node();
    }

    /// Parse a proof step: <n>label. assertion
    fn parse_proof_step(&mut self) {
        self.start_node(SyntaxKind::ProofStep);

        // Step label <n>
        if self.at(Token::Lt) {
            self.start_node(SyntaxKind::StepLabel);
            self.bump_skip_trivia(); // <
            if self.at(Token::Number) {
                self.bump_skip_trivia();
            }
            self.expect(Token::Gt);
            // Optional label name or number (e.g., <1>a or <1>1).
            // Handle cases:
            // - <1>a. or <1>1. - labeled step with explicit dot
            // - <1>a TAKE ... - labeled step without dot
            // - <1>1 \A z ... - numbered label followed by expression
            // - <1> P(b) == ... - proof-local definition (NOT a label)
            // - <1> P == ... - simple definition (NOT a label)
            if self.at(Token::Ident) || self.at(Token::Number) {
                let after = self.peek();
                // If current is Ident (not Number), we need to be careful:
                // - <1> P(b) == ... - the P is NOT a label (it's a definition name)
                // - <1>a TAKE ... - the a IS a label
                // We don't consume Ident if followed by ( or ==, which indicates a definition.
                let is_ident = self.at(Token::Ident);
                let is_definition_start =
                    is_ident && (after == Some(Token::LParen) || after == Some(Token::DefEq));

                let is_label = !is_definition_start
                    && (after == Some(Token::Dot) || after.is_some_and(is_proof_step_body_start));
                if is_label {
                    self.bump_skip_trivia();
                }
            }
            // Dot is optional in many real-world proofs (e.g., `<1> USE ...`, `<1>1 ...`).
            if self.at(Token::Dot) {
                self.bump_skip_trivia();
            }
            self.finish_node();
        }

        // Step kind
        match self.current() {
            Some(Token::Suffices) => {
                self.bump_skip_trivia();
                if self.at(Token::Assume) {
                    self.parse_assume_prove_stmt();
                } else {
                    self.parse_expr();
                }
            }
            Some(Token::Have) => {
                self.bump_skip_trivia();
                self.parse_expr();
            }
            Some(Token::Take) => {
                self.bump_skip_trivia();
                self.parse_bound_var_list();
            }
            Some(Token::Witness) => {
                self.bump_skip_trivia();
                self.parse_expr();
                while self.at(Token::Comma) {
                    self.bump_skip_trivia();
                    self.parse_expr();
                }
            }
            Some(Token::Pick) => {
                self.bump_skip_trivia();
                self.parse_bound_var_list();
                self.expect(Token::Colon);
                self.parse_expr();
            }
            Some(Token::Use) | Some(Token::Hide) => {
                self.bump_skip_trivia();
                self.parse_proof_hints();
            }
            Some(Token::Assume) => {
                self.bump_skip_trivia(); // ASSUME
                self.parse_assume_prove_stmt();
            }
            Some(Token::Case) => {
                // Proof CASE step: `CASE expr` (not CASE expression).
                self.bump_skip_trivia(); // CASE
                self.parse_expr();
            }
            Some(Token::Define) => {
                self.bump_skip_trivia();
                // DEFINE can have multiple definitions, including underscore-prefixed names
                while self.at(Token::Ident)
                    || (self.at(Token::Underscore) && self.peek() == Some(Token::Ident))
                {
                    self.parse_define_operator();
                }
            }
            Some(Token::Qed) => {
                self.bump_skip_trivia();
            }
            Some(Token::Ident) if self.is_proof_local_definition() => {
                // Proof-local definition without DEFINE keyword: <1> P(x) == expr
                self.parse_define_operator();
            }
            _ => {
                // Regular assertion
                self.parse_expr();
            }
        }

        // Optional proof for this step
        if self.at(Token::Proof)
            || self.at(Token::By)
            || self.at(Token::Obvious)
            || self.at(Token::Omitted)
        {
            self.parse_proof();
        }

        self.finish_node();
    }

    pub(super) fn parse_assume_prove_stmt(&mut self) {
        // Optional leading ASSUME keyword (present in TLAPS-style theorem statements and SUFFICES).
        if self.at(Token::Assume) {
            self.bump_skip_trivia();
        }

        // Optional NEW declarations immediately after ASSUME.
        if self.at(Token::New) {
            self.parse_new_decl_list();
            if self.at(Token::Comma) {
                self.bump_skip_trivia();
            }
        }

        // Parse assumptions until PROVE (or until we hit proof start / next step label).
        // Parse assumptions until PROVE (or until we hit proof start / next step label).
        while !self.at_eof()
            && !self.at_prove_kw()
            && !self.at(Token::By)
            && !self.at(Token::Obvious)
            && !self.at(Token::Omitted)
            && !self.at(Token::Proof)
            && !(self.at(Token::Lt) && self.is_step_label_start())
        {
            if self.at(Token::New) {
                self.parse_new_decl_list();
            } else if self.at(Token::Assume) {
                // Nested ASSUME/PROVE block (e.g., RecursiveFcnOfNat in NaturalsInduction.tla).
                // The inner ASSUME...PROVE constitutes a single assumption in the outer block.
                // Without this, the parser consumes just the ASSUME keyword as an unknown token,
                // exits the assumption loop, and leaves the remaining theorem body as unparsed
                // tokens that get interpreted as module-level OperatorDef nodes (#2900).
                self.parse_assume_prove_stmt();
            } else if let Some(token) = self.current() {
                if can_start_expr(token) {
                    self.parse_expr();
                } else {
                    // Consume unknown tokens without emitting errors (proof language is permissive).
                    self.bump_skip_trivia();
                }
            } else {
                break;
            }

            if self.at(Token::Comma) {
                self.bump_skip_trivia();
            } else {
                break;
            }
        }

        if self.at_prove_kw() {
            self.bump_skip_trivia(); // PROVE (lexed as Ident)
            if let Some(token) = self.current() {
                if can_start_expr(token) {
                    self.parse_expr();
                }
            }
        }
    }

    fn parse_new_decl_list(&mut self) {
        self.bump_skip_trivia(); // NEW

        // TLAPS frequently writes `NEW x` or `NEW x \\in S` and repeats NEW per declaration.
        // Avoid being overly greedy here: subsequent comma-separated items are often assumptions,
        // e.g., `ASSUME NEW i \\in S, i' = ...`.
        self.parse_new_decl();
    }

    fn parse_new_decl(&mut self) {
        if self.at(Token::Ident) {
            self.bump_skip_trivia();
            // Check for higher-order operator syntax: op(_,_) or op(_)
            if self.at(Token::LParen) {
                self.parse_operator_arity_spec();
            } else if self.at(Token::In_) {
                self.bump_skip_trivia();
                self.parse_expr();
            }
        }
    }

    /// Parse operator arity specification: (_) or (_,_) or (_,_,_) etc.
    fn parse_operator_arity_spec(&mut self) {
        self.bump_skip_trivia(); // (
                                 // Parse underscore-separated placeholders
        while !self.at(Token::RParen) && !self.at_eof() {
            if self.at(Token::Underscore) {
                self.bump_skip_trivia();
            }
            if self.at(Token::Comma) {
                self.bump_skip_trivia();
            } else {
                break;
            }
        }
        if self.at(Token::RParen) {
            self.bump_skip_trivia();
        }
    }
}
