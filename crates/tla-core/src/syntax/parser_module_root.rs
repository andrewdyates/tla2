// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Root/module parsing routines for the TLA+ parser.
//!
//! Extracted from parser.rs to keep parser files under size gates.

use super::parser_tables::{is_prefix_op_symbol, is_stdlib_operator_name};
use super::Parser;
use crate::syntax::kinds::SyntaxKind;
use crate::syntax::lexer::Token;

impl Parser {
    pub(super) fn parse_root(&mut self) {
        self.start_node(SyntaxKind::Root);
        self.skip_trivia();

        // Parse module(s), skipping any text before/after/between modules.
        // Many real-world .tla files contain:
        // - Documentation or README text before the module header
        // - CONFIG file content (not a TLA+ module)
        // - Trailing notes, shell commands after the module end
        // SANY effectively ignores non-module content, so we do the same.
        while !self.at_eof() {
            if self.at(Token::ModuleStart) {
                // Only treat dashes as a module header if followed by `MODULE`.
                let mut nth = 1;
                while self.peek_nth(nth) == Some(Token::ModuleStart) {
                    nth += 1;
                }
                if self.peek_nth(nth) == Some(Token::Module) {
                    self.parse_module();
                } else {
                    // Dashes not followed by MODULE - skip them
                    self.bump_skip_trivia();
                }
            } else {
                self.bump_skip_trivia();
            }
        }

        self.finish_node();
    }

    /// Parse a module: ---- MODULE Name ---- ... ====
    fn parse_module(&mut self) {
        self.start_node(SyntaxKind::Module);

        // ---- MODULE
        self.expect(Token::ModuleStart);
        while self.at(Token::ModuleStart) {
            self.bump_skip_trivia(); // Allow multiple ----
        }
        self.expect(Token::Module);

        // Module name (can start with number like 2PCwithBTM)
        self.parse_module_name();

        // Trailing dashes after module name.
        // Consume ModuleStart tokens that are part of the header line, but stop
        // if the next ModuleStart is followed by MODULE (that starts a submodule).
        while self.at(Token::ModuleStart) {
            // Lookahead: if this ModuleStart is followed by MODULE, it's a submodule
            // header, not trailing dashes of the current header.
            if self.peek() == Some(Token::Module) {
                break;
            }
            self.bump_skip_trivia();
        }

        // EXTENDS clause (optional)
        if self.at(Token::Extends) {
            self.parse_extends();
        }

        // Module body
        while !self.at_eof() && !self.at(Token::ModuleEnd) {
            self.parse_unit();
        }

        // ====
        if self.at(Token::ModuleEnd) {
            self.bump_skip_trivia();
            while self.at(Token::ModuleEnd) {
                self.bump_skip_trivia(); // Allow multiple ====
            }
        } else {
            self.error("expected module end (====)".to_string());
        }

        self.finish_node();
    }

    /// Parse EXTENDS M1, M2, ...
    fn parse_extends(&mut self) {
        self.start_node(SyntaxKind::ExtendsClause);
        self.bump_skip_trivia(); // EXTENDS

        // Parse comma-separated module names
        if self.at(Token::Ident) {
            self.bump_skip_trivia();
            while self.at(Token::Comma) {
                self.bump_skip_trivia();
                if self.at(Token::Ident) {
                    self.bump_skip_trivia();
                } else {
                    self.error("expected module name after comma".to_string());
                    break;
                }
            }
        }

        self.finish_node();
    }

    /// Parse a submodule definition (embedded module within a module)
    /// Syntax: ---- MODULE Name ---- ... ====
    fn parse_submodule(&mut self) {
        self.start_node(SyntaxKind::Module);

        // Parse module start delimiter (----)
        self.bump_skip_trivia(); // First dash set

        // MODULE keyword
        if self.at(Token::Module) {
            self.bump_skip_trivia();
        }

        // Module name (can start with number like 2PCwithBTM)
        if self.at(Token::Ident) || self.at(Token::Number) {
            self.parse_module_name_optional();
        }

        // Consume trailing dashes after module name, but stop if the next
        // ModuleStart is followed by MODULE (that starts another submodule).
        while self.at(Token::ModuleStart) {
            if self.peek() == Some(Token::Module) {
                break;
            }
            self.bump_skip_trivia();
        }
        // Also consume ModuleEnd (====) if used as a header separator
        // (unusual but tolerated by SANY)
        while self.at(Token::ModuleEnd) {
            self.bump_skip_trivia();
        }

        // Parse EXTENDS clause if present
        if self.at(Token::Extends) {
            self.parse_extends();
        }

        // Parse module body
        loop {
            self.skip_trivia();
            if self.at_eof() || self.at(Token::ModuleEnd) {
                break;
            }
            // Check for nested submodule end
            if self.at(Token::ModuleEnd) {
                break;
            }
            self.parse_unit();
        }

        // Module end delimiter (====)
        if self.at(Token::ModuleEnd) {
            self.bump_skip_trivia();
        }

        self.finish_node();
    }

    /// Parse a module unit (declaration, definition, etc.)
    fn parse_unit(&mut self) {
        self.skip_trivia();

        if self.at_eof() || self.at(Token::ModuleEnd) {
            return;
        }

        match self.current() {
            Some(Token::ModuleStart) => {
                // Could be separator line or start of submodule
                // Check if MODULE follows (submodule definition)
                // Note: we only look past ONE ModuleStart token because the lexer
                // skips whitespace, so we can't distinguish "same line" from "different line"
                // A submodule has: ---- MODULE Name ----
                // A separator has: ---- (alone on a line)
                let checkpoint = self.pos;
                self.pos += 1; // Skip ONE ModuleStart token
                self.skip_trivia_no_emit(); // Skip any trivia without emitting (lookahead)
                if self.at(Token::Module) {
                    // This is a submodule definition
                    self.pos = checkpoint;
                    self.parse_submodule();
                } else {
                    // Just a separator line - consume only this one ModuleStart
                    self.pos = checkpoint;
                    self.start_node(SyntaxKind::Separator);
                    self.bump(); // Consume the ModuleStart token
                    self.skip_trivia(); // Skip trivia for next parse
                    self.finish_node();
                }
            }
            Some(Token::Variable) => self.parse_variable_decl(),
            Some(Token::Constant) => self.parse_constant_decl(),
            Some(Token::Recursive) => self.parse_recursive_decl(),
            Some(Token::Assume) => self.parse_assume(),
            Some(Token::Theorem)
            | Some(Token::Lemma)
            | Some(Token::Proposition)
            | Some(Token::Corollary) => {
                self.parse_theorem();
            }
            Some(Token::Instance) => self.parse_instance(),
            Some(Token::Local) => {
                // LOCAL Op == ... or LOCAL INSTANCE
                self.bump_skip_trivia();
                match self.current() {
                    Some(Token::Instance) => self.parse_instance(),
                    Some(Token::Ident) => self.parse_operator_def(),
                    _ => {
                        self.error(
                            "expected INSTANCE or operator definition after LOCAL".to_string(),
                        );
                    }
                }
            }
            Some(Token::Use) | Some(Token::Hide) => {
                // Module-level USE/HIDE statement (TLAPS)
                self.parse_module_use();
            }
            Some(Token::Ident) => self.parse_operator_def(),
            // Standard library tokens can be operator names in standard modules (e.g., Seq in Sequences.tla)
            Some(op) if is_stdlib_operator_name(op) => self.parse_stdlib_operator_def(),
            // Prefix operator definitions: -. a == ..., ~ a == ...
            Some(op) if is_prefix_op_symbol(op) => self.parse_prefix_operator_def(),
            _ => {
                // Skip unrecognized tokens
                self.error(format!("unexpected token: {:?}", self.current()));
                self.bump_skip_trivia();
            }
        }
    }

    /// Parse module-level USE/HIDE statement (TLAPS)
    fn parse_module_use(&mut self) {
        self.start_node(SyntaxKind::UseStmt);
        self.bump_skip_trivia(); // USE or HIDE
        self.parse_proof_hints();
        self.finish_node();
    }

    /// Parse VARIABLE x, y, z
    fn parse_variable_decl(&mut self) {
        self.start_node(SyntaxKind::VariableDecl);
        self.bump_skip_trivia(); // VARIABLE(S)

        self.parse_name_list();

        self.finish_node();
    }

    /// Parse CONSTANT c1, c2(_, _)
    fn parse_constant_decl(&mut self) {
        self.start_node(SyntaxKind::ConstantDecl);
        self.bump_skip_trivia(); // CONSTANT(S)

        // Parse comma-separated constant declarations
        self.parse_constant_list();

        self.finish_node();
    }

    /// Parse a module name (required), which can start with a number (e.g., 2PCwithBTM)
    pub(super) fn parse_module_name(&mut self) {
        if self.at(Token::Ident) {
            self.bump_skip_trivia();
        } else if self.at(Token::Number) {
            // Module names like "2PCwithBTM" tokenize as Number + Ident
            self.bump_skip_trivia(); // Number
            if self.at(Token::Ident) {
                self.bump_skip_trivia(); // Rest of identifier
            }
        } else {
            self.error("expected module name".to_string());
        }
    }

    /// Parse a module name (optional), which can start with a number
    fn parse_module_name_optional(&mut self) {
        if self.at(Token::Ident) {
            self.bump_skip_trivia();
        } else if self.at(Token::Number) {
            // Module names like "2PCwithBTM" tokenize as Number + Ident
            self.bump_skip_trivia(); // Number
            if self.at(Token::Ident) {
                self.bump_skip_trivia(); // Rest of identifier
            }
        }
        // If neither, just return without error
    }

    /// Parse a list of names: x, y, z
    fn parse_name_list(&mut self) {
        self.start_node(SyntaxKind::NameList);

        if self.at(Token::Ident) {
            self.bump_skip_trivia();
            while self.at(Token::Comma) {
                self.bump_skip_trivia();
                if self.at(Token::Ident) {
                    self.bump_skip_trivia();
                } else {
                    self.error("expected identifier after comma".to_string());
                    break;
                }
            }
        }

        self.finish_node();
    }

    /// Parse constant declarations: c1, c2(_, _)
    fn parse_constant_list(&mut self) {
        if self.at(Token::Ident) {
            self.parse_constant_item();
            while self.at(Token::Comma) {
                self.bump_skip_trivia();
                self.parse_constant_item();
            }
        }
    }

    /// Parse a single constant declaration (possibly with arity)
    fn parse_constant_item(&mut self) {
        if self.at(Token::Ident) {
            self.bump_skip_trivia();
            // Check for arity: C(_, _)
            if self.at(Token::LParen) {
                self.bump_skip_trivia();
                while self.at(Token::Underscore) || self.at(Token::Comma) {
                    self.bump_skip_trivia();
                }
                self.expect(Token::RParen);
            }
        }
    }
}
