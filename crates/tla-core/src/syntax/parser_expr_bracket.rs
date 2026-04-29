// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Bracket expression parsing routines for the TLA+ parser.
//!
//! Handles `[...]` expressions: function definitions, EXCEPT, function sets,
//! records, and record sets. Extracted from parser_expr.rs to keep parser
//! files under size gates.

use super::parser_tables::is_keyword_as_field_name;
use super::Parser;
use crate::syntax::kinds::SyntaxKind;
use crate::syntax::lexer::Token;

impl Parser {
    /// Parse [x \in S |-> e] or [f EXCEPT ![a] = b] or [S -> T] or [a |-> 1, b |-> 2] or [a : S, b : T]
    pub(super) fn parse_bracket_expr(&mut self) {
        self.bump_skip_trivia(); // [

        if self.at(Token::RBracket) {
            // Empty - error
            self.start_node(SyntaxKind::Error);
            self.bump_skip_trivia();
            self.finish_node();
            return;
        }

        // Try to determine type by looking ahead
        // [x \in S |-> e] - function definition
        // [f EXCEPT ![...] = ...] - except expression
        // [S -> T] - function set
        // [a |-> e, ...] - record
        // [a : S, ...] - record set

        let checkpoint = self.pos;

        // Check for EXCEPT: [expr EXCEPT ...] where expr can be any expression
        // The expression before EXCEPT can be:
        // - Simple identifier: [f EXCEPT ...]
        // - @ token: [@ EXCEPT ...]
        // - Indexed access: [f[x] EXCEPT ...]
        // - Record literal: [[a |-> 1, b |-> 2] EXCEPT ...]
        // - Function literal: [[x \in S |-> e] EXCEPT ...]
        // Scan ahead for EXCEPT at depth 1 (inside outer brackets, not nested)
        {
            let mut depth = 0;
            let mut found_except = false;
            while self.pos < self.tokens.len() {
                match self.current() {
                    Some(Token::LBracket)
                    | Some(Token::LParen)
                    | Some(Token::LBrace)
                    | Some(Token::LAngle) => {
                        depth += 1;
                        self.pos += 1;
                    }
                    Some(Token::RBracket)
                    | Some(Token::RParen)
                    | Some(Token::RBrace)
                    | Some(Token::RAngle) => {
                        if depth == 0 {
                            break; // End of outer bracket
                        }
                        depth -= 1;
                        self.pos += 1;
                    }
                    Some(Token::Except) if depth == 0 => {
                        // Found EXCEPT at the right level
                        found_except = true;
                        break;
                    }
                    None => break,
                    _ => {
                        self.pos += 1;
                    }
                }
                self.skip_trivia_no_emit();
            }
            self.pos = checkpoint;

            if found_except {
                self.parse_except_expr();
                return;
            }
        }

        // Check for underscore-prefixed record field: [_field |-> e]
        // Tokenized as Underscore + Ident + MapsTo
        if self.at(Token::Underscore) {
            self.pos += 1;
            self.skip_trivia_no_emit();
            if self.at(Token::Ident) {
                self.pos += 1;
                self.skip_trivia_no_emit();
                if self.at(Token::MapsTo) {
                    self.pos = checkpoint;
                    self.parse_record();
                    return;
                }
            }
            self.pos = checkpoint;
        }

        // Check for x \in S |-> which is function definition
        // Also handles x,y \in S |-> (multiple bound vars)
        // And <<x, y>> \in S |-> (tuple pattern)
        if self.at(Token::Ident) {
            self.pos += 1;
            self.skip_trivia_no_emit();
            // Skip comma-separated identifiers: x,y,z \in S
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
                // Function definition
                self.pos = checkpoint;
                self.parse_func_def();
                return;
            }
            self.pos = checkpoint;
            // Check for |-> (record) or : (record set) - start over from checkpoint
            self.pos += 1; // skip ident
            self.skip_trivia_no_emit();
            if self.at(Token::MapsTo) {
                self.pos = checkpoint;
                self.parse_record();
                return;
            }
            if self.at(Token::Colon) {
                self.pos = checkpoint;
                self.parse_record_set();
                return;
            }
            self.pos = checkpoint;
        }

        // Check for tuple pattern: [<<x, y>> \in S |-> e]
        if self.at(Token::LAngle) {
            // Skip over the tuple to find \in
            self.pos += 1;
            self.skip_trivia_no_emit();
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
                // Function definition with tuple pattern
                self.pos = checkpoint;
                self.parse_func_def();
                return;
            }
            self.pos = checkpoint;
        }

        // Must be function set [S -> T] or something else
        self.start_node(SyntaxKind::FuncSetExpr);
        self.parse_expr();

        if self.at(Token::Arrow) {
            self.bump_skip_trivia();
            self.parse_expr();
        }

        self.expect(Token::RBracket);
        self.finish_node();
    }

    /// Parse function definition [x \in S |-> e]
    pub(super) fn parse_func_def(&mut self) {
        self.start_node(SyntaxKind::FuncDefExpr);

        self.parse_bound_var_list();

        self.expect(Token::MapsTo);
        self.parse_expr();
        self.expect(Token::RBracket);

        self.finish_node();
    }

    /// Parse [f EXCEPT ![a] = b, ![c] = d] or [@ EXCEPT ![a] = b] or [[rec] EXCEPT ...]
    pub(super) fn parse_except_expr(&mut self) {
        self.start_node(SyntaxKind::ExceptExpr);

        // Parse the expression before EXCEPT
        // This can be any expression: f, @, cache[q], [a |-> 1], [x \in S |-> e], etc.
        self.parse_except_base_expr();

        self.expect(Token::Except);

        // Except specs
        self.parse_except_spec();
        while self.at(Token::Comma) {
            self.bump_skip_trivia();
            self.parse_except_spec();
        }

        self.expect(Token::RBracket);
        self.finish_node();
    }

    /// Parse the base expression in an EXCEPT expression (everything before EXCEPT)
    /// This can be: @, f, f[x], [a |-> 1], [x \in S |-> e], etc.
    pub(super) fn parse_except_base_expr(&mut self) {
        // Handle @ special case
        if self.at(Token::At) {
            self.bump_skip_trivia();
            return;
        }

        // Handle identifier with optional subscripts and field accesses:
        // f, f[x], f[x][y], f.a, f[x].a, f.a[x].b, node[self].insts[s], etc.
        // Each subscript/field access must wrap the preceding expression in the appropriate node.
        if self.at(Token::Ident) {
            let mut current_checkpoint = self.checkpoint();
            self.bump_skip_trivia();
            loop {
                if self.at(Token::LBracket) {
                    // Wrap preceding expression in FuncApplyExpr: f[x]
                    self.start_node_at(current_checkpoint, SyntaxKind::FuncApplyExpr);
                    self.bump_skip_trivia(); // [
                    self.parse_expr();
                    // Handle tuple indexing: f[x,y,z]
                    while self.at(Token::Comma) {
                        self.bump_skip_trivia();
                        self.parse_expr();
                    }
                    self.expect(Token::RBracket);
                    self.finish_node();
                    current_checkpoint = self.checkpoint();
                } else if self.at(Token::Dot) {
                    // Wrap preceding expression in RecordAccessExpr: r.field
                    // TLC/SANY allows keywords as field names (e.g., bar.RECURSIVE)
                    self.start_node_at(current_checkpoint, SyntaxKind::RecordAccessExpr);
                    self.bump_skip_trivia(); // .
                    if self.at(Token::Ident) || self.current().is_some_and(is_keyword_as_field_name)
                    {
                        self.bump_skip_trivia();
                    }
                    self.finish_node();
                    current_checkpoint = self.checkpoint();
                } else {
                    break;
                }
            }
            return;
        }

        // Handle bracket expressions: [a |-> 1] or [x \in S |-> e]
        if self.at(Token::LBracket) {
            // Parse the nested bracket expression
            // We need to consume balanced brackets
            self.bump_skip_trivia(); // [

            // Determine what kind of bracket expression this is
            let checkpoint = self.pos;

            // Check for underscore-prefixed record: _field |->
            if self.at(Token::Underscore) {
                self.pos += 1;
                self.skip_trivia_no_emit();
                if self.at(Token::Ident) {
                    self.pos += 1;
                    self.skip_trivia_no_emit();
                    if self.at(Token::MapsTo) {
                        self.pos = checkpoint;
                        self.start_node(SyntaxKind::RecordExpr);
                        self.parse_record_field();
                        while self.at(Token::Comma) {
                            self.bump_skip_trivia();
                            self.parse_record_field();
                        }
                        self.expect(Token::RBracket);
                        self.finish_node();
                        return;
                    }
                }
                self.pos = checkpoint;
            }

            // Check for record: ident |->
            if self.at(Token::Ident) {
                self.pos += 1;
                self.skip_trivia_no_emit();
                if self.at(Token::MapsTo) {
                    self.pos = checkpoint;
                    self.start_node(SyntaxKind::RecordExpr);
                    self.parse_record_field();
                    while self.at(Token::Comma) {
                        self.bump_skip_trivia();
                        self.parse_record_field();
                    }
                    self.expect(Token::RBracket);
                    self.finish_node();
                    return;
                }
                // Check for function def: ident \in
                if self.at(Token::In_) {
                    self.pos = checkpoint;
                    self.start_node(SyntaxKind::FuncDefExpr);
                    self.parse_bound_var_list();
                    self.expect(Token::MapsTo);
                    self.parse_expr();
                    self.expect(Token::RBracket);
                    self.finish_node();
                    return;
                }
                // Check for record set: ident :
                if self.at(Token::Colon) {
                    self.pos = checkpoint;
                    self.start_node(SyntaxKind::RecordSetExpr);
                    self.parse_record_set_field();
                    while self.at(Token::Comma) {
                        self.bump_skip_trivia();
                        self.parse_record_set_field();
                    }
                    self.expect(Token::RBracket);
                    self.finish_node();
                    return;
                }
            }
            self.pos = checkpoint;

            // Check for tuple pattern in function def: <<x, y>> \in S |-> e
            if self.at(Token::LAngle) {
                // Skip over tuple to find \in
                self.pos += 1;
                self.skip_trivia_no_emit();
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
                    self.pos = checkpoint;
                    self.start_node(SyntaxKind::FuncDefExpr);
                    self.parse_bound_var_list();
                    self.expect(Token::MapsTo);
                    self.parse_expr();
                    self.expect(Token::RBracket);
                    self.finish_node();
                    return;
                }
                self.pos = checkpoint;
            }

            // Default: function set [S -> T] or error
            self.start_node(SyntaxKind::FuncSetExpr);
            self.parse_expr();
            if self.at(Token::Arrow) {
                self.bump_skip_trivia();
                self.parse_expr();
            }
            self.expect(Token::RBracket);
            self.finish_node();
            return;
        }

        // Fallback: parse any expression (should rarely get here)
        self.parse_expr();
    }

    /// Parse ![a][b].c = v or ![a, b] = v (multi-argument function)
    pub(super) fn parse_except_spec(&mut self) {
        self.start_node(SyntaxKind::ExceptSpec);

        self.expect(Token::Bang);

        // Path elements
        while self.at(Token::LBracket) || self.at(Token::Dot) {
            if self.at(Token::LBracket) {
                self.bump_skip_trivia();
                // Parse first index
                self.parse_expr();
                // Handle multi-argument: ![a, b, c] for f[a, b, c]
                while self.at(Token::Comma) {
                    self.bump_skip_trivia();
                    self.parse_expr();
                }
                self.expect(Token::RBracket);
            } else {
                // Field path: !.fieldName
                // TLC/SANY allows keywords as field names (e.g., !.RECURSIVE)
                self.bump_skip_trivia(); // .
                if self.at(Token::Ident) || self.current().is_some_and(is_keyword_as_field_name) {
                    self.bump_skip_trivia();
                }
            }
        }

        // Accept both `=` and `==` in EXCEPT specs.
        // SANY/TLC accepts `==` as the assignment in EXCEPT (e.g., `![e] == v`),
        // even though `=` is the canonical form. Apalache specs use this.
        if self.at(Token::Eq) || self.at(Token::DefEq) {
            self.bump_skip_trivia();
        } else {
            self.error("expected = or == in EXCEPT spec".to_string());
        }
        self.parse_expr();

        self.finish_node();
    }

    /// Parse record [a |-> 1, b |-> 2]
    pub(super) fn parse_record(&mut self) {
        self.start_node(SyntaxKind::RecordExpr);

        self.parse_record_field();
        while self.at(Token::Comma) {
            self.bump_skip_trivia();
            self.parse_record_field();
        }

        self.expect(Token::RBracket);
        self.finish_node();
    }

    /// Parse record field: a |-> e or _a |-> e (underscore-prefixed field)
    pub(super) fn parse_record_field(&mut self) {
        self.start_node(SyntaxKind::RecordField);

        // Handle underscore-prefixed field names: _animator |-> e
        // Tokenized as Underscore + Ident
        if self.at(Token::Underscore) {
            self.bump_skip_trivia();
        }
        if self.at(Token::Ident) {
            self.bump_skip_trivia();
        }
        self.expect(Token::MapsTo);
        self.parse_expr();

        self.finish_node();
    }

    /// Parse record set [a : S, b : T]
    pub(super) fn parse_record_set(&mut self) {
        self.start_node(SyntaxKind::RecordSetExpr);

        self.parse_record_set_field();
        while self.at(Token::Comma) {
            self.bump_skip_trivia();
            self.parse_record_set_field();
        }

        self.expect(Token::RBracket);
        self.finish_node();
    }

    /// Parse record set field: a : S
    pub(super) fn parse_record_set_field(&mut self) {
        self.start_node(SyntaxKind::RecordField);

        if self.at(Token::Ident) {
            self.bump_skip_trivia();
        }
        self.expect(Token::Colon);
        self.parse_expr();

        self.finish_node();
    }
}
