// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Parser for SMT-LIB invariant definitions.
//!
//! Expression parsing (recursive-descent for SMT-LIB expressions) is in
//! `parse_expr`.

mod parse_expr;

use crate::error::ChcError;
use crate::{ChcExpr, ChcProblem, ChcResult, ChcSort, ChcVar, PredicateId};
use rustc_hash::FxHashMap;

use super::model::{InvariantModel, PredicateInterpretation};

/// Parser for SMT-LIB invariant definitions
pub(crate) struct InvariantParser<'a> {
    input: &'a str,
    pos: usize,
    /// Map from predicate name to predicate info
    pred_map: FxHashMap<String, (PredicateId, Vec<ChcSort>)>,
}

impl<'a> InvariantParser<'a> {
    pub(crate) fn new(input: &'a str, problem: &ChcProblem) -> Self {
        let mut pred_map = FxHashMap::default();
        for pred in problem.predicates() {
            pred_map.insert(pred.name.clone(), (pred.id, pred.arg_sorts.clone()));
        }
        Self {
            input,
            pos: 0,
            pred_map,
        }
    }

    pub(crate) fn parse(&mut self) -> ChcResult<InvariantModel> {
        let mut model = InvariantModel::new();

        while self.pos < self.input.len() {
            self.skip_whitespace_and_comments();
            if self.pos >= self.input.len() {
                break;
            }

            // Look for (define-fun ...) or ( (define-fun ...) ) (Spacer format)
            if self.peek_char() == Some('(') {
                self.pos += 1;
                self.skip_whitespace_and_comments();

                // Check for Spacer format wrapper
                if self.peek_char() == Some('(') {
                    // Spacer format: ( (define-fun ...) (define-fun ...) )
                    while self.peek_char() == Some('(') {
                        self.pos += 1;
                        self.skip_whitespace_and_comments();

                        let cmd = self.parse_symbol()?;
                        if cmd == "define-fun" {
                            self.parse_define_fun(&mut model)?;
                        } else {
                            // Skip unknown command
                            self.skip_sexp()?;
                        }
                        self.skip_whitespace_and_comments();
                    }
                    // Skip closing paren of wrapper
                    if self.peek_char() == Some(')') {
                        self.pos += 1;
                    }
                } else {
                    let cmd = self.parse_symbol()?;
                    if cmd == "define-fun" {
                        self.parse_define_fun(&mut model)?;
                    } else {
                        // Skip unknown command
                        self.skip_sexp()?;
                    }
                }
            } else {
                // Skip any other character
                self.pos += 1;
            }
        }

        Ok(model)
    }

    fn parse_define_fun(&mut self, model: &mut InvariantModel) -> ChcResult<()> {
        self.skip_whitespace_and_comments();

        // Parse predicate name
        let pred_name = self.parse_symbol()?;
        self.skip_whitespace_and_comments();

        // Check if this predicate exists in the problem
        let (pred_id, expected_sorts) = match self.pred_map.get(&pred_name) {
            Some((id, sorts)) => (*id, sorts.clone()),
            None => {
                // Skip this definition - predicate not in problem
                self.skip_sexp()?; // params
                self.skip_sexp()?; // return type
                self.skip_sexp()?; // body
                self.expect_char(')')?;
                return Ok(());
            }
        };

        // Parse parameters: ((x Int) (y Bool) ...)
        self.expect_char('(')?;
        let mut vars = Vec::new();
        loop {
            self.skip_whitespace_and_comments();
            if self.peek_char() == Some(')') {
                break;
            }
            self.expect_char('(')?;
            self.skip_whitespace_and_comments();
            let var_name = self.parse_symbol()?;
            self.skip_whitespace_and_comments();
            let sort = self.parse_sort()?;
            self.skip_whitespace_and_comments();
            self.expect_char(')')?;
            vars.push(ChcVar::new(var_name, sort));
        }
        self.expect_char(')')?;

        // Verify parameter count matches
        if vars.len() != expected_sorts.len() {
            return Err(ChcError::Parse(format!(
                "Parameter count mismatch for {}: expected {}, got {}",
                pred_name,
                expected_sorts.len(),
                vars.len()
            )));
        }

        self.skip_whitespace_and_comments();

        // Parse return type (should be Bool)
        let ret_sort = self.parse_sort()?;
        if ret_sort != ChcSort::Bool {
            return Err(ChcError::Parse(format!(
                "Invariant {pred_name} must return Bool, got {ret_sort:?}"
            )));
        }

        self.skip_whitespace_and_comments();

        // Parse body expression
        let body = self.parse_expr(&vars)?;

        self.skip_whitespace_and_comments();
        self.expect_char(')')?;

        // Create interpretation
        let interp = PredicateInterpretation::new(vars, body);
        model.set(pred_id, interp);

        Ok(())
    }

    fn parse_expr_list(&mut self, vars: &[ChcVar]) -> ChcResult<Vec<ChcExpr>> {
        let mut args = Vec::new();
        loop {
            self.skip_whitespace_and_comments();
            if self.peek_char() == Some(')') {
                break;
            }
            args.push(self.parse_expr(vars)?);
        }
        Ok(args)
    }

    fn parse_sort(&mut self) -> ChcResult<ChcSort> {
        self.skip_whitespace_and_comments();

        if self.peek_char() == Some('(') {
            // Parametric sort like (Array Int Int) or indexed sort like (_ BitVec 32)
            self.pos += 1;
            self.skip_whitespace_and_comments();

            let head = self.parse_symbol()?;
            self.skip_whitespace_and_comments();

            if head == "_" {
                let sort_name = self.parse_symbol()?;
                self.skip_whitespace_and_comments();

                match sort_name.as_str() {
                    "BitVec" => {
                        let width = self.parse_numeral()? as u32;
                        self.skip_whitespace_and_comments();
                        self.expect_char(')')?;
                        Ok(ChcSort::BitVec(width))
                    }
                    _ => Err(ChcError::Parse(format!(
                        "Unknown indexed sort: {sort_name}"
                    ))),
                }
            } else if head == "Array" {
                let key_sort = self.parse_sort()?;
                self.skip_whitespace_and_comments();
                let val_sort = self.parse_sort()?;
                self.skip_whitespace_and_comments();
                self.expect_char(')')?;
                Ok(ChcSort::Array(Box::new(key_sort), Box::new(val_sort)))
            } else {
                // Z4 doesn't currently represent parametric sort applications. Consume the
                // arguments to keep parsing consistent and treat it as an uninterpreted sort.
                while self.peek_char() != Some(')') {
                    self.skip_sexp()?;
                    self.skip_whitespace_and_comments();
                }
                self.expect_char(')')?;
                Ok(ChcSort::Uninterpreted(head))
            }
        } else {
            let name = self.parse_symbol()?;
            match name.as_str() {
                "Bool" => Ok(ChcSort::Bool),
                "Int" => Ok(ChcSort::Int),
                "Real" => Ok(ChcSort::Real),
                _ => Ok(ChcSort::Uninterpreted(name)),
            }
        }
    }

    fn parse_symbol(&mut self) -> ChcResult<String> {
        self.skip_whitespace_and_comments();

        let start = self.pos;

        // Check for quoted symbol
        if self.peek_char() == Some('|') {
            self.pos += 1;
            let content_start = self.pos;
            while self.pos < self.input.len() && self.current_char() != Some('|') {
                self.pos += 1;
            }
            let symbol = self.input[content_start..self.pos].to_string();
            if self.current_char() == Some('|') {
                self.pos += 1;
            }
            return Ok(symbol);
        }

        // Regular symbol
        while self.pos < self.input.len() {
            match self.current_char() {
                Some(c) if is_symbol_char(c) => self.pos += 1,
                _ => break,
            }
        }

        if start == self.pos {
            return Err(ChcError::Parse("Expected symbol".into()));
        }

        Ok(self.input[start..self.pos].to_string())
    }

    fn parse_numeral(&mut self) -> ChcResult<i64> {
        self.skip_whitespace_and_comments();

        let start = self.pos;

        while self.pos < self.input.len() {
            match self.current_char() {
                Some(c) if c.is_ascii_digit() => self.pos += 1,
                _ => break,
            }
        }

        if start == self.pos {
            return Err(ChcError::Parse("Expected numeral".into()));
        }

        self.input[start..self.pos]
            .parse()
            .map_err(|_| ChcError::Parse("Invalid numeral".into()))
    }

    fn skip_whitespace_and_comments(&mut self) {
        while self.pos < self.input.len() {
            match self.current_char() {
                Some(c) if c.is_whitespace() => self.pos += 1,
                Some(';') => {
                    // Skip until end of line
                    while self.pos < self.input.len() && self.current_char() != Some('\n') {
                        self.pos += 1;
                    }
                }
                _ => break,
            }
        }
    }

    fn skip_sexp(&mut self) -> ChcResult<()> {
        self.skip_whitespace_and_comments();
        if self.peek_char() == Some('(') {
            let mut depth = 1;
            self.pos += 1;
            while depth > 0 && self.pos < self.input.len() {
                match self.current_char() {
                    Some('(') => depth += 1,
                    Some(')') => depth -= 1,
                    _ => {}
                }
                self.pos += 1;
            }
        } else {
            // Skip single token
            while self.pos < self.input.len() {
                match self.current_char() {
                    Some(c) if c.is_whitespace() || c == ')' => break,
                    _ => self.pos += 1,
                }
            }
        }
        Ok(())
    }

    fn expect_char(&mut self, expected: char) -> ChcResult<()> {
        self.skip_whitespace_and_comments();
        match self.current_char() {
            Some(c) if c == expected => {
                self.pos += 1;
                Ok(())
            }
            Some(c) => Err(ChcError::Parse(format!(
                "Expected '{expected}', found '{c}'"
            ))),
            None => Err(ChcError::Parse(format!(
                "Expected '{expected}', found end of input"
            ))),
        }
    }

    fn current_char(&self) -> Option<char> {
        self.input[self.pos..].chars().next()
    }

    fn peek_char(&self) -> Option<char> {
        self.current_char()
    }
}

/// Check if a character is valid in a symbol
fn is_symbol_char(c: char) -> bool {
    c.is_alphanumeric()
        || matches!(
            c,
            '_' | '-'
                | '+'
                | '*'
                | '/'
                | '.'
                | '!'
                | '@'
                | '#'
                | '$'
                | '%'
                | '^'
                | '&'
                | '<'
                | '>'
                | '='
                | '?'
                | '~'
                | '\''
        )
}

#[cfg(test)]
mod tests;
