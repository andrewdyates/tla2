// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![deny(clippy::unwrap_used)]

//! SMT-LIB parser
//!
//! Parses SMT-LIB 2.6 input into commands.

use crate::command::Command;
use crate::sexp::{ParseError, SExprParser};

/// SMT-LIB parser
pub(crate) struct Parser<'a> {
    sexp_parser: SExprParser<'a>,
}

impl<'a> Parser<'a> {
    /// Create a new parser for the given input
    #[must_use]
    pub(crate) fn new(input: &'a str) -> Self {
        Parser {
            sexp_parser: SExprParser::new(input),
        }
    }

    /// Parse the next command from the input
    ///
    /// Returns `None` when the input is exhausted.
    ///
    /// # Errors
    ///
    /// Returns an error if the input is malformed SMT-LIB.
    pub(crate) fn parse_command(&mut self) -> Result<Option<Command>, ParseError> {
        if self.sexp_parser.is_eof() {
            return Ok(None);
        }

        let sexp = self.sexp_parser.parse_sexp()?;
        let cmd = Command::from_sexp(&sexp)?;
        Ok(Some(cmd))
    }

    /// Parse all commands from the input
    ///
    /// # Errors
    ///
    /// Returns an error if the input is malformed SMT-LIB.
    pub(crate) fn parse_all(&mut self) -> Result<Vec<Command>, ParseError> {
        let mut commands = Vec::new();
        while let Some(cmd) = self.parse_command()? {
            commands.push(cmd);
        }
        Ok(commands)
    }
}

/// Parse SMT-LIB input into a list of commands
///
/// # Errors
///
/// Returns an error if the input is malformed SMT-LIB.
pub fn parse(input: &str) -> Result<Vec<Command>, ParseError> {
    let mut parser = Parser::new(input);
    parser.parse_all()
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::panic)]
#[path = "parser_tests.rs"]
mod tests;
