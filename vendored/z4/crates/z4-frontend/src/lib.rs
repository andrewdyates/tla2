// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![forbid(unsafe_code)]

//! Z4 Frontend - SMT-LIB 2.6 parser and preprocessor
//!
//! Parses SMT-LIB input and converts it to the internal representation.
//!
//! # Example
//!
//! ```
//! use z4_frontend::{parse, Command};
//!
//! let input = r#"
//!     (set-logic QF_LIA)
//!     (declare-const x Int)
//!     (assert (> x 0))
//!     (check-sat)
//! "#;
//!
//! let commands = parse(input).unwrap();
//! assert_eq!(commands.len(), 4);
//! assert!(matches!(&commands[0], Command::SetLogic(logic) if logic == "QF_LIA"));
//! ```

#![warn(missing_docs)]
#![warn(clippy::all)]

pub mod command;
pub(crate) mod elaborate;
pub(crate) mod lexer;
pub(crate) mod parser;
pub mod sexp;
pub mod stats;

pub use command::{Command, Constant, Sort, Term};
pub use elaborate::{
    CommandResult, Context, ElaborateError, Objective, ObjectiveDirection, OptionValue, SymbolInfo,
};
pub use parser::parse;
pub use sexp::{ParseError, SExpr};
pub use stats::{collect_formula_stats, FormulaStats};
