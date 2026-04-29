// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Constant value parsing and binding for model checking
//!
//! This module handles parsing constant values from TLC config files
//! and binding them to the evaluation context.
//!
//! # Supported formats
//!
//! - Integer literals: `3`, `-42`, `100`
//! - Set literals: `{a, b, c}`, `{1, 2, 3}`
//! - Nested sets: `{{a, b}, {c, d}}`
//! - Model values: identifiers like `a`, `p1`, `server`
//!
//! # Model Values
//!
//! TLC creates special "model values" for identifiers in constant assignments.
//! These are distinct values that compare equal only to themselves.
//! We represent them as Value::ModelValue(String).

mod bind;
mod parse;
#[cfg(test)]
mod parse_tests;

pub use bind::bind_constants_from_config;
pub use parse::{parse_constant_value, ConstantParseError};
