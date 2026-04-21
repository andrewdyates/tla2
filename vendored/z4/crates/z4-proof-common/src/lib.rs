// Copyright 2026 Andrew Yates
// Shared types and parsers for z4 proof checker crates.
// Depends on thiserror for typed error enums.

#![forbid(unsafe_code)]

pub mod dimacs;
pub mod error;
pub mod leb128;
pub mod literal;

pub use error::ParseError;
