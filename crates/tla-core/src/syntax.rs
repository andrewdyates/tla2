// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Lexer and concrete syntax tree for TLA+
//!
//! This module uses:
//! - `logos` for fast lexical analysis
//! - `rowan` for lossless syntax tree (preserves whitespace, comments)

pub mod kinds;
pub(crate) mod lexer;
pub(crate) mod parser;

pub use kinds::{SyntaxElement, SyntaxKind, SyntaxNode, SyntaxToken, TlaLanguage};
pub use parser::{
    parse, parse_multi_module, parse_to_syntax_tree, MultiModuleParseResult, ParseError,
    ParseResult, ParsedModule,
};
