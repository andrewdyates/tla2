// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared test helpers for unit tests within tla-check.
//!
//! This module is `#[cfg(test)]` only and provides canonical parsing/lowering
//! helpers so that individual test modules don't need to define their own.

use tla_core::{lower, parse_to_syntax_tree, FileId};

/// Parse TLA+ source, lower, and return Module.
///
/// Panics with diagnostic details if lowering produces errors or no module.
pub fn parse_module(src: &str) -> tla_core::ast::Module {
    parse_module_with_id(src, FileId(0))
}

/// Parse TLA+ source with a specific FileId, lower, and return Module.
///
/// Panics with diagnostic details if lowering produces errors or no module.
/// Use this variant for multi-module INSTANCE tests that need distinct FileIds.
pub fn parse_module_with_id(src: &str, file_id: FileId) -> tla_core::ast::Module {
    let tree = parse_to_syntax_tree(src);
    let lowered = lower(file_id, &tree);
    if !lowered.errors.is_empty() {
        panic!("parse_module: lowering errors: {:?}", lowered.errors);
    }
    lowered
        .module
        .expect("parse_module: module lowering produced None")
}
