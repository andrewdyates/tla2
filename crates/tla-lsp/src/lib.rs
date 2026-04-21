// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
#![forbid(unsafe_code)]

//! TLA2 Language Server Protocol implementation
//!
//! Provides IDE features for TLA+ including:
//! - Diagnostics (parse and resolution errors)
//! - Document symbols (outline)
//! - Go to definition
//! - Find references
//! - Hover information
//! - Completion (keywords, stdlib modules/operators, local symbols)
//! - Workspace symbol search

mod analysis;
mod backend;
mod completions;
mod diagnostics;
mod document;
mod handlers;
mod position;
mod server;
mod symbols;

#[cfg(test)]
mod tests;

pub use backend::TlaBackend;
pub use server::run_server;
