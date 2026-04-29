// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Quint JSON IR import: parse `.qnt.json` files into TLA2 AST.
//!
//! Quint is a modern specification language that compiles to TLA+.
//! Its compiler can emit a JSON IR format (`.qnt.json`) that encodes
//! modules, declarations, and expressions in a flat tagged-union style.
//!
//! This module parses that JSON IR and translates it into TLA2's AST,
//! allowing `tla2 check` to operate on Quint specs without going
//! through TLA+ source text.
//!
//! # Usage
//!
//! ```rust,no_run
//! use tla_core::quint::parse_quint_json;
//!
//! # fn main() -> Result<(), tla_core::quint::QuintError> {
//! let json = std::fs::read_to_string("spec.qnt.json")?;
//! let modules = parse_quint_json(&json)?;
//! assert!(!modules.is_empty());
//! # Ok(())
//! # }
//! ```
//!
//! Reference: <https://github.com/informalsystems/quint>

#[allow(dead_code)]
mod ir;
mod translate;

#[cfg(test)]
mod tests;

use crate::ast::Module;

/// Errors that can occur during Quint JSON parsing or translation.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum QuintError {
    /// JSON deserialization failed.
    #[error("Quint JSON parse error: {0}")]
    Json(#[from] serde_json::Error),

    /// IR-to-AST translation failed.
    #[error("Quint translation error: {0}")]
    Translation(String),

    /// IO error reading the file.
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),
}

/// Parse a Quint JSON IR string and return a list of TLA2 `Module`s.
///
/// The input should be the contents of a `.qnt.json` file produced by
/// the Quint compiler (`quint compile --target json`).
///
/// Returns one `Module` per Quint module in the IR. Most specs have a
/// single module, but the format supports multiple.
pub fn parse_quint_json(json: &str) -> Result<Vec<Module>, QuintError> {
    let quint_ir: ir::QuintIr = serde_json::from_str(json)?;
    quint_ir
        .modules
        .iter()
        .map(translate::translate_module)
        .collect()
}

/// Check if a file path looks like a Quint JSON IR file.
///
/// Returns `true` if the path ends with `.qnt.json`.
pub fn is_quint_json_path(path: &std::path::Path) -> bool {
    path.to_str()
        .map(|s| s.ends_with(".qnt.json"))
        .unwrap_or(false)
}
