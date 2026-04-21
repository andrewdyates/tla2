// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![forbid(unsafe_code)]

//! z4-lean-bridge: Lean 5 integration for Z4 SMT solver
//!
//! This crate provides a bridge between Z4 and Lean 5, enabling:
//! - Export of Z4 formulas to Lean syntax
//! - Verification of Z4 SAT/UNSAT results in Lean
//! - Proof-carrying UNSAT certificates via Alethe proofs
//!
//! # Architecture
//!
//! The bridge works via term export and proof certificates:
//! 1. Z4 formulas are exported to Lean syntax
//! 2. UNSAT certificates are produced as portable Alethe text
//! 3. Results can be checked by Lean proof assistants
//!
//! # Example
//!
//! ```text
//! use z4_lean_bridge::LeanExporter;
//! use z4_core::TermStore;
//!
//! let store = TermStore::new();
//! // ... build formula in store ...
//!
//! // Export to Lean
//! let exporter = LeanExporter::new(&store);
//! let lean_code = exporter.export_term(formula)?;
//! ```

mod exporter;
pub mod proof;

pub use exporter::LeanExporter;

use thiserror::Error;
use z4_core::Sort;

/// Errors that can occur when interacting with Lean.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum LeanError {
    /// Lean proof failed
    #[error("Lean proof failed: {message}")]
    ProofFailed { message: String },
}

/// Export a sort to Lean type syntax.
pub(crate) fn export_sort_to_lean(sort: &Sort) -> String {
    match sort {
        Sort::Bool => "Bool".to_string(),
        Sort::Int => "Int".to_string(),
        Sort::Real => "Real".to_string(),
        Sort::BitVec(bv) => format!("BitVec {}", bv.width),
        Sort::Array(arr) => {
            format!(
                "Array {} {}",
                export_sort_to_lean(&arr.index_sort),
                export_sort_to_lean(&arr.element_sort)
            )
        }
        Sort::String => "String".to_string(),
        Sort::RegLan => "RegLan".to_string(),
        Sort::FloatingPoint(eb, sb) => format!("FloatingPoint {eb} {sb}"),
        Sort::Uninterpreted(name) => sanitize_lean_name(name),
        Sort::Datatype(dt) => sanitize_lean_name(&dt.name),
        Sort::Seq(elem) => format!("List {}", export_sort_to_lean(elem)),
        _ => unreachable!("unexpected Sort variant"),
    }
}

/// Sanitize a name for use in Lean.
pub(crate) fn sanitize_lean_name(name: &str) -> String {
    // Lean identifiers can contain letters, digits, underscores, and apostrophes
    // They must start with a letter or underscore
    let mut result = String::with_capacity(name.len());
    let mut first = true;

    for c in name.chars() {
        if c.is_ascii_alphanumeric() || c == '_' || c == '\'' {
            if first && c.is_ascii_digit() {
                result.push('_');
            }
            result.push(c);
            first = false;
        } else if c == '!' || c == '?' {
            // Keep these for Lean naming conventions
            result.push(c);
            first = false;
        } else {
            // Replace other characters with underscore
            result.push('_');
            first = false;
        }
    }

    if result.is_empty() {
        return "_unnamed".to_string();
    }

    // Check for Lean reserved words
    if is_lean_reserved(&result) {
        format!("{result}_")
    } else {
        result
    }
}

/// Check if a name is a Lean reserved word.
fn is_lean_reserved(name: &str) -> bool {
    matches!(
        name,
        "def"
            | "theorem"
            | "lemma"
            | "axiom"
            | "example"
            | "structure"
            | "class"
            | "instance"
            | "inductive"
            | "where"
            | "with"
            | "do"
            | "if"
            | "then"
            | "else"
            | "match"
            | "let"
            | "in"
            | "have"
            | "show"
            | "by"
            | "fun"
            | "forall"
            | "exists"
            | "true"
            | "false"
            | "Type"
            | "Prop"
            | "Sort"
            | "Bool"
            | "Nat"
            | "Int"
    )
}

/// Escape a string for use in Lean string literals.
pub(crate) fn escape_lean_string(s: &str) -> String {
    let mut result = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '"' => result.push_str("\\\""),
            '\\' => result.push_str("\\\\"),
            '\n' => result.push_str("\\n"),
            '\r' => result.push_str("\\r"),
            '\t' => result.push_str("\\t"),
            _ => result.push(c),
        }
    }
    result
}

#[cfg(test)]
#[path = "lib_tests.rs"]
mod tests;
