// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![forbid(unsafe_code)]

//! Z4 Proof - Proof production and export
//!
//! Generate and export proofs in Alethe format.
//!
//! ## Alethe Format
//!
//! The Alethe format is the standard proof format for SMT solvers,
//! supported by carcara and SMTCoq. It uses SMT-LIB syntax with
//! additional proof commands.
//!
//! ## Example
//!
//! ```text
//! ; Declarations from problem
//! (declare-const a Int)
//! (declare-const b Int)
//!
//! ; Proof commands
//! (assume h1 (= a b))
//! (assume h2 (not (= a a)))
//! (step t1 (cl (= a a)) :rule refl)
//! (step t2 (cl) :rule resolution :premises (h2 t1))
//! ```
#![warn(missing_docs)]
#![warn(clippy::all)]

use hashbrown::HashMap;
use std::fmt::Write;
use z4_core::{quote_symbol, TermId, TermStore};
pub use z4_core::{AletheRule, BvGateType, Proof, ProofId, ProofStep, TheoryLemmaKind};

mod alethe_printer;
mod checker;
mod partial;
mod quality;
mod variables;

pub use checker::{check_proof, ProofCheckError};
pub use partial::{check_proof_partial, PartialProofCheck};
pub use quality::{check_proof_strict, check_proof_with_quality, ProofQuality};

use alethe_printer::AlethePrinter;
use variables::{collect_auxiliary_proof_declarations, collect_proof_variables};

/// Export a proof to Alethe format
///
/// Converts a Z4 proof to the Alethe format, which can be verified
/// by carcara or other Alethe-compatible checkers.
///
/// # Arguments
///
/// * `proof` - The proof to export
/// * `terms` - The term store containing all terms referenced in the proof
///
/// # Returns
///
/// A string containing the Alethe proof commands
#[must_use]
pub fn export_alethe(proof: &Proof, terms: &TermStore) -> String {
    let mut output = String::new();
    let printer = AlethePrinter::new(terms);

    // Collect all variables referenced in proof terms and emit declarations.
    // Carcara requires all symbols to be declared before use.
    let vars = collect_proof_variables(proof, terms);
    for (name, sort) in &vars {
        let _ = writeln!(output, "(declare-fun {} () {})", quote_symbol(name), sort);
    }

    for (idx, step) in proof.steps.iter().enumerate() {
        let step_id = ProofId(idx as u32);
        output.push_str(&printer.format_step(step, step_id));
        output.push('\n');
    }

    output
}

/// Export a proof to Alethe format with proof-only auxiliary declarations.
///
/// This variant emits `(declare-fun ...)` lines for auxiliary symbols that are:
/// 1. Referenced by proof steps, and
/// 2. Not part of the original problem assertion scope.
///
/// The declaration preamble is deterministic (sorted by symbol name).
#[must_use]
pub fn export_alethe_with_problem_scope(
    proof: &Proof,
    terms: &TermStore,
    problem_assertions: &[TermId],
) -> String {
    export_alethe_with_problem_scope_and_overrides(proof, terms, problem_assertions, None)
}

/// Export a proof to Alethe format with proof-only auxiliary declarations and
/// optional term-level rendering overrides.
#[must_use]
pub fn export_alethe_with_problem_scope_and_overrides(
    proof: &Proof,
    terms: &TermStore,
    problem_assertions: &[TermId],
    term_overrides: Option<&HashMap<TermId, String>>,
) -> String {
    let mut output = String::new();
    let printer = AlethePrinter::new_with_overrides(terms, term_overrides);

    for (name, sort) in collect_auxiliary_proof_declarations(proof, terms, problem_assertions) {
        let _ = writeln!(output, "(declare-fun {} () {sort})", quote_symbol(&name));
    }

    for (idx, step) in proof.steps.iter().enumerate() {
        let step_id = ProofId(idx as u32);
        output.push_str(&printer.format_step(step, step_id));
        output.push('\n');
    }

    output
}

#[cfg(test)]
#[path = "lib_tests.rs"]
mod tests;
