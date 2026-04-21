// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Certificate generation from Zenon proofs.
//!
//! This module provides conversion from tableau proofs (tree-structured) to
//! proof certificates (linear step sequences) that can be independently verified.
//!
//! # Module Structure
//!
//! - [`convert`]: Type conversion between Zenon and certificate representations
//! - [`builder`]: Certificate step accumulator
//! - [`generate`]: Proof tree traversal and certificate generation

mod builder;
mod convert;
mod generate;

pub use convert::{convert_formula, convert_term};
pub use generate::proof_to_certificate;

#[cfg(test)]
mod tests;
