#![forbid(unsafe_code)]
#![warn(missing_docs)]
// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! P vs NP Barrier Checking Tools
//!
//! This crate provides tools for automatically detecting when a proof attempt
//! hits one of the three known barriers to P vs NP separation:
//!
//! 1. **Relativization** (Baker-Gill-Solovay 1975)
//! 2. **Natural Proofs** (Razborov-Rudich 1997)
//! 3. **Algebrization** (Aaronson-Wigderson 2009)
//!
//! These barriers explain why certain proof techniques cannot work. By detecting
//! them early, we can save years of wasted effort pursuing doomed approaches.
//!
//! ## Example
//!
//! ```
//! use z4_barriers::{BarrierChecker, ProofSketch, ProofTechnique, ComplexityClass};
//!
//! // Create a proof sketch attempting to separate P from NP
//! let proof = ProofSketch::new(
//!     ComplexityClass::P,
//!     ComplexityClass::NP,
//! )
//! .with_technique(ProofTechnique::Diagonalization)
//! .with_technique(ProofTechnique::Simulation);
//!
//! // Check for barriers
//! let checker = BarrierChecker::new();
//! let barriers = checker.check_all(&proof);
//!
//! // Diagonalization + simulation relativizes
//! assert!(barriers.iter().any(|b| b.is_relativization()));
//! ```
//!
//! ## References
//!
//! - Baker, Gill, Solovay, "Relativizations of the P =? NP Question" (1975)
//! - Razborov, Rudich, "Natural Proofs" (1997)
//! - Aaronson, Wigderson, "Algebrization: A New Barrier in Complexity Theory" (2009)
//! - Arora & Barak, "Computational Complexity: A Modern Approach" (Ch. 3, 23)

mod barrier;
mod checker;
mod oracle;
mod proof_sketch;

pub use barrier::{AlgebrizationBarrier, Barrier, NaturalProofBarrier, RelativizationBarrier};
pub use checker::BarrierChecker;
pub use oracle::{AlgebraicOracle, Oracle, OracleType};
pub use proof_sketch::{ComplexityClass, FunctionProperty, ProofSketch, ProofTechnique};
