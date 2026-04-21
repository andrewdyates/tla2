// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
#![forbid(unsafe_code)]

//! tla-zenon - First-order tableau prover
//!
//! A Rust port of Zenon, the automated theorem prover used by TLAPM.
//! This implements the analytic tableau method for first-order logic.
//!
//! The tableau method works by proof by refutation:
//! 1. Negate the goal formula
//! 2. Apply decomposition rules to expand the formula
//! 3. If all branches contain contradictions, the original formula is valid
//!
//! # Tableau Rules
//!
//! - **Alpha rules**: Decompose conjunctions (single successor)
//! - **Beta rules**: Decompose disjunctions (branching)
//! - **Gamma rules**: Universal instantiation (∀x.P → P[t/x])
//! - **Delta rules**: Existential witness (∃x.P → P[c/x] for fresh c)
//!
//! # Example
//!
//! ```rust
//! use tla_zenon::{Formula, Prover, ProofResult};
//!
//! // Prove: (A ∧ B) → A
//! let a = Formula::var("A");
//! let b = Formula::var("B");
//! let goal = Formula::implies(Formula::and(a.clone(), b), a);
//!
//! let mut prover = Prover::new();
//! let result = prover.prove(&goal, Default::default());
//! assert!(matches!(result, ProofResult::Valid(_)));
//! ```

pub mod certificate;
pub mod formula;
pub mod proof;
pub mod prover;
pub mod rules;

pub use certificate::{convert_formula, convert_term, proof_to_certificate};
pub use formula::{Formula, Subst, Term};
pub use proof::{Proof, ProofNode, ProofRule};
pub use prover::{ProofResult, Prover, ProverConfig};
