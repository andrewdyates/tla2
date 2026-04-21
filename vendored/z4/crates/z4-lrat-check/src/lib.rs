// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

#![forbid(unsafe_code)]

//! Standalone LRAT proof checker library.
//!
//! Verifies LRAT (Linear Resolution Asymmetric Tautology) proofs for
//! SAT solver UNSAT results. Supports both text and binary LRAT formats.
//!
//! # Usage
//!
//! ```no_run
//! use z4_lrat_check::checker::LratChecker;
//! use z4_lrat_check::lrat_parser;
//!
//! let cnf = z4_lrat_check::dimacs::parse_cnf_with_ids(&b"p cnf 2 2\n1 2 0\n-1 2 0\n"[..]).expect("valid CNF");
//! let proof = lrat_parser::parse_text_lrat("3 2 0 1 2 0\n").expect("valid LRAT");
//! let mut checker = LratChecker::new(cnf.num_vars);
//! for (id, clause) in &cnf.clauses {
//!     checker.add_original(*id, clause);
//! }
//! assert!(checker.verify_proof(&proof));
//! ```

pub mod checker;
pub mod dimacs;
pub mod lrat_parser;

pub use checker::{ConcludeFailure, ConcludeResult, Stats};
