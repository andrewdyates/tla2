// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
#![forbid(unsafe_code)]

//! TLA+ to z4 SMT Solver Integration
//!
//! This crate provides constraint-based Init state enumeration using z4,
//! our pure-Rust SMT solver. It enables TLA2 to handle specs with complex
//! Init predicates that defeat brute-force enumeration.
//!
//! # Background (Part of #251)
//!
//! Some TLA+ specs have Init predicates too complex for direct enumeration:
//! - Einstein: `Permutation(S)` creates 120! combinations
//! - MCConsensus/MCVoting: ISpec pattern where Init is an invariant
//! - Specs with unconstrained function variables
//!
//! For these specs, SMT-based enumeration via z4's ALL-SAT solver is more
//! efficient than brute-force enumeration.
//!
//! # Architecture
//!
//! ```text
//! TLA+ Init predicate
//!         │
//!         ▼
//! ┌───────────────────┐
//! │  Z4Translator     │  TLA+ Expr → z4 Formula
//! └────────┬──────────┘
//!          ▼
//! ┌───────────────────┐
//! │  z4 SMT solver    │  QF_LIA / QF_AUFLIA
//! └────────┬──────────┘
//!          ▼
//! ┌───────────────────┐
//! │  Solution enum    │  ALL-SAT with blocking clauses
//! └────────┬──────────┘
//!          ▼
//! ┌───────────────────┐
//! │  Model → State    │  z4 model to TLA2 Value
//! └───────────────────┘
//! ```
//!
//! # Phases
//!
//! ## Phase 2a: Basic Bool/Int translation
//! - Boolean: TRUE, FALSE, /\, \/, ~, =>, <=>
//! - Integer: literals, +, -, *, \div, %, comparisons
//! - Finite set membership: x \in {a, b, c}
//! - Range membership: x \in lo..hi
//!
//! ## Phase 2b (Current): Function support for finite domains
//! - Function application: <code>f\[x\]</code> via ITE expansion
//! - Function set membership: f \in [D -> R] for finite D
//! - Automatic function variable declaration from constraints
//!
//! For finite domains, functions are represented as individual scalar
//! variables (f__key1, f__key2, ...) and function application is expanded
//! to ITE chains. This handles common TLA+ model checking patterns.
//!
//! ## Phase 2c (Planned): tla-check integration
//! - Connect to enumerate.rs
//! - Run blocked specs with z4 path
//! - Full array theory for larger domains (requires z4 API extension)
//!
//! # Example
//!
//! ```no_run
//! use num_bigint::BigInt;
//! use tla_core::ast::Expr;
//! use tla_core::span::Spanned;
//! use tla_z4::{SolveResult, TlaSort, Z4Translator};
//!
//! fn main() -> Result<(), tla_z4::Z4Error> {
//!     let mut trans = Z4Translator::new();
//!
//!     // Declare state variables
//!     trans.declare_var("x", TlaSort::Int)?;
//!     trans.declare_var("y", TlaSort::Int)?;
//!
//!     // Translate Init predicate: x = 0 /\\ y > 5
//!     let x_eq_0 = Spanned::dummy(Expr::Eq(
//!         Box::new(Spanned::dummy(Expr::Ident("x".to_string(), tla_core::name_intern::NameId::INVALID))),
//!         Box::new(Spanned::dummy(Expr::Int(BigInt::from(0)))),
//!     ));
//!     let y_gt_5 = Spanned::dummy(Expr::Gt(
//!         Box::new(Spanned::dummy(Expr::Ident("y".to_string(), tla_core::name_intern::NameId::INVALID))),
//!         Box::new(Spanned::dummy(Expr::Int(BigInt::from(5)))),
//!     ));
//!     let init_expr = Spanned::dummy(Expr::And(Box::new(x_eq_0), Box::new(y_gt_5)));
//!
//!     let init_term = trans.translate_bool(&init_expr)?;
//!     trans.assert(init_term);
//!
//!     // Check satisfiability
//!     if matches!(trans.check_sat(), SolveResult::Sat) {
//!         let model = trans.get_model().expect("SAT implies a model");
//!         let _x = model.int_val("x").unwrap();
//!         let _y = model.int_val("y").unwrap();
//!     }
//!     Ok(())
//! }
//! ```
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0

#![warn(missing_docs)]
pub mod bmc;
pub mod chc;
pub mod error;
pub mod translate;

pub use bmc::incremental::{IncrementalBmc, IncrementalBmcResult};
pub use bmc::{BmcState, BmcTranslator, BmcValue};
// k-Induction checker re-exports (Part of #3722)
pub use bmc::kinduction::{
    KInductionChecker, KInductionConfig as Z4KInductionConfig,
    KInductionResult as Z4KInductionResult,
};
pub use error::{Z4Error, Z4Result};
pub use translate::finite_set::FiniteSetEncoder;
pub use translate::function_encoder::{FuncTerm, FunctionEncoder};
pub use translate::nested_powerset::{
    k_subsets, BaseElement, NestedPowersetConfig, NestedPowersetEncoder, NestedPowersetSolution,
};
pub use translate::record_encoder::RecordEncoder;
pub use translate::sequence_encoder::{SeqTerm, SequenceEncoder};
pub use translate::{TlaSort, Z4Translator};

// Re-export z4 types needed by users
pub use z4_dpll::api::{Logic, Model, SolveResult, Solver, SolverError, Sort, Term};
pub use z4_dpll::UnknownReason;

// Re-export CHC types for PDR users (Part of #642)
pub use z4_chc::PdrConfig;
