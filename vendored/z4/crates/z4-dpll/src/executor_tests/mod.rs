// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Executor tests - split from executor.rs
//!
//! Module organization:
//! - `core`: Basic executor functionality (sat/unsat, push/pop)
//! - `model`: get-model, get-value, validate-model tests
//! - `commands`: SMT-LIB commands (info, options, assertions, proofs)
//! - `simplify`: Term simplification tests
//! - `smt`: SMT theory tests (arrays, LRA, LIA, UF)
//! - `strings`: String theory tests (QF_S, QF_SLIA) (#6356)
//! - `seq`: Sequence theory tests (QF_SEQ, QF_SEQLIA) (#6486)
//! - `bv`: Bitvector theory tests (QF_BV, QF_ABV, QF_UFBV, QF_AUFBV)
//! - `incremental`: Incremental solving tests
//! - `quantifier`: Quantifier instantiation tests (CEGQI)
//! - `regression`: Soundness regression tests
//! - `array_soundness`: QF_AX wrong-answer regressions (#4304)

mod array_soundness;
mod bv;
mod commands;
mod core;
mod incremental;
mod model;
mod optimization;
mod quantifier;
mod regression;
mod seq;
mod simplify;
mod smt;
mod strings;
