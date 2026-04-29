// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Petri net model checking frontend for `tla2`.
//!
//! This crate houses the imported Petri-net MCC engine inside the `tla2`
//! workspace. It parses PNML Petri nets, explores their state spaces, exposes
//! MCC examination APIs, and provides a `tla-mc-core` transition-system
//! adapter for generic exploration code.
//!
//! # Techniques
//!
//! - **BFS exploration** with FxHashSet deduplication (configurable `max_states`)
//! - **Structural reductions** — dead-transition, isolated-place,
//!   constant-place, and agglomeration reductions before exploration
//! - **LP state equation** — linear-programming bounds for reachability
//!   and upper-bounds without full state space exploration
//! - **Stubborn sets** — partial-order reduction during BFS
//! - **SCC analysis** — terminal-SCC detection for liveness
//! - **Buchi product** — LTL model checking via automaton product
//! - **CTL checker** — MCC CTL examination support
//! - **Property XML parsing** — CTL, LTL, and reachability formula input
//!
//! # Supported examinations
//!
//! Non-property examinations: ReachabilityDeadlock, OneSafe, StateSpace,
//! QuasiLiveness, StableMarking, and Liveness.
//!
//! Property-XML examinations: UpperBounds, ReachabilityCardinality,
//! ReachabilityFireability, CTLCardinality, CTLFireability,
//! LTLCardinality, and LTLFireability.
//!
//! # Model loading
//!
//! Use [`model::load_model_dir`] as the high-level entry point. It returns
//! a [`model::PreparedModel`] that wraps the parsed net with model name,
//! directory, source net kind, and property alias tables.
//!
//! # Limitations
//!
//! - [`parser::parse_pnml_dir`] remains the strict low-level parser for plain
//!   P/T nets (`ptnet`). Use [`model::load_model_dir`] for the high-level MCC
//!   loading path when supported colored nets (`symmetricnet`) should be
//!   attempted.
//! - Unsupported PNML net kinds or colored-net constructs surface
//!   [`error::PnmlError::UnsupportedNetType`]. The CLI converts those
//!   unsupported-model cases into MCC `CANNOT_COMPUTE` output.
//! - Explicit-state BFS bounded by available memory; LP and structural
//!   techniques extend coverage beyond the BFS horizon.

pub(crate) mod buchi;
pub(crate) mod circulation_loop;
pub mod cli;
pub(crate) mod colored_dead_transitions;
pub(crate) mod colored_reduce;
pub(crate) mod colored_relevance;
pub(crate) mod encode_aiger;
// TODO(#4210): Wire decompose() into examination pipeline; remove allow(dead_code).
#[allow(dead_code)]
pub(crate) mod decomposition;
pub mod error;
pub mod examination;
pub(crate) mod examinations;
pub mod explorer;
pub(crate) mod formula_simplify;
pub(crate) mod hlpnml;
pub(crate) mod intelligence_bus;
pub(crate) mod invariant;
pub(crate) mod lp_state_equation;
pub(crate) mod marking;
pub(crate) mod memory;
pub mod model;
pub mod output;
pub mod parser;
pub(crate) mod petri_net;
pub(crate) mod portfolio;
pub(crate) mod property_xml;
pub(crate) mod query_slice;
pub(crate) mod reduction;
pub(crate) mod resolved_predicate;
pub(crate) mod scc;
pub mod simplification_report;
pub(crate) mod structural;
pub(crate) mod stubborn;
pub mod system;
pub mod timeout;
pub(crate) mod unfold;

// Stable public API: core Petri net model types.
//
// These types are returned by `parser::parse_pnml_dir` and consumed by
// `explorer::ExplorationConfig::auto_sized`, `examination::run_examination`,
// and related functions. Re-exported here so downstream callers use
// `tla_petri::PetriNet` instead of depending on internal module layout.
pub use petri_net::{Arc, PetriNet, PlaceIdx, PlaceInfo, TransitionIdx, TransitionInfo};
pub use system::{CompactMarking, PetriNetSystem, StubbornPorProvider};

#[cfg(test)]
#[path = "wrong_answer_investigation_tests.rs"]
mod wrong_answer_investigation_tests;

#[cfg(test)]
#[path = "upper_bounds_regression_tests.rs"]
mod upper_bounds_regression_tests;

#[cfg(test)]
#[path = "upper_bounds_diagnostic_test.rs"]
mod upper_bounds_diagnostic_test;

#[cfg(test)]
#[path = "one_safe_regression_tests.rs"]
mod one_safe_regression_tests;

#[cfg(test)]
#[path = "output_tests.rs"]
mod output_tests;

#[cfg(test)]
#[path = "petri_net_tests.rs"]
mod petri_net_tests;

#[cfg(test)]
#[path = "memory_tests.rs"]
mod memory_tests;

#[cfg(test)]
#[path = "reachability_colored_regression_tests.rs"]
mod reachability_colored_regression_tests;

#[cfg(test)]
#[path = "simplification_report_model_tests.rs"]
mod simplification_report_model_tests;

#[cfg(test)]
#[path = "colored_reduction_tests.rs"]
mod colored_reduction_tests;
