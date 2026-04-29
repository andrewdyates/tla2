// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! MCC examination implementations.
//!
//! Each examination is an [`ExplorationObserver`] that computes a
//! specific property during BFS state space exploration.

pub(crate) mod bmc_runner;
pub(crate) mod ctl;
pub(crate) mod deadlock;
pub(crate) mod global_properties_bmc;
pub(crate) mod global_properties_pdr;
pub(crate) mod incremental_solver;
pub(crate) mod kinduction;
pub(crate) mod liveness;
pub(crate) mod ltl;
pub(crate) mod ltl_por;
pub(crate) mod maximal_path_suffix;
pub(crate) mod one_safe;
pub(crate) mod pdr_encoding;
pub(crate) mod quasi_liveness;
pub(crate) mod query_support;
pub(crate) mod reachability;
pub(crate) mod reachability_aiger;
pub(crate) mod reachability_bmc;
pub(crate) mod reachability_heuristic;
pub(crate) mod reachability_lp;
pub(crate) mod reachability_pdr;
pub(crate) mod reachability_por;
pub(crate) mod reachability_walk;
pub(crate) mod reachability_witness;
pub(crate) mod smt_encoding;
pub(crate) mod stable_marking;
pub(crate) mod state_space;
pub(crate) mod upper_bounds;
