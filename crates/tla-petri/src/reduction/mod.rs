// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Structural Petri net reductions for MCC competitiveness.
//!
//! Pre-processes a [`PetriNet`](crate::petri_net::PetriNet) to identify and
//! remove redundant structure before state space exploration. Production
//! entrypoints preserve exact markings or narrower contracts gated by the
//! property class via [`ReductionMode`].
//!
//! # Query-aware reduction selection
//!
//! Different temporal logics tolerate different structural reductions (following
//! Tapaal's approach). [`ReductionMode`] encodes five property classes from most
//! permissive to most restrictive:
//!
//! - **Reachability** — all rules safe (markings preserved modulo COI)
//! - **NextFreeCTL** — most rules except agglomeration
//! - **CTLWithNext** — only dead/constant/isolated (marking-preserving)
//! - **StutterInsensitiveLTL** — same as next-free CTL
//! - **StutterSensitiveLTL** — only dead/constant/isolated
//!
//! Use [`reduce_iterative_structural_with_mode`] for mode-gated reduction.
//! [`Examination::reduction_mode()`](crate::examination::Examination::reduction_mode)
//! maps each MCC examination to its safe mode.
//!
//! # Supported reductions
//!
//! These reductions can be applied iteratively to a fixpoint: removing one
//! structure can expose newly-reducible structure in the next pass.
//!
//! - **Dead transition removal** — transitions that can never fire because
//!   an input place has no token source and insufficient initial marking.
//! - **Isolated place removal** — places with no connected arcs.
//! - **Constant place removal** — places whose token count is invariant across
//!   all reachable markings (every consuming transition restores the same
//!   amount). Removed from the state vector but their fixed values are
//!   preserved for property evaluation.
//! - **Source place removal** — producer-only places that never constrain any
//!   live transition and are not query-protected. Removed as unobservable
//!   accumulators (Tapaal Rule C).
//! - **Pre-agglomeration** (Berthelot 1987) — when a transition `t` has
//!   exactly one output place `p` with weight 1, `p` has no other producer,
//!   zero initial tokens, and all consumers read weight 1: merge `t`'s
//!   inputs into each consumer, then remove `t` and `p`.
//! - **Post-agglomeration** (dual) — when a transition `t` has exactly one
//!   input place `p` with weight 1, `p` has no other consumer, zero initial
//!   tokens, and all producers write weight 1: merge `t`'s outputs into
//!   each producer, then remove `t` and `p`.
//! - **LP-based redundant place removal** (Colom & Silva 1991) — a place is
//!   removed if (1) its marking is reconstructable from a P-invariant, and
//!   (2) LP verification proves it never constrains any transition. Values
//!   are reconstructed during marking expansion.

mod analysis;
mod analysis_agglomeration;
mod analysis_cycle;
mod analysis_invariant;
mod analysis_structural_rules;
mod analysis_transitions;
mod apply;
mod apply_cycle;
mod gcd_scale;
mod irrelevance;
mod model;
mod observer;
mod redundant;

pub(crate) use analysis::analyze;
#[cfg(test)]
pub(crate) use analysis::{
    find_never_disabling_arcs, find_non_decreasing_places, find_parallel_places,
    find_source_places, find_token_eliminated_places,
};
pub(crate) use analysis_cycle::find_token_cycles;
#[cfg(test)]
pub(crate) use analysis_cycle::TokenCycle;
#[cfg(test)]
pub(crate) use apply::apply_query_guarded_prefire;
#[cfg(test)]
pub(crate) use apply::reduce;
#[cfg(test)]
pub(crate) use apply::reduce_iterative;
#[cfg(test)]
pub(crate) use apply::reduce_iterative_structural;
#[cfg(test)]
pub(crate) use apply::reduce_iterative_structural_deadlock_safe_with_protected;
#[cfg(test)]
pub(crate) use apply::reduce_iterative_structural_with_protected;
#[cfg(test)]
pub(crate) use apply::reduce_iterative_temporal_projection_candidate;
pub(crate) use apply::{
    reduce_iterative_structural_one_safe, reduce_iterative_structural_query_with_protected,
    reduce_iterative_structural_with_mode, reduce_query_guarded,
};
#[cfg(test)]
pub(crate) use apply_cycle::apply_token_cycles;
pub(crate) use gcd_scale::apply_final_place_gcd_scaling;
pub(crate) use irrelevance::reduce_irrelevant;
pub(crate) use model::{ReducedNet, ReductionMode, ReductionReport};
pub(crate) use observer::ParallelExpandingObserver;

#[cfg(test)]
mod tests;
