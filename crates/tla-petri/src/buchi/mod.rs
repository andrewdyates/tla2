// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! LTL-to-Buchi automaton conversion and product emptiness checking.
//!
//! Implements a simplified GPVW (Gerth-Peled-Vardi-Wolper) on-the-fly
//! construction for converting LTL formulas to Generalized Buchi Automata,
//! then checks language emptiness via product construction with the system
//! state graph and SCC-based accepting cycle detection.

mod atoms;
mod gba;
mod nnf;
mod on_the_fly;
#[cfg(test)]
mod product;

#[cfg(test)]
pub(crate) use atoms::resolve_atom;
pub(crate) use atoms::resolve_atom_with_aliases;
#[cfg(test)]
pub(crate) use atoms::LtlContext;
pub(crate) use nnf::{to_nnf, LtlNnf};

pub(crate) use on_the_fly::PorContext;

use gba::build_gba;
use nnf::negate;
use on_the_fly::on_the_fly_product_emptiness;
#[cfg(test)]
use product::product_has_accepting_cycle;

/// Check if A(φ) holds — i.e., all paths from state 0 satisfy φ.
///
/// Returns `Some(true)` if the formula holds, `Some(false)` if a
/// counterexample exists, or `None` if the product graph exceeded the
/// size limit (result is inconclusive).
///
/// **Legacy path**: requires a pre-built [`crate::explorer::FullReachabilityGraph`].
/// New code should prefer [`check_ltl_on_the_fly`] which computes system
/// successors lazily.
#[cfg(test)]
pub(crate) fn check_ltl_formula(formula: &LtlNnf, ctx: &LtlContext<'_>) -> Option<bool> {
    // We want to check A(φ). Negate to get ¬φ and check E(¬φ) = ∅.
    let neg = negate(formula);

    // Build the Generalized Buchi Automaton for ¬φ.
    let gba = build_gba(&neg);

    // Check if the product of the system × GBA has an accepting cycle
    // reachable from the initial state.
    // None = product overflow (inconclusive), Some(true) = accepting cycle found,
    // Some(false) = no accepting cycle.
    let has_cycle = product_has_accepting_cycle(&gba, ctx)?;
    Some(!has_cycle)
}

/// On-the-fly variant of [`check_ltl_formula`]: checks A(φ) without a
/// pre-built reachability graph.
///
/// System successors are computed lazily by firing transitions on `net`
/// (the reduced Petri net). Atom predicates are evaluated by expanding
/// reduced markings to `original_net` space via `reduced`.
///
/// Returns `Some(true)` if φ holds, `Some(false)` if ¬φ has an accepting
/// run, or `None` if the system-marking or product-state budget was exceeded.
pub(crate) fn check_ltl_on_the_fly(
    formula: &LtlNnf,
    net: &crate::petri_net::PetriNet,
    reduced: &crate::reduction::ReducedNet,
    original_net: &crate::petri_net::PetriNet,
    atoms: &[crate::resolved_predicate::ResolvedPredicate],
    por: Option<&PorContext>,
    max_system_states: usize,
    deadline: Option<std::time::Instant>,
) -> Result<Option<bool>, crate::error::PnmlError> {
    let neg = negate(formula);
    let gba = build_gba(&neg);
    let has_cycle = on_the_fly_product_emptiness(
        &gba,
        net,
        reduced,
        original_net,
        atoms,
        por,
        max_system_states,
        deadline,
    )?;
    Ok(has_cycle.map(|value| !value))
}

#[cfg(test)]
#[path = "integration_tests.rs"]
mod integration_tests;
