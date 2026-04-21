// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Combined theory solvers for Nelson-Oppen theory combination.
//!
//! Production dispatch uses `TheoryCombiner` (generic N-O combiner) for:
//! - QF_AX (EUF + Arrays)
//! - QF_UFLIA (EUF + LIA)
//! - QF_UFLRA (EUF + LRA)
//! - QF_AUFLIA (EUF + Arrays + LIA)
//! - QF_AUFLRA (EUF + Arrays + LRA)
//!
//! Remaining bespoke adapters handle logics not yet covered by the combiner:
//! - UfNraSolver: EUF + NRA
//! - LiraSolver: LIA + LRA (mixed integer/real)
//! - StringsLiaSolver: Strings + EUF + LIA
//! - AufLiraSolver: Arrays + EUF + LIA + LRA

/// Generates the mechanical `propagate()` delegation that collects theory
/// propagations from each sub-solver field.
macro_rules! delegate_propagate {
    ($first:ident $(, $rest:ident)*) => {
        fn propagate(&mut self) -> Vec<z4_core::TheoryPropagation> {
            let mut props = self.$first.propagate();
            $(props.extend(self.$rest.propagate());)*
            props
        }
    };
}

/// Generates mechanical `push()`, `pop()`, `reset()`, `soft_reset()` delegation to sub-solver fields.
/// Includes always-on scope depth tracking via `self.scope_depth` (#4995).
/// The using struct must have a `scope_depth: usize` field.
macro_rules! delegate_scope_ops {
    ($solver_name:literal, $($field:ident),+ $(,)?) => {
        fn push(&mut self) {
            self.scope_depth += 1;
            $(self.$field.push();)+
        }
        fn pop(&mut self) {
            debug_assert!(
                self.scope_depth > 0,
                concat!("BUG: ", $solver_name, "::pop() called at scope depth 0 (underflow)")
            );
            if self.scope_depth == 0 {
                return;
            }
            self.scope_depth -= 1;
            $(self.$field.pop();)+
        }
        fn reset(&mut self) {
            assert!(
                self.scope_depth == 0,
                concat!("BUG: ", $solver_name, "::reset() called with non-zero scope depth {} (unbalanced push/pop)"),
                self.scope_depth,
            );
            $(self.$field.reset();)+
        }
        fn soft_reset(&mut self) {
            assert!(
                self.scope_depth == 0,
                concat!("BUG: ", $solver_name, "::soft_reset() called with non-zero scope depth {} (unbalanced push/pop)"),
                self.scope_depth,
            );
            $(self.$field.soft_reset();)+
        }
    };
}

mod adapters;
mod check_loops;
pub(crate) mod combiner;
mod combiner_check;
mod combiner_models;
mod interface_bridge;
mod interface_bridge_eval;
mod models;

pub(crate) use adapters::{
    AufLiraSolver, LiraSolver, StringsLiaSolver, UfNraSolver, UfSeqLiaSolver, UfSeqSolver,
};
pub use combiner::TheoryCombiner;

#[cfg(test)]
mod interface_bridge_tests;
#[cfg(test)]
mod tests;
#[cfg(test)]
mod tests_combiner;
#[cfg(test)]
mod tests_soft_reset;
