// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Preprocessing framework for SMT assertions
//!
//! Provides a framework for preprocessing passes that transform assertions
//! before Tseitin encoding and theory solving. This is essential for:
//!
//! 1. **Soundness** - Variable substitution ensures semantic equivalence
//!    is propagated to CNF encoding (#1708, #1720, #1782)
//! 2. **Performance** - Simplification reduces CNF size
//!
//! # Architecture
//!
//! Each pass implements [`PreprocessingPass`] and operates on assertions.
//! The [`Preprocessor`] orchestrates passes in a fixed-point loop until
//! no pass makes modifications.
//!
//! # Reference
//!
//! Pattern follows Bitwuzla's preprocessing framework:
//! - `reference/bitwuzla/src/preprocess/preprocessor.cpp`
//! - `reference/bitwuzla/src/preprocess/pass/`

mod flatten_and;
mod ite_equality;
mod normalize_arith_som;
mod normalize_bv_arith;
mod normalize_eq_bv_concat;
mod propagate_values;
mod variable_subst;

pub(crate) use flatten_and::FlattenAnd;
pub(crate) use ite_equality::IteEquality;
pub(crate) use normalize_arith_som::NormalizeArithSom;
pub(crate) use normalize_bv_arith::NormalizeBvArith;
pub(crate) use normalize_eq_bv_concat::NormalizeEqBvConcat;
pub(crate) use propagate_values::PropagateValues;
pub(crate) use variable_subst::VariableSubstitution;

use std::sync::{Arc, Mutex};
use z4_core::{TermId, TermStore};

/// Wrapper to allow sharing VariableSubstitution pass with external code.
struct VariableSubstitutionWrapper(Arc<Mutex<VariableSubstitution>>);

impl PreprocessingPass for VariableSubstitutionWrapper {
    fn apply(&mut self, terms: &mut TermStore, assertions: &mut Vec<TermId>) -> bool {
        self.0.lock().unwrap().apply(terms, assertions)
    }

    fn reset(&mut self) {
        self.0.lock().unwrap().reset();
    }
}

/// A preprocessing pass that transforms assertions.
///
/// Passes should be idempotent - running a pass twice on the same input
/// should produce the same output (and return false the second time).
pub(crate) trait PreprocessingPass {
    /// Apply the pass to the assertions.
    ///
    /// # Arguments
    /// * `terms` - The term store for creating/inspecting terms
    /// * `assertions` - Mutable list of assertions to transform
    ///
    /// # Returns
    /// `true` if any modifications were made, `false` otherwise.
    fn apply(&mut self, terms: &mut TermStore, assertions: &mut Vec<TermId>) -> bool;

    /// Reset pass state for a new preprocessing round.
    ///
    /// Default implementation does nothing. Override if your pass
    /// maintains state between applications.
    fn reset(&mut self) {}
}

/// Orchestrates preprocessing passes in a fixed-point loop.
///
/// Runs all passes repeatedly until no pass makes modifications,
/// ensuring the assertions reach a stable preprocessed form.
pub(crate) struct Preprocessor {
    passes: Vec<Box<dyn PreprocessingPass>>,
    /// Maximum iterations to prevent infinite loops
    max_iterations: usize,
}

impl Default for Preprocessor {
    fn default() -> Self {
        Self::new()
    }
}

impl Preprocessor {
    /// Create a new preprocessor with default passes.
    ///
    /// Default passes (in order):
    /// 1. [`NormalizeEqBvConcat`] - Split BV concat equalities into component equalities
    /// 2. [`FlattenAnd`] - Flatten nested AND into individual assertions
    /// 3. [`PropagateValues`] - Propagate ground equalities `(= EXPR CONST)` (#5081)
    /// 4. [`IteEquality`] - Derive equalities from ITE-based assignments
    /// 5. [`VariableSubstitution`] - Substitute equivalent variables
    /// 6. [`NormalizeBvArith`] - Canonicalize BV arithmetic (bvadd/bvmul)
    ///
    /// Returns (preprocessor, variable_substitution_pass) where the pass can be
    /// queried for substitutions after preprocessing.
    pub(crate) fn new_with_subst() -> (Self, Arc<Mutex<VariableSubstitution>>) {
        let var_subst = Arc::new(Mutex::new(VariableSubstitution::new()));
        let preprocessor = Self {
            passes: vec![
                Box::new(NormalizeEqBvConcat::new()),
                Box::new(FlattenAnd::new()),
                Box::new(PropagateValues::new()),
                Box::new(IteEquality::new()),
                Box::new(VariableSubstitutionWrapper(var_subst.clone())),
                Box::new(NormalizeBvArith::new()),
            ],
            max_iterations: 100,
        };
        (preprocessor, var_subst)
    }

    /// Create a new preprocessor with default passes.
    pub(crate) fn new() -> Self {
        Self {
            passes: vec![
                Box::new(NormalizeEqBvConcat::new()),
                Box::new(FlattenAnd::new()),
                Box::new(PropagateValues::new()),
                Box::new(IteEquality::new()),
                Box::new(VariableSubstitution::new()),
                Box::new(NormalizeBvArith::new()),
            ],
            max_iterations: 100,
        }
    }

    /// Run all passes until fixed point.
    ///
    /// Returns the number of iterations performed.
    pub(crate) fn preprocess(
        &mut self,
        terms: &mut TermStore,
        assertions: &mut Vec<TermId>,
    ) -> usize {
        let mut iterations = 0;

        loop {
            iterations += 1;
            if iterations > self.max_iterations {
                // Exceeded max iterations - stop to prevent infinite loop
                break;
            }

            let mut modified = false;
            for pass in &mut self.passes {
                let pass_modified = pass.apply(terms, assertions);
                modified |= pass_modified;
            }

            if !modified {
                break;
            }

            // Reset passes for next iteration
            for pass in &mut self.passes {
                pass.reset();
            }
        }

        iterations
    }
}

#[cfg(test)]
mod tests;
