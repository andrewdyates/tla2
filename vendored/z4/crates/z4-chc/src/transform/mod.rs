// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! CHC problem transformations
//!
//! This module provides transformations that convert CHC problems into equivalent
//! forms that are more amenable to solving.
//!
//! # Architecture
//!
//! Based on Golem's transformer framework:
//! - `reference/golem/src/transformers/Transformer.h`
//! - `reference/golem/src/transformers/TransformationPipeline.h`
//!
//! Each transformer takes a CHC problem and returns a transformed problem plus
//! a back-translator for converting witnesses (invariants or counterexamples)
//! back to the original problem's vocabulary.

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

mod bv_to_bool;
mod bv_to_int;
mod clause_inlining;
mod dead_param_elimination;
mod local_var_elimination;

use crate::{ChcProblem, Counterexample, InvariantModel};

pub(crate) use bv_to_bool::BvToBoolBitBlaster;
pub(crate) use bv_to_int::BvToIntAbstractor;
pub(crate) use clause_inlining::ClauseInliner;
pub(crate) use dead_param_elimination::DeadParamEliminator;
pub(crate) use local_var_elimination::LocalVarEliminator;

// ============================================================================
// Type Aliases for Witnesses
// ============================================================================

/// Witness that the CHC system is satisfiable (safe).
/// Contains inductive interpretations for each predicate.
pub(crate) type ValidityWitness = InvariantModel;

/// Witness that the CHC system is unsatisfiable (unsafe).
/// Contains a concrete counterexample trace.
pub(crate) type InvalidityWitness = Counterexample;

// ============================================================================
// Transformation Result
// ============================================================================

/// Result of applying a transformation to a CHC problem.
pub(crate) struct TransformationResult {
    /// The transformed CHC problem.
    pub(crate) problem: ChcProblem,
    /// Back-translator for converting witnesses from the transformed problem
    /// back to the original problem.
    pub(crate) back_translator: Box<dyn BackTranslator>,
}

// ============================================================================
// Back Translator Trait
// ============================================================================

/// Translates witnesses from a transformed problem back to the original problem.
///
/// Reference: `reference/golem/src/transformers/Transformer.h:WitnessBackTranslator`
pub(crate) trait BackTranslator: Send {
    /// Translate an invariant model from the transformed problem
    /// back to the original problem's predicate vocabulary.
    fn translate_validity(&self, witness: ValidityWitness) -> ValidityWitness;

    /// Translate a counterexample from the transformed problem
    /// back to the original problem's state vocabulary.
    fn translate_invalidity(&self, witness: InvalidityWitness) -> InvalidityWitness;
}

/// Identity back-translator that passes witnesses through unchanged.
///
/// Used for transformations that don't change the witness representation.
pub(crate) struct IdentityBackTranslator;

impl BackTranslator for IdentityBackTranslator {
    fn translate_validity(&self, witness: ValidityWitness) -> ValidityWitness {
        witness
    }

    fn translate_invalidity(&self, witness: InvalidityWitness) -> InvalidityWitness {
        witness
    }
}

// ============================================================================
// Transformer Trait
// ============================================================================

/// A transformation that converts a CHC problem into an equivalent form.
///
/// Reference: `reference/golem/src/transformers/Transformer.h:Transformer`
///
/// Transformers must be consumed when applied (hence `self: Box<Self>`),
/// because they may need to move internal state into the back-translator.
pub(crate) trait Transformer {
    /// Apply the transformation to a CHC problem.
    ///
    /// Returns the transformed problem and a back-translator.
    fn transform(self: Box<Self>, problem: ChcProblem) -> TransformationResult;
}

// ============================================================================
// Transformation Pipeline
// ============================================================================

/// A pipeline of transformations applied in sequence.
///
/// Reference: `reference/golem/src/transformers/TransformationPipeline.h`
///
/// The pipeline applies transformations in order, composing their back-translators
/// so that witnesses can be translated back through the entire pipeline.
pub(crate) struct TransformationPipeline {
    transformers: Vec<Box<dyn Transformer>>,
}

impl Default for TransformationPipeline {
    fn default() -> Self {
        Self::new()
    }
}

impl TransformationPipeline {
    /// Create a new empty pipeline.
    pub(crate) fn new() -> Self {
        Self {
            transformers: Vec::new(),
        }
    }

    /// Add a transformer to the end of the pipeline.
    pub(crate) fn with<T: Transformer + 'static>(mut self, transformer: T) -> Self {
        self.transformers.push(Box::new(transformer));
        self
    }

    /// Number of transformers in the pipeline.
    #[cfg(test)]
    pub(crate) fn len(&self) -> usize {
        self.transformers.len()
    }

    /// Apply all transformations in sequence.
    ///
    /// Returns the final transformed problem and a composite back-translator
    /// that will translate witnesses back through all transformations in
    /// reverse order.
    pub(crate) fn transform(self, mut problem: ChcProblem) -> TransformationResult {
        let mut back_translators: Vec<Box<dyn BackTranslator>> = Vec::new();

        for transformer in self.transformers {
            let result = transformer.transform(problem);
            problem = result.problem;
            back_translators.push(result.back_translator);
        }

        // Reverse the back-translators so they're applied in reverse order
        back_translators.reverse();

        TransformationResult {
            problem,
            back_translator: Box::new(CompositeBackTranslator {
                inner: back_translators,
            }),
        }
    }
}

// ============================================================================
// Composite Back Translator
// ============================================================================

/// Composes multiple back-translators into a single translator.
///
/// Applies back-translators in order (which should be reverse of transformation order).
pub(crate) struct CompositeBackTranslator {
    pub(crate) inner: Vec<Box<dyn BackTranslator>>,
}

impl BackTranslator for CompositeBackTranslator {
    fn translate_validity(&self, mut witness: ValidityWitness) -> ValidityWitness {
        for translator in &self.inner {
            witness = translator.translate_validity(witness);
        }
        witness
    }

    fn translate_invalidity(&self, mut witness: InvalidityWitness) -> InvalidityWitness {
        for translator in &self.inner {
            witness = translator.translate_invalidity(witness);
        }
        witness
    }
}

#[allow(clippy::unwrap_used)]
#[cfg(test)]
#[path = "mod_tests.rs"]
mod tests;

#[allow(clippy::unwrap_used)]
#[cfg(test)]
#[path = "soundness_tests.rs"]
mod soundness_tests;
