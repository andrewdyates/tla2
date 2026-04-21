// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Structural invariant synthesis for patterned CHC problems.
//!
//! This module recognizes common patterns in CHC problems and synthesizes
//! candidate invariants directly, bypassing expensive PDR search. For
//! simple problems (bounded loops, constant stride), this provides 10-100x
//! speedup.
//!
//! # Patterns Recognized
//!
//! - **Bounded increment**: `x' = x + K` with `x < N` guard -> `x <= N - 1 + K`
//! - **Bounded decrement**: `x' = x - K` with `x > L` guard -> `x >= L + 1 - K`
//! - **Interval bounds**: Combined init and guard analysis -> `L <= x <= U`
//!
//! # Submodules
//!
//! - `types`: Type definitions (SynthesisResult, SynthesisPattern, etc.)
//! - `detection`: Pattern detection from transition clauses
//! - `building`: Candidate construction and inductive verification
//!
//! # Reference
//!
//! Part of #1869 - Structural invariant synthesis for patterned problems.
//! See also: Spacer's `expand_bnd_generalizer.cpp` for post-hoc bound expansion.

mod building;
mod detection;
mod types;

pub(crate) use types::{SynthesisPattern, SynthesisResult, SynthesizedInvariant};

use crate::classifier::{ProblemClass, ProblemClassifier};
use crate::ChcProblem;

/// Structural invariant synthesizer.
pub(crate) struct StructuralSynthesizer<'a> {
    problem: &'a ChcProblem,
}

impl<'a> StructuralSynthesizer<'a> {
    /// Create a new structural synthesizer for the given problem.
    pub(crate) fn new(problem: &'a ChcProblem) -> Self {
        Self { problem }
    }

    /// Attempt structural synthesis.
    ///
    /// Returns `Success` with a verified invariant, `NotInductive` if pattern
    /// was recognized but candidate failed verification, or `NoPattern` if
    /// no recognizable pattern was found.
    pub(crate) fn try_synthesize(&self) -> SynthesisResult {
        // Only attempt synthesis for simple problems
        let features = ProblemClassifier::classify(self.problem);
        if !matches!(
            features.class,
            ProblemClass::Trivial | ProblemClass::SimpleLoop | ProblemClass::MultiPredLinear
        ) {
            return SynthesisResult::NoPattern;
        }

        // Try to detect loop patterns
        let patterns = self.detect_patterns();
        if patterns.is_empty() {
            return SynthesisResult::NoPattern;
        }

        // Build candidate invariant from patterns
        let candidate = self.build_candidate(&patterns);
        if candidate.is_empty() {
            return SynthesisResult::NoPattern;
        }

        // Verify the candidate is inductive
        if self.verify_inductive(&candidate) {
            // Determine primary pattern for reporting
            let primary_pattern = patterns
                .first()
                .map_or(SynthesisPattern::IntervalBounds, |p| p.pattern);

            SynthesisResult::Success(SynthesizedInvariant {
                interpretations: candidate,
                pattern: primary_pattern,
            })
        } else {
            SynthesisResult::NotInductive
        }
    }
}

#[cfg(test)]
mod tests;
