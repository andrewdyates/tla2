// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Quantifier Manager for persisting quantifier instantiation state across solver rounds.
//!
//! This module provides a unified interface for managing quantifier instantiation,
//! including generation tracking across E-matching rounds and deferred instantiations.
//!
//! # Architecture
//!
//! The `QuantifierManager` corresponds to Z3's `qi_queue` + `quantifier_manager`.
//! It persists state that must survive across `check_sat` calls:
//!
//! - `GenerationTracker`: tracks term generations to avoid redundant instantiations
//! - `deferred`: instantiations that exceeded the eager threshold but may be needed later
//!
//! # References
//!
//! - Z3: `reference/z3/src/smt/qi_queue.cpp`
//! - Design: `designs/2026-01-23-quantifier-instantiation-loop.md`

use std::collections::VecDeque;

use crate::ematching::{
    perform_ematching_with_generations, DeferredInstantiation, EMatchingConfig, EMatchingResult,
    GenerationTracker,
};
use z4_core::{TermId, TermStore};
use z4_euf::EufModel;

/// Manages quantifier instantiation state across solver rounds.
///
/// This struct persists the generation tracker and deferred instantiations
/// that would otherwise be lost between E-matching calls.
///
/// # Phase A (#573)
///
/// Initial implementation: persist GenerationTracker across rounds so that:
/// - Generation tracking is not reset each call
/// - We can observe generation increments across rounds
/// - Foundation for later phases (B-E)
#[derive(Debug)]
pub(crate) struct QuantifierManager {
    /// Persisted generation tracker across rounds.
    ///
    /// Without persistence, each `perform_ematching()` call starts fresh,
    /// making generation-based cost filtering ineffective.
    generation_tracker: GenerationTracker,

    /// Deferred instantiations from previous rounds.
    ///
    /// Instantiations with cost > eager_threshold but <= lazy_threshold
    /// are collected here for later processing.
    ///
    /// Public to allow promote-unsat processing in executor (Phase D, #557).
    pub deferred: VecDeque<DeferredInstantiation>,

    /// Configuration for E-matching.
    config: EMatchingConfig,

    /// Round counter for debugging/profiling.
    round: usize,

    /// Saved states for push/pop incremental mode (#2844).
    /// Each entry stores the generation tracker and deferred queue at that scope level.
    scope_stack: Vec<QuantifierManagerSnapshot>,
}

/// Snapshot of QuantifierManager state saved on push (#2844).
#[derive(Clone, Debug)]
struct QuantifierManagerSnapshot {
    generation_tracker: GenerationTracker,
    deferred_len: usize,
    round: usize,
}

impl Default for QuantifierManager {
    fn default() -> Self {
        Self::new()
    }
}

impl QuantifierManager {
    /// Create a new quantifier manager with default configuration.
    pub(crate) fn new() -> Self {
        Self::with_config(EMatchingConfig::default())
    }

    /// Create a quantifier manager with custom configuration.
    pub(crate) fn with_config(config: EMatchingConfig) -> Self {
        Self {
            generation_tracker: GenerationTracker::new(),
            deferred: VecDeque::new(),
            config,
            round: 0,
            scope_stack: Vec::new(),
        }
    }

    /// Run one round of E-matching with the persisted generation tracker.
    ///
    /// Returns the E-matching result with instantiations and updated state.
    ///
    /// # Phase A behavior
    ///
    /// This phase simply persists the tracker across calls. Later phases will:
    /// - B: Process deferred instantiations
    /// - C: Skip satisfied instantiations
    /// - D: Promote conflict-inducing instantiations
    pub(crate) fn run_ematching_round(
        &mut self,
        terms: &mut TermStore,
        assertions: &[TermId],
        euf_model: Option<&EufModel>,
    ) -> EMatchingResult {
        self.round += 1;

        // Perform E-matching with our persisted tracker.
        // Pass EUF model from a previous solve for congruence-aware matching (#3325 B1b).
        let result = perform_ematching_with_generations(
            terms,
            assertions,
            &self.config,
            // Clone the tracker so we can update it after
            self.generation_tracker.clone(),
            euf_model,
        );

        // Persist the updated tracker for next round
        self.generation_tracker = result.generation_tracker.clone();

        // Collect deferred instantiations (Phase B will process these)
        for def in &result.deferred {
            self.deferred.push_back(def.clone());
        }

        result
    }

    /// Check if there are deferred instantiations waiting.
    ///
    /// When `has_deferred()` returns true and solver would return SAT,
    /// the result should be Unknown instead (Phase B).
    pub(crate) fn has_deferred(&self) -> bool {
        !self.deferred.is_empty()
    }
}

impl crate::incremental_state::IncrementalSubsystem for QuantifierManager {
    /// Save current state for incremental push (#2844).
    ///
    /// Captures the generation tracker, deferred queue length, and round counter
    /// so they can be restored on pop. This prevents state from inner scopes
    /// leaking into outer scopes after pop.
    fn push(&mut self) {
        self.scope_stack.push(QuantifierManagerSnapshot {
            generation_tracker: self.generation_tracker.clone(),
            deferred_len: self.deferred.len(),
            round: self.round,
        });
    }

    /// Restore state from before the matching push (#2844).
    ///
    /// Discards generation tracker entries and deferred instantiations
    /// accumulated in the popped scope. Returns false on underflow.
    fn pop(&mut self) -> bool {
        if let Some(snapshot) = self.scope_stack.pop() {
            self.generation_tracker = snapshot.generation_tracker;
            self.deferred.truncate(snapshot.deferred_len);
            self.round = snapshot.round;
            true
        } else {
            false
        }
    }

    /// Reset all state (for `(reset)` command).
    fn reset(&mut self) {
        self.generation_tracker = GenerationTracker::new();
        self.deferred.clear();
        self.round = 0;
        self.scope_stack.clear();
    }
}

#[cfg(test)]
impl QuantifierManager {
    pub(crate) fn deferred_count(&self) -> usize {
        self.deferred.len()
    }

    pub(crate) fn round(&self) -> usize {
        self.round
    }

    pub(crate) fn generation_tracker(&self) -> &GenerationTracker {
        &self.generation_tracker
    }

    pub(crate) fn clear(&mut self) {
        self.generation_tracker = GenerationTracker::new();
        self.deferred.clear();
        self.round = 0;
        self.scope_stack.clear();
    }
}

#[cfg(test)]
mod tests;
