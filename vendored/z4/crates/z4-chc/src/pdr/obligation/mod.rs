// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Proof obligation types for PDR solver.

use crate::smt::SmtValue;
use crate::{ChcExpr, PredicateId};
use rustc_hash::FxHashMap;
use std::cmp::Ordering;

use super::derivation::DerivationId;

/// A proof obligation: state to prove unreachable
#[derive(Debug, Clone)]
pub(crate) struct ProofObligation {
    /// Predicate
    pub(crate) predicate: PredicateId,
    /// State condition
    pub(crate) state: ChcExpr,
    /// Monotonic ID assigned when enqueued (deterministic tie-breaker).
    pub(crate) queue_id: u64,
    /// Frame level
    pub(crate) level: usize,
    /// Depth in search (for prioritization)
    pub(crate) depth: usize,
    /// Clause index (in `ChcProblem::clauses()`) used to derive this fact.
    /// None indicates a root obligation (e.g., query state).
    pub(crate) incoming_clause: Option<usize>,
    /// Clause index (in `ChcProblem::clauses()`) for the query that introduced this obligation.
    /// Set only on the root of an obligation chain.
    pub(crate) query_clause: Option<usize>,
    /// Parent obligation (for counterexample construction)
    pub(crate) parent: Option<Box<Self>>,
    /// SMT model for this state (for counterexample assignment extraction)
    pub(crate) smt_model: Option<FxHashMap<String, SmtValue>>,
    /// Optional derivation handle for multi-body clause tracking.
    /// When set, this POB is part of a derivation that tracks progress
    /// through a hyperedge (rule with multiple body predicates).
    /// Scaffolding for #1275; will be used when derivation tracking completes.
    pub(crate) derivation_id: Option<DerivationId>,
}

impl ProofObligation {
    /// Maximum weakness level for spurious CEX retries (same as Z3 Spacer).
    pub(crate) const MAX_WEAKNESS: u8 = 10;

    pub(crate) fn new(predicate: PredicateId, state: ChcExpr, level: usize) -> Self {
        Self {
            predicate,
            state,
            queue_id: 0,
            level,
            depth: 0,
            incoming_clause: None,
            query_clause: None,
            parent: None,
            smt_model: None,
            derivation_id: None,
        }
    }

    /// Scaffolding for #1275; will be used when derivation tracking completes.
    pub(crate) fn with_derivation_id(mut self, id: DerivationId) -> Self {
        self.derivation_id = Some(id);
        self
    }

    pub(crate) fn with_incoming_clause(mut self, clause_index: usize) -> Self {
        self.incoming_clause = Some(clause_index);
        self
    }

    pub(crate) fn with_query_clause(mut self, clause_index: usize) -> Self {
        self.query_clause = Some(clause_index);
        self
    }

    pub(crate) fn with_parent(mut self, parent: Self) -> Self {
        self.depth = parent.depth + 1;
        self.parent = Some(Box::new(parent));
        self
    }

    pub(crate) fn with_smt_model(mut self, model: FxHashMap<String, SmtValue>) -> Self {
        self.smt_model = Some(model);
        self
    }

    /// Priority key: (level, predicate, queue_id). Lower tuple values are higher priority.
    pub(crate) fn priority_key(&self) -> (usize, usize, u64) {
        (self.level, self.predicate.index(), self.queue_id)
    }
}

/// Wrapper for POB in priority queue - lower levels processed first
#[derive(Debug)]
pub(crate) struct PriorityPob(pub(crate) ProofObligation);

impl PartialEq for PriorityPob {
    fn eq(&self, other: &Self) -> bool {
        self.0.priority_key() == other.0.priority_key()
    }
}

impl Eq for PriorityPob {}

impl PartialOrd for PriorityPob {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for PriorityPob {
    fn cmp(&self, other: &Self) -> Ordering {
        // Reverse ordering: lower level = higher priority (comes out first from max-heap)
        // Also use predicate as tiebreaker (consistent with Golem)
        other.0.priority_key().cmp(&self.0.priority_key())
    }
}

/// Custom Drop to prevent stack overflow on deep obligation chains.
/// Default drop would recursively drop Box<ProofObligation> parents,
/// using O(N) stack frames for a chain of length N. This iterative
/// implementation uses O(1) stack space.
impl Drop for ProofObligation {
    fn drop(&mut self) {
        let mut current = self.parent.take();
        while let Some(mut boxed) = current {
            current = boxed.parent.take();
            // boxed drops here with no parent, so no recursion
        }
    }
}

#[allow(clippy::unwrap_used)]
#[cfg(test)]
mod tests;
