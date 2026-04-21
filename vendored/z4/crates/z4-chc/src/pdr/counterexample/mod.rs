// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Counterexample types for PDR solver.

use crate::smt::SmtValue;
use crate::{ChcExpr, PredicateId};
use rustc_hash::FxHashMap;

/// Counterexample trace
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct Counterexample {
    /// Steps in the counterexample (initial state -> ... -> bad state)
    pub steps: Vec<CounterexampleStep>,
    /// Optional derivation witness (Golem/Spacer-style)
    pub witness: Option<DerivationWitness>,
}

impl Counterexample {
    /// Create a counterexample with steps and no witness.
    pub fn new(steps: Vec<CounterexampleStep>) -> Self {
        Self {
            steps,
            witness: None,
        }
    }

    /// Create a counterexample with steps and a derivation witness.
    pub fn with_witness(steps: Vec<CounterexampleStep>, witness: DerivationWitness) -> Self {
        Self {
            steps,
            witness: Some(witness),
        }
    }

    /// Format the counterexample as a machine-readable certificate.
    ///
    /// The certificate includes:
    /// 1. A header identifying the result as UNSAFE
    /// 2. The counterexample trace as concrete variable assignments at each step
    /// 3. If a derivation witness is present, the derivation DAG with state formulas
    pub fn to_certificate(&self, problem: &crate::ChcProblem) -> String {
        use crate::pdr::model::InvariantModel;
        use std::fmt::Write;

        let mut out = String::new();
        let _ = writeln!(out, ";; Z4 CHC Certificate: UNSAFE");
        let _ = writeln!(out, ";; Format: z4-chc-cert v1");
        let _ = writeln!(out, ";;");
        let _ = writeln!(
            out,
            ";; Counterexample trace ({} step{}):",
            self.steps.len(),
            if self.steps.len() == 1 { "" } else { "s" }
        );

        for (i, step) in self.steps.iter().enumerate() {
            let pred_name = problem
                .get_predicate(step.predicate)
                .map_or("?", |p| p.name.as_str());
            let _ = writeln!(out, ";; Step {i}: {pred_name}");

            if step.assignments.is_empty() {
                let _ = writeln!(out, ";;   (no concrete assignments)");
            } else {
                // Sort assignments by name for deterministic output
                let mut assigns: Vec<_> = step.assignments.iter().collect();
                assigns.sort_by_key(|(k, _)| k.as_str());
                for (var, val) in assigns {
                    let _ = writeln!(out, ";;   {var} = {val}");
                }
            }
        }

        // If we have a derivation witness with concrete instances, emit those too
        if let Some(witness) = &self.witness {
            if witness.entries.iter().any(|e| !e.instances.is_empty()) {
                let _ = writeln!(out, ";;");
                let _ = writeln!(out, ";; Derivation witness:");
                for (i, entry) in witness.entries.iter().enumerate() {
                    let pred_name = problem
                        .get_predicate(entry.predicate)
                        .map_or("?", |p| p.name.as_str());
                    let _ = writeln!(
                        out,
                        ";; [{i}] {pred_name} (level {})",
                        entry.level
                    );
                    if !entry.instances.is_empty() {
                        let mut insts: Vec<_> = entry.instances.iter().collect();
                        insts.sort_by_key(|(k, _)| k.as_str());
                        for (var, val) in insts {
                            let _ = writeln!(out, ";;   {var} = {val:?}");
                        }
                    }
                    // Emit state formula as SMT-LIB
                    let state_str = InvariantModel::expr_to_smtlib(&entry.state);
                    let _ = writeln!(out, ";;   state: {state_str}");
                }
            }
        }

        out
    }
}

/// A step in a counterexample
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct CounterexampleStep {
    /// Predicate at this step
    pub predicate: PredicateId,
    /// Variable assignments at this step
    pub assignments: FxHashMap<String, i64>,
}

impl CounterexampleStep {
    /// Create a counterexample step.
    pub fn new(predicate: PredicateId, assignments: FxHashMap<String, i64>) -> Self {
        Self {
            predicate,
            assignments,
        }
    }
}

/// A proof witness for UNSAFE results.
///
/// This mirrors Golem/Spacer's derivation database concept: derived facts are recorded
/// together with the clause ("edge") used to derive them and their premise facts.
#[derive(Debug, Clone, Default)]
#[non_exhaustive]
pub struct DerivationWitness {
    /// Clause index (in `ChcProblem::clauses()`) for the violated query, if known.
    pub query_clause: Option<usize>,
    /// Index of the root derived fact in `entries` (typically the "bad" state).
    pub root: usize,
    /// Derived facts in a compact DAG form.
    pub entries: Vec<DerivationWitnessEntry>,
}

/// One derived fact in a witness derivation DAG.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct DerivationWitnessEntry {
    /// Predicate this fact is about.
    pub predicate: PredicateId,
    /// Level (number of transition steps from init) for this fact.
    pub level: usize,
    /// State formula (over canonical predicate variables).
    pub state: ChcExpr,
    /// Clause index (in `ChcProblem::clauses()`) used to derive this fact.
    /// None indicates an axiom/root (e.g., direct query state without a generating clause).
    pub incoming_clause: Option<usize>,
    /// Premise fact indices in `DerivationWitness.entries`.
    pub premises: Vec<usize>,
    /// Concrete variable instances from SMT model (like Golem's derivedFact).
    /// Maps variable names to their concrete values (Int, Bool, BitVec) at this derivation step.
    pub instances: FxHashMap<String, SmtValue>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct WitnessNodeKey {
    pub(crate) predicate: PredicateId,
    pub(crate) level: usize,
    pub(crate) state_hash: u64,
}

#[derive(Debug, Default)]
pub(crate) struct WitnessBuilder {
    pub(crate) entries: Vec<DerivationWitnessEntry>,
    pub(crate) index: FxHashMap<WitnessNodeKey, usize>,
}

impl WitnessBuilder {
    pub(crate) fn node(
        &mut self,
        predicate: PredicateId,
        level: usize,
        state: &ChcExpr,
        instances: Option<&FxHashMap<String, SmtValue>>,
    ) -> usize {
        let key = WitnessNodeKey {
            predicate,
            level,
            state_hash: state.structural_hash(),
        };
        if let Some(&idx) = self.index.get(&key) {
            // Collision safety (#2860): verify state expression matches.
            // If it doesn't match, treat as a new node (hash collision).
            if self.entries[idx].state == *state {
                if let Some(instances) = instances {
                    if self.entries[idx].instances.is_empty() && !instances.is_empty() {
                        self.entries[idx].instances = instances.clone();
                    }
                }
                return idx;
            }
            // Hash collision: fall through to create a new node.
            // The index entry is overwritten below, but the old entry remains
            // in the entries vec (referenced by its parent's premises list).
        }

        let idx = self.entries.len();
        self.entries.push(DerivationWitnessEntry {
            predicate,
            level,
            state: state.clone(),
            incoming_clause: None,
            premises: Vec::new(),
            instances: instances.cloned().unwrap_or_default(),
        });
        self.index.insert(key, idx);
        idx
    }

    pub(crate) fn set_derivation(
        &mut self,
        head: usize,
        incoming_clause: usize,
        premises: Vec<usize>,
    ) {
        debug_assert!(
            head < self.entries.len(),
            "set_derivation: head index {} out of range (entries len {})",
            head,
            self.entries.len()
        );
        debug_assert!(
            premises.iter().all(|&p| p < self.entries.len()),
            "set_derivation: premise index out of range"
        );
        let entry = &mut self.entries[head];
        if entry.incoming_clause.is_none() {
            entry.incoming_clause = Some(incoming_clause);
        }
        if entry.premises.is_empty() {
            entry.premises = premises;
        }
    }
}

#[allow(clippy::unwrap_used)]
#[cfg(test)]
mod tests;
