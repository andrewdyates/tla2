// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tableau prover.
//!
//! This module implements the main proof search algorithm using the tableau method.

use crate::formula::{Formula, Term};
use crate::proof::{Proof, ProofNode, ProofRule};
use crate::rules::{self, FormulaKind, RuleResult};
use std::collections::HashSet;
use std::time::{Duration, Instant};

/// Configuration for the prover.
#[derive(Clone, Debug)]
pub struct ProverConfig {
    /// Maximum search depth.
    pub max_depth: usize,
    /// Maximum number of nodes to expand.
    pub max_nodes: usize,
    /// Timeout for proof search.
    pub timeout: Duration,
    /// Maximum gamma rule applications per formula.
    pub max_gamma_instances: usize,
}

impl Default for ProverConfig {
    fn default() -> Self {
        ProverConfig {
            max_depth: 100,
            max_nodes: 10000,
            timeout: Duration::from_secs(60),
            max_gamma_instances: 3,
        }
    }
}

/// Result of a proof attempt.
#[derive(Clone, Debug)]
pub enum ProofResult {
    /// The formula is valid (proof found).
    Valid(Box<Proof>),
    /// The formula is invalid or unprovable.
    Invalid {
        /// Reason for failure.
        reason: String,
    },
    /// Proof search was inconclusive.
    Unknown {
        /// Reason for giving up.
        reason: String,
    },
}

impl ProofResult {
    /// Check if the proof succeeded.
    pub fn is_valid(&self) -> bool {
        matches!(self, ProofResult::Valid(_))
    }
}

/// A branch in the tableau (set of formulas on a path).
#[derive(Clone, Debug)]
struct Branch {
    /// Formulas on this branch.
    formulas: Vec<Formula>,
    /// Positive literals.
    positive: HashSet<Formula>,
    /// Negative literals (the inner formula).
    negative: HashSet<Formula>,
    /// Skolem constant counter.
    skolem_counter: usize,
    /// Gamma instance counts per formula.
    gamma_counts: std::collections::HashMap<String, usize>,
    /// Terms available for gamma instantiation.
    terms: Vec<Term>,
}

impl Branch {
    fn new() -> Self {
        Branch {
            formulas: Vec::new(),
            positive: HashSet::new(),
            negative: HashSet::new(),
            skolem_counter: 0,
            gamma_counts: std::collections::HashMap::new(),
            terms: Vec::new(),
        }
    }

    /// Add a formula to the branch.
    fn add(&mut self, formula: Formula) {
        // Collect terms for gamma instantiation
        self.collect_terms(&formula);

        // Track literals for contradiction detection
        match &formula {
            Formula::Atom(_) | Formula::Pred(_, _) | Formula::Eq(_, _) | Formula::True => {
                self.positive.insert(formula.clone());
            }
            Formula::Not(inner) => match &**inner {
                Formula::Atom(_) | Formula::Pred(_, _) | Formula::Eq(_, _) | Formula::False => {
                    self.negative.insert((**inner).clone());
                }
                _ => {}
            },
            _ => {}
        }

        self.formulas.push(formula);
    }

    /// Collect terms from a formula for gamma instantiation.
    fn collect_terms(&mut self, formula: &Formula) {
        match formula {
            Formula::Pred(_, _) | Formula::Eq(_, _) => {
                for term in Branch::extract_terms(formula) {
                    if !self.terms.contains(&term) {
                        self.terms.push(term);
                    }
                }
            }
            Formula::Not(inner) => self.collect_terms(inner),
            Formula::And(a, b)
            | Formula::Or(a, b)
            | Formula::Implies(a, b)
            | Formula::Equiv(a, b) => {
                self.collect_terms(a);
                self.collect_terms(b);
            }
            Formula::Forall(_, body) | Formula::Exists(_, body) => {
                self.collect_terms(body);
            }
            _ => {}
        }
    }

    fn extract_terms(formula: &Formula) -> Vec<Term> {
        match formula {
            Formula::Pred(_, args) => args.clone(),
            Formula::Eq(t1, t2) => vec![t1.clone(), t2.clone()],
            Formula::Not(inner) => Branch::extract_terms(inner),
            _ => vec![],
        }
    }

    /// Generate a fresh Skolem constant.
    fn fresh_skolem(&mut self) -> String {
        let name = format!("sk{}", self.skolem_counter);
        self.skolem_counter += 1;
        name
    }

    /// Check if the branch is closed (contains a contradiction).
    fn is_closed(&self) -> Option<(Formula, Formula)> {
        // Check for P and ¬P
        for pos in &self.positive {
            if self.negative.contains(pos) {
                return Some((pos.clone(), Formula::not(pos.clone())));
            }
        }

        // Check for True/False contradiction
        if self.positive.contains(&Formula::True) && self.negative.contains(&Formula::True) {
            return Some((Formula::True, Formula::not(Formula::True)));
        }
        if self.positive.contains(&Formula::False) {
            return Some((Formula::False, Formula::False));
        }
        if self.negative.contains(&Formula::False) {
            // ¬False is True, so we need to check positive for True contradiction
        }

        None
    }

    /// Check if the branch contains ¬(t = t) which is a contradiction by reflexivity.
    fn has_reflexivity_contradiction(&self) -> bool {
        for f in &self.formulas {
            if let Formula::Not(inner) = f {
                if let Formula::Eq(t1, t2) = &**inner {
                    if t1 == t2 {
                        return true;
                    }
                }
            }
        }
        false
    }

    /// Get the next non-literal formula to decompose.
    fn next_decomposable(&self) -> Option<(usize, &Formula)> {
        // Priority: alpha > delta > beta > gamma
        // (Alpha and delta don't branch, so prefer them)

        // First pass: alpha formulas
        for (i, f) in self.formulas.iter().enumerate() {
            if matches!(rules::classify(f), FormulaKind::Alpha) {
                return Some((i, f));
            }
        }

        // Second pass: delta formulas
        for (i, f) in self.formulas.iter().enumerate() {
            if matches!(rules::classify(f), FormulaKind::Delta) {
                return Some((i, f));
            }
        }

        // Third pass: beta formulas
        for (i, f) in self.formulas.iter().enumerate() {
            if matches!(rules::classify(f), FormulaKind::Beta) {
                return Some((i, f));
            }
        }

        // Fourth pass: gamma formulas (if we have terms to instantiate with)
        for (i, f) in self.formulas.iter().enumerate() {
            if matches!(rules::classify(f), FormulaKind::Gamma) {
                return Some((i, f));
            }
        }

        None
    }
}

/// The tableau prover.
pub struct Prover {
    /// Number of nodes expanded.
    nodes_expanded: usize,
    /// Start time.
    start_time: Option<Instant>,
}

impl Prover {
    /// Create a new prover.
    pub fn new() -> Self {
        Prover {
            nodes_expanded: 0,
            start_time: None,
        }
    }

    /// Prove a formula.
    pub fn prove(&mut self, goal: &Formula, config: ProverConfig) -> ProofResult {
        self.nodes_expanded = 0;
        self.start_time = Some(Instant::now());

        // Negate the goal for proof by refutation
        let negated = goal.negate();

        let mut branch = Branch::new();
        branch.add(negated.clone());

        // Add a default term if none available
        if branch.terms.is_empty() {
            branch.terms.push(Term::constant("c0"));
        }

        match self.prove_branch(&mut branch, &config, 0) {
            Some(tree) => {
                let root =
                    ProofNode::new(vec![negated], ProofRule::Refute(goal.clone()), vec![tree]);
                ProofResult::Valid(Box::new(Proof::new(goal.clone(), root)))
            }
            None => ProofResult::Unknown {
                reason: "Could not close all branches".to_string(),
            },
        }
    }

    /// Try to close a branch, returning the proof tree if successful.
    fn prove_branch(
        &mut self,
        branch: &mut Branch,
        config: &ProverConfig,
        depth: usize,
    ) -> Option<ProofNode> {
        // Check limits
        if depth > config.max_depth {
            return None;
        }
        if self.nodes_expanded > config.max_nodes {
            return None;
        }
        if let Some(start) = self.start_time {
            if start.elapsed() > config.timeout {
                return None;
            }
        }

        self.nodes_expanded += 1;

        // Check for immediate closure
        if let Some((pos, neg)) = branch.is_closed() {
            return Some(ProofNode::closed(pos, neg));
        }

        // Check for reflexivity contradiction: ¬(t = t)
        if branch.has_reflexivity_contradiction() {
            return Some(ProofNode::new(vec![], ProofRule::NotEqRefl, vec![]));
        }

        // Check for False on the branch
        for f in &branch.formulas {
            if matches!(f, Formula::False) {
                return Some(ProofNode::new(vec![], ProofRule::FalseElim, vec![]));
            }
            if let Formula::Not(inner) = f {
                if matches!(**inner, Formula::True) {
                    return Some(ProofNode::new(vec![], ProofRule::FalseElim, vec![]));
                }
            }
        }

        // Find a formula to decompose
        let decomposable = branch.next_decomposable();

        if let Some((idx, formula)) = decomposable {
            let formula = formula.clone();
            let kind = rules::classify(&formula);

            match kind {
                FormulaKind::Alpha => {
                    if let Some(RuleResult::Alpha { rule, conclusions }) =
                        rules::try_alpha(&formula)
                    {
                        // Remove the decomposed formula (keep others)
                        let mut new_branch = branch.clone();
                        new_branch.formulas.remove(idx);

                        // Add conclusions
                        for c in &conclusions {
                            new_branch.add(c.clone());
                        }

                        // Recurse
                        if let Some(child) = self.prove_branch(&mut new_branch, config, depth + 1) {
                            return Some(ProofNode::new(conclusions, rule, vec![child]));
                        }
                    }
                }

                FormulaKind::Beta => {
                    if let Some(RuleResult::Beta { rule, left, right }) = rules::try_beta(&formula)
                    {
                        // Left branch
                        let mut left_branch = branch.clone();
                        left_branch.formulas.remove(idx);
                        for c in &left {
                            left_branch.add(c.clone());
                        }

                        // Right branch
                        let mut right_branch = branch.clone();
                        right_branch.formulas.remove(idx);
                        for c in &right {
                            right_branch.add(c.clone());
                        }

                        // Both branches must close
                        let left_proof = self.prove_branch(&mut left_branch, config, depth + 1)?;
                        let right_proof =
                            self.prove_branch(&mut right_branch, config, depth + 1)?;

                        let conclusions = left.into_iter().chain(right).collect();
                        return Some(ProofNode::new(
                            conclusions,
                            rule,
                            vec![left_proof, right_proof],
                        ));
                    }
                }

                FormulaKind::Delta => {
                    let fresh = branch.fresh_skolem();
                    if let Some(RuleResult::Delta {
                        rule,
                        conclusions,
                        witness,
                    }) = rules::try_delta(&formula, &fresh)
                    {
                        let mut new_branch = branch.clone();
                        new_branch.formulas.remove(idx);

                        // Add the fresh constant as a term for gamma instantiation
                        new_branch.terms.push(Term::constant(&witness));

                        for c in &conclusions {
                            new_branch.add(c.clone());
                        }

                        if let Some(child) = self.prove_branch(&mut new_branch, config, depth + 1) {
                            return Some(ProofNode::new(conclusions, rule, vec![child]));
                        }
                    }
                }

                FormulaKind::Gamma => {
                    // Track how many times we've instantiated this formula
                    let formula_key = format!("{:?}", formula);
                    let count = *branch.gamma_counts.get(&formula_key).unwrap_or(&0);

                    if count < config.max_gamma_instances && !branch.terms.is_empty() {
                        // Try each available term
                        let terms = branch.terms.clone();
                        for term in terms.iter() {
                            if let Some(RuleResult::Gamma {
                                rule, conclusions, ..
                            }) = rules::try_gamma(&formula, term)
                            {
                                let mut new_branch = branch.clone();
                                // Keep the gamma formula for potential re-instantiation
                                // but increment its count
                                *new_branch
                                    .gamma_counts
                                    .entry(formula_key.clone())
                                    .or_insert(0) += 1;

                                for c in &conclusions {
                                    new_branch.add(c.clone());
                                }

                                if let Some(child) =
                                    self.prove_branch(&mut new_branch, config, depth + 1)
                                {
                                    return Some(ProofNode::new(conclusions, rule, vec![child]));
                                }
                            }
                        }
                    }
                }

                _ => {}
            }
        }

        // No more rules to apply, branch is open
        None
    }
}

impl Default for Prover {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
#[path = "prover_tests.rs"]
mod tests;
