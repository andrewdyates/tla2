// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Proof tree representation.
//!
//! This module defines the structure for representing tableau proofs.

use crate::formula::{Formula, Term};
use std::fmt;

/// A proof rule applied in the tableau.
#[derive(Clone, Debug, PartialEq)]
pub enum ProofRule {
    /// Axiom: the branch contains a contradiction (P and ¬P)
    Close(Formula, Formula),

    /// True introduction: ⊤ is always valid
    TrueIntro,

    /// False elimination: ⊥ closes the branch
    FalseElim,

    // Alpha rules (single successor, non-branching)
    /// α₁: A ∧ B ⊢ A, B
    AndElim(Formula),
    /// α₂: ¬(A ∨ B) ⊢ ¬A, ¬B
    NotOr(Formula),
    /// α₃: ¬(A → B) ⊢ A, ¬B
    NotImplies(Formula),
    /// α₄: ¬¬A ⊢ A
    NotNot(Formula),
    /// α₅: A ↔ B ⊢ (A → B), (B → A)
    EquivElim(Formula),

    // Beta rules (two successors, branching)
    /// β₁: A ∨ B ⊢ A | B
    OrElim(Formula),
    /// β₂: ¬(A ∧ B) ⊢ ¬A | ¬B
    NotAnd(Formula),
    /// β₃: A → B ⊢ ¬A | B
    ImpliesElim(Formula),
    /// β₄: ¬(A ↔ B) ⊢ (A ∧ ¬B) | (¬A ∧ B)
    NotEquiv(Formula),

    // Gamma rules (universal instantiation)
    /// γ: ∀x.P(x) ⊢ P(t) for term t
    ForallElim(Formula, Term),

    // Delta rules (existential witness)
    /// δ: ∃x.P(x) ⊢ P(c) for fresh constant c
    ExistsElim(Formula, String),

    /// γ': ¬∃x.P(x) ≡ ∀x.¬P(x)
    NotExists(Formula, String),

    /// δ': ¬∀x.P(x) ≡ ∃x.¬P(x)
    NotForall(Formula, String),

    /// Initial negation of the goal
    Refute(Formula),

    // Equality rules
    /// Reflexivity: t = t is always true
    EqRefl,
    /// ¬(t = t) closes the branch
    NotEqRefl,
    /// Symmetry: t1 = t2 ⊢ t2 = t1
    EqSym(Formula),
    /// Substitution: `t1 = t2, P[t1] ⊢ P[t2]`
    EqSubst(Formula, Formula),
}

impl ProofRule {
    /// Get the principal formula for this rule.
    pub fn principal(&self) -> Option<&Formula> {
        match self {
            ProofRule::Close(f, _) => Some(f),
            ProofRule::TrueIntro => None,
            ProofRule::FalseElim => None,
            ProofRule::AndElim(f) => Some(f),
            ProofRule::NotOr(f) => Some(f),
            ProofRule::NotImplies(f) => Some(f),
            ProofRule::NotNot(f) => Some(f),
            ProofRule::EquivElim(f) => Some(f),
            ProofRule::OrElim(f) => Some(f),
            ProofRule::NotAnd(f) => Some(f),
            ProofRule::ImpliesElim(f) => Some(f),
            ProofRule::NotEquiv(f) => Some(f),
            ProofRule::ForallElim(f, _) => Some(f),
            ProofRule::ExistsElim(f, _) => Some(f),
            ProofRule::NotExists(f, _) => Some(f),
            ProofRule::NotForall(f, _) => Some(f),
            ProofRule::Refute(f) => Some(f),
            ProofRule::EqRefl => None,
            ProofRule::NotEqRefl => None,
            ProofRule::EqSym(f) => Some(f),
            ProofRule::EqSubst(eq, _) => Some(eq),
        }
    }

    /// Get a human-readable name for this rule.
    pub fn name(&self) -> &'static str {
        match self {
            ProofRule::Close(_, _) => "close",
            ProofRule::TrueIntro => "true-intro",
            ProofRule::FalseElim => "false-elim",
            ProofRule::AndElim(_) => "∧-elim",
            ProofRule::NotOr(_) => "¬∨",
            ProofRule::NotImplies(_) => "¬→",
            ProofRule::NotNot(_) => "¬¬",
            ProofRule::EquivElim(_) => "↔-elim",
            ProofRule::OrElim(_) => "∨-elim",
            ProofRule::NotAnd(_) => "¬∧",
            ProofRule::ImpliesElim(_) => "→-elim",
            ProofRule::NotEquiv(_) => "¬↔",
            ProofRule::ForallElim(_, _) => "∀-elim",
            ProofRule::ExistsElim(_, _) => "∃-elim",
            ProofRule::NotExists(_, _) => "¬∃",
            ProofRule::NotForall(_, _) => "¬∀",
            ProofRule::Refute(_) => "refute",
            ProofRule::EqRefl => "=-refl",
            ProofRule::NotEqRefl => "¬=-refl",
            ProofRule::EqSym(_) => "=-sym",
            ProofRule::EqSubst(_, _) => "=-subst",
        }
    }
}

/// A node in the proof tree.
#[derive(Clone, Debug)]
pub struct ProofNode {
    /// The formula(s) at this node (conclusions added to the branch).
    pub conclusions: Vec<Formula>,
    /// The rule applied to derive this node.
    pub rule: ProofRule,
    /// Child proof nodes (0 for closed branches, 1 for alpha, 2 for beta).
    pub children: Vec<ProofNode>,
}

impl ProofNode {
    /// Create a new proof node.
    pub fn new(conclusions: Vec<Formula>, rule: ProofRule, children: Vec<ProofNode>) -> Self {
        ProofNode {
            conclusions,
            rule,
            children,
        }
    }

    /// Create a closed (axiom) node.
    pub fn closed(pos: Formula, neg: Formula) -> Self {
        ProofNode {
            conclusions: vec![],
            rule: ProofRule::Close(pos, neg),
            children: vec![],
        }
    }

    /// Check if this node represents a closed branch.
    pub fn is_closed(&self) -> bool {
        matches!(
            self.rule,
            ProofRule::Close(_, _)
                | ProofRule::FalseElim
                | ProofRule::TrueIntro
                | ProofRule::NotEqRefl
        )
    }

    /// Count the total number of nodes in this proof tree.
    pub fn node_count(&self) -> usize {
        1 + self.children.iter().map(|c| c.node_count()).sum::<usize>()
    }

    /// Get the depth of this proof tree.
    pub fn depth(&self) -> usize {
        if self.children.is_empty() {
            1
        } else {
            1 + self.children.iter().map(|c| c.depth()).max().unwrap_or(0)
        }
    }

    /// Pretty print this proof tree with indentation.
    fn fmt_indented(&self, f: &mut fmt::Formatter<'_>, indent: usize) -> fmt::Result {
        let prefix = "  ".repeat(indent);

        // Write rule name and conclusions
        write!(f, "{}[{}]", prefix, self.rule.name())?;
        if !self.conclusions.is_empty() {
            write!(f, " ")?;
            for (i, c) in self.conclusions.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{:?}", c)?;
            }
        }
        writeln!(f)?;

        // Write children
        for child in &self.children {
            child.fmt_indented(f, indent + 1)?;
        }

        Ok(())
    }
}

impl fmt::Display for ProofNode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_indented(f, 0)
    }
}

/// A complete proof.
#[derive(Clone, Debug)]
pub struct Proof {
    /// The original goal formula.
    pub goal: Formula,
    /// The proof tree (starting from negated goal).
    pub tree: ProofNode,
}

impl Proof {
    /// Create a new proof.
    pub fn new(goal: Formula, tree: ProofNode) -> Self {
        Proof { goal, tree }
    }

    /// Get statistics about this proof.
    pub fn stats(&self) -> ProofStats {
        ProofStats {
            nodes: self.tree.node_count(),
            depth: self.tree.depth(),
        }
    }

    /// Convert this proof to a verifiable certificate.
    ///
    /// The certificate can be independently verified by `tla_cert::CertificateChecker`.
    pub fn to_certificate(&self, id: impl Into<String>) -> tla_cert::Certificate {
        crate::certificate::proof_to_certificate(self, id.into())
    }
}

impl fmt::Display for Proof {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Proof of {:?}", self.goal)?;
        writeln!(f, "---")?;
        write!(f, "{}", self.tree)
    }
}

/// Statistics about a proof.
#[derive(Clone, Debug)]
pub struct ProofStats {
    /// Total number of nodes in the proof tree.
    pub nodes: usize,
    /// Maximum depth of the proof tree.
    pub depth: usize,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_proof_rule_names() {
        let p = Formula::atom("P");
        let q = Formula::atom("Q");

        assert_eq!(ProofRule::Close(p.clone(), q.clone()).name(), "close");
        assert_eq!(ProofRule::AndElim(p.clone()).name(), "∧-elim");
        assert_eq!(ProofRule::OrElim(p.clone()).name(), "∨-elim");
        assert_eq!(
            ProofRule::ForallElim(p.clone(), Term::constant("x")).name(),
            "∀-elim"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_proof_node_closed() {
        let p = Formula::atom("P");
        let not_p = Formula::not(p.clone());

        let node = ProofNode::closed(p, not_p);
        assert!(node.is_closed());
        assert!(node.children.is_empty());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_proof_node_count() {
        let p = Formula::atom("P");

        // Leaf node
        let leaf = ProofNode::closed(p.clone(), Formula::not(p.clone()));
        assert_eq!(leaf.node_count(), 1);
        assert_eq!(leaf.depth(), 1);

        // Node with 2 children
        let parent = ProofNode::new(
            vec![p.clone()],
            ProofRule::OrElim(Formula::or(p.clone(), p.clone())),
            vec![leaf.clone(), leaf.clone()],
        );
        assert_eq!(parent.node_count(), 3);
        assert_eq!(parent.depth(), 2);
    }
}
