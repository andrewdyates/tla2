// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! MCC output formatting.
//!
//! Produces `FORMULA` lines per the MCC output specification:
//! `FORMULA <name> <verdict> TECHNIQUES <list>`

use std::fmt;

/// MCC formula verdict.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Verdict {
    True,
    False,
    CannotCompute,
}

impl fmt::Display for Verdict {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::True => write!(f, "TRUE"),
            Self::False => write!(f, "FALSE"),
            Self::CannotCompute => write!(f, "CANNOT_COMPUTE"),
        }
    }
}

/// MCC technique tags.
///
/// The MCC specification requires each `FORMULA` line to end with
/// `TECHNIQUES <list>` where `<list>` is a space-separated subset of:
/// STRUCTURAL, EXPLICIT, SAT_SMT, DECISION_DIAGRAMS, TOPOLOGICAL, etc.
///
/// Multiple techniques may apply to a single formula (e.g., structural
/// simplification followed by explicit BFS exploration).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Techniques {
    tags: Vec<Technique>,
}

/// Individual MCC technique tags.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum Technique {
    /// Structural reductions (dead transitions, constant places, agglomeration).
    Structural,
    /// Explicit-state BFS/DFS exploration.
    Explicit,
    /// SAT/SMT-based analysis (z4, BMC, PDR).
    SatSmt,
    /// Decision diagram-based analysis (BDD, MDD).
    DecisionDiagrams,
    /// Topological / LP state-equation analysis.
    Topological,
}

impl fmt::Display for Technique {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Structural => write!(f, "STRUCTURAL"),
            Self::Explicit => write!(f, "EXPLICIT"),
            Self::SatSmt => write!(f, "SAT_SMT"),
            Self::DecisionDiagrams => write!(f, "DECISION_DIAGRAMS"),
            Self::Topological => write!(f, "TOPOLOGICAL"),
        }
    }
}

impl Techniques {
    /// Create a technique set with a single technique.
    #[must_use]
    pub fn single(technique: Technique) -> Self {
        Self {
            tags: vec![technique],
        }
    }

    /// Create a technique set defaulting to EXPLICIT.
    #[must_use]
    pub fn explicit() -> Self {
        Self::single(Technique::Explicit)
    }

    /// Add a technique to the set. Deduplicates.
    #[must_use]
    pub fn with(mut self, technique: Technique) -> Self {
        if !self.tags.contains(&technique) {
            self.tags.push(technique);
        }
        self
    }

    /// Format the technique list for MCC output (space-separated).
    #[must_use]
    pub fn as_mcc_str(&self) -> String {
        if self.tags.is_empty() {
            return String::from("EXPLICIT");
        }
        self.tags
            .iter()
            .map(|t| t.to_string())
            .collect::<Vec<_>>()
            .join(" ")
    }
}

impl Default for Techniques {
    fn default() -> Self {
        Self::explicit()
    }
}

/// Format a single FORMULA output line.
#[must_use]
pub fn formula_line(model_name: &str, examination: &str, verdict: Verdict) -> String {
    format!("FORMULA {model_name}-{examination} {verdict} TECHNIQUES EXPLICIT")
}

/// Format a CANNOT_COMPUTE line for all examinations of a model.
#[must_use]
pub fn cannot_compute_line(model_name: &str, examination: &str) -> String {
    formula_line(model_name, examination, Verdict::CannotCompute)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_verdict_display_true() {
        assert_eq!(Verdict::True.to_string(), "TRUE");
    }

    #[test]
    fn test_verdict_display_false() {
        assert_eq!(Verdict::False.to_string(), "FALSE");
    }

    #[test]
    fn test_verdict_display_cannot_compute() {
        assert_eq!(Verdict::CannotCompute.to_string(), "CANNOT_COMPUTE");
    }

    #[test]
    fn test_formula_line_true() {
        let line = formula_line("ModelA-PT-001", "ReachabilityFireability-00", Verdict::True);
        assert_eq!(
            line,
            "FORMULA ModelA-PT-001-ReachabilityFireability-00 TRUE TECHNIQUES EXPLICIT"
        );
    }

    #[test]
    fn test_formula_line_false() {
        let line = formula_line(
            "ModelA-PT-001",
            "ReachabilityFireability-01",
            Verdict::False,
        );
        assert_eq!(
            line,
            "FORMULA ModelA-PT-001-ReachabilityFireability-01 FALSE TECHNIQUES EXPLICIT"
        );
    }

    #[test]
    fn test_cannot_compute_line_format() {
        let line = cannot_compute_line("ModelA-PT-001", "StateSpace");
        assert_eq!(
            line,
            "FORMULA ModelA-PT-001-StateSpace CANNOT_COMPUTE TECHNIQUES EXPLICIT"
        );
    }

    #[test]
    fn test_formula_line_contains_required_mcc_tokens() {
        // MCC parser requires: "FORMULA", verdict in {TRUE,FALSE,CANNOT_COMPUTE}, "TECHNIQUES"
        let line = formula_line("X", "Y", Verdict::True);
        assert!(line.starts_with("FORMULA "));
        assert!(line.contains(" TECHNIQUES "));
    }

    // -- Techniques tests --

    #[test]
    fn test_technique_display() {
        assert_eq!(Technique::Structural.to_string(), "STRUCTURAL");
        assert_eq!(Technique::Explicit.to_string(), "EXPLICIT");
        assert_eq!(Technique::SatSmt.to_string(), "SAT_SMT");
        assert_eq!(Technique::DecisionDiagrams.to_string(), "DECISION_DIAGRAMS");
        assert_eq!(Technique::Topological.to_string(), "TOPOLOGICAL");
    }

    #[test]
    fn test_techniques_default_is_explicit() {
        let t = Techniques::default();
        assert_eq!(t.as_mcc_str(), "EXPLICIT");
    }

    #[test]
    fn test_techniques_single() {
        let t = Techniques::single(Technique::Structural);
        assert_eq!(t.as_mcc_str(), "STRUCTURAL");
    }

    #[test]
    fn test_techniques_multiple() {
        let t = Techniques::single(Technique::Structural).with(Technique::Explicit);
        assert_eq!(t.as_mcc_str(), "STRUCTURAL EXPLICIT");
    }

    #[test]
    fn test_techniques_deduplicates() {
        let t = Techniques::single(Technique::Explicit)
            .with(Technique::Explicit)
            .with(Technique::Explicit);
        assert_eq!(t.as_mcc_str(), "EXPLICIT");
    }

    #[test]
    fn test_techniques_empty_fallback() {
        let t = Techniques { tags: vec![] };
        assert_eq!(t.as_mcc_str(), "EXPLICIT");
    }
}
