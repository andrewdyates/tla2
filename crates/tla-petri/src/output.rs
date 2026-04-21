// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
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
}
