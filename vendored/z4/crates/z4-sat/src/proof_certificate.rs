// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Lazily-materialized proof certificate for UNSAT results (Phase 4a, #8077).
//!
//! A `ProofCertificate` is intended to accompany every UNSAT result from the
//! SAT solver. The proof is not reconstructed until the consumer explicitly
//! requests it via [`ProofCertificate::materialize()`], [`ProofCertificate::write_lrat()`],
//! or [`ProofCertificate::write_drat()`].
//!
//! This module defines the certificate type and its public API. The actual
//! integration with `SatResult::Unsat` is deferred to a later phase to avoid
//! a breaking API change.
//!
//! ## Design
//!
//! The certificate holds a `DeferredProof` containing the data needed for
//! backward reconstruction. On first access, the proof is materialized into
//! a sequence of [`ProofStep`] values and cached via `OnceCell`. Subsequent
//! accesses return the cached result.
//!
//! For this initial implementation, `DeferredProof` stores pre-computed steps
//! directly. A future phase will store the minimal solver state needed to
//! invoke `reconstruct_lrat_backward()` on demand.

use std::cell::OnceCell;
use std::io::{self, Write};

use crate::literal::Literal;
use crate::solver::backward_proof::LratStep;

/// A single LRAT proof step in a materialized proof certificate.
///
/// Each step represents a derived clause and the clause IDs of its antecedents
/// (the hints that an LRAT checker needs to verify the derivation).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProofStep {
    /// The clause ID of the derived clause.
    pub clause_id: u64,
    /// The literals of the derived clause (empty for the contradiction step).
    pub literals: Vec<Literal>,
    /// The clause IDs of the antecedent clauses (LRAT hints).
    pub hints: Vec<u64>,
}

impl ProofStep {
    /// Convert to DIMACS literal representation for output.
    fn dimacs_literals(&self) -> Vec<i32> {
        self.literals.iter().map(|lit| lit.to_dimacs()).collect()
    }
}

impl From<LratStep> for ProofStep {
    fn from(step: LratStep) -> Self {
        Self {
            clause_id: step.clause_id,
            literals: step.literals,
            hints: step.hints,
        }
    }
}

/// Compact representation sufficient for backward reconstruction.
///
/// For this initial implementation, stores pre-computed proof steps directly.
/// A future phase will store the minimal solver snapshot needed to invoke
/// `reconstruct_lrat_backward()` on demand, deferring the O(n) reconstruction
/// cost until the proof is actually requested.
pub(crate) struct DeferredProof {
    /// Pre-computed proof steps from backward reconstruction.
    /// In a future phase, this will be replaced with a solver state snapshot.
    steps: Vec<LratStep>,
    /// Whether the backward reconstruction was complete.
    complete: bool,
}

impl DeferredProof {
    /// Create a deferred proof from pre-computed backward reconstruction results.
    pub(crate) fn from_backward_result(steps: Vec<LratStep>, complete: bool) -> Self {
        Self { steps, complete }
    }

    /// Create an empty deferred proof (for cases where no proof data is available).
    pub(crate) fn empty() -> Self {
        Self {
            steps: Vec::new(),
            complete: false,
        }
    }
}

/// A lazily-materialized proof certificate.
///
/// Always present on UNSAT results. The proof is not reconstructed
/// until the consumer explicitly requests it via [`materialize()`](Self::materialize),
/// [`write_lrat()`](Self::write_lrat), or [`write_drat()`](Self::write_drat).
///
/// # Zero-cost path
///
/// If the consumer never inspects the proof (the common case in production),
/// no reconstruction work is performed. Call [`is_deferred()`](Self::is_deferred)
/// to check whether materialization has occurred.
///
/// # Thread safety
///
/// `ProofCertificate` uses `OnceCell` (not `OnceLock`) and is therefore `!Sync`.
/// This is intentional: SAT solver results are typically consumed on a single
/// thread. If cross-thread sharing is needed, wrap in `Arc<Mutex<_>>`.
pub struct ProofCertificate {
    /// LRAT proof steps, lazily materialized from `deferred`.
    steps: OnceCell<Vec<ProofStep>>,
    /// Data needed for deferred backward reconstruction.
    deferred: DeferredProof,
}

impl std::fmt::Debug for ProofCertificate {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ProofCertificate")
            .field("materialized", &self.steps.get().is_some())
            .field("complete", &self.deferred.complete)
            .finish()
    }
}

impl ProofCertificate {
    /// Create a new deferred proof certificate.
    ///
    /// The proof steps are not materialized until explicitly requested.
    pub(crate) fn new(deferred: DeferredProof) -> Self {
        Self {
            steps: OnceCell::new(),
            deferred,
        }
    }

    /// Create a proof certificate from pre-computed backward reconstruction results.
    ///
    /// This is the primary constructor used by the solver after calling
    /// `reconstruct_lrat_backward()`.
    pub(crate) fn from_backward_result(steps: Vec<LratStep>, complete: bool) -> Self {
        Self::new(DeferredProof::from_backward_result(steps, complete))
    }

    /// Create an empty proof certificate (placeholder for cases where no proof
    /// data is available, e.g., UNSAT detected during preprocessing).
    pub(crate) fn empty() -> Self {
        Self::new(DeferredProof::empty())
    }

    /// Materialize the full LRAT proof. First call converts the deferred
    /// representation into proof steps; subsequent calls return the cached result.
    #[must_use]
    pub fn materialize(&self) -> &[ProofStep] {
        self.steps.get_or_init(|| {
            self.deferred
                .steps
                .iter()
                .cloned()
                .map(ProofStep::from)
                .collect()
        })
    }

    /// Write LRAT proof to the given writer.
    ///
    /// LRAT format: `clause_id lit1 lit2 ... 0 hint1 hint2 ... 0`
    ///
    /// Materializes the proof if not already done.
    pub fn write_lrat(&self, w: &mut dyn Write) -> io::Result<()> {
        let steps = self.materialize();
        for step in steps {
            write!(w, "{} ", step.clause_id)?;
            for dimacs_lit in step.dimacs_literals() {
                write!(w, "{dimacs_lit} ")?;
            }
            write!(w, "0 ")?;
            for &hint in &step.hints {
                write!(w, "{hint} ")?;
            }
            writeln!(w, "0")?;
        }
        Ok(())
    }

    /// Write DRAT proof (LRAT without clause IDs or hints) to the given writer.
    ///
    /// DRAT format: `lit1 lit2 ... 0`
    ///
    /// Materializes the proof if not already done.
    pub fn write_drat(&self, w: &mut dyn Write) -> io::Result<()> {
        let steps = self.materialize();
        for step in steps {
            for dimacs_lit in step.dimacs_literals() {
                write!(w, "{dimacs_lit} ")?;
            }
            writeln!(w, "0")?;
        }
        Ok(())
    }

    /// Number of proof steps (materializes if needed).
    #[must_use]
    pub fn step_count(&self) -> usize {
        self.materialize().len()
    }

    /// Returns true if the proof has not yet been materialized (zero cost path).
    #[must_use]
    pub fn is_deferred(&self) -> bool {
        self.steps.get().is_none()
    }

    /// Returns true if the backward reconstruction was complete.
    ///
    /// A complete proof means all antecedent clauses were resolved. An
    /// incomplete proof may have gaps (e.g., clauses lost to garbage collection
    /// or binary clause reasons not yet tracked).
    #[must_use]
    pub fn is_complete(&self) -> bool {
        self.deferred.complete
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::literal::Variable;

    fn make_test_steps() -> Vec<LratStep> {
        let v0 = Variable(0);
        let v1 = Variable(1);
        vec![
            LratStep {
                clause_id: 4,
                literals: vec![Literal::positive(v0), Literal::negative(v1)],
                hints: vec![1, 2],
            },
            LratStep {
                clause_id: 5,
                literals: vec![Literal::negative(v0)],
                hints: vec![3, 4],
            },
            LratStep {
                clause_id: 6,
                literals: vec![],
                hints: vec![4, 5],
            },
        ]
    }

    #[test]
    fn test_proof_certificate_is_deferred_before_materialization() {
        let cert = ProofCertificate::from_backward_result(make_test_steps(), true);
        assert!(
            cert.is_deferred(),
            "certificate should be deferred before materialization"
        );
    }

    #[test]
    fn test_proof_certificate_not_deferred_after_materialization() {
        let cert = ProofCertificate::from_backward_result(make_test_steps(), true);
        let _ = cert.materialize();
        assert!(
            !cert.is_deferred(),
            "certificate should not be deferred after materialization"
        );
    }

    #[test]
    fn test_proof_certificate_materialize_returns_steps() {
        let cert = ProofCertificate::from_backward_result(make_test_steps(), true);
        let steps = cert.materialize();
        assert_eq!(steps.len(), 3);
        assert_eq!(steps[0].clause_id, 4);
        assert_eq!(steps[0].hints, vec![1, 2]);
        assert_eq!(steps[1].clause_id, 5);
        assert_eq!(steps[2].clause_id, 6);
        assert!(steps[2].literals.is_empty(), "last step should be empty clause");
    }

    #[test]
    fn test_proof_certificate_materialize_is_idempotent() {
        let cert = ProofCertificate::from_backward_result(make_test_steps(), true);
        let steps1 = cert.materialize();
        let steps2 = cert.materialize();
        assert_eq!(steps1.len(), steps2.len());
        // Same pointer -- OnceCell caching
        assert!(std::ptr::eq(steps1, steps2));
    }

    #[test]
    fn test_proof_certificate_step_count() {
        let cert = ProofCertificate::from_backward_result(make_test_steps(), true);
        assert_eq!(cert.step_count(), 3);
        // After step_count, no longer deferred
        assert!(!cert.is_deferred());
    }

    #[test]
    fn test_proof_certificate_write_lrat_produces_output() {
        let cert = ProofCertificate::from_backward_result(make_test_steps(), true);
        let mut buf = Vec::new();
        cert.write_lrat(&mut buf)
            .expect("write_lrat should succeed");
        let output = String::from_utf8(buf).expect("should be valid UTF-8");
        assert!(!output.is_empty(), "LRAT output should not be empty");
        // Each line ends with "0\n" (the hint terminator)
        let lines: Vec<&str> = output.lines().collect();
        assert_eq!(lines.len(), 3, "should have 3 proof steps");
        // First line should start with clause_id 4
        assert!(
            lines[0].starts_with("4 "),
            "first line should start with clause ID 4, got: {}",
            lines[0]
        );
        // Last line should be for the empty clause (clause_id 6, no literals)
        assert!(
            lines[2].starts_with("6 0 "),
            "last line should start with '6 0 ' (empty clause), got: {}",
            lines[2]
        );
    }

    #[test]
    fn test_proof_certificate_write_drat_produces_output() {
        let cert = ProofCertificate::from_backward_result(make_test_steps(), true);
        let mut buf = Vec::new();
        cert.write_drat(&mut buf)
            .expect("write_drat should succeed");
        let output = String::from_utf8(buf).expect("should be valid UTF-8");
        assert!(!output.is_empty(), "DRAT output should not be empty");
        let lines: Vec<&str> = output.lines().collect();
        assert_eq!(lines.len(), 3, "should have 3 proof steps");
        // DRAT has no clause IDs or hints -- just literals terminated by 0
        // Last line should be "0" (empty clause, no literals)
        assert_eq!(
            lines[2].trim(),
            "0",
            "last line should be '0' (empty clause), got: {}",
            lines[2]
        );
    }

    #[test]
    fn test_proof_certificate_empty() {
        let cert = ProofCertificate::empty();
        assert!(cert.is_deferred());
        assert!(!cert.is_complete());
        assert_eq!(cert.step_count(), 0);
        assert!(!cert.is_deferred()); // step_count materialized it
    }

    #[test]
    fn test_proof_certificate_is_complete() {
        let complete = ProofCertificate::from_backward_result(make_test_steps(), true);
        assert!(complete.is_complete());

        let incomplete = ProofCertificate::from_backward_result(make_test_steps(), false);
        assert!(!incomplete.is_complete());
    }

    #[test]
    fn test_proof_certificate_debug_format() {
        let cert = ProofCertificate::from_backward_result(make_test_steps(), true);
        let debug_str = format!("{cert:?}");
        assert!(
            debug_str.contains("materialized: false"),
            "debug should show unmaterialized state"
        );
        let _ = cert.materialize();
        let debug_str = format!("{cert:?}");
        assert!(
            debug_str.contains("materialized: true"),
            "debug should show materialized state"
        );
    }

    #[test]
    fn test_proof_step_from_lrat_step() {
        let v0 = Variable(0);
        let lrat_step = LratStep {
            clause_id: 42,
            literals: vec![Literal::positive(v0)],
            hints: vec![10, 20],
        };
        let proof_step = ProofStep::from(lrat_step);
        assert_eq!(proof_step.clause_id, 42);
        assert_eq!(proof_step.literals.len(), 1);
        assert_eq!(proof_step.hints, vec![10, 20]);
    }
}
