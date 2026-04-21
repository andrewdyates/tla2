// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Symmetric `Safe`-result cross-validation (#4315).
//!
//! This is the portfolio-layer defense-in-depth gate that closes the systemic
//! blind spot exposed by TL54's #4310 P0 (false UNSAT via circular_pointer).
//! Before TL78 landed this module, `runner.rs:312-331` validated *unsafe*
//! witnesses by simulating the returned counterexample trace against the
//! circuit, rejecting a result whose witness did not actually violate the
//! property — but the symmetric path for `Safe` had no validator at all. Any
//! engine that said "Safe" was trusted unconditionally.
//!
//! Four witness shapes are recognized:
//! * `SafeWitness::InductiveInvariant { lemmas, .. }` — a CNF inductive
//!   invariant (the standard IC3 proof witness). The validator re-runs the
//!   three inductive-invariant checks against a **fresh** independent SAT
//!   backend (SimpleSolver for small circuits, Z4NoPreprocess for larger
//!   ones — same tiering as IC3's internal validator):
//!   1. `init ⇒ inv`
//!   2. `inv ∧ T ⇒ inv'`
//!   3. `inv ⇒ ¬bad`
//!   This is the path that would have caught #4310 (false UNSAT via
//!   circular_pointer): an unsound invariant fails one of the three checks.
//! * `SafeWitness::Trivial` — the property is trivially safe (no bad lits,
//!   or all bad lits are constant FALSE). Validated by re-checking the
//!   circuit's bad-lit structure directly.
//! * `SafeWitness::EngineVerified { engine }` — engine ran its own internal
//!   safety check (e.g. BMC-with-bound, k-induction inductive step) but
//!   does not emit a formal invariant we can re-verify. Accepted with a log
//!   line. Future work: graduate k-induction to emit an `InductiveInvariant`
//!   so it joins the fully-validated path.
//! * `SafeWitness::Unwitnessed` — engine cannot prove Safe and made no
//!   internal safety claim. The portfolio conservatively **downgrades the
//!   result to `Unknown`** unless another engine has already produced a
//!   witnessed corroborating `Safe`.

use std::time::{Duration, Instant};

use crate::sat_types::{Lit, SatResult, SatSolver, SimpleSolver, SolverBackend};
use crate::transys::Transys;

/// Proof witness attached to a `Safe` verdict from an engine.
#[derive(Debug, Clone)]
pub enum SafeWitness {
    /// Engine produced an inductive invariant expressed as CNF clauses
    /// (each inner `Vec<Lit>` is one disjunctive clause). `depth` is the
    /// convergence depth (IC3 frame index) reported by the engine. This is
    /// the only witness shape that gets full independent SAT re-verification
    /// — a rejection here is a SOUNDNESS ALERT.
    InductiveInvariant {
        lemmas: Vec<Vec<Lit>>,
        depth: usize,
    },
    /// Property is trivially safe: `bad_lits` is empty or all bad lits are
    /// constant FALSE. No inductive invariant is needed — the circuit cannot
    /// reach a bad state by construction. Validator re-checks bad_lits
    /// directly and rejects if the claim is false.
    Trivial,
    /// Engine does not emit a formal proof witness but ran its own internal
    /// safety check (BMC-with-bound, k-induction inductive step, etc.). The
    /// validator cannot re-verify this independently, so it accepts it but
    /// logs that no symmetric check was performed. The conservative downgrade
    /// path is reserved for `Unwitnessed`, which signals "engine made no
    /// promise at all".
    EngineVerified { engine: &'static str },
    /// Engine cannot (or did not) produce a proof witness. Downgrade to
    /// `Unknown` unless another engine produces a witnessed `Safe`.
    Unwitnessed,
}

/// Outcome of running `validate_safe()` on a proposed `Safe` verdict.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SafeValidation {
    /// Witness passed all independent checks — accept the `Safe` verdict.
    Accepted,
    /// Validator ran out of budget / cancellation — indeterminate. Caller
    /// should not accept this as a proof but can keep waiting for sibling
    /// engines.
    Indeterminate { reason: String },
    /// Witness was actively rejected by an independent check. SOUNDNESS ALERT.
    Rejected { reason: String },
    /// Engine did not expose a witness. Conservative downgrade to `Unknown`.
    Downgrade { reason: String },
}

impl SafeValidation {
    /// `true` iff the portfolio should emit the original `Safe` verdict.
    #[inline]
    pub fn accepted(&self) -> bool {
        matches!(self, SafeValidation::Accepted)
    }
}

/// Default validation budget for `validate_safe()`. Matches the small-circuit
/// tier of IC3's internal validator (`ic3/validate.rs:51`).
const DEFAULT_VALIDATE_BUDGET: Duration = Duration::from_secs(10);

/// Symmetric validator for `Safe` verdicts — the counterpart to
/// `Transys::verify_witness()` for the `Unsafe` path.
///
/// Runs on a fresh independent SAT backend (no state shared with the
/// producing engine) so a bug in the producing engine's solver cannot
/// silently make the validator agree.
pub fn validate_safe(witness: &SafeWitness, ts: &Transys) -> SafeValidation {
    validate_safe_with_budget(witness, ts, DEFAULT_VALIDATE_BUDGET)
}

/// Same as [`validate_safe`] but with an explicit validation budget.
pub fn validate_safe_with_budget(
    witness: &SafeWitness,
    ts: &Transys,
    budget: Duration,
) -> SafeValidation {
    match witness {
        SafeWitness::Unwitnessed => SafeValidation::Downgrade {
            reason: "engine returned Safe without a proof witness (#4315 \
                 conservative fallback)"
                .into(),
        },
        SafeWitness::EngineVerified { engine } => {
            eprintln!(
                "portfolio validate_safe: accepting {engine}'s internal \
                 safety proof without independent re-verification (no formal \
                 witness to check; #4315 logged)"
            );
            SafeValidation::Accepted
        }
        SafeWitness::Trivial => validate_trivial_safe(ts),
        SafeWitness::InductiveInvariant { lemmas, depth } => {
            validate_inductive_invariant(ts, lemmas, *depth, budget)
        }
    }
}

/// Validate a `Safe` claim whose justification is "the property is trivially
/// safe". Re-checks the bad-lit structure directly from `ts`; rejects any
/// non-constant bad literal.
fn validate_trivial_safe(ts: &Transys) -> SafeValidation {
    if ts.bad_lits.is_empty() {
        return SafeValidation::Accepted;
    }
    for &bad in &ts.bad_lits {
        if bad != Lit::FALSE {
            return SafeValidation::Rejected {
                reason: format!(
                    "trivial-safe witness rejected: bad_lit {bad:?} is \
                     not constant FALSE (there are {} non-trivial bad lits)",
                    ts.bad_lits.iter().filter(|l| **l != Lit::FALSE).count(),
                ),
            };
        }
    }
    SafeValidation::Accepted
}

/// Inductive-invariant validator. Mirrors `Ic3Engine::validate_invariant_budgeted`
/// but runs on a fresh solver with no access to the engine's internal state:
/// the only inputs are the `Transys` (trust-rooted here — it is what the
/// engines themselves were checking) and the `lemmas` that the engine claims
/// as its proof.
fn validate_inductive_invariant(
    ts: &Transys,
    lemmas: &[Vec<Lit>],
    depth: usize,
    budget: Duration,
) -> SafeValidation {
    let start = Instant::now();
    let should_abort = |s: &Instant| -> bool { s.elapsed() > budget };

    // Degenerate case: an empty lemma set cannot prove a non-trivial property.
    // If bad_lits is empty / all FALSE we would already have taken the
    // `Trivial` path above — so reject here unless the property really is
    // trivial (defense-in-depth).
    if lemmas.is_empty() {
        // Treat "empty lemmas" as an implicit trivial claim and re-verify.
        return validate_trivial_safe(ts).map_reject_reason(|r| {
            format!(
                "inductive-invariant witness has 0 lemmas AND property is \
                 not trivially safe: {r}",
            )
        });
    }

    eprintln!(
        "portfolio validate_safe: checking {} lemmas (depth={}, budget={:.1}s)",
        lemmas.len(),
        depth,
        budget.as_secs_f64(),
    );

    // Build next-var map for priming. IC3's `next_vars` is cached on the
    // engine; here we derive it from `ts.next_state`'s next-state literals.
    // Each latch maps to a (possibly constant) next-state literal. We prime
    // a lemma by substituting each latch `l` with its next-state literal,
    // flipping polarity as needed. For non-latch vars (inputs, gate outputs)
    // we leave them unchanged — this mirrors `validate_invariant_budgeted`'s
    // fallback for literals whose variable is not a current-state latch.
    //
    // IC3's `next_vars` is a `latch -> next_var` map; here we have
    // `next_state: latch -> Lit`, which is strictly more general (the
    // literal can carry polarity). Use the polarity-aware substitution.
    let prime_lit = |l: Lit| -> Lit {
        let var = l.var();
        if let Some(&nxt) = ts.next_state.get(&var) {
            if l.is_positive() {
                nxt
            } else {
                !nxt
            }
        } else {
            l
        }
    };

    let solver_factory = || -> Box<dyn SatSolver> {
        if ts.latch_vars.len() <= 60 {
            let mut s = SimpleSolver::new();
            s.ensure_vars(ts.max_var + 1);
            Box::new(s)
        } else {
            SolverBackend::Z4NoPreprocess.make_solver_no_inprocessing(ts.max_var + 1)
        }
    };

    // Check 1: Init ⇒ Inv.
    //
    // For each lemma L = l1 ∨ l2 ∨ …, assert !L (the negated cube) as
    // assumptions and check SAT over init ∧ T ∧ constraints. If SAT, init
    // admits a state that violates the lemma — the invariant claim is
    // unsound.
    {
        let mut solver = solver_factory();
        solver.add_clause(&[Lit::TRUE]);
        for clause in &ts.init_clauses {
            solver.add_clause(&clause.lits);
        }
        for clause in &ts.trans_clauses {
            solver.add_clause(&clause.lits);
        }
        for &c in &ts.constraint_lits {
            solver.add_clause(&[c]);
        }
        for (i, lemma) in lemmas.iter().enumerate() {
            if should_abort(&start) {
                return SafeValidation::Indeterminate {
                    reason: format!(
                        "validate_safe budget exceeded at Init⇒Inv check \
                         lemma {}/{} ({:.1}s)",
                        i,
                        lemmas.len(),
                        start.elapsed().as_secs_f64(),
                    ),
                };
            }
            let neg: Vec<Lit> = lemma.iter().map(|l| !*l).collect();
            match solver.solve(&neg) {
                SatResult::Sat => {
                    return SafeValidation::Rejected {
                        reason: format!(
                            "Init does NOT imply lemma {}: {:?} (SOUNDNESS \
                             ALERT — engine claimed inductive invariant but \
                             initial states violate it)",
                            i, lemma,
                        ),
                    };
                }
                SatResult::Unsat => {}
                SatResult::Unknown => {
                    return SafeValidation::Indeterminate {
                        reason: format!(
                            "validator SAT solver returned Unknown during \
                             Init⇒Inv check at lemma {i}"
                        ),
                    };
                }
            }
        }
    }

    // Check 2: Inv ∧ T ⇒ Inv' (consecution / inductiveness).
    //
    // Add every lemma as a clause over current-state vars, then for each
    // lemma check that its primed negation is UNSAT.
    {
        let mut solver = solver_factory();
        solver.add_clause(&[Lit::TRUE]);
        for clause in &ts.trans_clauses {
            solver.add_clause(&clause.lits);
        }
        for &c in &ts.constraint_lits {
            solver.add_clause(&[c]);
        }
        for lemma in lemmas {
            solver.add_clause(lemma);
        }
        for (i, lemma) in lemmas.iter().enumerate() {
            if should_abort(&start) {
                return SafeValidation::Indeterminate {
                    reason: format!(
                        "validate_safe budget exceeded at Inv∧T⇒Inv' check \
                         lemma {}/{} ({:.1}s)",
                        i,
                        lemmas.len(),
                        start.elapsed().as_secs_f64(),
                    ),
                };
            }
            let neg_primed: Vec<Lit> = lemma.iter().map(|l| !prime_lit(*l)).collect();
            match solver.solve(&neg_primed) {
                SatResult::Sat => {
                    return SafeValidation::Rejected {
                        reason: format!(
                            "Inv ∧ T does NOT preserve lemma {}: {:?} \
                             (SOUNDNESS ALERT — invariant is not inductive, \
                             #4315 symmetric validator disagrees with engine)",
                            i, lemma,
                        ),
                    };
                }
                SatResult::Unsat => {}
                SatResult::Unknown => {
                    return SafeValidation::Indeterminate {
                        reason: format!(
                            "validator SAT solver returned Unknown during \
                             Inv∧T⇒Inv' check at lemma {i}"
                        ),
                    };
                }
            }
        }
    }

    // Check 3: Inv ⇒ ¬bad.
    {
        let mut solver = solver_factory();
        solver.add_clause(&[Lit::TRUE]);
        for clause in &ts.trans_clauses {
            solver.add_clause(&clause.lits);
        }
        for &c in &ts.constraint_lits {
            solver.add_clause(&[c]);
        }
        for lemma in lemmas {
            solver.add_clause(lemma);
        }
        for &bad in &ts.bad_lits {
            if should_abort(&start) {
                return SafeValidation::Indeterminate {
                    reason: format!(
                        "validate_safe budget exceeded at Inv⇒¬bad check \
                         ({:.1}s)",
                        start.elapsed().as_secs_f64(),
                    ),
                };
            }
            // Constant-FALSE bad lit is trivially non-reachable.
            if bad == Lit::FALSE {
                continue;
            }
            match solver.solve(&[bad]) {
                SatResult::Sat => {
                    return SafeValidation::Rejected {
                        reason: format!(
                            "Inv admits a bad state: bad_lit={:?} (SOUNDNESS \
                             ALERT — engine's invariant does NOT prove the \
                             property)",
                            bad,
                        ),
                    };
                }
                SatResult::Unsat => {}
                SatResult::Unknown => {
                    return SafeValidation::Indeterminate {
                        reason: format!(
                            "validator SAT solver returned Unknown during \
                             Inv⇒¬bad check for bad_lit={bad:?}"
                        ),
                    };
                }
            }
        }
    }

    eprintln!(
        "portfolio validate_safe: ACCEPTED inductive invariant ({} lemmas, \
         depth={}, elapsed={:.3}s)",
        lemmas.len(),
        depth,
        start.elapsed().as_secs_f64(),
    );
    SafeValidation::Accepted
}

impl SafeValidation {
    /// Internal helper: map a `Rejected` reason through a transform while
    /// preserving all other variants unchanged.
    fn map_reject_reason<F: FnOnce(String) -> String>(self, f: F) -> Self {
        match self {
            SafeValidation::Rejected { reason } => SafeValidation::Rejected { reason: f(reason) },
            other => other,
        }
    }
}

// -----------------------------------------------------------------------------
// Tests — unit tests for validate_safe. See the portfolio tests module for
// the integration tests that wire this into `runner::portfolio_check`.
// -----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse_aag;
    use crate::transys::Transys;

    /// An `Unwitnessed` verdict must always downgrade — this is the core
    /// conservative fallback that would have caught #4310 on its own.
    #[test]
    fn test_validate_safe_unwitnessed_downgrades() {
        // Trivially safe circuit — but we pretend the engine couldn't emit
        // a witness.
        let circuit = parse_aag("aag 0 0 0 1 0\n0\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let outcome = validate_safe(&SafeWitness::Unwitnessed, &ts);
        match outcome {
            SafeValidation::Downgrade { .. } => {}
            other => panic!("expected Downgrade for Unwitnessed, got {other:?}"),
        }
    }

    /// Trivial-safe witness on a circuit with no bad properties must be
    /// accepted.
    #[test]
    fn test_validate_safe_trivial_passes() {
        // aag 0 0 0 1 0 with bad=0 (constant FALSE).
        let circuit = parse_aag("aag 0 0 0 1 0\n0\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let outcome = validate_safe(&SafeWitness::Trivial, &ts);
        assert_eq!(outcome, SafeValidation::Accepted);
    }

    /// Trivial-safe witness on a circuit whose bad is a real signal must be
    /// REJECTED — you cannot claim "trivially safe" on a non-trivial
    /// property.
    #[test]
    fn test_validate_safe_trivial_on_nontrivial_rejected() {
        // aag 1 0 1 0 0 1: one latch, bad = latch. Not trivially safe.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let outcome = validate_safe(&SafeWitness::Trivial, &ts);
        match outcome {
            SafeValidation::Rejected { .. } => {}
            other => panic!("expected Rejected, got {other:?}"),
        }
    }

    /// Legitimate inductive invariant: latch stays at 0 → invariant !latch
    /// → proves the property.
    #[test]
    fn test_validate_safe_inductive_invariant_passes() {
        // aag 1 0 1 0 0 1: latch var = 2, next = 0 (stuck at 0), bad = latch.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        // The inductive invariant is just the clause {!latch}: i.e. latch
        // is always false.
        let latch = ts.latch_vars[0];
        let lemmas = vec![vec![Lit::neg(latch)]];
        let witness = SafeWitness::InductiveInvariant { lemmas, depth: 1 };
        let outcome = validate_safe(&witness, &ts);
        assert_eq!(
            outcome,
            SafeValidation::Accepted,
            "valid invariant !latch should be accepted"
        );
    }

    /// Bogus invariant: claim `latch` is always TRUE on a stuck-at-0
    /// latch. `init ⇒ inv` fails at step 1.
    #[test]
    fn test_validate_safe_bogus_invariant_init_fails() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let latch = ts.latch_vars[0];
        // Lemma {latch} claims "latch is TRUE" — violates init state.
        let lemmas = vec![vec![Lit::pos(latch)]];
        let witness = SafeWitness::InductiveInvariant { lemmas, depth: 1 };
        let outcome = validate_safe(&witness, &ts);
        match outcome {
            SafeValidation::Rejected { reason } => {
                assert!(
                    reason.contains("Init"),
                    "expected Init⇒Inv rejection, got: {reason}"
                );
            }
            other => panic!("expected Rejected, got {other:?}"),
        }
    }

    /// Bogus invariant: claim a vacuous lemma that holds at init but does
    /// not prove ¬bad. Here `latch` is free (next = latch i.e. stuck at
    /// whatever it was), bad = latch. The property is NOT trivially safe
    /// and an empty invariant cannot prove it — validator should reject
    /// via Check 3 (Inv ⇒ ¬bad).
    #[test]
    fn test_validate_safe_insufficient_invariant_bad_reachable() {
        // aag 1 0 1 0 0 1: latch with self-loop (stuck at whatever init).
        // next = 2 (= latch current), bad = latch.
        // No init clause — latch can be T or F initially, so bad IS
        // reachable at step 0 when latch=1. Invariant {TRUE} (always true)
        // is technically inductive but doesn't prove ¬bad.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 2\n2\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        // Pass a lemma that's always TRUE (tautology): {TRUE}. This
        // passes Check 1 and Check 2 but must fail Check 3.
        let lemmas = vec![vec![Lit::TRUE]];
        let witness = SafeWitness::InductiveInvariant { lemmas, depth: 0 };
        let outcome = validate_safe(&witness, &ts);
        match outcome {
            SafeValidation::Rejected { reason } => {
                assert!(
                    reason.contains("bad") || reason.contains("Inv"),
                    "expected Inv⇒¬bad rejection, got: {reason}"
                );
            }
            other => panic!("expected Rejected for insufficient invariant, got {other:?}"),
        }
    }

    /// Empty-lemmas witness on a non-trivial property must be rejected.
    #[test]
    fn test_validate_safe_empty_lemmas_on_nontrivial_rejected() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 2\n2\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let witness = SafeWitness::InductiveInvariant {
            lemmas: Vec::new(),
            depth: 0,
        };
        let outcome = validate_safe(&witness, &ts);
        match outcome {
            SafeValidation::Rejected { .. } => {}
            other => panic!(
                "expected Rejected for empty-lemmas witness on non-trivial \
                 property, got {other:?}"
            ),
        }
    }

    /// Empty-lemmas witness on a trivial property must be accepted.
    #[test]
    fn test_validate_safe_empty_lemmas_on_trivial_accepted() {
        let circuit = parse_aag("aag 0 0 0 1 0\n0\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let witness = SafeWitness::InductiveInvariant {
            lemmas: Vec::new(),
            depth: 0,
        };
        let outcome = validate_safe(&witness, &ts);
        assert_eq!(outcome, SafeValidation::Accepted);
    }

    /// `EngineVerified` is accepted with no re-verification — we trust the
    /// engine's internal check (e.g. k-induction inductive step) but log.
    /// This preserves existing k-induction + BMC Safe results until those
    /// engines can emit a formal invariant.
    #[test]
    fn test_validate_safe_engine_verified_accepted() {
        // Circuit with non-trivial property. The validator does NOT re-check.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let witness = SafeWitness::EngineVerified { engine: "k-induction" };
        let outcome = validate_safe(&witness, &ts);
        assert_eq!(outcome, SafeValidation::Accepted);
    }
}
