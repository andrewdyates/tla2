// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Phase B1c (#3325): E-matching refinement with theory-provided model.
///
/// This test exercises the Phase B1c refinement loop: after the theory solver
/// returns SAT, E-matching runs again with the fresh EUF model. The model's
/// congruence classes may enable trigger matches that weren't available during
/// preprocessing (which used the model from the previous check-sat, or None).
///
/// The formula:
///   (forall x. P(x) => Q(x))   ; trigger: P(x)
///   P(a)                         ; ground term for trigger matching
///   (not (Q a))                  ; contradicts P(a) => Q(a)
///
/// E-matching in preprocessing matches P(x) against P(a), producing P(a)=>Q(a).
/// Combined with (not (Q a)), this is UNSAT.
///
/// This test verifies the refinement infrastructure doesn't break existing UNSAT.
/// A deeper B1c test would require congruence-derived triggers, which need
/// multi-check-sat to have a prior EUF model.
#[test]
fn test_ematching_refinement_basic_unsat() {
    let input = r#"
        (set-logic UF)
        (declare-sort U 0)
        (declare-fun P (U) Bool)
        (declare-fun Q (U) Bool)
        (declare-fun a () U)
        (assert (forall ((x U)) (! (=> (P x) (Q x)) :pattern ((P x)))))
        (assert (P a))
        (assert (not (Q a)))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    assert_eq!(outputs, vec!["unsat"]);
}
/// Phase B1c (#3325): Multi-check-sat with refinement.
///
/// Exercises Phase B1c across two check-sat calls. The first call establishes
/// an EUF model. The second call's preprocessing uses that model (Phase B1b),
/// and any SAT result triggers refinement (Phase B1c) with the fresh model.
///
/// First check-sat: P(a) is SAT (no quantifiers).
/// Second check-sat: adds forall x. P(x) => Q(x), with P(a) already true.
/// E-matching matches P(x) against P(a), producing P(a) => Q(a).
/// With (not (Q a)), this is UNSAT.
#[test]
fn test_ematching_refinement_multi_checksat() {
    let input = r#"
        (set-logic UF)
        (declare-sort U 0)
        (declare-fun P (U) Bool)
        (declare-fun Q (U) Bool)
        (declare-fun a () U)
        (assert (P a))
        (check-sat)
        (assert (forall ((x U)) (! (=> (P x) (Q x)) :pattern ((P x)))))
        (assert (not (Q a)))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    assert_eq!(outputs[0], "sat"); // First check-sat: just P(a)
    assert_eq!(outputs[1], "unsat"); // Second: P(a), forall P=>Q, not Q(a)
}
/// Phase B1c (#3325): Congruence-derived trigger matching.
///
/// This tests the core B1c capability: trigger matching that requires functional
/// congruence information from the EUF solver, unavailable from explicit equality
/// assertions alone.
///
/// Formula:
///   (forall x. not (P x x))           trigger: (P x x)
///   (P (f a) (f b))                   ground fact
///   (= a b)                           explicit equality
///
/// Preprocessing E-matching:
///   - `from_assertions` sees `(= a b)` → knows a ≡ b
///   - Does NOT derive f(a) ≡ f(b) (requires congruence closure on f)
///   - Trigger `(P x x)` against `P(f(a), f(b))`:
///     x = f(a) from arg1, x = f(b) from arg2, but f(a) ≢ f(b) → NO MATCH
///   - Ground formula (without quantifier) is SAT
///
/// Phase B1c (after theory solve):
///   - EUF solver processes `(= a b)` → congruence closure: f(a) = f(b)
///   - Fresh EUF model: f(a) and f(b) in same congruence class
///   - E-matching re-runs: `(P x x)` matches `P(f(a), f(b))` with x=f(a)
///   - Instantiation: `(not (P (f a) (f a)))`
///   - Re-solve: `P(f(a), f(b)) ∧ f(a)=f(b) ∧ ¬P(f(a), f(a))` → UNSAT
#[test]
fn test_ematching_congruence_derived_trigger_match() {
    let input = r#"
        (set-logic UF)
        (declare-sort U 0)
        (declare-fun f (U) U)
        (declare-fun P (U U) Bool)
        (declare-fun a () U)
        (declare-fun b () U)
        (assert (forall ((x U)) (! (not (P x x)) :pattern ((P x x)))))
        (assert (P (f a) (f b)))
        (assert (= a b))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    // With B1c congruence-derived matching: UNSAT
    // Without B1c: would be Unknown (trigger requires f(a) ≡ f(b) from congruence closure)
    assert!(
        outputs == vec!["unsat"],
        "Expected UNSAT from congruence-derived trigger match, got: {outputs:?}",
    );
}
/// Phase B1c (#3325): Congruence-derived matching via multi-check-sat.
///
/// First check-sat establishes an EUF model. Second check-sat uses B1b
/// (preprocessing with prior model) and B1c (refinement with fresh model)
/// together.
///
/// First check-sat: `(= a b), P(f(a), f(b))` → SAT, EUF model has f(a)≡f(b)
/// Second check-sat: adds `forall x. not (P x x)` with trigger `(P x x)`.
///   B1b: preprocessing uses prior EUF model → f(a)≡f(b) already known →
///   match found during preprocessing → UNSAT.
#[test]
fn test_ematching_congruence_multi_checksat() {
    let input = r#"
        (set-logic UF)
        (declare-sort U 0)
        (declare-fun f (U) U)
        (declare-fun P (U U) Bool)
        (declare-fun a () U)
        (declare-fun b () U)
        (assert (= a b))
        (assert (P (f a) (f b)))
        (check-sat)
        (assert (forall ((x U)) (! (not (P x x)) :pattern ((P x x)))))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    assert_eq!(outputs[0], "sat"); // Ground-only: consistent
                                   // Second check-sat: B1b uses prior model (f(a)≡f(b)) for preprocessing match
    assert!(
        outputs[1] == "unsat",
        "Expected UNSAT from congruence-derived match (B1b or B1c), got: {:?}",
        outputs[1],
    );
}
/// #5927: DPLL(T)-interleaved E-matching — congruence-dependent multi-step chain.
///
/// This tests the interleaved E-matching refinement loop. The pattern matches
/// require congruence equalities that are only available after the theory solver
/// runs:
///
/// Formula:
///   (forall x. (=> (P x) (Q (f x))))   trigger: (P x)
///   (forall y. (=> (Q y) (R y)))        trigger: (Q y)
///   (P a)
///   (= (f a) b)
///   (not (R b))
///
/// Step 1 (preprocessing E-matching):
///   - Match P(x) against P(a) → Q(f(a))
///   - Q(y) trigger needs Q(something), but Q(f(a)) just produced
///   - Multi-round preprocessing: match Q(y) against Q(f(a)) → R(f(a))
///
/// Step 2 (initial solve): ground problem includes Q(f(a)), R(f(a)), (= (f a) b).
///   - If congruence closure derives f(a) = b, then R(f(a)) and R(b) are the same.
///   - With (not (R b)), this should be UNSAT.
///
/// The interleaved loop ensures that after the theory solver establishes
/// congruence equalities, E-matching can discover new matches.
#[test]
fn test_interleaved_ematching_congruence_chain_5927() {
    let input = r#"
        (set-logic UF)
        (declare-sort U 0)
        (declare-fun f (U) U)
        (declare-fun P (U) Bool)
        (declare-fun Q (U) Bool)
        (declare-fun R (U) Bool)
        (declare-fun a () U)
        (declare-fun b () U)
        (assert (forall ((x U)) (! (=> (P x) (Q (f x))) :pattern ((P x)))))
        (assert (forall ((y U)) (! (=> (Q y) (R y)) :pattern ((Q y)))))
        (assert (P a))
        (assert (= (f a) b))
        (assert (not (R b)))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    // Without interleaved E-matching: might return Unknown if congruence
    // equality f(a)=b is needed to connect R(f(a)) to (not (R b)).
    // With interleaved E-matching: UNSAT (congruence closure + E-matching chain).
    assert_eq!(
        outputs,
        vec!["unsat"],
        "Interleaved E-matching should derive UNSAT via congruence chain"
    );
}
