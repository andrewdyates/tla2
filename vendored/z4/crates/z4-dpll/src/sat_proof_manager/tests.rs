// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use z4_core::{Sort, TermStore};
use z4_sat::{ClauseTrace, Literal, Variable};

fn setup_test_terms() -> (TermStore, HashMap<u32, TermId>, HashMap<TermId, TermId>) {
    let mut terms = TermStore::new();
    let mut var_to_term = HashMap::new();
    let mut negations = HashMap::new();

    // Create test terms: p, q as Boolean variables
    let p = terms.mk_var("p", Sort::Bool);
    let q = terms.mk_var("q", Sort::Bool);
    let not_p = terms.mk_not(p);
    let not_q = terms.mk_not(q);

    var_to_term.insert(0, p);
    var_to_term.insert(1, q);
    negations.insert(p, not_p);
    negations.insert(q, not_q);

    (terms, var_to_term, negations)
}

#[test]
fn test_lit_to_term_positive() {
    let (mut terms, var_to_term, _negations) = setup_test_terms();
    let mut manager = SatProofManager::new(&var_to_term, &mut terms);

    let lit = Literal::positive(Variable::new(0));
    let term = manager.lit_to_term(lit).unwrap();
    assert_eq!(term, var_to_term[&0]);
}

#[test]
fn test_lit_to_term_negative() {
    let (mut terms, var_to_term, negations) = setup_test_terms();
    let mut manager = SatProofManager::new(&var_to_term, &mut terms);

    let lit = Literal::negative(Variable::new(0));
    let term = manager.lit_to_term(lit).unwrap();
    assert_eq!(term, negations[&var_to_term[&0]]);
}

#[test]
fn test_clause_to_terms() {
    let (mut terms, var_to_term, _negations) = setup_test_terms();
    let mut manager = SatProofManager::new(&var_to_term, &mut terms);

    let clause = vec![
        Literal::positive(Variable::new(0)),
        Literal::negative(Variable::new(1)),
    ];
    let terms_result = manager.clause_to_terms(&clause).unwrap();
    assert_eq!(terms_result.len(), 2);
}

#[test]
fn test_can_process_empty() {
    let (mut terms, var_to_term, _negations) = setup_test_terms();
    let manager = SatProofManager::new(&var_to_term, &mut terms);

    let trace = ClauseTrace::new();
    assert!(!manager.can_process(&trace));
}

#[test]
fn test_can_process_with_clauses() {
    let (mut terms, var_to_term, _negations) = setup_test_terms();
    let manager = SatProofManager::new(&var_to_term, &mut terms);

    let mut trace = ClauseTrace::new();
    trace.add_clause(1, vec![Literal::positive(Variable::new(0))], true);
    assert!(manager.can_process(&trace));
}

#[test]
fn test_process_trace_uses_resolution_hints() {
    let (mut terms, var_to_term, negations) = setup_test_terms();
    let mut manager = SatProofManager::new(&var_to_term, &mut terms);

    let p = var_to_term[&0];
    let not_p = negations[&p];

    let mut proof = Proof::new();
    let p_id = proof.add_assume(p, Some("h0".to_string()));
    let not_p_id = proof.add_assume(not_p, Some("h1".to_string()));

    let mut trace = ClauseTrace::new();
    trace.add_clause(1, vec![Literal::positive(Variable::new(0))], true);
    trace.add_clause(2, vec![Literal::negative(Variable::new(0))], true);
    trace.add_clause_with_hints(3, Vec::new(), false, vec![1, 2]);

    let empty_id = manager
        .process_trace(&trace, &mut proof)
        .expect("expected empty clause derivation");

    let ProofStep::Resolution {
        clause,
        clause1,
        clause2,
        ..
    } = proof
        .get_step(empty_id)
        .expect("final proof step must exist")
    else {
        panic!("expected final step to be resolution");
    };

    assert!(clause.is_empty(), "expected empty resolvent");
    let premise_set: HashSet<ProofId> = [*clause1, *clause2].into_iter().collect();
    let expected: HashSet<ProofId> = [p_id, not_p_id].into_iter().collect();
    assert_eq!(premise_set, expected);
}

#[test]
fn test_process_trace_empty_uses_contradictory_assumptions() {
    let (mut terms, var_to_term, negations) = setup_test_terms();
    let mut manager = SatProofManager::new(&var_to_term, &mut terms);

    let p = var_to_term[&0];
    let not_p = negations[&p];

    let mut proof = Proof::new();
    let p_id = proof.add_assume(p, Some("h0".to_string()));
    let not_p_id = proof.add_assume(not_p, Some("h1".to_string()));

    let mut trace = ClauseTrace::new();
    trace.mark_empty();

    let empty_id = manager
        .process_trace(&trace, &mut proof)
        .expect("expected empty clause derivation from assumptions");

    let ProofStep::Resolution {
        clause,
        clause1,
        clause2,
        ..
    } = proof
        .get_step(empty_id)
        .expect("final proof step must exist")
    else {
        panic!("expected final step to be resolution");
    };

    assert!(clause.is_empty(), "expected empty resolvent");
    let premise_set: HashSet<ProofId> = [*clause1, *clause2].into_iter().collect();
    let expected: HashSet<ProofId> = [p_id, not_p_id].into_iter().collect();
    assert_eq!(premise_set, expected);
}

#[test]
fn test_process_trace_retains_original_empty_clause_as_last_resort() {
    let (mut terms, var_to_term, _negations) = setup_test_terms();
    let mut manager = SatProofManager::new(&var_to_term, &mut terms);

    let mut proof = Proof::new();
    let p = var_to_term[&0];
    proof.add_assume(p, Some("h0".to_string()));

    let mut trace = ClauseTrace::new();
    trace.add_clause(1, Vec::new(), true);

    let empty_id = manager
        .process_trace(&trace, &mut proof)
        .expect("expected empty clause from original trace entry");

    let Some(ProofStep::Step {
        rule,
        clause,
        premises,
        ..
    }) = proof.get_step(empty_id)
    else {
        panic!("expected trust step for original empty clause");
    };

    assert_eq!(*rule, AletheRule::Trust);
    assert!(clause.is_empty(), "expected empty clause");
    assert!(premises.is_empty(), "expected premise-less trust step");
}

/// After #6365, normalize_positive_literal is identity — AND atoms stay as AND.
/// SAT-level contradiction between positive and negative AND-atom literals
/// produces an empty clause via resolution on (and ...) / (not (and ...)).
#[test]
fn test_process_trace_and_atom_no_de_morgan_normalization() {
    let mut terms = TermStore::new();
    let mut var_to_term = HashMap::new();

    let q = terms.mk_var("q", Sort::Bool);
    let r = terms.mk_var("r", Sort::Bool);
    let not_r = terms.mk_not(r);
    let and_q_not_r = terms.mk_and(vec![q, not_r]);

    var_to_term.insert(0, and_q_not_r);

    let mut proof = Proof::new();
    let and_id = proof.add_assume(and_q_not_r, Some("h0".to_string()));
    let not_and = terms.mk_not_raw(and_q_not_r);
    let not_and_id = proof.add_assume(not_and, Some("h1".to_string()));

    let mut trace = ClauseTrace::new();
    trace.add_clause(1, vec![Literal::positive(Variable::new(0))], true);
    trace.add_clause(2, vec![Literal::negative(Variable::new(0))], true);
    trace.add_clause_with_hints(3, Vec::new(), false, vec![1, 2]);

    let empty_id = {
        let mut manager = SatProofManager::new(&var_to_term, &mut terms);
        manager
            .process_trace(&trace, &mut proof)
            .expect("expected empty clause derivation")
    };

    let ProofStep::Resolution {
        clause,
        clause1,
        clause2,
        ..
    } = proof
        .get_step(empty_id)
        .expect("expected final resolution step")
    else {
        panic!("expected final step to be resolution");
    };
    assert!(clause.is_empty(), "expected empty resolvent");
    let premise_set: HashSet<ProofId> = [*clause1, *clause2].into_iter().collect();
    let expected: HashSet<ProofId> = [and_id, not_and_id].into_iter().collect();
    assert_eq!(
        premise_set, expected,
        "resolution should use (and ...) and (not (and ...)) assumptions"
    );
}

/// Theory lemma annotation in add_original_clause_step (#6031 Phase 4).
///
/// When a theory lemma annotation matches a clause in the SAT trace,
/// `add_original_clause_step` should emit a `TheoryLemma` proof step
/// instead of the generic `assume` + `or` pattern.
#[test]
fn test_add_original_clause_step_emits_theory_lemma_when_annotated() {
    use z4_core::{FarkasAnnotation, TheoryLemmaKind, TheoryLemmaProof};

    let (mut terms, var_to_term, _negations) = setup_test_terms();
    let p = var_to_term[&0];
    let q = var_to_term[&1];

    let clause = vec![p, q];
    let mut existing_clause_map: HashMap<Vec<TermId>, ProofId> = HashMap::new();

    let theory_annot = TheoryLemmaProof {
        kind: TheoryLemmaKind::LraFarkas,
        farkas: Some(FarkasAnnotation::from_ints(&[1, 1])),
        lia: None,
    };

    let mut proof = Proof::new();
    let id = SatProofManager::add_original_clause_step(
        &mut terms,
        &mut proof,
        &clause,
        &mut existing_clause_map,
        None,                // no clausification annotation
        Some(&theory_annot), // theory lemma annotation present
    );

    // The emitted step must be a TheoryLemma with LraFarkas kind
    let step = proof
        .get_step(id)
        .expect("proof step must exist at returned id");
    match step {
        ProofStep::TheoryLemma {
            clause: emitted_clause,
            kind,
            farkas,
            ..
        } => {
            assert_eq!(emitted_clause, &clause, "clause content must match");
            assert_eq!(*kind, TheoryLemmaKind::LraFarkas, "kind must be LraFarkas");
            assert!(farkas.is_some(), "Farkas annotation must be preserved");
            assert_eq!(
                farkas.as_ref().unwrap().coefficients.len(),
                2,
                "Farkas annotation must have 2 coefficient entries"
            );
        }
        other => panic!(
            "expected TheoryLemma step, got {:?}",
            std::mem::discriminant(other)
        ),
    }
}

/// Theory lemma annotation: duplicate clause only emits once (#6031 Phase 4).
///
/// When the same normalized clause appears twice in the trace, the second
/// occurrence should reuse the existing proof step (via existing_clause_map).
#[test]
fn test_add_original_clause_step_deduplicates_theory_lemma() {
    use z4_core::{FarkasAnnotation, TheoryLemmaKind, TheoryLemmaProof};

    let (mut terms, var_to_term, _negations) = setup_test_terms();
    let p = var_to_term[&0];
    let q = var_to_term[&1];

    let clause = vec![p, q];
    let mut existing_clause_map: HashMap<Vec<TermId>, ProofId> = HashMap::new();
    let theory_annot = TheoryLemmaProof {
        kind: TheoryLemmaKind::LraFarkas,
        farkas: Some(FarkasAnnotation::from_ints(&[1, 1])),
        lia: None,
    };

    let mut proof = Proof::new();
    let id1 = SatProofManager::add_original_clause_step(
        &mut terms,
        &mut proof,
        &clause,
        &mut existing_clause_map,
        None,
        Some(&theory_annot),
    );
    let id2 = SatProofManager::add_original_clause_step(
        &mut terms,
        &mut proof,
        &clause,
        &mut existing_clause_map,
        None,
        Some(&theory_annot),
    );

    assert_eq!(id1, id2, "duplicate clause should reuse same proof step");
    assert_eq!(proof.len(), 1, "only one proof step should be emitted");
}

/// Without theory annotation, multi-literal clause emits assume + or (#6031 Phase 4).
#[test]
fn test_add_original_clause_step_without_annotation_emits_assume_or() {
    let (mut terms, var_to_term, _negations) = setup_test_terms();
    let p = var_to_term[&0];
    let q = var_to_term[&1];

    let clause = vec![p, q];
    let mut existing_clause_map: HashMap<Vec<TermId>, ProofId> = HashMap::new();

    let mut proof = Proof::new();
    let id = SatProofManager::add_original_clause_step(
        &mut terms,
        &mut proof,
        &clause,
        &mut existing_clause_map,
        None, // no clausification annotation
        None, // no theory lemma annotation
    );

    // Should emit assume + or (2 steps)
    assert_eq!(proof.len(), 2, "assume + or should produce 2 steps");
    let step = proof.get_step(id).expect("proof step must exist");
    match step {
        ProofStep::Step {
            rule: AletheRule::Or,
            clause: emitted_clause,
            premises,
            ..
        } => {
            assert_eq!(emitted_clause, &clause, "clause content must match");
            assert_eq!(premises.len(), 1, "or rule should have 1 premise (assume)");
        }
        other => panic!("expected Or step, got {:?}", std::mem::discriminant(other)),
    }
}

#[test]
fn test_add_original_clause_step_unit_clause_emits_single_assume() {
    let (mut terms, var_to_term, _negations) = setup_test_terms();
    let p = var_to_term[&0];

    let clause = vec![p];
    let mut existing_clause_map: HashMap<Vec<TermId>, ProofId> = HashMap::new();

    let mut proof = Proof::new();
    let id = SatProofManager::add_original_clause_step(
        &mut terms,
        &mut proof,
        &clause,
        &mut existing_clause_map,
        None,
        None,
    );

    assert_eq!(
        proof.len(),
        1,
        "unit original clause should emit one assume"
    );
    let Some(ProofStep::Assume(term)) = proof.get_step(id) else {
        panic!("expected unit clause to emit an assume step");
    };
    assert_eq!(*term, p, "assume step should use the unit literal directly");
}

#[test]
fn test_add_original_clause_step_empty_clause_emits_trust() {
    let (mut terms, _var_to_term, _negations) = setup_test_terms();
    let mut existing_clause_map: HashMap<Vec<TermId>, ProofId> = HashMap::new();

    let mut proof = Proof::new();
    let id = SatProofManager::add_original_clause_step(
        &mut terms,
        &mut proof,
        &[],
        &mut existing_clause_map,
        None,
        None,
    );

    let Some(ProofStep::Step {
        rule,
        clause,
        premises,
        ..
    }) = proof.get_step(id)
    else {
        panic!("expected empty clause to emit a trust step");
    };
    assert_eq!(*rule, AletheRule::Trust);
    assert!(clause.is_empty(), "trust clause should stay empty");
    assert!(
        premises.is_empty(),
        "empty input clause should be premise-less"
    );
}

#[test]
fn test_add_original_clause_step_clausification_annotation_emits_tautology_rule() {
    use z4_core::ClausificationProof;

    let (mut terms, var_to_term, _negations) = setup_test_terms();
    let p = var_to_term[&0];
    let q = var_to_term[&1];
    let and_term = terms.mk_and(vec![p, q]);
    let clause = vec![terms.mk_not_raw(and_term), p];
    let annotation = ClausificationProof {
        rule: AletheRule::AndPos(0),
        source_term: and_term,
    };
    let mut existing_clause_map: HashMap<Vec<TermId>, ProofId> = HashMap::new();

    let mut proof = Proof::new();
    let id = SatProofManager::add_original_clause_step(
        &mut terms,
        &mut proof,
        &clause,
        &mut existing_clause_map,
        Some(&annotation),
        None,
    );

    let Some(ProofStep::Step {
        rule,
        clause: emitted_clause,
        premises,
        args,
    }) = proof.get_step(id)
    else {
        panic!("expected clausification annotation to emit a tautology rule step");
    };
    assert_eq!(*rule, AletheRule::AndPos(0));
    assert_eq!(emitted_clause, &clause);
    assert!(
        premises.is_empty(),
        "tautology clause should be premise-less"
    );
    assert_eq!(
        args,
        &vec![and_term],
        "source term should be forwarded as an argument"
    );
}

#[test]
fn test_derive_clause_from_hints_returns_no_usable_hints_for_missing_ids() {
    let (mut terms, var_to_term, _negations) = setup_test_terms();
    let mut manager = SatProofManager::new(&var_to_term, &mut terms);
    let mut proof = Proof::new();

    let error = manager
        .derive_clause_from_hints(&[], &[99], &HashMap::new(), &HashMap::new(), &mut proof)
        .expect_err("missing hints should be rejected");

    assert_eq!(error, HintDerivationError::NoUsableHints);
}

#[test]
fn test_derive_clause_from_hints_returns_existing_proof_when_target_already_matches() {
    let (mut terms, var_to_term, _negations) = setup_test_terms();
    let p = var_to_term[&0];
    let q = var_to_term[&1];
    let mut proof = Proof::new();
    let existing_id = proof.add_assume(terms.mk_or(vec![p, q]), Some("h1".to_string()));
    let mut manager = SatProofManager::new(&var_to_term, &mut terms);

    let clause_terms: HashMap<u64, Vec<TermId>> = HashMap::from([(1, vec![p, q])]);
    let clause_proofs: HashMap<u64, ProofId> = HashMap::from([(1, existing_id)]);

    let derived_id = manager
        .derive_clause_from_hints(
            &[q, p, p],
            &[1, 1, 99],
            &clause_terms,
            &clause_proofs,
            &mut proof,
        )
        .expect("already-matching target clause should reuse the existing proof");

    assert_eq!(
        derived_id, existing_id,
        "deduplicated hints should return the original proof when no resolution is needed"
    );
    assert_eq!(
        proof.len(),
        1,
        "matching the target without resolution should not emit extra proof steps"
    );
}

#[test]
fn test_derive_clause_from_hints_reports_no_resolution_pivot() {
    let (mut terms, var_to_term, _negations) = setup_test_terms();
    let p = var_to_term[&0];
    let q = var_to_term[&1];
    let mut proof = Proof::new();
    let p_id = proof.add_assume(p, Some("hp".to_string()));
    let q_id = proof.add_assume(q, Some("hq".to_string()));
    let mut manager = SatProofManager::new(&var_to_term, &mut terms);

    let clause_terms: HashMap<u64, Vec<TermId>> = HashMap::from([(1, vec![p]), (2, vec![q])]);
    let clause_proofs: HashMap<u64, ProofId> = HashMap::from([(1, p_id), (2, q_id)]);

    let error = manager
        .derive_clause_from_hints(&[], &[1, 2], &clause_terms, &clause_proofs, &mut proof)
        .expect_err("non-resolving hints should report missing pivot");

    assert_eq!(
        error,
        HintDerivationError::NoResolutionPivot {
            usable_hint_count: 2
        }
    );
}

#[test]
fn test_derive_clause_from_hints_reports_final_clause_mismatch() {
    let (mut terms, var_to_term, negations) = setup_test_terms();
    let p = var_to_term[&0];
    let q = var_to_term[&1];
    let not_p = negations[&p];
    let mut proof = Proof::new();
    let p_or_q_id = proof.add_assume(terms.mk_or(vec![p, q]), Some("h1".to_string()));
    let not_p_id = proof.add_assume(not_p, Some("h2".to_string()));
    let mut manager = SatProofManager::new(&var_to_term, &mut terms);

    let clause_terms: HashMap<u64, Vec<TermId>> =
        HashMap::from([(1, vec![p, q]), (2, vec![not_p])]);
    let clause_proofs: HashMap<u64, ProofId> = HashMap::from([(1, p_or_q_id), (2, not_p_id)]);

    let error = manager
        .derive_clause_from_hints(&[p], &[1, 2], &clause_terms, &clause_proofs, &mut proof)
        .expect_err("resolving to the wrong clause should report the mismatch");

    assert_eq!(
        error,
        HintDerivationError::FinalClauseMismatch {
            expected_clause: vec![p],
            derived_clause: vec![q],
        }
    );
}

#[test]
fn test_close_clause_via_originals_direct_success() {
    let (mut terms, var_to_term, negations) = setup_test_terms();

    let p = var_to_term[&0];
    let q = var_to_term[&1];
    let not_p = negations[&p];
    let p_or_q = terms.mk_or(vec![p, q]);
    let not_p_or_q = terms.mk_or(vec![not_p, q]);

    let mut proof = Proof::new();
    let current_id = proof.add_assume(p_or_q, Some("current".to_string()));
    let not_p_or_q_id = proof.add_assume(not_p_or_q, Some("h2".to_string()));
    let mut manager = SatProofManager::new(&var_to_term, &mut terms);

    let clause_terms: HashMap<u64, Vec<TermId>> =
        HashMap::from([(1, vec![p, q]), (2, vec![not_p, q])]);
    let clause_proofs: HashMap<u64, ProofId> = HashMap::from([(1, current_id), (2, not_p_or_q_id)]);

    let closed_id = manager
        .close_clause_via_originals(
            vec![p, q],
            current_id,
            &[q],
            &clause_terms,
            &clause_proofs,
            &mut proof,
        )
        .expect("closure should resolve directly to a strictly closer target clause");

    let Some(ProofStep::Resolution {
        clause,
        clause1,
        clause2,
        ..
    }) = proof.get_step(closed_id)
    else {
        panic!("expected final closure step to be a resolution");
    };
    assert_eq!(
        clause,
        &vec![q],
        "direct closure should derive the target unit clause"
    );
    let premise_set: HashSet<ProofId> = [*clause1, *clause2].into_iter().collect();
    let expected: HashSet<ProofId> = [current_id, not_p_or_q_id].into_iter().collect();
    assert_eq!(
        premise_set, expected,
        "direct closure should resolve the current clause against the original clause that removes the mismatching literal"
    );
}

#[test]
fn test_derive_clause_from_hints_closes_via_originals() {
    let (mut terms, var_to_term, negations) = setup_test_terms();

    let p = var_to_term[&0];
    let q = var_to_term[&1];
    let not_p = negations[&p];
    let not_q = negations[&q];
    let p_or_q = terms.mk_or(vec![p, q]);
    let not_p_or_q = terms.mk_or(vec![not_p, q]);

    let mut proof = Proof::new();
    let clause_1_id = proof.add_assume(p_or_q, Some("h1".to_string()));
    let clause_2_id = proof.add_assume(not_p_or_q, Some("h2".to_string()));
    let clause_3_id = proof.add_assume(not_q, Some("h3".to_string()));
    let mut manager = SatProofManager::new(&var_to_term, &mut terms);

    let clause_terms: HashMap<u64, Vec<TermId>> =
        HashMap::from([(1, vec![p, q]), (2, vec![not_p, q]), (3, vec![not_q])]);
    let clause_proofs: HashMap<u64, ProofId> =
        HashMap::from([(1, clause_1_id), (2, clause_2_id), (3, clause_3_id)]);

    let derived_id = manager
        .derive_clause_from_hints(&[], &[1, 1, 2], &clause_terms, &clause_proofs, &mut proof)
        .expect("hint replay should resolve duplicate hints and then close via originals");

    let ProofStep::Resolution {
        clause,
        clause1,
        clause2,
        ..
    } = proof
        .get_step(derived_id)
        .expect("derived proof step must exist")
    else {
        panic!("expected final derived step to be a resolution");
    };

    assert!(
        clause.is_empty(),
        "closure should derive the empty target clause"
    );
    let premise_set: HashSet<ProofId> = [*clause1, *clause2].into_iter().collect();
    let expected: HashSet<ProofId> = [clause_3_id, ProofId(3)].into_iter().collect();
    assert_eq!(
        premise_set, expected,
        "closure should resolve the intermediate unit clause against the original not-q clause"
    );
}

#[test]
fn test_close_clause_via_originals_returns_none_without_strict_progress() {
    let (mut terms, var_to_term, negations) = setup_test_terms();

    let p = var_to_term[&0];
    let q = var_to_term[&1];
    let not_p = negations[&p];
    let p_or_q = terms.mk_or(vec![p, q]);
    let not_p_or_q = terms.mk_or(vec![not_p, q]);

    let mut proof = Proof::new();
    let current_id = proof.add_assume(p_or_q, Some("current".to_string()));
    let rhs_id = proof.add_assume(not_p_or_q, Some("rhs".to_string()));
    let mut manager = SatProofManager::new(&var_to_term, &mut terms);

    let clause_terms: HashMap<u64, Vec<TermId>> =
        HashMap::from([(1, vec![p, q]), (2, vec![not_p, q])]);
    let clause_proofs: HashMap<u64, ProofId> = HashMap::from([(1, current_id), (2, rhs_id)]);

    let before_len = proof.len();
    let closed = manager.close_clause_via_originals(
        vec![p, q],
        current_id,
        &[],
        &clause_terms,
        &clause_proofs,
        &mut proof,
    );

    assert!(
        closed.is_none(),
        "closure must reject steps that do not strictly reduce target mismatch"
    );
    assert_eq!(
        proof.len(),
        before_len + 1,
        "closure may emit progress-making resolution steps before determining the target is unreachable"
    );
    let Some(ProofStep::Resolution { clause, .. }) = proof.get_step(ProofId(before_len as u32))
    else {
        panic!("expected the progress-making step to be recorded as a resolution");
    };
    assert_eq!(
        clause,
        &vec![q],
        "the recorded progress step should be the intermediate resolvent that reduced mismatch"
    );
}

#[test]
fn test_derive_empty_from_units_returns_none_without_complementary_proofs() {
    let (mut terms, var_to_term, negations) = setup_test_terms();
    let mut manager = SatProofManager::new(&var_to_term, &mut terms);

    let p = var_to_term[&0];
    let q = var_to_term[&1];
    let not_p = negations[&p];

    let mut proof = Proof::new();
    let q_id = proof.add_assume(q, Some("hq".to_string()));

    let clause_terms: HashMap<u64, Vec<TermId>> =
        HashMap::from([(1, vec![p]), (2, vec![not_p]), (3, vec![q])]);
    let clause_proofs: HashMap<u64, ProofId> = HashMap::from([(3, q_id)]);

    let empty_id = manager.derive_empty_from_units(&clause_terms, &clause_proofs, &mut proof);
    assert!(
        empty_id.is_none(),
        "unit contradiction detection must ignore clauses that do not have proof IDs"
    );
}

#[test]
fn test_derive_empty_from_units_finds_first_contradictory_pair() {
    let (mut terms, var_to_term, negations) = setup_test_terms();
    let mut manager = SatProofManager::new(&var_to_term, &mut terms);

    let p = var_to_term[&0];
    let q = var_to_term[&1];
    let not_q = negations[&q];

    let mut proof = Proof::new();
    let p_id = proof.add_assume(p, Some("h0".to_string()));
    let q_id = proof.add_assume(q, Some("h1".to_string()));
    let not_q_id = proof.add_assume(not_q, Some("h2".to_string()));

    let clause_terms: HashMap<u64, Vec<TermId>> =
        HashMap::from([(1, vec![p]), (2, vec![q]), (3, vec![not_q])]);
    let clause_proofs: HashMap<u64, ProofId> = HashMap::from([(1, p_id), (2, q_id), (3, not_q_id)]);

    let empty_id = manager
        .derive_empty_from_units(&clause_terms, &clause_proofs, &mut proof)
        .expect("contradictory unit clauses should derive empty");

    let ProofStep::Resolution {
        clause,
        clause1,
        clause2,
        ..
    } = proof
        .get_step(empty_id)
        .expect("empty-clause proof step must exist")
    else {
        panic!("expected empty derivation to be a resolution");
    };

    assert!(
        clause.is_empty(),
        "unit contradiction should derive the empty clause"
    );
    let premise_set: HashSet<ProofId> = [*clause1, *clause2].into_iter().collect();
    let expected: HashSet<ProofId> = [q_id, not_q_id].into_iter().collect();
    assert_eq!(
        premise_set, expected,
        "non-contradictory units must be skipped until a complementary pair appears"
    );
}

#[test]
fn test_derive_empty_from_assumptions_ignores_non_assume_steps() {
    let (mut terms, var_to_term, negations) = setup_test_terms();
    let mut manager = SatProofManager::new(&var_to_term, &mut terms);

    let p = var_to_term[&0];
    let q = var_to_term[&1];
    let not_q = negations[&q];

    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Trust, vec![p], Vec::new(), Vec::new());
    let q_id = proof.add_assume(q, Some("hq".to_string()));
    let not_q_id = proof.add_assume(not_q, Some("hnotq".to_string()));

    let empty_id = manager
        .derive_empty_from_assumptions(&mut proof)
        .expect("contradictory assumptions should derive empty");

    let ProofStep::Resolution {
        clause,
        clause1,
        clause2,
        ..
    } = proof
        .get_step(empty_id)
        .expect("empty-clause proof step must exist")
    else {
        panic!("expected empty derivation to be a resolution");
    };

    assert!(
        clause.is_empty(),
        "contradictory assumptions should produce the empty clause"
    );
    let premise_set: HashSet<ProofId> = [*clause1, *clause2].into_iter().collect();
    let expected: HashSet<ProofId> = [q_id, not_q_id].into_iter().collect();
    assert_eq!(
        premise_set, expected,
        "only assume steps should participate in contradictory-assumption detection"
    );
}

#[test]
fn test_derive_empty_from_assumptions_returns_none_without_complementary_pair() {
    let (mut terms, var_to_term, _negations) = setup_test_terms();
    let mut manager = SatProofManager::new(&var_to_term, &mut terms);

    let p = var_to_term[&0];
    let q = var_to_term[&1];

    let mut proof = Proof::new();
    proof.add_assume(p, Some("hp".to_string()));
    proof.add_assume(q, Some("hq".to_string()));

    let empty_id = manager.derive_empty_from_assumptions(&mut proof);
    assert!(
        empty_id.is_none(),
        "assumption contradiction detection should return None when no complements exist"
    );
}

#[test]
fn test_process_trace_hint_mismatch_falls_back_to_trust_with_premises() {
    let (mut terms, var_to_term, _negations) = setup_test_terms();
    let mut manager = SatProofManager::new(&var_to_term, &mut terms);

    let p = var_to_term[&0];
    let q = var_to_term[&1];

    let mut proof = Proof::new();
    let p_id = proof.add_assume(p, Some("h0".to_string()));
    let q_id = proof.add_assume(q, Some("h1".to_string()));

    let mut trace = ClauseTrace::new();
    trace.add_clause(1, vec![Literal::positive(Variable::new(0))], true);
    trace.add_clause(2, vec![Literal::positive(Variable::new(1))], true);
    trace.add_clause_with_hints(3, Vec::new(), false, vec![1, 2]);

    let empty_id = manager
        .process_trace(&trace, &mut proof)
        .expect("expected empty clause fallback");
    let Some(ProofStep::Step {
        rule,
        clause,
        premises,
        ..
    }) = proof.get_step(empty_id)
    else {
        panic!("expected trust fallback proof step");
    };

    assert_eq!(*rule, AletheRule::Trust, "fallback should emit trust");
    assert!(
        clause.is_empty(),
        "learned empty clause should be preserved"
    );

    let premise_set: HashSet<ProofId> = premises.iter().copied().collect();
    let expected: HashSet<ProofId> = [p_id, q_id].into_iter().collect();
    assert_eq!(
        premise_set, expected,
        "trust fallback should preserve reconstructable premise IDs"
    );
}
