// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
#[cfg(not(kani))]
use hashbrown::{HashMap, HashSet};
use num_bigint::BigInt;
use num_rational::BigRational;
#[cfg(kani)]
use z4_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use z4_core::{
    BoundRefinementRequest, Sort, TermId, TermStore, TheoryLit, TheoryPropagation, TheoryResult,
};
use z4_sat::{ExtCheckResult, Extension, SolverContext};
use z4_sat::{Literal, Variable};

use crate::executor::BoundRefinementReplayKey;

/// Mock theory solver for testing TheoryExtension
struct MockTheory {
    assertions: Vec<(TermId, bool)>,
    push_count: u32,
    pop_count: u32,
    reset_count: u32,
    check_calls: usize,
    check_result: TheoryResult,
    propagations: Vec<TheoryPropagation>,
    pending_bound_refinements: Vec<BoundRefinementRequest>,
    axiom_terms: Vec<(TermId, bool, TermId, bool)>,
    rejected_propagations: Vec<(TermId, u64)>,
}

impl MockTheory {
    fn new() -> Self {
        Self {
            assertions: vec![],
            push_count: 0,
            pop_count: 0,
            reset_count: 0,
            check_calls: 0,
            check_result: TheoryResult::Sat,
            propagations: vec![],
            pending_bound_refinements: Vec::new(),
            axiom_terms: Vec::new(),
            rejected_propagations: Vec::new(),
        }
    }

    fn with_check_result(mut self, result: TheoryResult) -> Self {
        self.check_result = result;
        self
    }

    fn with_propagations(mut self, props: Vec<TheoryPropagation>) -> Self {
        self.propagations = props;
        self
    }

    fn with_bound_refinements(mut self, refinements: Vec<BoundRefinementRequest>) -> Self {
        self.pending_bound_refinements = refinements;
        self
    }

    fn with_axiom_terms(mut self, axiom_terms: Vec<(TermId, bool, TermId, bool)>) -> Self {
        self.axiom_terms = axiom_terms;
        self
    }
}

impl TheorySolver for MockTheory {
    fn assert_literal(&mut self, literal: TermId, value: bool) {
        self.assertions.push((literal, value));
    }

    fn check(&mut self) -> TheoryResult {
        self.check_calls += 1;
        self.check_result.clone()
    }

    fn propagate(&mut self) -> Vec<TheoryPropagation> {
        std::mem::take(&mut self.propagations)
    }

    fn push(&mut self) {
        self.push_count += 1;
    }

    fn pop(&mut self) {
        self.pop_count += 1;
    }

    fn reset(&mut self) {
        self.reset_count += 1;
        self.assertions.clear();
        self.pending_bound_refinements.clear();
        self.rejected_propagations.clear();
    }

    fn take_bound_refinements(&mut self) -> Vec<BoundRefinementRequest> {
        std::mem::take(&mut self.pending_bound_refinements)
    }

    fn generate_bound_axiom_terms(&self) -> Vec<(TermId, bool, TermId, bool)> {
        self.axiom_terms.clone()
    }

    fn mark_propagation_rejected(&mut self, lit: TermId, reason_data: u64) {
        self.rejected_propagations.push((lit, reason_data));
    }
}

/// Simulates theories like LRA that only expose bound refinements during
/// an earlier eager `check()` call and clear the queue on the later final
/// `check()` if the extension did not already preserve them.
struct PropagateOnlyRefinementTheory {
    pending_bound_refinements: Vec<BoundRefinementRequest>,
    check_calls: usize,
}

impl PropagateOnlyRefinementTheory {
    fn new(refinement: BoundRefinementRequest) -> Self {
        Self {
            pending_bound_refinements: vec![refinement],
            check_calls: 0,
        }
    }
}

impl TheorySolver for PropagateOnlyRefinementTheory {
    fn assert_literal(&mut self, _literal: TermId, _value: bool) {}

    fn check(&mut self) -> TheoryResult {
        self.check_calls += 1;
        if self.check_calls > 1 {
            self.pending_bound_refinements.clear();
        }
        TheoryResult::Sat
    }

    fn propagate(&mut self) -> Vec<TheoryPropagation> {
        Vec::new()
    }

    fn push(&mut self) {}

    fn pop(&mut self) {
        self.pending_bound_refinements.clear();
    }

    fn reset(&mut self) {
        self.pending_bound_refinements.clear();
    }

    fn take_bound_refinements(&mut self) -> Vec<BoundRefinementRequest> {
        std::mem::take(&mut self.pending_bound_refinements)
    }
}

/// Mock solver context for testing
struct MockContext {
    trail: Vec<Literal>,
    values: HashMap<u32, bool>,
    decision_level: u32,
}

impl MockContext {
    fn new() -> Self {
        Self {
            trail: vec![],
            values: HashMap::new(),
            decision_level: 0,
        }
    }

    fn with_trail(mut self, trail: Vec<Literal>) -> Self {
        for lit in &trail {
            self.values.insert(lit.variable().id(), lit.is_positive());
        }
        self.trail = trail;
        self
    }

    fn with_level(mut self, level: u32) -> Self {
        self.decision_level = level;
        self
    }
}

impl SolverContext for MockContext {
    fn value(&self, var: Variable) -> Option<bool> {
        self.values.get(&var.id()).copied()
    }

    fn decision_level(&self) -> u32 {
        self.decision_level
    }

    fn var_level(&self, _var: Variable) -> Option<u32> {
        Some(0)
    }

    fn trail(&self) -> &[Literal] {
        &self.trail
    }

    fn new_assignments(&self, _last_pos: usize) -> &[Literal] {
        &self.trail
    }
}

type TestSetup = (
    TermStore,
    HashMap<u32, TermId>,
    HashMap<TermId, u32>,
    Vec<TermId>,
    HashSet<TermId>,
    [TermId; 3],
);

fn create_test_setup() -> TestSetup {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let y = terms.mk_var("y", Sort::Bool);
    let z = terms.mk_var("z", Sort::Bool);

    let var_to_term: HashMap<u32, TermId> = [(1, x), (2, y), (3, z)].into_iter().collect();
    let term_to_var: HashMap<TermId, u32> = [(x, 1), (y, 2), (z, 3)].into_iter().collect();
    let mut theory_atoms = vec![x, y, z];
    theory_atoms.sort_unstable_by_key(|term| term.0);
    let theory_atom_set: HashSet<TermId> = theory_atoms.iter().copied().collect();

    (
        terms,
        var_to_term,
        term_to_var,
        theory_atoms,
        theory_atom_set,
        [x, y, z],
    )
}

#[cfg(test)]
type LraBoundAxiomSetup = (
    TermStore,
    HashMap<u32, TermId>,
    HashMap<TermId, u32>,
    Vec<TermId>,
    HashSet<TermId>,
    [TermId; 2],
);

/// Create a real-arithmetic setup whose validated bound axiom is tautological:
/// `(x >= 0) OR (x <= 0)`.
#[cfg(test)]
fn create_lra_bound_axiom_setup() -> LraBoundAxiomSetup {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let zero = terms.mk_rational(BigRational::from(BigInt::from(0)));
    let x_ge_0 = terms.mk_ge(x, zero);
    let x_le_0 = terms.mk_le(x, zero);

    let var_to_term: HashMap<u32, TermId> = [(1, x_ge_0), (2, x_le_0)].into_iter().collect();
    let term_to_var: HashMap<TermId, u32> = [(x_ge_0, 1), (x_le_0, 2)].into_iter().collect();
    let mut theory_atoms = vec![x_ge_0, x_le_0];
    theory_atoms.sort_unstable_by_key(|term| term.0);
    let theory_atom_set: HashSet<TermId> = theory_atoms.iter().copied().collect();

    (
        terms,
        var_to_term,
        term_to_var,
        theory_atoms,
        theory_atom_set,
        [x_ge_0, x_le_0],
    )
}

#[test]
fn var_for_term_returns_variable_when_mapped() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _xyz) =
        create_test_setup();
    let x = _xyz[0];
    let mut theory = MockTheory::new();
    let ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    assert_eq!(ext.var_for_term(x), Some(Variable::new(1)));
}

#[test]
fn var_for_term_returns_none_for_unmapped_term() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _xyz) =
        create_test_setup();
    let mut theory = MockTheory::new();
    let ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    let unmapped = TermId(999);
    assert_eq!(ext.var_for_term(unmapped), None);
}

#[test]
fn term_to_literal_positive_value() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _xyz) =
        create_test_setup();
    let x = _xyz[0];
    let mut theory = MockTheory::new();
    let ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    let lit = ext.term_to_literal(x, true).unwrap();
    assert!(lit.is_positive());
    assert_eq!(lit.variable(), Variable::new(1));
}

#[test]
fn term_to_literal_negative_value() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _xyz) =
        create_test_setup();
    let x = _xyz[0];
    let mut theory = MockTheory::new();
    let ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    let lit = ext.term_to_literal(x, false).unwrap();
    assert!(!lit.is_positive());
    assert_eq!(lit.variable(), Variable::new(1));
}

#[test]
fn term_to_literal_returns_none_for_unmapped() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _xyz) =
        create_test_setup();
    let mut theory = MockTheory::new();
    let ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    let unmapped = TermId(999);
    assert_eq!(ext.term_to_literal(unmapped, true), None);
}

#[test]
fn is_theory_atom_returns_true_for_atoms() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _xyz) =
        create_test_setup();
    let mut theory = MockTheory::new();
    let ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    assert!(ext.is_theory_atom(Variable::new(1)));
    assert!(ext.is_theory_atom(Variable::new(2)));
    assert!(ext.is_theory_atom(Variable::new(3)));
}

#[test]
fn is_theory_atom_works_with_unsorted_atom_order() {
    let (terms, var_to_term, term_to_var, mut theory_atoms, theory_atom_set, _xyz) =
        create_test_setup();
    theory_atoms.swap(0, 2);

    let mut theory = MockTheory::new();
    let ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    assert!(ext.is_theory_atom(Variable::new(1)));
    assert!(ext.is_theory_atom(Variable::new(2)));
    assert!(ext.is_theory_atom(Variable::new(3)));
}

#[test]
fn is_theory_atom_returns_false_for_non_atoms() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _xyz) =
        create_test_setup();
    let mut theory = MockTheory::new();
    let ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    // Variable 4 is not mapped
    assert!(!ext.is_theory_atom(Variable::new(4)));
}

#[test]
fn retain_new_axioms_skips_duplicate_axioms_across_extension_instances_issue_6586() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, xyz) = create_test_setup();
    let axiom = (xyz[0], true, xyz[1], false);
    let mut seen_axioms = HashSet::new();

    let mut theory = MockTheory::new().with_axiom_terms(vec![axiom]);
    let mut first = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );
    first.retain_new_axioms(&mut seen_axioms);
    assert_eq!(first.pending_axiom_terms, vec![axiom]);
    assert_eq!(first.pending_axiom_clauses.len(), 1);
    assert_eq!(seen_axioms.len(), 1);

    let mut theory = MockTheory::new().with_axiom_terms(vec![axiom]);
    let mut second = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );
    second.retain_new_axioms(&mut seen_axioms);
    assert!(second.pending_axiom_terms.is_empty());
    assert!(second.pending_axiom_clauses.is_empty());
    assert_eq!(seen_axioms.len(), 1);
}

#[test]
fn propagate_records_farkas_for_validated_bound_axioms_issue_6686() {
    use crate::proof_tracker::ProofTracker;
    use z4_core::{ProofStep, TheoryLemmaKind};

    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, [x_ge_0, x_le_0]) =
        create_lra_bound_axiom_setup();
    let mut theory = MockTheory::new().with_axiom_terms(vec![(x_ge_0, true, x_le_0, true)]);
    let mut tracker = ProofTracker::new();
    tracker.enable();
    tracker.set_theory("LRA");
    let negations = HashMap::new();

    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    )
    .with_proof_tracking(&mut tracker, &negations);

    let result = ext.propagate(&MockContext::new());
    assert_eq!(
        result.clauses.len(),
        1,
        "expected one pending bound axiom clause"
    );
    assert_eq!(
        result.clauses[0],
        vec![
            Literal::positive(Variable::new(1)),
            Literal::positive(Variable::new(2))
        ],
        "bound axiom literals should match the registered theory atoms"
    );
    assert!(
        result.conflict.is_none() && result.propagations.is_empty() && !result.stop,
        "bound-axiom injection should only add clauses: {result:?}"
    );
    assert!(
        ext.pending_axiom_terms.is_empty() && ext.pending_axiom_farkas.is_empty(),
        "propagate() should consume aligned bound-axiom proof data"
    );

    drop(ext);
    let proof = tracker.take_proof();
    let theory_lemmas: Vec<_> = proof
        .steps
        .iter()
        .filter_map(|step| match step {
            ProofStep::TheoryLemma {
                clause,
                farkas,
                kind,
                ..
            } => Some((clause.clone(), farkas.clone(), *kind)),
            _ => None,
        })
        .collect();
    assert_eq!(
        theory_lemmas.len(),
        1,
        "bound axiom injection should record exactly one theory lemma: {theory_lemmas:?}"
    );

    let (clause, farkas, kind) = &theory_lemmas[0];
    assert_eq!(*kind, TheoryLemmaKind::LraFarkas);
    assert_eq!(clause, &vec![x_ge_0, x_le_0]);
    let farkas = farkas
        .as_ref()
        .expect("validated LRA bound axiom should retain extracted Farkas coefficients");
    assert_eq!(
        farkas.coefficients.len(),
        clause.len(),
        "Farkas coefficients must stay aligned with bound-axiom literals"
    );
}

#[test]
fn retain_new_axioms_keeps_farkas_alignment_before_propagate_issue_6686() {
    use crate::proof_tracker::ProofTracker;
    use z4_core::{ProofStep, TheoryLemmaKind};

    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, [x_ge_0, x_le_0]) =
        create_lra_bound_axiom_setup();
    let mut theory = MockTheory::new().with_axiom_terms(vec![(x_ge_0, true, x_le_0, true)]);
    let mut tracker = ProofTracker::new();
    tracker.enable();
    tracker.set_theory("LRA");
    let negations = HashMap::new();

    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    )
    .with_proof_tracking(&mut tracker, &negations);

    let mut seen_axioms = HashSet::new();
    ext.retain_new_axioms(&mut seen_axioms);
    assert_eq!(seen_axioms.len(), 1, "expected one retained bound axiom");
    assert_eq!(
        ext.pending_axiom_clauses.len(),
        1,
        "retain_new_axioms() must not silently drop clauses with aligned Farkas sidecars"
    );
    assert_eq!(
        ext.pending_axiom_terms,
        vec![(x_ge_0, true, x_le_0, true)],
        "bound-axiom terms should stay aligned with clauses after retain_new_axioms()"
    );
    assert_eq!(
        ext.pending_axiom_farkas.len(),
        1,
        "retained bound axioms should keep one aligned Farkas sidecar"
    );
    assert!(
        ext.pending_axiom_farkas[0].is_some(),
        "retain_new_axioms() must preserve validation Farkas certificates"
    );

    let result = ext.propagate(&MockContext::new());
    assert_eq!(
        result.clauses,
        vec![vec![
            Literal::positive(Variable::new(1)),
            Literal::positive(Variable::new(2))
        ]],
        "propagate() should inject the retained bound axiom"
    );
    assert!(
        ext.pending_axiom_terms.is_empty() && ext.pending_axiom_farkas.is_empty(),
        "propagate() should consume aligned bound-axiom proof data"
    );

    drop(ext);
    let proof = tracker.take_proof();
    let theory_lemmas: Vec<_> = proof
        .steps
        .iter()
        .filter_map(|step| match step {
            ProofStep::TheoryLemma {
                clause,
                farkas,
                kind,
                ..
            } => Some((clause.clone(), farkas.clone(), *kind)),
            _ => None,
        })
        .collect();
    assert_eq!(
        theory_lemmas.len(),
        1,
        "bound axiom injection should record exactly one theory lemma after retain_new_axioms()"
    );

    let (clause, farkas, kind) = &theory_lemmas[0];
    assert_eq!(*kind, TheoryLemmaKind::LraFarkas);
    assert_eq!(clause, &vec![x_ge_0, x_le_0]);
    assert!(
        farkas.is_some(),
        "proof export should keep the bound-axiom Farkas annotation after retain_new_axioms()"
    );
}

#[test]
fn propagate_pushes_theory_level_to_match_sat_level() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _xyz) =
        create_test_setup();
    let mut theory = MockTheory::new();
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    let ctx = MockContext::new().with_level(3);
    ext.propagate(&ctx);

    assert_eq!(ext.theory.push_count, 3);
}

#[test]
fn propagate_asserts_theory_atoms_from_trail() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _xyz) =
        create_test_setup();
    let x = _xyz[0];
    let y = _xyz[1];
    let mut theory = MockTheory::new();
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    let trail = vec![
        Literal::positive(Variable::new(1)),
        Literal::negative(Variable::new(2)),
    ];
    let ctx = MockContext::new().with_trail(trail);
    ext.propagate(&ctx);

    assert_eq!(ext.theory.assertions.len(), 2);
    assert!(ext.theory.assertions.contains(&(x, true)));
    assert!(ext.theory.assertions.contains(&(y, false)));
}

#[test]
fn propagate_returns_none_when_no_propagations() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _xyz) =
        create_test_setup();
    let mut theory = MockTheory::new();
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    let ctx = MockContext::new();
    let result = ext.propagate(&ctx);

    // ExtPropagateResult is a struct, not an enum
    assert!(result.clauses.is_empty());
    assert!(result.conflict.is_none());
}

#[test]
fn propagate_returns_conflict_on_theory_unsat() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _xyz) =
        create_test_setup();
    let x = _xyz[0];
    let y = _xyz[1];

    let conflict = vec![TheoryLit::new(x, true), TheoryLit::new(y, false)];
    let mut theory = MockTheory::new().with_check_result(TheoryResult::Unsat(conflict));
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    let ctx = MockContext::new();
    let result = ext.propagate(&ctx);

    assert!(result.conflict.is_some());
}

#[test]
fn propagate_returns_clauses_for_propagations() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _xyz) =
        create_test_setup();
    let x = _xyz[0];
    let y = _xyz[1];
    let z = _xyz[2];

    // Theory says: if x=true and y=true, then z=true
    let prop = TheoryPropagation {
        literal: TheoryLit::new(z, true),
        reason: vec![TheoryLit::new(x, true), TheoryLit::new(y, true)],
    };
    let mut theory = MockTheory::new().with_propagations(vec![prop]);
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    // z is unassigned
    let trail = vec![
        Literal::positive(Variable::new(1)),
        Literal::positive(Variable::new(2)),
    ];
    let ctx = MockContext::new().with_trail(trail);
    let result = ext.propagate(&ctx);

    // Propagations go through the lightweight path (#4919)
    assert_eq!(result.propagations.len(), 1);
    // Clause should be (z ∨ ¬x ∨ ¬y) — propagated lit first
    let (clause, propagated) = &result.propagations[0];
    assert_eq!(clause.len(), 3);
    assert_eq!(*propagated, clause[0]);
}

#[test]
fn propagate_skips_invalid_semantic_propagation_without_rejection_cache_reset_issue_7965() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, [x_ge_0, _x_le_0]) =
        create_lra_bound_axiom_setup();

    let invalid_prop = TheoryPropagation {
        literal: TheoryLit::new(x_ge_0, true),
        reason: vec![],
    };
    let mut theory = MockTheory::new().with_propagations(vec![invalid_prop]);
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    let ctx = MockContext::new();
    let result = ext.propagate(&ctx);

    assert!(
        result.propagations.is_empty(),
        "semantic rejection should drop the invalid propagation"
    );
    assert!(
        ext.theory.rejected_propagations.is_empty(),
        "semantic rejection should no longer clear the theory cache via mark_propagation_rejected()"
    );
}

#[test]
fn check_returns_sat_when_theory_sat() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _xyz) =
        create_test_setup();
    let mut theory = MockTheory::new();
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    let ctx = MockContext::new();
    let result = ext.check(&ctx);

    assert!(matches!(result, ExtCheckResult::Sat));
}

#[test]
fn check_returns_conflict_when_theory_unsat() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _xyz) =
        create_test_setup();
    let x = _xyz[0];

    let conflict = vec![TheoryLit::new(x, true)];
    let mut theory = MockTheory::new().with_check_result(TheoryResult::Unsat(conflict));
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    let ctx = MockContext::new();
    let result = ext.check(&ctx);

    match result {
        ExtCheckResult::Conflict(clause) => {
            assert_eq!(clause.len(), 1);
        }
        _ => panic!("Expected Conflict, got {result:?}"),
    }
}

#[test]
fn check_returns_unknown_for_unknown_result() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _xyz) =
        create_test_setup();
    let mut theory = MockTheory::new().with_check_result(TheoryResult::Unknown);
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    let ctx = MockContext::new();
    let result = ext.check(&ctx);

    assert!(matches!(result, ExtCheckResult::Unknown));
}

#[test]
fn backtrack_pops_theory_levels() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _xyz) =
        create_test_setup();
    let mut theory = MockTheory::new();
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    // First push to level 5
    let ctx = MockContext::new().with_level(5);
    ext.propagate(&ctx);
    assert_eq!(ext.theory.push_count, 5);
    assert_eq!(ext.theory_level, 5);

    // Now backtrack to level 2
    ext.backtrack(2);

    assert_eq!(ext.theory.pop_count, 3);
    assert_eq!(ext.theory_level, 2);
    assert_eq!(ext.last_trail_pos, 0); // Restored from stack (was 0 at push time)
}

#[test]
fn backtrack_restores_trail_position_from_stack() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _xyz) =
        create_test_setup();
    let mut theory = MockTheory::new();
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    // SAT variables 1, 2, 3 map to theory atoms x, y, z
    let var_x = Variable::new(1);
    let var_y = Variable::new(2);
    let var_z = Variable::new(3);

    // Push to level 1 with empty trail
    let ctx1 = MockContext::new().with_level(1);
    ext.propagate(&ctx1);
    assert_eq!(ext.theory_level, 1);
    assert_eq!(ext.last_trail_pos, 0); // No trail assignments

    // Push to level 2 with 2 trail assignments
    let ctx2 = MockContext::new()
        .with_level(2)
        .with_trail(vec![Literal::positive(var_x), Literal::negative(var_y)]);
    ext.propagate(&ctx2);
    assert_eq!(ext.theory_level, 2);
    assert_eq!(ext.last_trail_pos, 2); // Processed 2 assignments

    // Push to level 3 with 1 more trail assignment (3 total)
    let ctx3 = MockContext::new().with_level(3).with_trail(vec![
        Literal::positive(var_x),
        Literal::negative(var_y),
        Literal::positive(var_z),
    ]);
    ext.propagate(&ctx3);
    assert_eq!(ext.theory_level, 3);
    assert_eq!(ext.last_trail_pos, 3); // Processed 3 assignments

    // Backtrack to level 2: should restore trail pos to 2 (saved before push to 3)
    ext.backtrack(2);
    assert_eq!(ext.theory_level, 2);
    assert_eq!(ext.last_trail_pos, 2); // Restored, NOT reset to 0

    // Backtrack to level 0: should restore trail pos to 0
    ext.backtrack(0);
    assert_eq!(ext.theory_level, 0);
    assert_eq!(ext.last_trail_pos, 0);
}

#[test]
fn backtrack_handles_no_ops() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _xyz) =
        create_test_setup();
    let mut theory = MockTheory::new();
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    // At level 0, backtrack to 0
    ext.backtrack(0);

    assert_eq!(ext.theory.pop_count, 0);
    assert_eq!(ext.theory_level, 0);
}

#[test]
fn init_resets_theory_and_state() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _xyz) =
        create_test_setup();
    let mut theory = MockTheory::new();
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    // Set some state
    let ctx = MockContext::new().with_level(3);
    ext.propagate(&ctx);
    ext.last_trail_pos = 10;

    // Now init
    ext.init();

    assert_eq!(ext.theory.reset_count, 1);
    assert_eq!(ext.last_trail_pos, 0);
    assert_eq!(ext.theory_level, 0);
}

#[test]
fn can_propagate_always_returns_true() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _xyz) =
        create_test_setup();
    let mut theory = MockTheory::new();
    let ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    let ctx = MockContext::new();
    assert!(ext.can_propagate(&ctx));
}

#[test]
fn propagate_checks_level0_after_zero_propagation_streak() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _xyz) =
        create_test_setup();
    let mut theory = MockTheory::new();
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );
    ext.has_checked = true;
    ext.zero_propagation_streak = 5;

    let ctx = MockContext::new().with_trail(vec![Literal::positive(Variable::new(1))]);
    let result = ext.propagate(&ctx);

    assert!(result.clauses.is_empty());
    assert!(result.propagations.is_empty());
    assert!(result.conflict.is_none());
    assert_eq!(ext.theory.check_calls, 1);
    assert_eq!(ext.deferred_atom_count, 0);
    assert_eq!(ext.last_trail_pos, 1);
    assert_eq!(ext.eager_stats().batch_defers, 0);
    assert_eq!(ext.eager_stats().level0_batch_guard_hits, 1);
    assert_eq!(ext.eager_stats().level0_checks, 1);
}

#[test]
fn propagate_checks_level0_when_deferred_atoms_are_near_batch_target() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _xyz) =
        create_test_setup();
    let mut theory = MockTheory::new();
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );
    ext.has_checked = true;
    ext.zero_propagation_streak = 5;
    ext.deferred_atom_count = 19;

    let ctx = MockContext::new().with_trail(vec![Literal::positive(Variable::new(1))]);
    let result = ext.propagate(&ctx);

    assert!(result.clauses.is_empty());
    assert!(result.propagations.is_empty());
    assert!(result.conflict.is_none());
    assert_eq!(ext.theory.check_calls, 1);
    assert_eq!(ext.deferred_atom_count, 0);
    assert_eq!(ext.last_trail_pos, 1);
    assert_eq!(ext.eager_stats().batch_defers, 0);
    assert_eq!(ext.eager_stats().level0_batch_guard_hits, 0);
    assert_eq!(ext.eager_stats().level0_checks, 1);
}

#[test]
fn propagate_does_not_batch_when_split_is_pending() {
    use num_bigint::BigInt;
    use num_rational::BigRational;
    use z4_core::SplitRequest;

    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _xyz) =
        create_test_setup();
    let mut theory = MockTheory::new();
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );
    ext.has_checked = true;
    ext.zero_propagation_streak = 5;
    ext.pending_split = Some(TheoryResult::NeedSplit(SplitRequest {
        variable: theory_atoms[0],
        value: BigRational::new(BigInt::from(5), BigInt::from(2)),
        floor: BigInt::from(2),
        ceil: BigInt::from(3),
    }));

    let ctx = MockContext::new()
        .with_level(1)
        .with_trail(vec![Literal::positive(Variable::new(1))]);
    let result = ext.propagate(&ctx);

    assert!(result.clauses.is_empty());
    assert!(result.propagations.is_empty());
    assert!(result.conflict.is_none());
    assert_eq!(ext.theory.check_calls, 1);
    assert_eq!(ext.deferred_atom_count, 0);
}

#[test]
fn propagate_stores_split_request_in_pending() {
    use num_bigint::BigInt;
    use num_rational::BigRational;
    use z4_core::SplitRequest;

    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _) = create_test_setup();
    let split = SplitRequest {
        variable: theory_atoms[0],
        value: BigRational::new(BigInt::from(5), BigInt::from(2)),
        floor: BigInt::from(2),
        ceil: BigInt::from(3),
    };
    let mut theory = MockTheory::new().with_check_result(TheoryResult::NeedSplit(split.clone()));
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    let ctx = MockContext::new();
    let result = ext.propagate(&ctx);
    assert!(result.conflict.is_none());
    assert!(result.clauses.is_empty());
    let pending = ext.take_pending_split();
    assert!(pending.is_some(), "split should be stored as pending");
    match pending.unwrap() {
        TheoryResult::NeedSplit(s) => assert_eq!(s.variable, split.variable),
        other => panic!("expected NeedSplit, got {other:?}"),
    }
    assert!(ext.take_pending_split().is_none());
}

/// Mock theory solver that claims EUF semantic checks are supported.
/// Used to test the `verify_euf_conflict` integration in the extension path.
#[cfg(test)]
struct EufMockTheory {
    inner: MockTheory,
}

#[cfg(test)]
impl EufMockTheory {
    fn new() -> Self {
        Self {
            inner: MockTheory::new(),
        }
    }

    fn with_check_result(mut self, result: TheoryResult) -> Self {
        self.inner = self.inner.with_check_result(result);
        self
    }
}

#[cfg(test)]
impl TheorySolver for EufMockTheory {
    fn assert_literal(&mut self, literal: TermId, value: bool) {
        self.inner.assert_literal(literal, value);
    }

    fn check(&mut self) -> TheoryResult {
        self.inner.check()
    }

    fn propagate(&mut self) -> Vec<TheoryPropagation> {
        self.inner.propagate()
    }

    fn push(&mut self) {
        self.inner.push();
    }

    fn pop(&mut self) {
        self.inner.pop();
    }

    fn reset(&mut self) {
        self.inner.reset();
    }

    fn supports_euf_semantic_check(&self) -> bool {
        true
    }
}

#[cfg(test)]
type EufTestSetup = (
    TermStore,
    HashMap<u32, TermId>,
    HashMap<TermId, u32>,
    Vec<TermId>,
    HashSet<TermId>,
    [TermId; 3],
    [TermId; 3],
);

/// Create a test setup with EUF equality terms.
///
/// Returns: (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set,
///           [a, b, c], [eq_ab, eq_bc, eq_ac])
///
/// Variables a, b, c are Int-sorted. Equalities map to SAT variables 1-3.
#[cfg(test)]
fn create_euf_test_setup() -> EufTestSetup {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let c = terms.mk_var("c", Sort::Int);

    let eq_ab = terms.mk_eq(a, b);
    let eq_bc = terms.mk_eq(b, c);
    let eq_ac = terms.mk_eq(a, c);

    let var_to_term: HashMap<u32, TermId> =
        [(1, eq_ab), (2, eq_bc), (3, eq_ac)].into_iter().collect();
    let term_to_var: HashMap<TermId, u32> =
        [(eq_ab, 1), (eq_bc, 2), (eq_ac, 3)].into_iter().collect();
    let mut theory_atoms = vec![eq_ab, eq_bc, eq_ac];
    theory_atoms.sort_unstable_by_key(|term| term.0);
    let theory_atom_set: HashSet<TermId> = theory_atoms.iter().copied().collect();

    (
        terms,
        var_to_term,
        term_to_var,
        theory_atoms,
        theory_atom_set,
        [a, b, c],
        [eq_ab, eq_bc, eq_ac],
    )
}

/// Valid EUF conflict (a=b, b=c, ¬(a=c)) accepted in propagate().
#[test]
fn propagate_euf_semantic_check_accepts_valid_conflict() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _, eqs) =
        create_euf_test_setup();
    let [eq_ab, eq_bc, eq_ac] = eqs;

    // Transitivity conflict: a=b ∧ b=c ∧ ¬(a=c) is UNSAT
    let conflict = vec![
        TheoryLit::new(eq_ab, true),
        TheoryLit::new(eq_bc, true),
        TheoryLit::new(eq_ac, false),
    ];
    let mut theory = EufMockTheory::new().with_check_result(TheoryResult::Unsat(conflict));
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    let ctx = MockContext::new();
    let result = ext.propagate(&ctx);

    // Should produce a conflict (not be skipped by verification)
    assert!(
        result.conflict.is_some(),
        "valid EUF conflict should pass semantic check and produce conflict"
    );
}

/// Invalid EUF conflict (a=b, ¬(a=c)) — semantically satisfiable — skipped.
#[test]
fn propagate_euf_semantic_check_rejects_invalid_conflict() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _, eqs) =
        create_euf_test_setup();
    let [eq_ab, _eq_bc, eq_ac] = eqs;

    // a=b ∧ ¬(a=c) is SAT (just set c ≠ a, c ≠ b)
    let conflict = vec![TheoryLit::new(eq_ab, true), TheoryLit::new(eq_ac, false)];
    let mut theory = EufMockTheory::new().with_check_result(TheoryResult::Unsat(conflict));
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    let ctx = MockContext::new();
    let result = ext.propagate(&ctx);

    // Should be skipped — EUF semantic check detects the conflict is satisfiable
    assert!(
        result.conflict.is_none(),
        "invalid EUF conflict should fail semantic check and be skipped"
    );
}

/// Valid EUF conflict accepted in check().
#[test]
fn check_euf_semantic_check_accepts_valid_conflict() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _, eqs) =
        create_euf_test_setup();
    let [eq_ab, eq_bc, eq_ac] = eqs;

    let conflict = vec![
        TheoryLit::new(eq_ab, true),
        TheoryLit::new(eq_bc, true),
        TheoryLit::new(eq_ac, false),
    ];
    let mut theory = EufMockTheory::new().with_check_result(TheoryResult::Unsat(conflict));
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    let ctx = MockContext::new();
    let result = ext.check(&ctx);

    assert!(
        matches!(result, ExtCheckResult::Conflict(_)),
        "valid EUF conflict should pass semantic check in check()"
    );
}

/// Invalid EUF conflict returns Unknown in check().
#[test]
fn check_euf_semantic_check_rejects_invalid_conflict() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _, eqs) =
        create_euf_test_setup();
    let [eq_ab, _eq_bc, eq_ac] = eqs;

    let conflict = vec![TheoryLit::new(eq_ab, true), TheoryLit::new(eq_ac, false)];
    let mut theory = EufMockTheory::new().with_check_result(TheoryResult::Unsat(conflict));
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    let ctx = MockContext::new();
    let result = ext.check(&ctx);

    assert!(
        matches!(result, ExtCheckResult::Unknown),
        "invalid EUF conflict should fail semantic check and return Unknown"
    );
}

#[test]
fn check_stores_split_request_in_pending() {
    use num_bigint::BigInt;
    use num_rational::BigRational;
    use z4_core::SplitRequest;

    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _) = create_test_setup();
    let split = SplitRequest {
        variable: theory_atoms[0],
        value: BigRational::new(BigInt::from(5), BigInt::from(2)),
        floor: BigInt::from(2),
        ceil: BigInt::from(3),
    };
    let mut theory = MockTheory::new().with_check_result(TheoryResult::NeedSplit(split.clone()));
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    let ctx = MockContext::new();
    let result = ext.check(&ctx);
    assert!(
        matches!(result, ExtCheckResult::Unknown),
        "check() with split should return Unknown, got {result:?}"
    );
    let pending = ext.take_pending_split();
    assert!(pending.is_some(), "split should be stored as pending");
    match pending.unwrap() {
        TheoryResult::NeedSplit(s) => assert_eq!(s.variable, split.variable),
        other => panic!("expected NeedSplit, got {other:?}"),
    }
}

#[test]
fn check_stores_pending_bound_refinements_on_sat() {
    use num_bigint::BigInt;
    use num_rational::BigRational;

    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, _) = create_test_setup();
    let refinement = BoundRefinementRequest {
        variable: theory_atoms[0],
        rhs_term: None,
        bound_value: BigRational::from(BigInt::from(3)),
        is_upper: true,
        is_integer: false,
        reason: vec![TheoryLit::new(theory_atoms[1], true)],
    };
    let mut theory = MockTheory::new().with_bound_refinements(vec![refinement.clone()]);
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    let ctx = MockContext::new();
    let result = ext.check(&ctx);
    assert!(matches!(result, ExtCheckResult::Sat));

    let pending = ext.take_pending_bound_refinements();
    assert_eq!(pending, vec![refinement]);
    assert!(ext.take_pending_bound_refinements().is_empty());
}

#[test]
fn propagate_preserves_pending_bound_refinements_until_final_check() {
    use num_bigint::BigInt;
    use num_rational::BigRational;

    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, xyz) = create_test_setup();
    let refinement = BoundRefinementRequest {
        variable: xyz[0],
        rhs_term: None,
        bound_value: BigRational::from(BigInt::from(3)),
        is_upper: true,
        is_integer: false,
        reason: vec![TheoryLit::new(xyz[1], true)],
    };
    let mut theory = PropagateOnlyRefinementTheory::new(refinement.clone());
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    let ctx = MockContext::new().with_trail(vec![Literal::positive(Variable::new(1))]);
    let result = ext.propagate(&ctx);
    assert!(result.clauses.is_empty());
    assert!(result.propagations.is_empty());
    assert!(result.conflict.is_none());

    let final_result = ext.check(&ctx);
    assert!(matches!(final_result, ExtCheckResult::Sat));
    assert_eq!(ext.take_pending_bound_refinements(), vec![refinement]);
}

#[test]
fn propagate_inline_bound_refinement_replay_stops_with_pending_requests_issue_6586() {
    use num_bigint::BigInt;
    use num_rational::BigRational;

    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, xyz) = create_test_setup();
    let refinement = BoundRefinementRequest {
        variable: xyz[0],
        rhs_term: None,
        bound_value: BigRational::from(BigInt::from(3)),
        is_upper: true,
        is_integer: false,
        reason: vec![TheoryLit::new(xyz[1], true)],
    };
    let mut theory = PropagateOnlyRefinementTheory::new(refinement.clone());
    let known_replays = HashSet::new();
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    )
    .with_inline_bound_refinement_replay(&known_replays);
    assert!(
        ext.should_stop_for_inline_bound_refinement_handoff(std::slice::from_ref(&refinement)),
        "inline replay mode should recognize unseen refinement requests before propagate()"
    );

    let ctx = MockContext::new().with_trail(vec![Literal::positive(Variable::new(1))]);
    let result = ext.propagate(&ctx);
    assert!(result.clauses.is_empty());
    assert!(result.propagations.is_empty());
    assert!(result.conflict.is_none());
    assert!(
        result.stop,
        "inline replay mode should stop SAT search when a new refinement appears"
    );
    assert_eq!(ext.take_pending_bound_refinements(), vec![refinement]);
}

#[test]
fn propagate_inline_bound_refinement_replay_ignores_known_requests_issue_6586() {
    use num_bigint::BigInt;
    use num_rational::BigRational;

    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, xyz) = create_test_setup();
    let refinement = BoundRefinementRequest {
        variable: xyz[0],
        rhs_term: None,
        bound_value: BigRational::from(BigInt::from(3)),
        is_upper: true,
        is_integer: false,
        reason: vec![TheoryLit::new(xyz[1], true)],
    };
    let mut theory = PropagateOnlyRefinementTheory::new(refinement.clone());
    let known_replays: HashSet<_> = [BoundRefinementReplayKey::new(&refinement)]
        .into_iter()
        .collect();
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    )
    .with_inline_bound_refinement_replay(&known_replays);

    let ctx = MockContext::new().with_trail(vec![Literal::positive(Variable::new(1))]);
    let result = ext.propagate(&ctx);
    assert!(
        !result.stop,
        "already replayed refinements should not re-trigger inline handoff"
    );
    assert_eq!(ext.take_pending_bound_refinements(), vec![refinement]);
}

#[test]
fn backtrack_clears_pending_bound_refinements_from_current_branch() {
    use num_bigint::BigInt;
    use num_rational::BigRational;

    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set, xyz) = create_test_setup();
    let refinement = BoundRefinementRequest {
        variable: xyz[0],
        rhs_term: None,
        bound_value: BigRational::from(BigInt::from(3)),
        is_upper: true,
        is_integer: false,
        reason: vec![TheoryLit::new(xyz[1], true)],
    };
    let mut theory = MockTheory::new().with_bound_refinements(vec![refinement.clone()]);
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );

    let ctx = MockContext::new()
        .with_level(1)
        .with_trail(vec![Literal::positive(Variable::new(1))]);
    let _ = ext.propagate(&ctx);
    assert_eq!(ext.pending_bound_refinements, vec![refinement]);

    ext.backtrack(0);
    assert!(ext.pending_bound_refinements.is_empty());
}
