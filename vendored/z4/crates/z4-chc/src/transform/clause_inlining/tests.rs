// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::unwrap_used)]

use super::*;
use crate::{ChcSort, ChcVar};

#[test]
fn test_inline_fact_clause() {
    // Init(0) ⇐ true
    // Loop(x) ⇐ Init(x)
    // Query: false ⇐ Loop(z), z > 100
    // After: Query should have no predicates (all inlined)

    let mut problem = ChcProblem::new();
    let init = problem.declare_predicate("Init", vec![ChcSort::Int]);
    let loop_pred = problem.declare_predicate("Loop", vec![ChcSort::Int]);

    // Init(x) ⇐ x = 0
    let x = ChcVar::new("x", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(init, vec![ChcExpr::var(x)]),
    ));

    // Loop(y) ⇐ Init(y)
    let y = ChcVar::new("y", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(init, vec![ChcExpr::var(y.clone())])]),
        ClauseHead::Predicate(loop_pred, vec![ChcExpr::var(y)]),
    ));

    // Query: false ⇐ Loop(z), z > 100
    let z = ChcVar::new("z", ChcSort::Int);
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(loop_pred, vec![ChcExpr::var(z.clone())])],
        Some(ChcExpr::gt(ChcExpr::var(z), ChcExpr::int(100))),
    )));

    let inliner = ClauseInliner::new();
    let result = inliner.inline(&problem);

    // Both Init and Loop should be inlined since they have unique definitions
    // No intermediate predicates should remain in any clause body
    for clause in result.clauses() {
        for (pred_id, _) in &clause.body.predicates {
            assert_ne!(*pred_id, init, "Init should be inlined");
            assert_ne!(*pred_id, loop_pred, "Loop should be inlined");
        }
    }

    // After full inlining, only the query should remain (with constraint)
    assert_eq!(result.clauses().len(), 1, "Only query should remain");
    assert!(
        result.clauses()[0].is_query(),
        "Remaining clause should be query"
    );
    assert!(
        result.clauses()[0].body.constraint.is_some(),
        "Query should have constraint from inlined definitions"
    );
}

#[test]
fn test_no_inline_recursive() {
    // Loop(x) ⇐ Loop(x-1), x > 0
    // Should NOT inline (self-recursive)

    let mut problem = ChcProblem::new();
    let loop_pred = problem.declare_predicate("Loop", vec![ChcSort::Int]);

    // Loop(x) ⇐ x = 0 (base case)
    let x = ChcVar::new("x", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(loop_pred, vec![ChcExpr::var(x)]),
    ));

    // Loop(x+1) ⇐ Loop(x), x >= 0
    let y = ChcVar::new("y", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(loop_pred, vec![ChcExpr::var(y.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(y.clone()), ChcExpr::int(0))),
        ),
        ClauseHead::Predicate(
            loop_pred,
            vec![ChcExpr::add(ChcExpr::var(y), ChcExpr::int(1))],
        ),
    ));

    // Query
    let z = ChcVar::new("z", ChcSort::Int);
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(loop_pred, vec![ChcExpr::var(z.clone())])],
        Some(ChcExpr::gt(ChcExpr::var(z), ChcExpr::int(100))),
    )));

    let inliner = ClauseInliner::new();
    let result = inliner.inline(&problem);

    // Loop should NOT be inlined because it has multiple definitions
    // and one is self-recursive
    let loop_clauses: Vec<_> = result
        .clauses()
        .iter()
        .filter(|c| c.head.predicate_id() == Some(loop_pred))
        .collect();
    assert!(
        loop_clauses.len() >= 2,
        "Loop should not be inlined (has multiple definitions)"
    );
}

#[test]
fn test_multi_def_inlining() {
    // P has 2 definitions and 1 tail use → multi-def inlining expands
    // Q's clause into 2 clauses (one per P definition), eliminating P.
    //
    // Before:
    //   P(x) ⇐ x = 0
    //   P(x) ⇐ x = 1
    //   Q(y) ⇐ P(y)
    //   false ⇐ Q(y), y > 10
    //
    // After multi-def inlining of P:
    //   Q(y) ⇐ (y = 0)     ; from P's first definition
    //   Q(y) ⇐ (y = 1)     ; from P's second definition
    //   false ⇐ Q(y), y > 10

    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int]);

    // P(x) ⇐ x = 0
    let x = ChcVar::new("x", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x.clone())]),
    ));

    // P(x) ⇐ x = 1
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(1))),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x)]),
    ));

    // Q(y) ⇐ P(y)
    let y = ChcVar::new("y", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(p, vec![ChcExpr::var(y.clone())])]),
        ClauseHead::Predicate(q, vec![ChcExpr::var(y.clone())]),
    ));

    // Query
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(q, vec![ChcExpr::var(y.clone())])],
        Some(ChcExpr::gt(ChcExpr::var(y), ChcExpr::int(10))),
    )));

    let inliner = ClauseInliner::new();
    let result = inliner.inline(&problem);

    // P should be inlined via multi-def expansion (2 defs, 1 tail use).
    // After P is inlined into Q, Q has 2 definitions and 1 tail use,
    // so Q is also eligible for unique-def inlining in the cleanup phase
    // (each Q definition is a fact clause with no body predicates).
    // The result is all predicates eliminated — only queries remain.
    let p_in_body = result
        .clauses()
        .iter()
        .any(|c| c.body.predicates.iter().any(|(id, _)| *id == p));
    assert!(!p_in_body, "P should be inlined via multi-def expansion");

    let q_in_body = result
        .clauses()
        .iter()
        .any(|c| c.body.predicates.iter().any(|(id, _)| *id == q));
    assert!(
        !q_in_body,
        "Q should also be inlined (becomes unique-def fact after P expansion)"
    );

    // Only query clauses should remain
    assert!(
        result.clauses().iter().all(HornClause::is_query),
        "All remaining clauses should be queries"
    );
    assert_eq!(
        result.clauses().len(),
        2,
        "Should have 2 query clauses (one per P definition path)"
    );
}

#[test]
fn test_break_cycle() {
    // A(x) ⇐ B(x)
    // B(x) ⇐ A(x)
    // Should break cycle and inline at most one

    let mut problem = ChcProblem::new();
    let a = problem.declare_predicate("A", vec![ChcSort::Int]);
    let b = problem.declare_predicate("B", vec![ChcSort::Int]);
    let c = problem.declare_predicate("C", vec![ChcSort::Int]);

    let x = ChcVar::new("x", ChcSort::Int);

    // A(x) ⇐ B(x), x >= 0
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(b, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ),
        ClauseHead::Predicate(a, vec![ChcExpr::var(x.clone())]),
    ));

    // B(x) ⇐ A(x), x < 100
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(a, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(100))),
        ),
        ClauseHead::Predicate(b, vec![ChcExpr::var(x.clone())]),
    ));

    // C(x) ⇐ A(x)
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(a, vec![ChcExpr::var(x.clone())])]),
        ClauseHead::Predicate(c, vec![ChcExpr::var(x.clone())]),
    ));

    // Query
    problem.add_clause(HornClause::query(ClauseBody::predicates_only(vec![(
        c,
        vec![ChcExpr::var(x)],
    )])));

    let inliner = ClauseInliner::new();
    let result = inliner.inline(&problem);

    // The cyclic predicates A and B should not cause infinite loop
    // At least one should remain (cycle is broken)
    let has_a = result
        .clauses()
        .iter()
        .any(|c| c.head.predicate_id() == Some(a));
    let has_b = result
        .clauses()
        .iter()
        .any(|c| c.head.predicate_id() == Some(b));

    // At least one of A or B should still exist (cycle prevents full inlining)
    assert!(
        has_a || has_b,
        "At least one cyclic predicate should remain"
    );
}

/// Tests inlining of predicates with complex head expressions.
///
/// This exercises the code path at lines 422-438 that handles non-variable
/// head arguments (e.g., P(x+1) instead of P(x)).
#[test]
fn test_inline_complex_head_expr() {
    // P(x+1) ⇐ x >= 0    ; defining clause with complex head
    // Q(y) ⇐ P(y)        ; usage
    // false ⇐ Q(z)       ; query
    //
    // After inlining P:
    // Q(y) should become: Q(y) ⇐ (x+1 = y) ∧ (x >= 0)

    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int]);

    let x = ChcVar::new("x", ChcSort::Int);

    // P(x+1) ⇐ x >= 0
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(p, vec![ChcExpr::add(ChcExpr::var(x), ChcExpr::int(1))]),
    ));

    // Q(y) ⇐ P(y)
    let y = ChcVar::new("y", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(p, vec![ChcExpr::var(y.clone())])]),
        ClauseHead::Predicate(q, vec![ChcExpr::var(y)]),
    ));

    // Query: false ⇐ Q(z), z > 100
    let z = ChcVar::new("z", ChcSort::Int);
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(q, vec![ChcExpr::var(z.clone())])],
        Some(ChcExpr::gt(ChcExpr::var(z), ChcExpr::int(100))),
    )));

    let inliner = ClauseInliner::new();
    let result = inliner.inline(&problem);

    // P should be inlined (unique non-recursive definition)
    let has_p_in_body = result
        .clauses()
        .iter()
        .any(|c| c.body.predicates.iter().any(|(id, _)| *id == p));
    assert!(!has_p_in_body, "P should be inlined into Q's definition");

    // The defining clause for Q should now have a constraint
    // that captures the complex head expression relationship (x+1 = y)
    let q_def: Vec<_> = result
        .clauses()
        .iter()
        .filter(|c| c.head.predicate_id() == Some(q))
        .collect();

    if !q_def.is_empty() {
        // Q's definition should have been updated with inlined constraint
        let q_clause = q_def[0];
        assert!(
            q_clause.body.constraint.is_some(),
            "Q's definition should have constraint after inlining P"
        );

        // The constraint should include the head expression equality
        let constraint_str = format!("{}", q_clause.body.constraint.as_ref().unwrap());
        // Should contain some form of equality involving the arithmetic expression
        assert!(
            constraint_str.contains("1") || constraint_str.contains("+"),
            "Constraint should capture the x+1 relationship: {constraint_str}"
        );
    }

    // Verify the solver can still process the transformed problem correctly
    // by checking it has valid structure
    assert!(
        !result.clauses().is_empty(),
        "Should have at least one clause"
    );
    let queries: Vec<_> = result.clauses().iter().filter(|c| c.is_query()).collect();
    assert_eq!(queries.len(), 1, "Should have exactly one query");
}

#[test]
fn test_chain_inlining() {
    // Tests that chained definitions are inlined in order:
    // A(x) ⇐ x = 0
    // B(x) ⇐ A(x)
    // C(x) ⇐ B(x)
    // Query: false ⇐ C(x)
    // After: Query should have constraint from A

    let mut problem = ChcProblem::new();
    let a = problem.declare_predicate("A", vec![ChcSort::Int]);
    let b = problem.declare_predicate("B", vec![ChcSort::Int]);
    let c = problem.declare_predicate("C", vec![ChcSort::Int]);

    let x = ChcVar::new("x", ChcSort::Int);

    // A(x) ⇐ x = 0
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(a, vec![ChcExpr::var(x.clone())]),
    ));

    // B(x) ⇐ A(x)
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(a, vec![ChcExpr::var(x.clone())])]),
        ClauseHead::Predicate(b, vec![ChcExpr::var(x.clone())]),
    ));

    // C(x) ⇐ B(x)
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(b, vec![ChcExpr::var(x.clone())])]),
        ClauseHead::Predicate(c, vec![ChcExpr::var(x.clone())]),
    ));

    // Query: false ⇐ C(x)
    problem.add_clause(HornClause::query(ClauseBody::predicates_only(vec![(
        c,
        vec![ChcExpr::var(x)],
    )])));

    let inliner = ClauseInliner::new();
    let result = inliner.inline(&problem);

    // All intermediate predicates should be inlined
    // The query should now be a fact (no predicates in body)
    let queries: Vec<_> = result.clauses().iter().filter(|c| c.is_query()).collect();
    assert_eq!(queries.len(), 1, "Should have exactly one query");

    // After full inlining, query body should be empty (a fact)
    assert!(
        queries[0].body.predicates.is_empty(),
        "Query should have no predicates after full chain inlining"
    );
}

/// Regression test for #5295: back-translation must synthesize interpretations
/// for inlined predicates with complex head arguments (e.g., P(x+1)).
///
/// Before fix: synthesize_interpretation returned None for complex heads,
/// causing the predicate's interpretation to be missing from the back-translated
/// model. Portfolio then rejected valid Safe results as "invalid invariant."
#[test]
fn test_back_translate_complex_head_synthesizes_interpretation() {
    use crate::pdr::model::PredicateInterpretation;
    use crate::transform::ValidityWitness;

    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int]);

    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    // P(x+1) <= x >= 0   (complex head arg)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(p, vec![ChcExpr::add(ChcExpr::var(x), ChcExpr::int(1))]),
    ));

    // Q(y) <= P(y)
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(p, vec![ChcExpr::var(y.clone())])]),
        ClauseHead::Predicate(q, vec![ChcExpr::var(y)]),
    ));

    // Query: false <= Q(z), z > 100
    let z = ChcVar::new("z", ChcSort::Int);
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(q, vec![ChcExpr::var(z.clone())])],
        Some(ChcExpr::gt(ChcExpr::var(z), ChcExpr::int(100))),
    )));

    // Transform using the Transformer trait (produces a back-translator)
    let inliner = Box::new(ClauseInliner::new());
    let TransformationResult {
        problem: _transformed,
        back_translator,
    } = inliner.transform(problem);

    // Simulate a solver model with only Q's interpretation (P was inlined)
    let q_var = ChcVar::new("q_arg", ChcSort::Int);
    let q_interp = PredicateInterpretation::new(
        vec![q_var.clone()],
        ChcExpr::ge(ChcExpr::var(q_var), ChcExpr::int(1)),
    );

    let mut model = ValidityWitness::new();
    model.set(q, q_interp);
    // P has NO interpretation — it was inlined away

    // Back-translate: P's interpretation should be synthesized
    let translated = back_translator.translate_validity(model);

    // P must now have an interpretation (the fix for #5295)
    assert!(
        translated.get(&p).is_some(),
        "BUG #5295: back-translator failed to synthesize interpretation for \
         inlined predicate P with complex head arg (x+1)"
    );
}

/// Regression for #425: back-translation after multi-def inlining must
/// existentially eliminate clause-local witness variables when reconstructing
/// the outer predicate from the inlined inner-loop invariant.
#[test]
fn test_back_translate_count_by_2_m_nest_eliminates_clause_local_witnesses() {
    use crate::pdr::{PdrConfig, PdrResult, PdrSolver};
    use crate::ChcParser;
    use rustc_hash::FxHashSet;

    let input = include_str!(
        "../../../../../benchmarks/chc-comp/2025/extra-small-lia/count_by_2_m_nest_000.smt2"
    );
    let original = ChcParser::parse(input).expect("benchmark should parse");
    let original_for_verify = original.clone();

    let TransformationResult {
        problem: transformed,
        back_translator,
    } = Box::new(ClauseInliner::new()).transform(original);

    assert_eq!(
        transformed.predicates().len(),
        1,
        "count_by_2_m_nest should inline to a single predicate"
    );

    let mut solver = PdrSolver::new(transformed, PdrConfig::default());
    let model = match solver.solve() {
        PdrResult::Safe(model) => model,
        _ => panic!("inlined count_by_2_m_nest should solve to Safe"),
    };

    let translated = back_translator.translate_validity(model);
    assert_eq!(
        translated.len(),
        original_for_verify.predicates().len(),
        "back-translation should reconstruct all original predicates"
    );

    for (pred_id, interp) in translated.iter() {
        let allowed: FxHashSet<ChcVar> = interp.vars.iter().cloned().collect();
        assert!(
            interp
                .formula
                .vars()
                .into_iter()
                .all(|var| allowed.contains(&var)),
            "back-translated predicate {} still contains clause-local variables: {}",
            pred_id.index(),
            interp.formula
        );
    }

    let mut verifier = PdrSolver::new(original_for_verify, PdrConfig::default());
    assert!(
        verifier.verify_model(&translated),
        "back-translated model for count_by_2_m_nest must validate on the original problem"
    );
}

/// Regression test: 2-predicate chain with 3-arg Post predicate.
/// After inlining, the query constraint should be UNSAT because stored = val
/// from the transition but not(stored = val) from the query.
/// Part of #7897: this case was returning "Trivially unsafe" incorrectly.
#[test]
fn test_inline_multi_arg_chain_soundness() {
    let mut problem = ChcProblem::new();
    let pre = problem.declare_predicate("Pre", vec![ChcSort::Int, ChcSort::Int]);
    let post = problem.declare_predicate("Post", vec![ChcSort::Int, ChcSort::Int, ChcSort::Int]);

    // Pre(p, v) <= (p = 0 /\ v >= 0)
    let p = ChcVar::new("p", ChcSort::Int);
    let v = ChcVar::new("v", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::and(
            ChcExpr::eq(ChcExpr::var(p.clone()), ChcExpr::int(0)),
            ChcExpr::ge(ChcExpr::var(v.clone()), ChcExpr::int(0)),
        )),
        ClauseHead::Predicate(pre, vec![ChcExpr::var(p.clone()), ChcExpr::var(v.clone())]),
    ));

    // Post(p2, s, v) <= Pre(p, v) /\ p2 = 1 /\ s = v
    let p2 = ChcVar::new("p2", ChcSort::Int);
    let s = ChcVar::new("s", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(pre, vec![ChcExpr::var(p.clone()), ChcExpr::var(v.clone())])],
            Some(ChcExpr::and(
                ChcExpr::eq(ChcExpr::var(p2.clone()), ChcExpr::int(1)),
                ChcExpr::eq(ChcExpr::var(s.clone()), ChcExpr::var(v.clone())),
            )),
        ),
        ClauseHead::Predicate(
            post,
            vec![
                ChcExpr::var(p2),
                ChcExpr::var(s.clone()),
                ChcExpr::var(v.clone()),
            ],
        ),
    ));

    // false <= Post(px, sx, vx) /\ sx != vx
    let px = ChcVar::new("px", ChcSort::Int);
    let sx = ChcVar::new("sx", ChcSort::Int);
    let vx = ChcVar::new("vx", ChcSort::Int);
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(
            post,
            vec![
                ChcExpr::var(px),
                ChcExpr::var(sx.clone()),
                ChcExpr::var(vx.clone()),
            ],
        )],
        Some(ChcExpr::not(ChcExpr::eq(
            ChcExpr::var(sx),
            ChcExpr::var(vx),
        ))),
    )));

    let inliner = ClauseInliner::new();
    let result = inliner.inline(&problem);

    // After inlining, only the query clause should remain
    assert_eq!(result.clauses().len(), 1, "Only query should remain");
    assert!(
        result.clauses()[0].is_query(),
        "Remaining clause should be query"
    );
    // The remaining clause should have no predicates in the body
    assert!(
        result.clauses()[0].body.predicates.is_empty(),
        "All predicates should be inlined"
    );

    // Print the inlined constraint for debugging
    let constraint = result.clauses()[0]
        .body
        .constraint
        .as_ref()
        .expect("Query should have a constraint after inlining");
    eprintln!("Inlined constraint: {constraint}");

    // CRITICAL: the query constraint should be UNSAT because the chain implies
    // stored = val, but the query asserts not(stored = val).
    // Check with SMT solver.
    use crate::smt::SmtResult;
    let mut smt = result.make_smt_context();
    match smt.check_sat(constraint) {
        SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
            // Correct! The constraint should be UNSAT.
        }
        SmtResult::Sat(model) => {
            panic!(
                "BUG: Inlined constraint should be UNSAT but SMT says SAT.\n\
                 Constraint: {constraint}\n\
                 Model: {model:?}\n\
                 This means the inliner lost the 's = v' constraint during inlining."
            );
        }
        SmtResult::Unknown => {
            panic!("SMT returned Unknown for inlined constraint - check SMT solver completeness");
        }
    }
}

/// Test that full preprocessing pipeline produces UNSAT constraint for
/// the multi-arg chain. This catches bugs where DeadParamEliminator or
/// LocalVarEliminator interact with ClauseInliner to lose constraints.
#[test]
fn test_full_preprocess_pipeline_multi_arg_chain() {
    use crate::transform::{DeadParamEliminator, LocalVarEliminator, TransformationPipeline};

    let mut problem = ChcProblem::new();
    let pre = problem.declare_predicate("Pre", vec![ChcSort::Int, ChcSort::Int]);
    let post = problem.declare_predicate("Post", vec![ChcSort::Int, ChcSort::Int, ChcSort::Int]);

    // Pre(p, v) <= (p = 0 /\ v >= 0)
    let p = ChcVar::new("p", ChcSort::Int);
    let v = ChcVar::new("v", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::and(
            ChcExpr::eq(ChcExpr::var(p.clone()), ChcExpr::int(0)),
            ChcExpr::ge(ChcExpr::var(v.clone()), ChcExpr::int(0)),
        )),
        ClauseHead::Predicate(pre, vec![ChcExpr::var(p.clone()), ChcExpr::var(v.clone())]),
    ));

    // Post(p2, s, v) <= Pre(p, v) /\ p2 = 1 /\ s = v
    let p2 = ChcVar::new("p2", ChcSort::Int);
    let s = ChcVar::new("s", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(pre, vec![ChcExpr::var(p.clone()), ChcExpr::var(v.clone())])],
            Some(ChcExpr::and(
                ChcExpr::eq(ChcExpr::var(p2.clone()), ChcExpr::int(1)),
                ChcExpr::eq(ChcExpr::var(s.clone()), ChcExpr::var(v.clone())),
            )),
        ),
        ClauseHead::Predicate(
            post,
            vec![
                ChcExpr::var(p2),
                ChcExpr::var(s.clone()),
                ChcExpr::var(v.clone()),
            ],
        ),
    ));

    // false <= Post(px, sx, vx) /\ sx != vx
    let px = ChcVar::new("px", ChcSort::Int);
    let sx = ChcVar::new("sx", ChcSort::Int);
    let vx = ChcVar::new("vx", ChcSort::Int);
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(
            post,
            vec![
                ChcExpr::var(px),
                ChcExpr::var(sx.clone()),
                ChcExpr::var(vx.clone()),
            ],
        )],
        Some(ChcExpr::not(ChcExpr::eq(
            ChcExpr::var(sx),
            ChcExpr::var(vx),
        ))),
    )));

    // Run the full preprocessing pipeline (same order as PreprocessSummary::build
    // for the LIA case, skipping BV transforms)
    let pipeline = TransformationPipeline::new()
        .with(DeadParamEliminator::new())
        .with(LocalVarEliminator::new())
        .with(DeadParamEliminator::new())
        .with(ClauseInliner::new());
    let result = pipeline.transform(problem);
    let preprocessed = result.problem;

    eprintln!("Preprocessed problem:");
    eprintln!("  Clauses: {}", preprocessed.clauses().len());
    eprintln!("  Predicates: {}", preprocessed.predicates().len());
    for (i, clause) in preprocessed.clauses().iter().enumerate() {
        eprintln!(
            "  Clause {i}: body_preds={}, constraint={:?}",
            clause.body.predicates.len(),
            clause.body.constraint.as_ref().map(|c| format!("{c}"))
        );
    }

    // All queries should have UNSAT constraints
    for query in preprocessed.queries() {
        let constraint = query.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));
        eprintln!("  Query constraint: {constraint}");

        use crate::smt::SmtResult;
        let mut smt = preprocessed.make_smt_context();
        match smt.check_sat(&constraint) {
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                // Correct
            }
            SmtResult::Sat(model) => {
                panic!(
                    "BUG: Preprocessed query constraint should be UNSAT but SMT says SAT.\n\
                     Constraint: {constraint}\n\
                     Model: {model:?}\n\
                     Full preprocessing pipeline lost the 's = v' implication."
                );
            }
            SmtResult::Unknown => {
                panic!("SMT returned Unknown for preprocessed constraint");
            }
        }
    }
}

/// Test that parsing + preprocessing produces UNSAT constraint for the
/// multi-arg chain when loaded from SMT2 format.
/// Part of #7897: the binary returns "unknown" instead of "sat".
#[test]
fn test_parse_preprocess_multi_arg_chain_soundness() {
    use crate::parser::ChcParser;
    use crate::transform::{DeadParamEliminator, LocalVarEliminator, TransformationPipeline};

    let input = r#"
(set-logic HORN)
(declare-fun Pre (Int Int) Bool)
(declare-fun Post (Int Int Int) Bool)

(assert (forall ((p Int) (v Int))
    (=> (and (= p 0) (>= v 0))
        (Pre p v))))

(assert (forall ((p Int) (v Int) (p2 Int) (s Int))
    (=> (and (Pre p v)
             (= p2 1)
             (= s v))
        (Post p2 s v))))

(assert (forall ((px Int) (sx Int) (vx Int))
    (=> (and (Post px sx vx) (not (= sx vx)))
        false)))

(check-sat)
"#;

    let problem = ChcParser::parse(input).expect("parse should succeed");

    eprintln!("Parsed problem:");
    eprintln!("  Predicates: {}", problem.predicates().len());
    eprintln!("  Clauses: {}", problem.clauses().len());
    for (i, clause) in problem.clauses().iter().enumerate() {
        eprintln!(
            "  Clause {i}: head={:?}, body_preds={}, constraint={}",
            clause.head,
            clause.body.predicates.len(),
            clause
                .body
                .constraint
                .as_ref()
                .map_or("None".to_string(), |c| format!("{c}"))
        );
    }

    // Run the same preprocessing pipeline as the portfolio
    let pipeline = TransformationPipeline::new()
        .with(DeadParamEliminator::new())
        .with(LocalVarEliminator::new())
        .with(DeadParamEliminator::new())
        .with(ClauseInliner::new());
    let result = pipeline.transform(problem);
    let preprocessed = result.problem;

    eprintln!("After preprocessing:");
    eprintln!("  Clauses: {}", preprocessed.clauses().len());
    eprintln!("  Predicates: {}", preprocessed.predicates().len());
    for (i, clause) in preprocessed.clauses().iter().enumerate() {
        eprintln!(
            "  Clause {i}: body_preds={}, constraint={}",
            clause.body.predicates.len(),
            clause
                .body
                .constraint
                .as_ref()
                .map_or("None".to_string(), |c| format!("{c}"))
        );
    }

    // After inlining, the query constraint should be UNSAT
    for query in preprocessed.queries() {
        let constraint = query.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));
        eprintln!("Query constraint: {constraint}");

        use crate::smt::SmtResult;
        let mut smt = preprocessed.make_smt_context();
        match smt.check_sat(&constraint) {
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                // Correct! Chain implies s=v, and query says not(s=v).
            }
            SmtResult::Sat(model) => {
                panic!(
                    "BUG: Parsed+preprocessed constraint should be UNSAT but SMT says SAT.\n\
                     Constraint: {constraint}\n\
                     Model: {model:?}"
                );
            }
            SmtResult::Unknown => {
                panic!("SMT returned Unknown for parsed+preprocessed constraint");
            }
        }
    }
}
