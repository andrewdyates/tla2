// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::PdrSolver;
use crate::transform::ClauseInliner;
use crate::{ChcExpr, ChcParser, PdrConfig};

fn expected_non_lia_fact_bundle(must_summary: &ChcExpr) -> ChcExpr {
    let mut conjuncts = Vec::new();
    for conjunct in must_summary.collect_conjuncts() {
        if matches!(conjunct, ChcExpr::Bool(true)) {
            continue;
        }
        if conjunct.contains_array_ops() && !conjunct.is_bool_sorted_top_level() {
            continue;
        }
        if !conjuncts.contains(&conjunct) {
            conjuncts.push(conjunct);
        }
    }
    ChcExpr::not(ChcExpr::or_all(conjuncts.into_iter().map(ChcExpr::not)))
}

#[test]
fn startup_direct_safety_is_skipped_for_single_predicate_bv() {
    let smt2 = r#"
(set-logic HORN)
(declare-fun inv ((_ BitVec 8)) Bool)
(assert (forall ((x (_ BitVec 8))) (=> (= x #x00) (inv x))))
(assert (forall ((x (_ BitVec 8)) (x2 (_ BitVec 8)))
  (=> (and (inv x) (= x2 x)) (inv x2))))
(assert (forall ((x (_ BitVec 8))) (=> (and (inv x) (= x #x01)) false)))
(check-sat)
"#;

    let solver = PdrSolver::new(ChcParser::parse(smt2).unwrap(), PdrConfig::default());
    assert!(
        solver.skip_startup_direct_safety_proof(),
        "single-predicate native-BV problems should bypass startup direct safety"
    );
    assert!(
        !solver.use_bv_native_fast_startup_path(),
        "small native-BV simple loops should still run the full startup discovery pipeline"
    );
}

#[test]
fn startup_direct_safety_still_runs_for_non_bv_problem() {
    let smt2 = r#"
(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x Int) (x2 Int)) (=> (and (inv x) (= x2 x)) (inv x2))))
(assert (forall ((x Int)) (=> (and (inv x) (= x 1)) false)))
(check-sat)
"#;

    let solver = PdrSolver::new(ChcParser::parse(smt2).unwrap(), PdrConfig::default());
    assert!(
        !solver.skip_startup_direct_safety_proof(),
        "non-BV problems should keep the startup direct safety shortcut"
    );
}

#[test]
fn startup_direct_safety_still_runs_for_multi_transition_bv_problem() {
    let smt2 = r#"
(set-logic HORN)
(declare-fun inv ((_ BitVec 8)) Bool)
(assert (forall ((x (_ BitVec 8))) (=> (= x #x00) (inv x))))
(assert (forall ((x (_ BitVec 8)) (x2 (_ BitVec 8)))
  (=> (and (inv x) (= x2 (bvadd x #x01))) (inv x2))))
(assert (forall ((x (_ BitVec 8)) (x2 (_ BitVec 8)))
  (=> (and (inv x) (= x2 (bvsub x #x01))) (inv x2))))
(assert (forall ((x (_ BitVec 8))) (=> (and (inv x) (= x #x01)) false)))
(check-sat)
"#;

    let solver = PdrSolver::new(ChcParser::parse(smt2).unwrap(), PdrConfig::default());
    assert!(
        !solver.skip_startup_direct_safety_proof(),
        "multi-transition BV problems should keep the startup direct safety shortcut"
    );
}

#[test]
fn startup_fast_path_is_used_for_large_single_predicate_bv_problem() {
    const TEMP_COUNT: usize = 192;

    let binder_vars = (1..=TEMP_COUNT)
        .map(|i| format!("(t{i} (_ BitVec 8))"))
        .collect::<Vec<_>>()
        .join(" ");

    let mut transition = String::from("(and (inv x)");
    for i in 0..TEMP_COUNT {
        let src = if i == 0 {
            "x".to_string()
        } else {
            format!("t{i}")
        };
        let dst = format!("t{}", i + 1);
        transition.push_str(&format!(" (= {dst} (bvadd {src} #x01))"));
    }
    transition.push_str(&format!(" (= x2 t{TEMP_COUNT}))"));

    let smt2 = format!(
        r#"
(set-logic HORN)
(declare-fun inv ((_ BitVec 8)) Bool)
(assert (forall ((x (_ BitVec 8))) (=> (= x #x00) (inv x))))
(assert (forall ((x (_ BitVec 8))
                 (x2 (_ BitVec 8))
                 {binder_vars})
          (=> {transition} (inv x2))))
(assert (forall ((x (_ BitVec 8))) (=> (and (inv x) (= x #x01)) false)))
(check-sat)
"#
    );

    let solver = PdrSolver::new(ChcParser::parse(&smt2).unwrap(), PdrConfig::default());
    assert!(
        solver.skip_startup_direct_safety_proof(),
        "large native-BV simple loops should still bypass startup direct safety"
    );
    assert!(
        solver.use_bv_native_fast_startup_path(),
        "large native-BV simple loops should keep the lightweight startup path"
    );
}

#[test]
fn startup_nonfixpoint_applies_transition_affine_hints() {
    let smt2 = r#"
(set-logic HORN)

(declare-fun P (Int Int) Bool)
(declare-fun Q (Int Int) Bool)

(assert (forall ((a Int) (b Int))
  (=> (and (= a 0) (= b 0)) (P a b))))

(assert (forall ((a Int) (b Int) (a2 Int) (b2 Int))
  (=> (and (P a b) (= a2 (+ a 1)) (= b2 (+ b 2))) (P a2 b2))))

(assert (forall ((a Int) (b Int) (u Int) (v Int))
  (=> (and (P a b) (= u (+ a 1)) (= v (+ b 2))) (Q u v))))

(assert (forall ((u Int) (v Int) (u2 Int) (v2 Int))
  (=> (and (Q u v) (= u2 (+ u 1)) (= v2 (+ v 2))) (Q u2 v2))))

(assert (forall ((u Int) (v Int)) (=> (and (Q u v) (< v 0)) false)))

(check-sat)
"#;

    let mut solver = PdrSolver::new(ChcParser::parse(smt2).unwrap(), PdrConfig::default());
    let q = solver.problem.lookup_predicate("Q").unwrap();

    let result = solver.run_nonfixpoint_discovery();
    assert!(
        result.is_none(),
        "nonfixpoint discovery should not terminate solve early in this fixture"
    );

    let q_vars = solver.canonical_vars(q).unwrap().to_vec();
    let expected = solver
        .normalize_affine_equality_for_target(
            q,
            &ChcExpr::eq(
                ChcExpr::mul(ChcExpr::int(2), ChcExpr::var(q_vars[0].clone())),
                ChcExpr::var(q_vars[1].clone()),
            ),
        )
        .expect("normalize propagated affine equality");

    assert!(
        solver.frames[1].contains_lemma(q, &expected),
        "startup should inject propagated affine hint for Q"
    );
}

#[test]
fn startup_parity_retry_recovers_count_by_2_m_nest_after_inlining() {
    let input = include_str!(
        "../../../../../../benchmarks/chc-comp/2025/extra-small-lia/count_by_2_m_nest_000.smt2"
    );

    let problem = ChcParser::parse(input).unwrap();
    let inlined = ClauseInliner::new().inline(&problem);
    assert_eq!(
        inlined.predicates().len(),
        1,
        "multi-def inlining should collapse count_by_2_m_nest to one predicate"
    );

    let mut solver = PdrSolver::new(inlined, PdrConfig::default());
    assert!(
        solver.run_fixpoint_discovery().is_none(),
        "startup fixpoint should not terminate early for this benchmark"
    );
    assert!(
        solver.run_nonfixpoint_discovery().is_none(),
        "nonfixpoint startup should not terminate early for this benchmark"
    );

    let pred = solver.problem.predicates()[0].id;
    let vars = solver.canonical_vars(pred).unwrap().to_vec();

    let outer_mod_16 = ChcExpr::eq(
        ChcExpr::mod_op(ChcExpr::var(vars[0].clone()), ChcExpr::Int(16)),
        ChcExpr::Int(0),
    );
    let inner_exit_bound = ChcExpr::le(ChcExpr::var(vars[1].clone()), ChcExpr::Int(16));

    assert!(
        solver.frames[1].contains_lemma(pred, &inner_exit_bound),
        "parity retry should recover the deferred inner-loop exit bound"
    );
    assert!(
        solver.frames[1].contains_lemma(pred, &outer_mod_16),
        "inner-loop parity + exit bound should strengthen the outer counter to mod 16"
    );
}

#[test]
fn startup_nonfixpoint_builds_splitter_resistant_simple_bv_fact_bundle() {
    let input = include_str!(
        "../../../../../../benchmarks/chc-comp/chc-comp25-repo/vmt-chc-benchmarks/bv/simple.c_000.smt2"
    );

    let solver = PdrSolver::new(ChcParser::parse(input).unwrap(), PdrConfig::default());
    let pred = solver.problem.predicates()[0].id;
    let vars = solver.canonical_vars(pred).unwrap().to_vec();
    let must_summary = ChcExpr::and_all([
        ChcExpr::not(ChcExpr::var(vars[0].clone())),
        ChcExpr::not(ChcExpr::var(vars[1].clone())),
        ChcExpr::not(ChcExpr::var(vars[2].clone())),
    ]);
    let expected = expected_non_lia_fact_bundle(&must_summary);

    assert_eq!(
        solver.build_conjunctive_fact_clause_lemma(must_summary.collect_conjuncts()),
        expected,
        "simple.c_000 should encode the startup fact bundle in a splitter-resistant BV form"
    );
    assert_ne!(
        expected,
        ChcExpr::and_all(must_summary.collect_conjuncts()),
        "non-LIA startup fact bundles must avoid a plain top-level And that generic frame insertion can split"
    );
}

#[test]
fn startup_post_cancel_convergence_proven_uses_fresh_query_only_issue_4730() {
    let src = include_str!("mod.rs");
    let block_start = src
        .find("if let Some(mut model) = self.check_invariants_prove_safety() {")
        .expect("post-cancel startup safety block should exist");
    let block = &src[block_start..];
    let convergence_branch = block
        .find("if model.convergence_proven {")
        .map(|offset| &block[offset..])
        .expect("post-cancel startup safety block should branch on convergence_proven");

    assert!(
        convergence_branch.contains("self.verify_model_fresh_query_only(&model)"),
        "convergence-proven startup models must keep a fresh-context query-only confirmation"
    );
    assert!(
        !convergence_branch.contains("self.verify_model_query_only(&model)"),
        "convergence-proven startup models must not fall back to warm-context query-only verification"
    );
}
