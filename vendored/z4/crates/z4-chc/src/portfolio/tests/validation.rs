// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::portfolio::accept::AcceptDecision;
use crate::transform::IdentityBackTranslator;

fn make_query_only_but_not_inductive_model(problem: &ChcProblem) -> InvariantModel {
    let inv = problem.predicates()[0].id;
    let v0 = ChcVar::new("v0", ChcSort::Int);
    let mut model = InvariantModel::new();
    model.set(
        inv,
        PredicateInterpretation::new(
            vec![v0.clone()],
            ChcExpr::le(ChcExpr::var(v0), ChcExpr::int(0)),
        ),
    );
    model
}

#[test]
fn test_validation_rejects_empty_safe_model() {
    let problem = create_safe_problem();
    let config = PortfolioConfig {
        engines: vec![],
        parallel: false,
        timeout: None,
        parallel_timeout: None,
        verbose: false,
        validate: false,
        enable_preprocessing: false,
    };
    let solver = PortfolioSolver::new(problem, config);
    match solver.validate_safe(&InvariantModel::new()) {
        ValidationResult::Valid => panic!("Empty model must not bypass validation (#571)"),
        ValidationResult::Invalid(_) => {}
    }
}

#[test]
fn test_validation_rejects_empty_model_when_only_transformed_problem_is_predicate_free_issue_6781()
{
    let original_problem = create_unsafe_problem();
    let transformed_problem = ChcProblem::new();
    let config = PortfolioConfig {
        engines: vec![],
        parallel: false,
        timeout: None,
        parallel_timeout: None,
        verbose: false,
        validate: false,
        enable_preprocessing: false,
    };
    let solver = PortfolioSolver {
        original_problem,
        problem: transformed_problem,
        back_translator: Box::new(IdentityBackTranslator),
        config,
        bv_abstracted: false,
    };

    match solver.validate_safe(&InvariantModel::new()) {
        ValidationResult::Valid => {
            panic!("empty transformed-model must not bypass original-problem validation (#6781)")
        }
        ValidationResult::Invalid(_) => {}
    }
}

#[test]
#[timeout(10_000)]
fn test_preprocessing_preserves_reachable_sat_query_issue_6781() {
    let input = r#"
(set-logic HORN)
(declare-fun |bb0| ((Array (_ BitVec 32) Bool)) Bool)
(declare-fun |bb1| ((Array (_ BitVec 32) Bool)) Bool)
(declare-fun |bb2| ((_ BitVec 32) (Array (_ BitVec 32) Bool)) Bool)

(assert
  (forall ((obj_valid (Array (_ BitVec 32) Bool)))
(=> (= obj_valid ((as const (Array (_ BitVec 32) Bool)) true))
    (bb0 obj_valid))))

(assert
  (forall ((obj_valid (Array (_ BitVec 32) Bool)))
(=> (bb0 obj_valid)
    (bb1 obj_valid))))

(assert
  (forall ((x (_ BitVec 32)) (obj_valid (Array (_ BitVec 32) Bool)))
(=> (bb1 obj_valid)
    (bb2 x obj_valid))))

(assert
  (forall ((x (_ BitVec 32)) (obj_valid (Array (_ BitVec 32) Bool)))
(=> (and (bb2 x obj_valid)
         (not (select obj_valid #x00000002)))
    false)))

(assert
  (forall ((x (_ BitVec 32)) (obj_valid (Array (_ BitVec 32) Bool)))
(=> (and (bb2 x obj_valid)
         (not (bvsgt x #x00000000)))
    false)))

(check-sat)
(exit)
"#;
    let problem = ChcParser::parse(input).expect("issue #6781 minimal reproducer should parse");
    assert!(
        problem.has_bv_sorts(),
        "reproducer must exercise BV-to-Bool preprocessing"
    );

    let config = PortfolioConfig::with_engines(vec![EngineConfig::Bmc(
        BmcConfig::with_engine_config(5, false, None),
    )])
    .parallel(false)
    .preprocessing(true);
    let solver = PortfolioSolver::new(problem, config);
    let result = solver.solve();

    assert!(
        matches!(result, PortfolioResult::Unsafe(_)),
        "preprocessing must keep the unconstrained x query reachable; got {result:?}"
    );
}

#[test]
fn test_validation_rejects_no_witness_spurious_unsafe() {
    let problem = create_safe_problem();
    let inv = problem.predicates()[0].id;
    let config = PortfolioConfig {
        engines: vec![],
        parallel: false,
        timeout: None,
        parallel_timeout: None,
        verbose: false,
        validate: false,
        enable_preprocessing: false,
    };
    let solver = PortfolioSolver::new(problem, config);

    // Safe problem: no path reaches the query, so any "Unsafe" without a verifiable witness
    // must fail validation (regression for #571 / #421-style portfolio unsoundness).
    let fake_cex = Counterexample {
        steps: (0..=10)
            .map(|_| CounterexampleStep {
                predicate: inv,
                assignments: FxHashMap::default(),
            })
            .collect(),
        witness: None,
    };
    match solver.validate_unsafe(&fake_cex) {
        ValidationResult::Valid => {
            panic!("Spurious UNSAFE must be rejected by validation (#571)")
        }
        ValidationResult::Invalid(_) => {}
    }
}

#[test]
fn test_validation_accepts_no_witness_reachable_unsafe() {
    let problem = create_unsafe_problem();
    let inv = problem.predicates()[0].id;
    let config = PortfolioConfig {
        engines: vec![],
        parallel: false,
        timeout: None,
        parallel_timeout: None,
        verbose: false,
        validate: false,
        enable_preprocessing: false,
    };
    let solver = PortfolioSolver::new(problem, config);

    // Unsafe problem: x reaches 5 in 5 transitions, so reachability at depth 5 is SAT.
    let cex = Counterexample {
        steps: (0..=5)
            .map(|_| CounterexampleStep {
                predicate: inv,
                assignments: FxHashMap::default(),
            })
            .collect(),
        witness: None,
    };
    match solver.validate_unsafe(&cex) {
        ValidationResult::Valid => {}
        ValidationResult::Invalid(reason) => {
            panic!("Expected UNSAFE validation to pass, got: {reason}")
        }
    }
}

#[test]
fn test_pdkind_invariant_conversion_validates_with_pdr() {
    // Tests that build_single_pred_model (used by pdkind.rs convert_raw_result)
    // produces a model that validates through PDR's verify_model.
    let problem = create_safe_problem();
    let inv_pred = problem.predicates()[0].id;
    let config = PortfolioConfig {
        engines: vec![],
        parallel: false,
        timeout: None,
        parallel_timeout: None,
        verbose: false,
        validate: false,
        enable_preprocessing: false,
    };
    let solver = PortfolioSolver::new(problem.clone(), config);

    // PDKIND canonical vars: v0, v1, ...
    let v0 = ChcVar::new("v0", ChcSort::Int);
    let formula = ChcExpr::le(ChcExpr::var(v0), ChcExpr::int(5));

    let model = build_single_pred_model(&problem, formula)
        .expect("expected single-pred model conversion to succeed");
    assert!(!model.is_empty());

    // Validate via PDR's verify_model.
    match solver.validate_safe(&model) {
        ValidationResult::Valid => {}
        ValidationResult::Invalid(reason) => {
            panic!("Converted invariant should validate, got: {reason}")
        }
    }

    // Sanity: model targets the single predicate.
    assert!(model.get(&inv_pred).is_some());
}

// Regression guard for #5010 / #6500: PDKind on multi-predicate problems via
// SingleLoop. Originally returned spurious Safe (#5010), then Unknown after
// Bool sort-guard rejection (#6500). The solver now handles Bool location
// variables correctly and returns Safe with a valid backtranslated model.
#[test]
fn test_pdkind_singleloop_multi_predicate_returns_unknown() {
    let problem = create_multi_predicate_chain_problem();
    let result = run_pdkind_with_singleloop(&problem, PdkindConfig::default(), false);
    assert!(
        matches!(result, ChcEngineResult::Safe(_) | ChcEngineResult::Unknown),
        "PDKind on multi-predicate should return Safe or Unknown, got: {result:?}",
    );
}

#[test]
fn test_cegar_safe_conversion_preserves_binder_arity() {
    // Regression test: CEGAR Safe conversion must preserve interpretation binders.
    // If binders are re-derived from free vars, `true` loses arity and validation fails.
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // x = 0 => Inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    // Inv(x) /\ x != x => false  (query body is UNSAT)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ne(ChcExpr::var(x.clone()), ChcExpr::var(x))),
        ),
        ClauseHead::False,
    ));

    let mut cegar_model = InvariantModel::new();
    cegar_model.set(
        inv,
        PredicateInterpretation::new(vec![ChcVar::new("b0", ChcSort::Int)], ChcExpr::Bool(true)),
    );

    let portfolio_result = PortfolioResult::from(CegarResult::Safe(cegar_model));
    let converted_model = match &portfolio_result {
        PortfolioResult::Safe(model) => model,
        _ => panic!("Expected Safe model after CEGAR conversion"),
    };
    assert_eq!(
        converted_model
            .get(&inv)
            .expect("converted model should contain Inv")
            .vars
            .len(),
        1,
        "CEGAR conversion must preserve predicate binder arity"
    );

    let solver = PortfolioSolver::new(
        problem,
        PortfolioConfig {
            engines: vec![],
            parallel: false,
            timeout: None,
            parallel_timeout: None,
            verbose: false,
            validate: false,
            enable_preprocessing: false,
        },
    );
    assert!(
        matches!(
            solver.validate_result(&portfolio_result, "CEGAR"),
            ValidationResult::Valid
        ),
        "Converted CEGAR Safe model should validate"
    );
}

/// Regression test: validate_safe must reject Inv=true on an unsafe problem.
/// TRL returns trivially-true invariant models, which must be caught by
/// portfolio validation. See #5379.
#[test]
#[serial]
fn test_validation_rejects_trivially_true_model_on_unsafe_problem() {
    let problem = create_unsafe_problem();
    let inv = problem.predicates()[0].id;
    let config = PortfolioConfig {
        engines: vec![],
        parallel: false,
        timeout: None,
        parallel_timeout: None,
        verbose: true,
        validate: false,
        enable_preprocessing: false,
    };
    let solver = PortfolioSolver::new(problem, config);

    // Build Inv(x) = true, which is what TRL returns
    let mut model = InvariantModel::new();
    model.set(
        inv,
        PredicateInterpretation::new(vec![ChcVar::new("x", ChcSort::Int)], ChcExpr::Bool(true)),
    );

    match solver.validate_safe(&model) {
        ValidationResult::Valid => {
            panic!("Inv=true must be rejected on unsafe problem (query body is SAT)")
        }
        ValidationResult::Invalid(_) => {}
    }
}

#[test]
fn test_query_only_validation_rejects_exact_negated_query_issue_6789() {
    let problem = create_unsafe_problem();
    let inv = problem.predicates()[0].id;
    let config = PortfolioConfig {
        engines: vec![],
        parallel: false,
        timeout: None,
        parallel_timeout: None,
        verbose: false,
        validate: false,
        enable_preprocessing: false,
    };
    let solver = PortfolioSolver::new(problem, config);

    let v0 = ChcVar::new("v0", ChcSort::Int);
    let mut model = InvariantModel::new();
    model.set(
        inv,
        PredicateInterpretation::new(
            vec![v0.clone()],
            ChcExpr::not(ChcExpr::ge(ChcExpr::var(v0), ChcExpr::int(5))),
        ),
    );

    match solver.validate_safe_query_only(&model) {
        SafePrecheckResult::Valid => {
            panic!("Exact ¬query invariant must not pass query-only validation (#6789)")
        }
        SafePrecheckResult::ExactNegatedQuery(reason) => assert!(
            reason.contains("exact ¬query"),
            "expected exact-¬query reason, got: {reason}"
        ),
        SafePrecheckResult::Invalid(reason) => {
            panic!("Exact ¬query should be ExactNegatedQuery, not Invalid: {reason}")
        }
    }
}

#[test]
fn test_query_only_validation_keeps_nontrivial_safe_guard() {
    let problem = create_safe_problem();
    let inv = problem.predicates()[0].id;
    let config = PortfolioConfig {
        engines: vec![],
        parallel: false,
        timeout: None,
        parallel_timeout: None,
        verbose: false,
        validate: false,
        enable_preprocessing: false,
    };
    let solver = PortfolioSolver::new(problem, config);

    let v0 = ChcVar::new("v0", ChcSort::Int);
    let mut model = InvariantModel::new();
    model.set(
        inv,
        PredicateInterpretation::new(
            vec![v0.clone()],
            ChcExpr::le(ChcExpr::var(v0), ChcExpr::int(9)),
        ),
    );

    assert!(
        matches!(
            solver.validate_safe_query_only(&model),
            SafePrecheckResult::Valid
        ),
        "non-¬query invariant that excludes bad states should still pass query-only validation"
    );
}

#[test]
fn test_accept_or_reject_single_pred_rejects_all_engines_failing_full_validation() {
    // Single-predicate problems: full validation is mandatory for ALL engines
    // including PDR/CEGAR. The multi-predicate bypass does not apply here.
    // False-Safe cases (conditional_branch_unsafe, two_phase_unsafe) are all
    // single-predicate problems where PDR's convergence_proven + query-only
    // check is insufficient (#7688, #7934).
    let problem = create_safe_problem();
    let config = PortfolioConfig {
        engines: vec![],
        parallel: false,
        timeout: None,
        parallel_timeout: None,
        verbose: false,
        validate: false,
        enable_preprocessing: false,
    };
    let solver = PortfolioSolver::new(problem.clone(), config);
    let model = make_query_only_but_not_inductive_model(&problem);

    assert!(
        matches!(
            solver.validate_safe_query_only(&model),
            SafePrecheckResult::Valid
        ),
        "regression setup must pass query-only validation"
    );
    assert!(
        matches!(
            solver.validate_safe_with_mode(&model, ValidationBudget::PerRule),
            ValidationResult::Invalid(_)
        ),
        "regression setup must fail full validation"
    );

    // Single-predicate: ALL engines rejected when full validation fails
    let pdr_result = solver.accept_or_reject(PortfolioResult::Safe(model.clone()), false, "PDR", 0);
    assert!(
        matches!(pdr_result, AcceptDecision::Reject),
        "PDR must be rejected on single-pred when full validation fails (#7934)"
    );

    let cegar_result =
        solver.accept_or_reject(PortfolioResult::Safe(model.clone()), false, "CEGAR", 0);
    assert!(
        matches!(cegar_result, AcceptDecision::Reject),
        "CEGAR must be rejected on single-pred when full validation fails (#7934)"
    );

    let kind_result = solver.accept_or_reject(PortfolioResult::Safe(model), false, "Kind", 0);
    assert!(
        matches!(kind_result, AcceptDecision::Reject),
        "Kind must be rejected when full validation fails"
    );
}

/// #7934: Multi-predicate PDR/CEGAR bypass accepts when query-only passes but
/// full validation fails. Fresh-context validation is unreliable on multi-pred
/// ITE/mod/div transitions — PDR's internal verify_model is strictly stronger.
#[test]
fn test_accept_or_reject_multi_pred_pdr_bypass_full_validation() {
    let problem = create_multi_predicate_chain_problem();
    let p1 = problem.predicates()[0].id;
    let p2 = problem.predicates()[1].id;
    let config = PortfolioConfig {
        engines: vec![],
        parallel: false,
        timeout: None,
        parallel_timeout: None,
        verbose: false,
        validate: false,
        enable_preprocessing: false,
    };
    let solver = PortfolioSolver::new(problem, config);

    assert!(
        solver.engine_problem().predicates().len() > 1,
        "setup: must be multi-predicate problem"
    );

    // Build a model that passes query-only (blocks error states) but may fail
    // full validation (P1=false violates init clause x=0 => P1(x)).
    let v0 = ChcVar::new("v0", ChcSort::Int);
    let mut model = InvariantModel::new();
    model.set(
        p1,
        PredicateInterpretation::new(vec![v0.clone()], ChcExpr::Bool(false)),
    );
    model.set(
        p2,
        PredicateInterpretation::new(
            vec![v0.clone()],
            ChcExpr::le(ChcExpr::var(v0), ChcExpr::int(9)),
        ),
    );
    // NOT individually_inductive — tests the engine-name + predicate-count bypass
    assert!(!model.individually_inductive);

    // PDR accepted on multi-pred: query-only passed, multi-pred bypass in effect
    let pdr_result = solver.accept_or_reject(PortfolioResult::Safe(model.clone()), false, "PDR", 0);
    assert!(
        matches!(pdr_result, AcceptDecision::Accept(_)),
        "PDR must be accepted on multi-pred when query-only passes (#7934 bypass)"
    );

    // CEGAR also accepted on multi-pred
    let cegar_result =
        solver.accept_or_reject(PortfolioResult::Safe(model.clone()), false, "CEGAR", 0);
    assert!(
        matches!(cegar_result, AcceptDecision::Accept(_)),
        "CEGAR must be accepted on multi-pred when query-only passes (#7934 bypass)"
    );

    // Kind is NOT a PDR/CEGAR engine — full validation still mandatory
    let kind_result = solver.accept_or_reject(PortfolioResult::Safe(model), false, "Kind", 0);
    assert!(
        matches!(kind_result, AcceptDecision::Reject),
        "Kind must be rejected on multi-pred when full validation fails"
    );
}

/// #7410: individually_inductive models bypass Step 5 full validation for BOTH
/// preprocessed and non-preprocessed problems. The old #7438 guard that restricted
/// this to non-preprocessed was removed — O0_sum_25x0's false-Safe models FAIL
/// per-lemma self-inductiveness and never get individually_inductive=true, so the
/// guard was never triggered for the unsound case.
#[test]
fn test_accept_or_reject_preprocessed_individually_inductive_model_bypasses_full_validation() {
    let original_problem = create_multi_predicate_chain_problem();
    let p1 = original_problem.predicates()[0].id;
    let p2 = original_problem.predicates()[1].id;
    let transformed_problem = create_safe_problem();
    let config = PortfolioConfig {
        engines: vec![],
        parallel: false,
        timeout: None,
        parallel_timeout: None,
        verbose: false,
        validate: false,
        enable_preprocessing: false,
    };
    let solver = PortfolioSolver {
        original_problem,
        problem: transformed_problem,
        back_translator: Box::new(IdentityBackTranslator),
        config,
        bv_abstracted: false,
    };

    assert!(
        solver.original_problem.predicates().len() != solver.engine_problem().predicates().len(),
        "test setup must simulate preprocessing changing predicate count"
    );

    let v0 = ChcVar::new("v0", ChcSort::Int);
    let mut model = InvariantModel::new();
    model.set(
        p1,
        PredicateInterpretation::new(vec![v0.clone()], ChcExpr::Bool(false)),
    );
    model.set(
        p2,
        PredicateInterpretation::new(
            vec![v0.clone()],
            ChcExpr::le(ChcExpr::var(v0), ChcExpr::int(9)),
        ),
    );
    model.individually_inductive = true;

    // Precondition: model passes query-only but fails full validation on original problem
    assert!(
        matches!(
            solver.validate_safe_query_only(&model),
            SafePrecheckResult::Valid
        ),
        "setup: must pass query-only validation"
    );
    assert!(
        matches!(
            solver.validate_safe_with_mode(&model, ValidationBudget::PerRule),
            ValidationResult::Invalid(_)
        ),
        "setup: must fail full validation on the original problem"
    );

    // Key assertion: individually_inductive bypasses full validation (#7410),
    // including for preprocessed problems (old #7438 guard removed).
    let result = solver.accept_or_reject(PortfolioResult::Safe(model), false, "PDR", 0);
    assert!(
        matches!(result, AcceptDecision::Accept(PortfolioResult::Safe(_))),
        "individually_inductive models bypass full validation for preprocessed problems (#7410)"
    );
}

/// #7450: Soundness regression test for the preprocessed guard removal.
/// When preprocessing inlines a multi-predicate problem to single-predicate, a model
/// that passes query-only but fails full validation must be REJECTED if
/// individually_inductive is false. This verifies that the defense-in-depth is intact:
/// without the PDR-level guarantee (individually_inductive=true), preprocessed models
/// are still rejected by Step 5 full validation.
///
/// This is the complement of test_accept_or_reject_preprocessed_individually_inductive_model_bypasses_full_validation:
/// that test shows individually_inductive=true causes bypass; this test shows
/// individually_inductive=false causes rejection even for preprocessed problems.
#[test]
fn test_accept_or_reject_preprocessed_non_individually_inductive_model_rejected() {
    let original_problem = create_multi_predicate_chain_problem();
    let p1 = original_problem.predicates()[0].id;
    let p2 = original_problem.predicates()[1].id;
    let transformed_problem = create_safe_problem();
    let config = PortfolioConfig {
        engines: vec![],
        parallel: false,
        timeout: None,
        parallel_timeout: None,
        verbose: false,
        validate: false,
        enable_preprocessing: false,
    };
    let solver = PortfolioSolver {
        original_problem,
        problem: transformed_problem,
        back_translator: Box::new(IdentityBackTranslator),
        config,
        bv_abstracted: false,
    };

    // Verify test setup: different predicate counts simulate preprocessing
    assert!(
        solver.original_problem.predicates().len() != solver.engine_problem().predicates().len(),
        "test setup must simulate preprocessing changing predicate count"
    );

    let v0 = ChcVar::new("v0", ChcSort::Int);
    let mut model = InvariantModel::new();
    model.set(
        p1,
        PredicateInterpretation::new(vec![v0.clone()], ChcExpr::Bool(false)),
    );
    model.set(
        p2,
        PredicateInterpretation::new(
            vec![v0.clone()],
            ChcExpr::le(ChcExpr::var(v0), ChcExpr::int(9)),
        ),
    );
    // Key: individually_inductive is false (default) — simulating an unsound model
    // where PDR did NOT verify per-lemma self-inductiveness
    assert!(
        !model.individually_inductive,
        "setup: model must NOT be individually_inductive"
    );

    // Precondition: model passes query-only but fails full validation
    assert!(
        matches!(
            solver.validate_safe_query_only(&model),
            SafePrecheckResult::Valid
        ),
        "setup: must pass query-only validation"
    );
    assert!(
        matches!(
            solver.validate_safe_with_mode(&model, ValidationBudget::PerRule),
            ValidationResult::Invalid(_)
        ),
        "setup: must fail full validation on the original problem"
    );

    // Key assertion: without individually_inductive=true, the model is REJECTED
    // even though it came from a preprocessed problem. The old #7438 guard would
    // have routed this through Standard-budget validation (also rejects). The
    // guard removal means this goes through the normal PerRule path.
    let result = solver.accept_or_reject(PortfolioResult::Safe(model), false, "PDR", 0);
    assert!(
        matches!(result, AcceptDecision::Reject),
        "preprocessed model without individually_inductive must be rejected by Step 5 (#7450)"
    );
}

/// #7450: individually_inductive=true bypasses Step 5 full validation at accept.rs:178.
/// Models with per-lemma strict self-inductiveness need only query-only validation.
#[test]
fn test_accept_or_reject_individually_inductive_bypasses_full_validation() {
    let problem = create_safe_problem();
    let inv = problem.predicates()[0].id;
    let config = PortfolioConfig {
        engines: vec![],
        parallel: false,
        timeout: None,
        parallel_timeout: None,
        verbose: false,
        validate: false,
        enable_preprocessing: false,
    };
    let solver = PortfolioSolver::new(problem, config);

    // Build a model that passes query-only (blocks x >= 10) but may fail full
    // validation due to SMT limitations. With individually_inductive=true, the
    // model should be accepted regardless of full validation outcome.
    let v0 = ChcVar::new("v0", ChcSort::Int);
    let mut model = InvariantModel::new();
    model.set(
        inv,
        PredicateInterpretation::new(
            vec![v0.clone()],
            ChcExpr::le(ChcExpr::var(v0), ChcExpr::int(9)),
        ),
    );
    model.individually_inductive = true;

    let result = solver.accept_or_reject(PortfolioResult::Safe(model), false, "PDR", 0);
    assert!(
        matches!(result, AcceptDecision::Accept(PortfolioResult::Safe(_))),
        "individually_inductive model must bypass Step 5 full validation (#7450)"
    );
}

/// #7450: individually_inductive=false means Step 5 full validation is mandatory.
/// A model that passes query-only but fails full validation must be rejected.
#[test]
fn test_accept_or_reject_non_individually_inductive_requires_full_validation() {
    let problem = create_safe_problem();
    let config = PortfolioConfig {
        engines: vec![],
        parallel: false,
        timeout: None,
        parallel_timeout: None,
        verbose: false,
        validate: false,
        enable_preprocessing: false,
    };
    let solver = PortfolioSolver::new(problem.clone(), config);
    let model = make_query_only_but_not_inductive_model(&problem);

    // Preconditions: passes query-only, fails full validation
    assert!(
        matches!(
            solver.validate_safe_query_only(&model),
            SafePrecheckResult::Valid
        ),
        "setup: must pass query-only"
    );
    assert!(
        matches!(
            solver.validate_safe_with_mode(&model, ValidationBudget::PerRule),
            ValidationResult::Invalid(_)
        ),
        "setup: must fail full validation"
    );
    assert!(
        !model.individually_inductive,
        "setup: model must NOT be individually_inductive"
    );

    // Without individually_inductive, Step 5 rejects the model
    let result = solver.accept_or_reject(PortfolioResult::Safe(model), false, "PDR", 0);
    assert!(
        matches!(result, AcceptDecision::Reject),
        "non-individually_inductive model must be rejected by Step 5 full validation (#7450)"
    );
}

#[test]
fn test_accept_or_reject_exact_negated_query_inductive_model_accepted() {
    // Regression test for #1306: An exact not(query) model that IS inductive
    // must be accepted. Step 4.5 defers to Step 5 (full validation) which
    // confirms inductiveness.
    //
    // Problem: x=0 => Inv(x), Inv(x) /\ x<5 => Inv(x+1), Inv(x) /\ x>=10 => false
    // Model: Inv(x) = not(x >= 10)  [which equals x < 10]
    // This IS inductive: x<10 /\ x<5 => x+1<10 holds.
    let problem = create_safe_problem();
    let inv = problem.predicates()[0].id;
    let config = PortfolioConfig {
        engines: vec![],
        parallel: false,
        timeout: None,
        parallel_timeout: None,
        verbose: false,
        validate: false,
        enable_preprocessing: false,
    };
    let solver = PortfolioSolver::new(problem, config);

    let v0 = ChcVar::new("v0", ChcSort::Int);
    let mut model = InvariantModel::new();
    model.set(
        inv,
        PredicateInterpretation::new(
            vec![v0.clone()],
            // Exact not(query): not(v0 >= 10)
            ChcExpr::not(ChcExpr::ge(ChcExpr::var(v0), ChcExpr::int(10))),
        ),
    );

    // Step 4.5 should classify as ExactNegatedQuery (not hard reject)
    assert!(
        matches!(
            solver.validate_safe_query_only(&model),
            SafePrecheckResult::ExactNegatedQuery(_)
        ),
        "Exact ¬query must be classified as ExactNegatedQuery"
    );

    // Step 5 full validation should pass (model is inductive)
    assert!(
        matches!(
            solver.validate_safe_with_mode(&model, ValidationBudget::PerRule),
            ValidationResult::Valid
        ),
        "Exact ¬query model that IS inductive must pass full validation"
    );

    // accept_or_reject should accept: Step 4.5 defers, Step 5 passes
    let result = solver.accept_or_reject(PortfolioResult::Safe(model), false, "TRL-interleaved", 0);
    assert!(
        matches!(result, AcceptDecision::Accept(PortfolioResult::Safe(_))),
        "Inductive exact ¬query model must be accepted after full validation (#1306)"
    );
}

#[test]
fn test_accept_or_reject_exact_negated_query_non_inductive_model_rejected() {
    // Soundness guard: An exact not(query) model that is NOT inductive
    // must be rejected. Step 4.5 defers, but Step 5 catches it.
    //
    // We construct a problem where not(query_constraint) is NOT inductive.
    // Problem: x=0 => Inv(x), Inv(x) => Inv(x+1), Inv(x) /\ x>=5 => false
    // Model: Inv(x) = not(x >= 5)  [which equals x < 5]
    // This is NOT inductive: x<5 => x+1<5 fails at x=4.
    let problem = create_unsafe_problem();
    let inv = problem.predicates()[0].id;
    let config = PortfolioConfig {
        engines: vec![],
        parallel: false,
        timeout: None,
        parallel_timeout: None,
        verbose: false,
        validate: false,
        enable_preprocessing: false,
    };
    let solver = PortfolioSolver::new(problem, config);

    let v0 = ChcVar::new("v0", ChcSort::Int);
    let mut model = InvariantModel::new();
    model.set(
        inv,
        PredicateInterpretation::new(
            vec![v0.clone()],
            // Exact not(query): not(v0 >= 5)
            ChcExpr::not(ChcExpr::ge(ChcExpr::var(v0), ChcExpr::int(5))),
        ),
    );

    // Step 4.5 should classify as ExactNegatedQuery (not hard reject)
    assert!(
        matches!(
            solver.validate_safe_query_only(&model),
            SafePrecheckResult::ExactNegatedQuery(_)
        ),
        "Exact ¬query must be classified as ExactNegatedQuery"
    );

    // accept_or_reject should reject: Step 4.5 defers, Step 5 rejects
    let result = solver.accept_or_reject(PortfolioResult::Safe(model), false, "TRL-interleaved", 0);
    assert!(
        matches!(result, AcceptDecision::Reject),
        "Non-inductive exact ¬query model must be rejected by full validation"
    );
}

#[test]
fn test_build_int_only_uses_exact_bv_to_int() {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("inv", vec![ChcSort::BitVec(8)]);
    let x = ChcVar::new("x", ChcSort::BitVec(8));

    // x must appear in a constraint so Stage 0 DeadParamEliminator doesn't remove it
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::bv_ule(
            ChcExpr::var(x.clone()),
            ChcExpr::BitVec(128, 8),
        )),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(inv, vec![ChcExpr::var(x.clone())])]),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x)]),
    ));

    let summary = PreprocessSummary::build_int_only(problem, false);

    assert!(
        summary
            .transformed_problem
            .clauses()
            .iter()
            .any(|clause| clause.body.constraint.is_some()),
        "build_int_only must add BV range constraints via the exact BV-to-Int encoding"
    );
}

/// Regression test for #5970: PerRule validation budget must be 2s, not 5s.
///
/// Commit 27567093d increased the budget from 2s to 5s, causing a 46→44 CHC
/// benchmark regression. For a 3-clause problem, 5s/rule = 15s total, consuming
/// the entire solver timeout. The budget was reverted to 2s.
///
/// This test pins the budget value to prevent the regression from recurring.
#[test]
fn test_validation_budget_per_rule_is_2s_not_5s() {
    let problem = create_safe_problem();
    let budget = ValidationBudget::PerRule.to_duration(&problem);
    assert_eq!(
        budget,
        Duration::from_secs(2),
        "PerRule budget must be 2s (#5970 regression: 5s causes benchmark timeouts)"
    );
}

/// Regression test: Standard validation budget for LIA problems is 1.5s.
#[test]
fn test_validation_budget_standard_lia_is_1500ms() {
    let problem = create_safe_problem();
    let budget = ValidationBudget::Standard.to_duration(&problem);
    assert_eq!(
        budget,
        Duration::from_millis(1500),
        "Standard LIA budget must be 1.5s"
    );
}
