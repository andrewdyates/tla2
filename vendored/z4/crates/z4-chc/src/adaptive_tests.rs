// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::classifier::{ProblemClass, ProblemClassifier};
use crate::engine_result::ValidationEvidence;
use crate::pdr::{
    Counterexample, CounterexampleStep, InvariantModel, PdrConfig, PdrResult,
    PredicateInterpretation,
};
use crate::portfolio::{EngineConfig, PortfolioResult, PreprocessSummary};
use crate::ChcParser;
use crate::{ChcExpr, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause, VerifiedChcResult};
use ntest::timeout;
use rustc_hash::FxHashMap;
use std::time::Duration;

fn create_simple_loop() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // x = 0 => Inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    // Inv(x) /\ x < 5 => Inv(x + 1)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(5))),
        ),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    // Inv(x) /\ x > 5 => false (safe: x never exceeds 5)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(5))),
        ),
        ClauseHead::False,
    ));

    problem
}

fn create_identity_simple_loop(arg_sort: ChcSort) -> ChcProblem {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![arg_sort.clone()]);
    let x = ChcVar::new("x", arg_sort);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(true)),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(inv, vec![ChcExpr::var(x.clone())])], None),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(inv, vec![ChcExpr::var(x)])], None),
        ClauseHead::False,
    ));

    problem
}

fn create_unsafe_simple_loop() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // x = 0 => Inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    // Inv(x) => Inv(x + 1)
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(inv, vec![ChcExpr::var(x.clone())])]),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    // Inv(x) /\ x >= 5 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(5))),
        ),
        ClauseHead::False,
    ));

    problem
}

fn create_acyclic_zani_array_bv_chain() -> ChcProblem {
    parse_benchmark(
        r#"
(set-logic HORN)
(declare-fun bb0 ((Array (_ BitVec 32) Bool) (Array (_ BitVec 32) (_ BitVec 32)) (Array (_ BitVec 64) (_ BitVec 8)) (_ BitVec 64)) Bool)
(declare-fun bb1 ((Array (_ BitVec 32) Bool) (Array (_ BitVec 32) (_ BitVec 32)) (Array (_ BitVec 64) (_ BitVec 8)) (_ BitVec 64)) Bool)
(declare-fun bb2 ((Array (_ BitVec 32) Bool) (Array (_ BitVec 32) (_ BitVec 32)) (Array (_ BitVec 64) (_ BitVec 8)) (_ BitVec 64)) Bool)
(declare-fun bb3 ((Array (_ BitVec 32) Bool) (Array (_ BitVec 32) (_ BitVec 32)) (Array (_ BitVec 64) (_ BitVec 8)) (_ BitVec 64)) Bool)
(declare-fun bb4 ((Array (_ BitVec 32) Bool) (Array (_ BitVec 32) (_ BitVec 32)) (Array (_ BitVec 64) (_ BitVec 8)) (_ BitVec 64)) Bool)

; Entry: object 1 is valid, has size 4, and address 8 stores 0x42.
(assert
  (forall (
    (ov (Array (_ BitVec 32) Bool))
    (os (Array (_ BitVec 32) (_ BitVec 32)))
    (m  (Array (_ BitVec 64) (_ BitVec 8)))
    (addr (_ BitVec 64))
  )
    (=>
      (and
        (= ov (store ((as const (Array (_ BitVec 32) Bool)) false) #x00000001 true))
        (= os (store ((as const (Array (_ BitVec 32) (_ BitVec 32))) #x00000000) #x00000001 #x00000004))
        (= addr #x0000000000000008)
        (= m (store ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x00) addr #x42))
      )
      (bb0 ov os m addr)
    )
  )
)

; Acyclic basic-block chain: bb0 -> bb1 -> bb2 -> bb3 -> bb4.
(assert
  (forall (
    (ov (Array (_ BitVec 32) Bool))
    (os (Array (_ BitVec 32) (_ BitVec 32)))
    (m  (Array (_ BitVec 64) (_ BitVec 8)))
    (addr (_ BitVec 64))
  )
    (=>
      (and (bb0 ov os m addr) (select ov #x00000001))
      (bb1 ov os m addr)
    )
  )
)

(assert
  (forall (
    (ov (Array (_ BitVec 32) Bool))
    (os (Array (_ BitVec 32) (_ BitVec 32)))
    (m  (Array (_ BitVec 64) (_ BitVec 8)))
    (addr (_ BitVec 64))
  )
    (=>
      (and
        (bb1 ov os m addr)
        (= (select os #x00000001) #x00000004)
      )
      (bb2 ov os m addr)
    )
  )
)

(assert
  (forall (
    (ov (Array (_ BitVec 32) Bool))
    (os (Array (_ BitVec 32) (_ BitVec 32)))
    (m  (Array (_ BitVec 64) (_ BitVec 8)))
    (addr (_ BitVec 64))
  )
    (=>
      (and
        (bb2 ov os m addr)
        (= addr #x0000000000000008)
      )
      (bb3 ov os m addr)
    )
  )
)

(assert
  (forall (
    (ov (Array (_ BitVec 32) Bool))
    (os (Array (_ BitVec 32) (_ BitVec 32)))
    (m  (Array (_ BitVec 64) (_ BitVec 8)))
    (addr (_ BitVec 64))
  )
    (=>
      (and
        (bb3 ov os m addr)
        (= (select m addr) #x42)
      )
      (bb4 ov os m addr)
    )
  )
)

; Safety query: all invariants established above must hold at bb4.
(assert
  (forall (
    (ov (Array (_ BitVec 32) Bool))
    (os (Array (_ BitVec 32) (_ BitVec 32)))
    (m  (Array (_ BitVec 64) (_ BitVec 8)))
    (addr (_ BitVec 64))
  )
    (=>
      (and
        (bb4 ov os m addr)
        (or
          (not (select ov #x00000001))
          (not (= (select os #x00000001) #x00000004))
          (not (= addr #x0000000000000008))
          (not (= (select m addr) #x42))
        )
      )
      false
    )
  )
)

(check-sat)
"#,
        "acyclic_zani_array_bv_chain",
    )
}

fn parse_benchmark(input: &str, label: &str) -> ChcProblem {
    ChcParser::parse(input).unwrap_or_else(|err| panic!("parse {label}: {err}"))
}

fn assert_adaptive_benchmark_is_not_safe(input: &str, label: &str) {
    let problem = parse_benchmark(input, label);
    let adaptive = AdaptivePortfolio::new(
        problem,
        AdaptiveConfig {
            time_budget: Duration::from_secs(15),
            verbose: false,
            validate: false,
            ..AdaptiveConfig::default()
        },
    );

    match adaptive.solve() {
        VerifiedChcResult::Safe(_) => {
            panic!("Adaptive false-SAT regression (#7688): {label} must not return Safe");
        }
        VerifiedChcResult::Unsafe(_) | VerifiedChcResult::Unknown(_) => {}
    }
}

fn false_model_for_first_predicate(problem: &ChcProblem) -> InvariantModel {
    let pred = problem
        .predicates()
        .first()
        .expect("test problem should have a predicate");
    let canonical_vars = pred
        .arg_sorts
        .iter()
        .enumerate()
        .map(|(i, sort)| ChcVar::new(format!("__p{}_a{}", pred.id.index(), i), sort.clone()))
        .collect();
    let mut model = InvariantModel::new();
    model.set(
        pred.id,
        PredicateInterpretation::new(canonical_vars, ChcExpr::Bool(false)),
    );
    model
}

fn empty_counterexample_for_first_predicate(problem: &ChcProblem, depth: usize) -> Counterexample {
    let pred = problem
        .predicates()
        .first()
        .expect("test problem should have a predicate")
        .id;
    Counterexample::new(
        (0..=depth)
            .map(|_| CounterexampleStep::new(pred, FxHashMap::default()))
            .collect(),
    )
}

#[test]
fn test_adaptive_classifies_simple_loop() {
    let problem = create_simple_loop();
    let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::default());
    let features = adaptive.features();

    assert_eq!(features.class, ProblemClass::SimpleLoop);
}

#[test]
fn test_adaptive_solves_simple_loop() {
    let problem = create_simple_loop();
    let config = AdaptiveConfig {
        time_budget: Duration::from_secs(10),
        verbose: false,
        skip_classification: false,
        ..AdaptiveConfig::default()
    };
    let adaptive = AdaptivePortfolio::new(problem, config);
    let result = adaptive.solve();

    match result {
        VerifiedChcResult::Safe(_) => {
            // Expected: problem is safe
        }
        VerifiedChcResult::Unknown(_) => {
            panic!("Adaptive portfolio returned Unknown on a trivial safe loop.")
        }
        VerifiedChcResult::Unsafe(_) => {
            panic!("Problem is safe, should not return Unsafe");
        }
    }
}

#[test]
#[cfg_attr(debug_assertions, timeout(30_000))]
#[cfg_attr(not(debug_assertions), timeout(20_000))]
fn test_adaptive_acyclic_array_bv_bmc_probe_returns_safe() {
    let problem = create_acyclic_zani_array_bv_chain();
    let adaptive = AdaptivePortfolio::new(
        problem,
        AdaptiveConfig::with_budget(Duration::from_secs(10), false),
    );
    let features = adaptive.features();
    assert_eq!(features.class, ProblemClass::MultiPredLinear);
    assert!(features.is_linear);
    assert!(!features.has_cycles);
    assert!(features.uses_arrays);
    assert!(adaptive.problem.has_bv_sorts());

    let result = adaptive.try_acyclic_array_bv_bmc_probe(&features, None);
    assert!(
        matches!(result, Some(PortfolioResult::Safe(_))),
        "acyclic array/BV BMC probe should prove the chain safe, got {result:?}"
    );

    assert!(
        matches!(adaptive.solve(), VerifiedChcResult::Safe(_)),
        "adaptive solver should return Safe on the acyclic array/BV chain"
    );
}

#[test]
#[cfg_attr(debug_assertions, timeout(30_000))]
#[cfg_attr(not(debug_assertions), timeout(20_000))]
fn test_adaptive_issue_7688_accumulator_unsafe_not_safe() {
    assert_adaptive_benchmark_is_not_safe(
        include_str!(
            "../../../benchmarks/chc-comp/2025/extra-small-lia/accumulator_unsafe_000.smt2"
        ),
        "accumulator_unsafe_000",
    );
}

/// Regression: Kind finds counterexample at k=11 for accumulator_unsafe,
/// but adaptive layer discarded it (returned None). With #7897 fix,
/// Kind Unsafe results flow through to VerifiedChcResult::Unsafe.
#[test]
#[cfg_attr(debug_assertions, timeout(30_000))]
#[cfg_attr(not(debug_assertions), timeout(20_000))]
fn test_issue_7897_kind_unsafe_flows_through_adaptive() {
    let problem = parse_benchmark(
        include_str!(
            "../../../benchmarks/chc-comp/2025/extra-small-lia/accumulator_unsafe_000.smt2"
        ),
        "accumulator_unsafe_000",
    );
    // Kind needs k=11 to find the counterexample. In debug mode, each
    // k-induction query is slower, so give the solver enough time for
    // the full simple-loop pipeline (Kind 8s + PDR probe 6s + portfolio).
    let adaptive = AdaptivePortfolio::new(
        problem,
        AdaptiveConfig {
            time_budget: Duration::from_secs(25),
            verbose: false,
            validate: false,
            ..AdaptiveConfig::default()
        },
    );

    match adaptive.solve() {
        VerifiedChcResult::Unsafe(_) => {} // expected
        VerifiedChcResult::Safe(_) => {
            panic!("accumulator_unsafe_000 must not return Safe (false-SAT)");
        }
        VerifiedChcResult::Unknown(reason) => {
            panic!(
                "accumulator_unsafe_000 should return Unsafe, got Unknown: {:?}.                  Kind finds counterexample at k=11 but adaptive discards it (#7897)",
                reason
            );
        }
    }
}

/// Regression: Simple loop counter reaching 5 should be reported as Unsafe.
/// KIND finds this at k=5 (x starts at 0, increments to 5, query x >= 5).
#[test]
#[cfg_attr(debug_assertions, timeout(30_000))]
#[cfg_attr(not(debug_assertions), timeout(20_000))]
fn test_issue_7897_kind_unsafe_simple_counter() {
    let problem = create_unsafe_simple_loop();
    let adaptive = AdaptivePortfolio::new(
        problem,
        AdaptiveConfig {
            time_budget: Duration::from_secs(10),
            verbose: false,
            validate: false,
            ..AdaptiveConfig::default()
        },
    );

    match adaptive.solve() {
        VerifiedChcResult::Unsafe(_) => {} // expected
        VerifiedChcResult::Safe(_) => {
            panic!("unsafe simple loop must not return Safe");
        }
        VerifiedChcResult::Unknown(reason) => {
            panic!(
                "unsafe simple loop should return Unsafe, got Unknown: {:?}.                  Kind should find counterexample at k=5 (#7897)",
                reason
            );
        }
    }
}

#[test]
#[cfg_attr(debug_assertions, timeout(30_000))]
#[cfg_attr(not(debug_assertions), timeout(20_000))]
fn test_adaptive_issue_7688_two_phase_unsafe_not_safe() {
    assert_adaptive_benchmark_is_not_safe(
        include_str!("../../../benchmarks/chc-comp/2025/extra-small-lia/two_phase_unsafe_000.smt2"),
        "two_phase_unsafe_000",
    );
}

#[test]
fn test_validate_adaptive_result_rejects_false_safe_when_validate_disabled() {
    let problem = create_simple_loop();
    let invalid_model = false_model_for_first_predicate(&problem);
    let adaptive = AdaptivePortfolio::new(
        problem,
        AdaptiveConfig {
            validate: false,
            ..AdaptiveConfig::default()
        },
    );

    let validated = adaptive.validate_adaptive_result(PdrResult::Safe(invalid_model));
    assert!(
        matches!(validated, PdrResult::Unknown),
        "mandatory Safe validation must reject invalid direct-engine models even when validate=false"
    );
}

#[test]
fn test_try_synthesis_returns_validated_safe_model() {
    let adaptive = AdaptivePortfolio::new(create_simple_loop(), AdaptiveConfig::default());
    assert!(
        matches!(adaptive.try_synthesis(), Some(PortfolioResult::Safe(_))),
        "structural synthesis should still produce a validated Safe result on the bounded loop canary"
    );
}

#[test]
fn test_finalize_verified_result_rejects_invalid_unsafe_when_validate_disabled() {
    let problem = create_simple_loop();
    let fake_cex = empty_counterexample_for_first_predicate(&problem, 10);
    let adaptive = AdaptivePortfolio::new(
        problem,
        AdaptiveConfig {
            validate: false,
            ..AdaptiveConfig::default()
        },
    );

    let result = adaptive.finalize_verified_result(
        PortfolioResult::Unsafe(fake_cex),
        ValidationEvidence::FullVerification,
    );
    assert!(
        matches!(result, VerifiedChcResult::Unknown(_)),
        "verified adaptive API must reject spurious Unsafe even when validate=false"
    );
}

#[test]
fn test_finalize_verified_result_accepts_reachable_unsafe_when_validate_disabled() {
    let problem = create_unsafe_simple_loop();
    let reachable_cex = empty_counterexample_for_first_predicate(&problem, 5);
    let adaptive = AdaptivePortfolio::new(
        problem,
        AdaptiveConfig {
            validate: false,
            ..AdaptiveConfig::default()
        },
    );

    let result = adaptive.finalize_verified_result(
        PortfolioResult::Unsafe(reachable_cex),
        ValidationEvidence::FullVerification,
    );
    assert!(
        matches!(result, VerifiedChcResult::Unsafe(_)),
        "verified adaptive API must preserve a reachable Unsafe after fresh validation"
    );
}

#[test]
fn test_bv_simple_loop_uses_native_direct_route() {
    let problem = create_identity_simple_loop(ChcSort::BitVec(8));
    let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::default());
    let features = adaptive.features();

    assert_eq!(features.class, ProblemClass::SimpleLoop);
    assert!(adaptive.use_bv_native_direct_route(&features));
}

#[test]
fn test_bv_native_direct_route_requires_non_array_non_real_bv_simple_loop() {
    let int_problem = create_identity_simple_loop(ChcSort::Int);
    let int_adaptive = AdaptivePortfolio::new(int_problem, AdaptiveConfig::default());
    let int_features = int_adaptive.features();
    assert_eq!(int_features.class, ProblemClass::SimpleLoop);
    assert!(!int_adaptive.use_bv_native_direct_route(&int_features));

    let array_problem = create_identity_simple_loop(ChcSort::Array(
        Box::new(ChcSort::Int),
        Box::new(ChcSort::BitVec(8)),
    ));
    let array_adaptive = AdaptivePortfolio::new(array_problem, AdaptiveConfig::default());
    let array_features = array_adaptive.features();
    assert_eq!(array_features.class, ProblemClass::SimpleLoop);
    assert!(array_features.uses_arrays);
    assert!(!array_adaptive.use_bv_native_direct_route(&array_features));

    let real_problem = create_identity_simple_loop(ChcSort::Real);
    let real_adaptive = AdaptivePortfolio::new(real_problem, AdaptiveConfig::default());
    let real_features = real_adaptive.features();
    assert_eq!(real_features.class, ProblemClass::SimpleLoop);
    assert!(real_features.uses_real);
    assert!(!real_adaptive.use_bv_native_direct_route(&real_features));
}

#[test]
fn test_adaptive_array_bv_safe_simple_loop_classification_and_portfolio_shape() {
    // Verify that BV-indexed array problems are classified correctly and
    // routed to the array-safe portfolio (PDR + BMC, no TPA/Kind/TRL).
    // Solving BV-indexed arrays requires SMT-level array reasoning that
    // is too slow in debug mode for a solve assertion. Release-mode
    // benchmark tests cover the end-to-end solve.
    let problem = ChcParser::parse(include_str!("../../../benchmarks/chc/array_bv_safe.smt2"))
        .expect("array_bv_safe benchmark should parse");
    let adaptive = AdaptivePortfolio::new(
        problem,
        AdaptiveConfig {
            time_budget: Duration::from_secs(10),
            ..AdaptiveConfig::default()
        },
    );
    let features = adaptive.features();

    assert_eq!(features.class, ProblemClass::SimpleLoop);
    assert!(features.uses_arrays);

    // Verify the portfolio config excludes unsupported engines.
    let config = adaptive.simple_loop_array_portfolio_config(Duration::from_secs(10));
    for engine in &config.engines {
        assert!(
            !matches!(
                engine,
                EngineConfig::Kind(_) | EngineConfig::Tpa(_) | EngineConfig::Trl(_)
            ),
            "array-safe portfolio must not include Kind/TPA/TRL, found: {}",
            engine.name()
        );
    }
    // Must include PDR (array MBP) and BMC (bounded search).
    let has_pdr = config
        .engines
        .iter()
        .any(|e| matches!(e, EngineConfig::Pdr(_)));
    let has_bmc = config
        .engines
        .iter()
        .any(|e| matches!(e, EngineConfig::Bmc(_)));
    assert!(has_pdr, "array-safe portfolio must include PDR");
    assert!(has_bmc, "array-safe portfolio must include BMC");
}

#[test]
fn test_adaptive_bv_simple_loop_triple_lane_solves_safe_problem() {
    let input = r#"
(set-logic HORN)
(declare-fun |inv| ((_ BitVec 8)) Bool)

(assert (forall ((x (_ BitVec 8)))
  (=> (= x #x00) (inv x))))

(assert (forall ((x (_ BitVec 8)) (xp (_ BitVec 8)))
  (=> (and (inv x) (bvule x #x03) (= xp (bvadd x #x01)))
      (inv xp))))

(assert (forall ((x (_ BitVec 8)))
  (=> (and (inv x) (bvule #x05 x))
      false)))

(check-sat)
(exit)
"#;
    let problem = ChcParser::parse(input).expect("BV simple-loop benchmark should parse");
    let adaptive = AdaptivePortfolio::new(
        problem,
        AdaptiveConfig {
            time_budget: Duration::from_secs(5),
            ..AdaptiveConfig::default()
        },
    );
    let features = adaptive.features();

    assert_eq!(features.class, ProblemClass::SimpleLoop);
    // Helper recognizes BV direct-route shape, but the direct route is
    // disabled (see adaptive.rs:548-567). Routing goes through triple-lane
    // (BvToBool + BvToInt + BV-native) which solves more BV benchmarks
    // (9/30 vs 0/30 per W1:3265 A/B test). W1:3285 confirmed direct route
    // cannot solve nested4 either.
    assert!(adaptive.use_bv_native_direct_route(&features));
    assert!(
        matches!(adaptive.solve(), VerifiedChcResult::Safe(_)),
        "BV triple-lane should solve the tiny BV simple-loop benchmark"
    );
}

/// Verify the nested4 benchmark shape selects the BV-native direct route.
/// nested4 is the canonical #5877 regression canary: 1 predicate (3 Bool + 5 BV32),
/// 3 clauses (init, transition, query), classified as SimpleLoop.
#[test]
fn test_bv_native_direct_route_selected_for_nested4_shape() {
    // nested4 shape: 1 predicate with mixed Bool+BV32 args, 3 clauses, SimpleLoop
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate(
        "state",
        vec![
            ChcSort::Bool,
            ChcSort::Bool,
            ChcSort::Bool,
            ChcSort::BitVec(32),
            ChcSort::BitVec(32),
            ChcSort::BitVec(32),
            ChcSort::BitVec(32),
            ChcSort::BitVec(32),
        ],
    );
    let args: Vec<ChcExpr> = (0..8)
        .map(|i| {
            ChcExpr::var(ChcVar::new(
                &format!("x{i}"),
                if i < 3 {
                    ChcSort::Bool
                } else {
                    ChcSort::BitVec(32)
                },
            ))
        })
        .collect();

    // Init clause
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(true)),
        ClauseHead::Predicate(inv, args.clone()),
    ));

    // Transition clause
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(inv, args.clone())], None),
        ClauseHead::Predicate(inv, args.clone()),
    ));

    // Query clause
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(inv, args)], None),
        ClauseHead::False,
    ));

    let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::default());
    let features = adaptive.features();

    assert_eq!(features.class, ProblemClass::SimpleLoop);
    assert!(features.is_single_predicate);
    assert_eq!(features.num_transitions, 1);
    assert!(!features.uses_arrays);
    assert!(!features.uses_real);
    assert!(
        adaptive.use_bv_native_direct_route(&features),
        "nested4-shape problem should select the BV-native direct route"
    );
}

#[test]
fn test_skip_classification_uses_default() {
    let problem = create_simple_loop();
    let config = AdaptiveConfig {
        time_budget: Duration::from_secs(5),
        verbose: false,
        skip_classification: true,
        ..AdaptiveConfig::default()
    };
    let adaptive = AdaptivePortfolio::new(problem, config);

    // Should still solve correctly, just using default portfolio
    let result = adaptive.solve();
    match result {
        VerifiedChcResult::Safe(_) => {}
        VerifiedChcResult::Unknown(_) => panic!(
            "Adaptive portfolio (skip_classification) returned Unknown on a trivial safe loop."
        ),
        VerifiedChcResult::Unsafe(_) => {
            panic!("Problem is safe");
        }
    }
}

/// Create an entry-exit-only SAFE problem
/// x > 5 /\ x < 3 => false (constraint is UNSAT)
fn create_entry_exit_only_safe() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let x = ChcVar::new("x", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::and(
            ChcExpr::gt(ChcExpr::var(x.clone()), ChcExpr::int(5)),
            ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(3)),
        )),
        ClauseHead::False,
    ));

    problem
}

/// Create an entry-exit-only UNSAFE problem
/// x > 0 /\ x < 10 => false (constraint is SAT)
fn create_entry_exit_only_unsafe() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let x = ChcVar::new("x", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::and(
            ChcExpr::gt(ChcExpr::var(x.clone()), ChcExpr::int(0)),
            ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(10)),
        )),
        ClauseHead::False,
    ));

    problem
}

#[test]
fn test_entry_exit_only_classification() {
    let safe = create_entry_exit_only_safe();
    let adaptive = AdaptivePortfolio::new(safe, AdaptiveConfig::default());
    assert_eq!(adaptive.features().class, ProblemClass::EntryExitOnly);

    let unsafe_problem = create_entry_exit_only_unsafe();
    let adaptive = AdaptivePortfolio::new(unsafe_problem, AdaptiveConfig::default());
    assert_eq!(adaptive.features().class, ProblemClass::EntryExitOnly);
}

#[test]
fn test_entry_exit_only_safe() {
    let problem = create_entry_exit_only_safe();
    let config = AdaptiveConfig {
        time_budget: Duration::from_secs(5),
        verbose: false,
        skip_classification: false,
        ..AdaptiveConfig::default()
    };
    let adaptive = AdaptivePortfolio::new(problem, config);
    let result = adaptive.solve();

    match result {
        VerifiedChcResult::Safe(_) => {
            // Expected: constraint is UNSAT, so problem is safe
        }
        other => {
            panic!("Expected Safe, got {other:?}");
        }
    }
}

#[test]
fn test_entry_exit_only_unsafe() {
    let problem = create_entry_exit_only_unsafe();
    let config = AdaptiveConfig {
        time_budget: Duration::from_secs(5),
        verbose: false,
        skip_classification: false,
        ..AdaptiveConfig::default()
    };
    let adaptive = AdaptivePortfolio::new(problem, config);
    let result = adaptive.solve();

    match result {
        VerifiedChcResult::Unsafe(_) => {
            // Expected: constraint is SAT, so problem is unsafe
        }
        other => {
            panic!("Expected Unsafe, got {other:?}");
        }
    }
}

/// Create a multi-predicate problem with two predicates.
///
/// Models: x >= 0, y >= 0, x + y increment, safe if x + y <= 20
/// Predicates: Inv1(x), Inv2(y)
///
/// Init: x = 0 => Inv1(x)
///       y = 0 => Inv2(y)
/// Trans: Inv1(x) /\ x < 10 => Inv1(x + 1)
///        Inv2(y) /\ y < 10 => Inv2(y + 1)
/// Query: Inv1(x) /\ Inv2(y) /\ x + y > 20 => false
fn create_multi_predicate_safe() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let inv1 = problem.declare_predicate("Inv1", vec![ChcSort::Int]);
    let inv2 = problem.declare_predicate("Inv2", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    // Init: x = 0 => Inv1(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv1, vec![ChcExpr::var(x.clone())]),
    ));

    // Init: y = 0 => Inv2(y)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(y.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv2, vec![ChcExpr::var(y.clone())]),
    ));

    // Trans: Inv1(x) /\ x < 10 => Inv1(x + 1)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv1, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(10))),
        ),
        ClauseHead::Predicate(
            inv1,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    // Trans: Inv2(y) /\ y < 10 => Inv2(y + 1)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv2, vec![ChcExpr::var(y.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(y.clone()), ChcExpr::int(10))),
        ),
        ClauseHead::Predicate(
            inv2,
            vec![ChcExpr::add(ChcExpr::var(y.clone()), ChcExpr::int(1))],
        ),
    ));

    // Query: Inv1(x) /\ Inv2(y) /\ x + y > 20 => false
    // Safe because max(x) = 10, max(y) = 10, so x + y <= 20
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![
                (inv1, vec![ChcExpr::var(x.clone())]),
                (inv2, vec![ChcExpr::var(y.clone())]),
            ],
            Some(ChcExpr::gt(
                ChcExpr::add(ChcExpr::var(x), ChcExpr::var(y)),
                ChcExpr::int(20),
            )),
        ),
        ClauseHead::False,
    ));

    problem
}

fn create_two_predicate_gate_problem(constraint: Option<ChcExpr>) -> ChcProblem {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(true)),
        ClauseHead::Predicate(p, vec![ChcExpr::int(0)]),
    ));

    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(p, vec![ChcExpr::var(x.clone())])], constraint),
        ClauseHead::Predicate(
            q,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(q, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(10))),
        ),
        ClauseHead::False,
    ));

    problem
}

fn create_four_predicate_gate_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let predicates: Vec<_> = (0..4)
        .map(|i| problem.declare_predicate(&format!("P{i}"), vec![ChcSort::Int]))
        .collect();
    let x = ChcVar::new("x", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(true)),
        ClauseHead::Predicate(predicates[0], vec![ChcExpr::int(0)]),
    ));

    for window in predicates.windows(2) {
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(window[0], vec![ChcExpr::var(x.clone())])],
                Some(ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(10))),
            ),
            ClauseHead::Predicate(
                window[1],
                vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
            ),
        ));
    }

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(predicates[3], vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(20))),
        ),
        ClauseHead::False,
    ));

    problem
}

fn create_four_predicate_array_gate_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let array_sort = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::BitVec(8)));
    let predicates: Vec<_> = (0..4)
        .map(|i| problem.declare_predicate(&format!("AP{i}"), vec![array_sort.clone()]))
        .collect();
    let arr = ChcVar::new("arr", array_sort);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(true)),
        ClauseHead::Predicate(predicates[0], vec![ChcExpr::var(arr.clone())]),
    ));

    for window in predicates.windows(2) {
        problem.add_clause(HornClause::new(
            ClauseBody::new(vec![(window[0], vec![ChcExpr::var(arr.clone())])], None),
            ClauseHead::Predicate(window[1], vec![ChcExpr::var(arr.clone())]),
        ));
    }

    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(predicates[3], vec![ChcExpr::var(arr)])], None),
        ClauseHead::False,
    ));

    problem
}

#[test]
fn test_multi_pred_classification() {
    let problem = create_multi_predicate_safe();
    let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::default());
    let features = adaptive.features();

    // Should be classified as multi-predicate (either Linear or Complex)
    assert!(
        matches!(
            features.class,
            ProblemClass::MultiPredLinear | ProblemClass::MultiPredComplex
        ),
        "Expected multi-predicate class, got {:?}",
        features.class
    );
}

/// Test that multi-predicate paths have failure-guided retry capability.
///
/// Part of #2082 - this test verifies the failure retry code path is reachable.
/// The retry mechanism may or may not trigger depending on whether the portfolio
/// returns Unknown, but the code structure is exercised.
#[test]
fn test_multi_pred_failure_retry_path() {
    let problem = create_multi_predicate_safe();
    let config = AdaptiveConfig {
        time_budget: Duration::from_secs(10),
        verbose: false,
        skip_classification: false,
        ..AdaptiveConfig::default()
    };
    let adaptive = AdaptivePortfolio::new(problem, config);
    let result = adaptive.solve();

    // Multi-predicate benchmark can still return Unknown.
    // VerifiedChcResult maps NotApplicable → Unknown, so no NotApplicable arm needed.
    match result {
        VerifiedChcResult::Safe(_) => {
            // Expected: problem is safe, found invariant
        }
        VerifiedChcResult::Unknown(_) => {
            // Acceptable: conservative while exercising retry logic.
        }
        VerifiedChcResult::Unsafe(_) => {
            panic!("Problem is safe, should not return Unsafe");
        }
    }
}

#[test]
fn test_multi_pred_linear_portfolio_uses_single_pdkind_engine() {
    let problem = create_multi_predicate_safe();
    let features = ProblemClassifier::classify(&problem);
    let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::default());
    let config = adaptive.multi_pred_linear_portfolio_config(
        PdrConfig::default(),
        PdrConfig::portfolio_variant_with_splits(),
        &features,
    );

    let kind_count = config
        .engines
        .iter()
        .filter(|engine| matches!(engine, EngineConfig::Kind(_)))
        .count();
    let pdr_count = config
        .engines
        .iter()
        .filter(|engine| matches!(engine, EngineConfig::Pdr(_)))
        .count();
    let tpa_count = config
        .engines
        .iter()
        .filter(|engine| matches!(engine, EngineConfig::Tpa(_)))
        .count();
    let dar_count = config
        .engines
        .iter()
        .filter(|engine| matches!(engine, EngineConfig::Dar(_)))
        .count();

    // #6500: Kind via SingleLoop replaced the no-op PDKind for non-DT problems.
    assert_eq!(
        kind_count, 1,
        "multi-pred linear should run one Kind (#6500)"
    );
    assert_eq!(
        pdr_count, 2,
        "multi-pred linear should keep two PDR variants"
    );
    assert_eq!(tpa_count, 1, "multi-pred linear should include one TPA");
    assert_eq!(dar_count, 1, "multi-pred linear should include one DAR");
}

#[test]
fn test_multi_pred_linear_direct_kind_uses_query_only_evidence_source_regression() {
    let src = include_str!("adaptive_multi_pred.rs");
    let fn_start = src
        .find("pub(super) fn solve_multi_pred_linear(")
        .expect("adaptive_multi_pred.rs should define solve_multi_pred_linear");
    let fn_body = &src[fn_start..];
    let kind_start = fn_body
        .find("if let Some(result) = self.try_kind(kind_budget) {")
        .expect("MultiPredLinear path should try direct Kind before fallback");
    let kind_return = fn_body[kind_start..]
        .find("return (result, evidence);")
        .map(|offset| kind_start + offset + "return (result, evidence);".len())
        .expect("direct Kind branch should return the computed evidence");
    let kind_branch = &fn_body[kind_start..kind_return];

    assert!(
        kind_branch.contains("ValidationEvidence::CounterexampleVerification"),
        "direct Kind branch must preserve explicit counterexample evidence on MultiPredLinear"
    );
    assert!(
        kind_branch.contains("ValidationEvidence::QueryOnly"),
        "direct adaptive Kind on MultiPredLinear must report QueryOnly evidence for Safe results"
    );
    assert!(
        !kind_branch.contains("ValidationEvidence::FullVerification"),
        "direct adaptive Kind branch on MultiPredLinear must not silently claim FullVerification"
    );
}

#[test]
fn test_multi_pred_portfolio_timeout_reserves_retry_budget() {
    assert_eq!(
        AdaptivePortfolio::multi_pred_portfolio_timeout(Duration::from_secs(15)),
        Duration::from_millis(10_500)
    );
}

#[test]
fn test_multi_pred_portfolio_timeout_clamps_small_remaining_budget() {
    assert_eq!(
        AdaptivePortfolio::multi_pred_portfolio_timeout(Duration::from_secs(2)),
        Duration::from_secs(2)
    );
}

#[test]
fn test_multi_pred_pdr_config_disables_entry_cegar_discharge() {
    let config = AdaptivePortfolio::multi_pred_pdr_config(PdrConfig::default());
    assert!(
        !config.use_entry_cegar_discharge,
        "multi-predicate adaptive PDR runs should skip entry-CEGAR discharge"
    );
}

#[test]
fn test_non_inlined_pdr_gate_skips_zero_predicate_problems() {
    let problem = ChcProblem::new();
    let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::default());
    let features = adaptive.features();

    assert_eq!(features.num_predicates, 0);
    assert!(
        !adaptive.should_try_non_inlined_pdr(&features),
        "problems without predicates should never run non-inlined PDR"
    );
}

#[test]
fn test_non_inlined_pdr_gate_skips_single_predicate_problems() {
    let problem = create_simple_loop();
    let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::default());
    let features = adaptive.features();

    assert!(features.is_single_predicate);
    assert!(
        !adaptive.should_try_non_inlined_pdr(&features),
        "single-predicate problems should stay on the normal path"
    );
}

#[test]
fn test_non_inlined_pdr_gate_always_tries_two_predicate_problems() {
    // #7934: The wide gate (all 2+ predicate problems) is required to
    // preserve per-predicate structure that clause inlining would destroy.
    // Narrowing to mod/div/ITE-only caused the s_multipl_* regression.
    let x = ChcVar::new("x", ChcSort::Int);
    let problem =
        create_two_predicate_gate_problem(Some(ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(10))));
    let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::default());
    let features = adaptive.features();

    assert_eq!(features.num_predicates, 2);
    assert!(
        adaptive.should_try_non_inlined_pdr(&features),
        "all 2+ predicate problems should try non-inlined PDR (#7934 wide gate)"
    );
}

#[test]
fn test_non_inlined_pdr_gate_keeps_trying_mod_constraints_for_two_predicates() {
    let x = ChcVar::new("x", ChcSort::Int);
    let problem = create_two_predicate_gate_problem(Some(ChcExpr::eq(
        ChcExpr::mod_op(ChcExpr::var(x), ChcExpr::int(2)),
        ChcExpr::int(0),
    )));
    let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::default());
    let features = adaptive.features();

    assert_eq!(features.num_predicates, 2);
    assert!(
        adaptive.should_try_non_inlined_pdr(&features),
        "mod/div-triggered problems should still try the non-inlined PDR stage"
    );
}

#[test]
fn test_non_inlined_pdr_gate_always_tries_long_predicate_chains() {
    let problem = create_four_predicate_gate_problem();
    let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::default());
    let features = adaptive.features();

    assert_eq!(features.num_predicates, 4);
    assert!(
        adaptive.should_try_non_inlined_pdr(&features),
        "4+ predicate problems should always try the non-inlined PDR stage"
    );
}

#[test]
fn test_non_inlined_pdr_budget_preserves_standard_long_chain_budget_without_arrays() {
    let problem = create_four_predicate_gate_problem();
    let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::default());
    let features = adaptive.features();

    assert!(!features.uses_arrays);
    assert_eq!(
        adaptive.non_inlined_pdr_stage_budget(&features, None),
        Duration::from_millis(3500)
    );
}

#[test]
fn test_non_inlined_pdr_budget_caps_array_heavy_long_chains_7897() {
    let problem = create_four_predicate_array_gate_problem();
    let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::default());
    let features = adaptive.features();

    assert_eq!(features.num_predicates, 4);
    assert!(features.uses_arrays);
    assert_eq!(
        adaptive.non_inlined_pdr_stage_budget(&features, None),
        Duration::from_millis(1750)
    );
}

/// Regression test for #6847: stack overflow on multi-predicate problems
/// with many arguments per predicate. The adaptive solver must run on a
/// thread with a large stack so that deep ChcExpr trees from SingleLoop
/// encoding don't overflow during recursive Arc<ChcExpr> Drop.
/// Note: the 5s internal time_budget is not a hard wall — the adaptive
/// solver can overrun significantly (20s debug, 90s+ release). The
/// time_budget enforcement gap is tracked by a separate issue.
#[test]
#[cfg_attr(debug_assertions, timeout(60_000))]
#[cfg_attr(not(debug_assertions), timeout(180_000))]
fn test_adaptive_multi_pred_many_args_no_stack_overflow_6847() {
    // Create a multi-predicate problem with many arguments (similar to
    // zani's merge_deps harness: 12 relations, 32 args per predicate).
    // Use a simpler variant (4 relations, 16 args) that exercises the
    // same SingleLoop encoding path without taking too long.
    let num_preds = 4;
    let args_per_pred = 16;
    let mut problem = ChcProblem::new();

    let mut pred_ids = Vec::new();
    for i in 0..num_preds {
        let sorts = vec![ChcSort::Int; args_per_pred];
        let id = problem.declare_predicate(&format!("P{i}"), sorts);
        pred_ids.push(id);
    }

    // Init clause: true => P0(0, 0, ..., 0)
    let zeros: Vec<ChcExpr> = (0..args_per_pred).map(|_| ChcExpr::int(0)).collect();
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(true)),
        ClauseHead::Predicate(pred_ids[0], zeros),
    ));

    // Transition clauses: Pi(x0..xN) => P(i+1)(x0+1..xN+1)
    for i in 0..num_preds - 1 {
        let vars: Vec<ChcVar> = (0..args_per_pred)
            .map(|j| ChcVar::new(format!("x{j}"), ChcSort::Int))
            .collect();
        let args: Vec<ChcExpr> = vars.iter().map(|v| ChcExpr::var(v.clone())).collect();
        let next_args: Vec<ChcExpr> = vars
            .iter()
            .map(|v| ChcExpr::add(ChcExpr::var(v.clone()), ChcExpr::int(1)))
            .collect();
        problem.add_clause(HornClause::new(
            ClauseBody::new(vec![(pred_ids[i], args)], None),
            ClauseHead::Predicate(pred_ids[i + 1], next_args),
        ));
    }

    // Query clause: P(N-1)(x0..xN) /\ x0 > 1000 => false
    let vars: Vec<ChcVar> = (0..args_per_pred)
        .map(|j| ChcVar::new(format!("x{j}"), ChcSort::Int))
        .collect();
    let args: Vec<ChcExpr> = vars.iter().map(|v| ChcExpr::var(v.clone())).collect();
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(pred_ids[num_preds - 1], args)],
            Some(ChcExpr::gt(
                ChcExpr::var(vars[0].clone()),
                ChcExpr::int(1000),
            )),
        ),
        ClauseHead::False,
    ));

    // Solve with a short budget — we only care about not crashing.
    let config = AdaptiveConfig {
        time_budget: Duration::from_secs(5),
        verbose: false,
        ..AdaptiveConfig::default()
    };
    let adaptive = AdaptivePortfolio::new(problem, config);
    let result = adaptive.solve();

    // Any result is acceptable — the key is that we didn't stack overflow.
    match result {
        VerifiedChcResult::Safe(_)
        | VerifiedChcResult::Unsafe(_)
        | VerifiedChcResult::Unknown(_) => {}
    }
}

#[test]
fn test_adaptive_portfolio_drop_deep_problem_small_stack_6847() {
    fn build_deep_problem(depth: usize) -> ChcProblem {
        let mut problem = ChcProblem::new();
        let pred = problem.declare_predicate("P", vec![ChcSort::Int]);
        let x = ChcVar::new("x", ChcSort::Int);
        let arg = ChcExpr::var(x);

        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::Bool(true)),
            ClauseHead::Predicate(pred, vec![ChcExpr::int(0)]),
        ));

        let mut deep = ChcExpr::Int(0);
        for _ in 0..depth {
            deep = ChcExpr::add(arg.clone(), deep);
        }

        problem.add_clause(HornClause::new(
            ClauseBody::new(vec![(pred, vec![arg])], Some(deep)),
            ClauseHead::False,
        ));
        problem
    }

    let problem = build_deep_problem(20_000);
    let handle = std::thread::Builder::new()
        .name("adaptive-drop-small-stack".to_string())
        .stack_size(2 * 1024 * 1024)
        .spawn(move || {
            let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::default());
            drop(adaptive);
        })
        .expect("small-stack regression thread should spawn");

    handle
        .join()
        .expect("AdaptivePortfolio drop should not overflow the caller stack");
}

/// BV MBP Packet 4 integration test: verify BV-native PDR converges on a
/// BV counting loop using the BV MBP interval projection path.
///
/// Problem: x starts at 0, increments by 1 while bvule(x, 3), asserts
/// bvule(5, x) is unreachable. Invariant: not(bvule(5, x)).
///
/// Uses PdrSolver directly (not PortfolioSolver) because the portfolio's
/// #6789 tautological guard rejects invariants that are exactly ¬query.
/// The invariant IS correct and 1-inductive; the guard is conservative.
/// The test verifies the full BV MBP integration: BV-native preprocessing,
/// MBP interval projection in project_bitvec_var, and PDR fixed-point.
///
/// Part of #7015 (BV MBP design, Packet 4).
#[test]
#[timeout(10_000)]
fn test_bv_native_pdr_interval_lemma_convergence() {
    let input = r#"
(set-logic HORN)
(declare-fun |inv| ((_ BitVec 8)) Bool)

(assert (forall ((x (_ BitVec 8)))
  (=> (= x #x00) (inv x))))

(assert (forall ((x (_ BitVec 8)) (xp (_ BitVec 8)))
  (=> (and (inv x) (bvule x #x03) (= xp (bvadd x #x01)))
      (inv xp))))

(assert (forall ((x (_ BitVec 8)))
  (=> (and (inv x) (bvule #x05 x))
      false)))

(check-sat)
(exit)
"#;
    let problem = ChcParser::parse(input).expect("BV counting loop should parse");

    // Run BV-native PDR directly (bypasses portfolio #6789 guard)
    let summary = PreprocessSummary::build_bv_native(problem, false);
    let pdr_config = PdrConfig {
        use_must_summaries: true,
        use_lemma_hints: true,
        max_frames: 50,
        ..PdrConfig::default()
    };
    let mut pdr = PdrSolver::new(summary.transformed_problem, pdr_config);
    let result = pdr.solve();
    assert!(
        matches!(result, PdrResult::Safe(_)),
        "BV-native PDR with interval MBP should prove the counting loop safe. Got: {result:?}"
    );
}

/// Regression test for #7897/#7931: adaptive solver must solve the accumulator
/// pattern via algebraic invariant synthesis. The loop computes sum = 0+1+...+(n-1)
/// = n*(n-1)/2, which requires a polynomial invariant that PDR alone cannot discover.
/// Algebraic synthesis detects the quadratic closed form and emits the invariant.
#[test]
#[timeout(30_000)]
fn test_adaptive_accumulator_algebraic_synthesis_7897() {
    let input = r#"
(set-logic HORN)
(declare-fun Inv (Int Int Int) Bool)

(assert (forall ((n Int) (i Int) (sum Int))
  (=> (and (<= 0 n) (<= n 100) (= i 0) (= sum 0))
      (Inv n i sum))))

(assert (forall ((n Int) (i Int) (sum Int) (i2 Int) (sum2 Int))
  (=> (and (Inv n i sum)
           (< i n)
           (= i2 (+ i 1))
           (= sum2 (+ sum i)))
      (Inv n i2 sum2))))

(assert (forall ((n Int) (i Int) (sum Int))
  (=> (and (Inv n i sum)
           (> sum (* n n)))
      false)))

(check-sat)
"#;
    let problem = ChcParser::parse(input).expect("accumulator should parse");
    let config = AdaptiveConfig::with_budget(Duration::from_secs(10), false);
    let solver = AdaptivePortfolio::new(problem, config);
    let result = solver.solve();
    assert!(
        matches!(result, VerifiedChcResult::Safe(_)),
        "Adaptive solver should prove accumulator safe via algebraic synthesis (#7897). Got: {result:?}"
    );
}
