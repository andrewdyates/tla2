// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ntest::timeout;
use z4_chc::{testing, ChcParser, EngineConfig, PdrConfig, PortfolioConfig, PortfolioResult};

fn portfolio_pdr_splits_config(base_pdr: PdrConfig) -> PortfolioConfig {
    let verbose = base_pdr.verbose;
    let cancellation_token = base_pdr.cancellation_token.clone();
    let user_hints = base_pdr.user_hints.clone();

    let mut pdr_no_splits = PdrConfig::production(verbose);
    let mut pdr_with_splits = PdrConfig::production_variant_with_splits(verbose);

    for pdr in [&mut pdr_no_splits, &mut pdr_with_splits] {
        pdr.max_frames = base_pdr.max_frames;
        pdr.max_iterations = base_pdr.max_iterations;
        pdr.max_obligations = base_pdr.max_obligations;
        pdr.cancellation_token = cancellation_token.clone();
        pdr.user_hints = user_hints.clone();
    }

    PortfolioConfig::with_engines(vec![
        EngineConfig::Pdr(pdr_no_splits),
        EngineConfig::Pdr(pdr_with_splits),
    ])
    .preprocessing(false)
}

fn solve_portfolio(input: &str, base_pdr: PdrConfig) -> PortfolioResult {
    let problem = ChcParser::parse(input).unwrap();
    let solver =
        testing::new_portfolio_solver(problem.clone(), portfolio_pdr_splits_config(base_pdr));
    let result = solver.solve();

    // Issue #758: Verify the proof when returning Safe.
    // Without this verification, Z4 can return "Safe" without proving anything.
    if let PortfolioResult::Safe(model) = &result {
        let mut verifier = testing::new_pdr_solver(problem, PdrConfig::default());
        assert!(
            verifier.verify_model(model),
            "BUG: Safe result has invalid proof (model verification failed)"
        );
    }

    result
}

/// Timeout: 1s (measured <10ms)
#[test]
#[timeout(1_000)]
fn portfolio_default_includes_multiple_pdr_variants() {
    let config = PortfolioConfig::default();

    let num_pdr = config
        .engines()
        .iter()
        .filter(|engine| matches!(engine, EngineConfig::Pdr(_)))
        .count();
    assert!(
        num_pdr >= 2,
        "Default portfolio should include multiple PDR variants"
    );
}

#[test]
#[timeout(180_000)]
fn portfolio_solves_bouncy_two_counters_equality_safe() {
    let input = r#"
(set-logic HORN)

(declare-fun |itp2| ( Int Int Int ) Bool)
(declare-fun |itp1| ( Int Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) )
    (=>
      (and
        (and (= B 0) (= A 0) (= C 0))
      )
      (itp1 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) )
    (=>
      (and
        (itp1 A C B)
        (and (= E C) (= D (+ 1 A)) (= F (+ 1 B)))
      )
      (itp1 D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) )
    (=>
      (and
        (itp1 A B C)
        true
      )
      (itp2 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) )
    (=>
      (and
        (itp2 C A B)
        (and (= E (+ 1 A)) (= D C) (= F (+ (- 1) B)))
      )
      (itp2 D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) )
    (=>
      (and
        (itp2 A B C)
        (and (= A B) (not (= C 0)))
      )
      false
    )
  )
)

(check-sat)
"#;

    let mut base_pdr = PdrConfig::production(false);
    base_pdr.max_frames = 40;
    base_pdr.max_iterations = 5_000;
    base_pdr.max_obligations = 200_000;

    eprintln!("Starting portfolio solver for bouncy_two_counters_equality...");
    let result = solve_portfolio(input, base_pdr);
    eprintln!("Portfolio solver completed with {result:?}");
    assert!(
        matches!(result, PortfolioResult::Safe(_)),
        "expected Safe, got {result:?}"
    );
}

/// Test dillig12_m with E=1 constrained at init.
///
/// **Current status:** REGRESSION TARGET
///
/// This benchmark currently returns Unknown because:
/// 1. Case-split optimization doesn't apply (E is constrained at init, not unconstrained)
/// 2. PDR cannot discover the required D=2*E invariant within the iteration limit
///
/// When E is unconstrained (original dillig12_m), case-split discovers the conditional invariant.
/// When E=1 (constrained as in this test), we need direct invariant discovery for D=2*C.
///
/// Related issues:
/// - #1261: This test failure
/// - #1263: Broader pdr_examples regression
/// - #1306: Case-split implementation (works for unconstrained E only)
/// - #966, #967: Invariant discovery improvements needed
///
/// Expected to become Safe after #966 or similar invariant discovery improvements.
#[test]
#[timeout(60_000)] // portfolio has substantial overhead in debug; allow variance
fn portfolio_dillig12_m_e1_unknown() {
    let input = r#"
(set-logic HORN)
(declare-fun |SAD| ( Int Int ) Bool)
(declare-fun |FUN| ( Int Int Int Int Int ) Bool)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) )
    (=>
      (and (and (= C 0) (= B 0) (= A 0) (= D 0) (= E 1)))
      (FUN A B C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) )
    (=>
      (and
        (FUN A B C D J)
        (and (= I (ite (= J 1) (+ E F) E))
     (= H (+ C F))
     (= G (+ 1 B))
     (= F (+ 1 A))
     (= E (+ D G)))
      )
      (FUN F G H I J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) )
    (=>
      (and
        (FUN A B E D C)
        (let ((a!1 (= F (ite (= C 1) (+ 2 D (* (- 2) E)) 1))))
  (and a!1 (= G 0)))
      )
      (SAD F G)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) )
    (=>
      (and
        (SAD B A)
        (and (or (= C (+ 1 A)) (= C (+ 2 A))) (<= A B))
      )
      (SAD B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) )
    (=>
      (and
        (SAD A B)
        (and (>= B A) (>= B 5))
      )
      false
    )
  )
)
(check-sat)
(exit)
"#;

    // Use very low iteration limits to make Unknown return quickly.
    // The goal is just to confirm the solver returns Unknown (not Safe/Unsafe).
    let mut base_pdr = PdrConfig::production(false);
    base_pdr.max_frames = 2; // Very low - just need Unknown
    base_pdr.max_iterations = 5; // Very low - just need Unknown
    base_pdr.max_obligations = 200; // Very low - just need Unknown

    let result = solve_portfolio(input, base_pdr);
    // Regression target: expect Unknown until invariant discovery is improved
    // (see #966, #967 for required capabilities)
    assert!(
        matches!(result, PortfolioResult::Unknown),
        "Regression target: expected Unknown (Safe would indicate issue is fixed), got {result:?}"
    );
}
/// Regression test for #5213: portfolio must not return Safe on UNSAFE problems.
///
/// Models a simple program: x starts at 0, increments by 1, with assertion x <= 5.
/// The assertion is violated when x reaches 6, so the system is UNSAFE.
///
/// Before fix: engines like PDR could return Safe with budget-limited verification
/// that skipped transition clause checks, and the portfolio accepted it without
/// re-validation. After fix: all Safe results are validated at portfolio level.
///
/// Timeout: 30s (measured <1s)
#[test]
#[timeout(30_000)]
fn portfolio_rejects_safe_on_unsafe_counter_issue_5213() {
    use z4_chc::{ChcExpr, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause};

    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // Init: x = 0 => Inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    // Trans: Inv(x) => Inv(x + 1) — unbounded increment
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(inv, vec![ChcExpr::var(x.clone())])], None),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    // Query: Inv(x) /\ x > 5 => false
    // UNSAFE: x reaches 6 after 6 transitions
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(5))),
        ),
        ClauseHead::False,
    ));

    // Test with PDR-only (previously skipped validation) and full portfolio.
    // Both must reject false Safe results on this UNSAFE problem.
    let engine_configs: Vec<(&str, PortfolioConfig)> = vec![
        (
            "PDR-only",
            PortfolioConfig::with_engines(vec![EngineConfig::Pdr(PdrConfig::default())])
                .preprocessing(false),
        ),
        ("full-portfolio", PortfolioConfig::default()),
    ];

    for (name, config) in engine_configs {
        let solver = testing::new_portfolio_solver(problem.clone(), config);
        let result = solver.solve();
        // Must find Unsafe — this is a trivial 6-step counterexample (x: 0→1→...→6 > 5).
        // Accepting Unknown masks completeness regressions (#3015).
        assert!(
            matches!(result, PortfolioResult::Unsafe(_)),
            "expected Unsafe from {name} on UNSAFE counter problem, got {result:?}.\n\
             x starts at 0 and increments unboundedly, so x > 5 is reachable."
        );
    }
}

/// BV-to-Int abstraction end-to-end test (#5981).
///
/// Constructs a BV8 CHC problem: counter starts at 0, increments by 1 while x < 5,
/// and the property asserts x <= 10. The BV-to-Int transformer converts BV8 sorts
/// to Int with range constraints, enabling the LIA invariant discovery to prove safety.
///
/// Timeout: 60s (BV abstraction + PDR solving)
#[test]
#[timeout(60_000)]
fn portfolio_bv8_counter_safe_via_bv_to_int_abstraction_5981() {
    use std::sync::Arc;
    use z4_chc::{ChcExpr, ChcOp, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause};

    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::BitVec(8)]);
    let x = ChcVar::new("x", ChcSort::BitVec(8));

    // Init: x = 0 => Inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::BitVec(0, 8))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    // Trans: Inv(x) AND bvult(x, 5) => Inv(bvadd(x, 1))
    let x_plus_1 = ChcExpr::Op(
        ChcOp::BvAdd,
        vec![
            Arc::new(ChcExpr::var(x.clone())),
            Arc::new(ChcExpr::BitVec(1, 8)),
        ],
    );
    let x_lt_5 = ChcExpr::Op(
        ChcOp::BvULt,
        vec![
            Arc::new(ChcExpr::var(x.clone())),
            Arc::new(ChcExpr::BitVec(5, 8)),
        ],
    );
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(inv, vec![ChcExpr::var(x.clone())])], Some(x_lt_5)),
        ClauseHead::Predicate(inv, vec![x_plus_1]),
    ));

    // Query: Inv(x) AND bvugt(x, 10) => false
    // SAFE: x only reaches 0..5, so bvugt(x, 10) is never true.
    let x_gt_10 = ChcExpr::Op(
        ChcOp::BvUGt,
        vec![
            Arc::new(ChcExpr::var(x.clone())),
            Arc::new(ChcExpr::BitVec(10, 8)),
        ],
    );
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(inv, vec![ChcExpr::var(x)])], Some(x_gt_10)),
        ClauseHead::False,
    ));

    // Full portfolio with preprocessing (includes BV-to-Int abstraction)
    let config = PortfolioConfig::default();
    let solver = testing::new_portfolio_solver(problem, config);
    let result = solver.solve();

    assert!(
        matches!(result, PortfolioResult::Safe(_)),
        "BV8 counter should be Safe via BV-to-Int abstraction, got {result:?}"
    );
}

/// BV32-to-Int abstraction test (#5981) — zani target width.
///
/// Same counter pattern as the BV8 test but with BV32, matching the bit-width
/// of u32 loop counters in zani Kani harnesses. Verifies that BV-to-Int
/// abstraction scales to realistic widths (range constraint is 0 <= x < 2^32).
///
/// Timeout: 60s
#[test]
#[timeout(60_000)]
fn portfolio_bv32_counter_safe_via_bv_to_int_abstraction_5981() {
    use std::sync::Arc;
    use z4_chc::{ChcExpr, ChcOp, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause};

    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::BitVec(32)]);
    let x = ChcVar::new("x", ChcSort::BitVec(32));

    // Init: x = 0 => Inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::BitVec(0, 32))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    // Trans: Inv(x) AND bvult(x, 5) => Inv(bvadd(x, 1))
    let x_plus_1 = ChcExpr::Op(
        ChcOp::BvAdd,
        vec![
            Arc::new(ChcExpr::var(x.clone())),
            Arc::new(ChcExpr::BitVec(1, 32)),
        ],
    );
    let x_lt_5 = ChcExpr::Op(
        ChcOp::BvULt,
        vec![
            Arc::new(ChcExpr::var(x.clone())),
            Arc::new(ChcExpr::BitVec(5, 32)),
        ],
    );
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(inv, vec![ChcExpr::var(x.clone())])], Some(x_lt_5)),
        ClauseHead::Predicate(inv, vec![x_plus_1]),
    ));

    // Query: Inv(x) AND bvugt(x, 10) => false
    let x_gt_10 = ChcExpr::Op(
        ChcOp::BvUGt,
        vec![
            Arc::new(ChcExpr::var(x.clone())),
            Arc::new(ChcExpr::BitVec(10, 32)),
        ],
    );
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(inv, vec![ChcExpr::var(x)])], Some(x_gt_10)),
        ClauseHead::False,
    ));

    let config = PortfolioConfig::default();
    let solver = testing::new_portfolio_solver(problem, config);
    let result = solver.solve();

    assert!(
        matches!(result, PortfolioResult::Safe(_)),
        "BV32 counter should be Safe via BV-to-Int abstraction, got {result:?}"
    );
}

/// BV32 accumulator loop test (#2682) — zani accumulator harness pattern.
///
/// Models `while i < n { sum += i; i += 1; }` with n=5.
/// Predicate: Inv(i: BV32, sum: BV32)
/// Init: i=0, sum=0
/// Trans: Inv(i, sum) AND bvult(i, 5) => Inv(bvadd(i, 1), bvadd(sum, i))
/// Query: Inv(i, sum) AND bvugt(sum, 100) => false
///   (safe because max sum = 0+1+2+3+4 = 10 < 100)
///
/// Exercises the BV-to-Int abstraction pipeline on the representative zani
/// pattern of accumulator loops with two BV predicate arguments.
#[test]
#[timeout(180_000)] // 35s release; debug mode ~5x slower under BV-to-Int abstraction
fn portfolio_bv32_accumulator_safe_via_bv_to_int_2682() {
    use std::sync::Arc;
    use z4_chc::{ChcExpr, ChcOp, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause};

    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::BitVec(32), ChcSort::BitVec(32)]);
    let i = ChcVar::new("i", ChcSort::BitVec(32));
    let sum = ChcVar::new("sum", ChcSort::BitVec(32));

    // Init: i=0, sum=0 => Inv(i, sum)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::and(
            ChcExpr::eq(ChcExpr::var(i.clone()), ChcExpr::BitVec(0, 32)),
            ChcExpr::eq(ChcExpr::var(sum.clone()), ChcExpr::BitVec(0, 32)),
        )),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::var(i.clone()), ChcExpr::var(sum.clone())],
        ),
    ));

    // Trans: Inv(i, sum) AND bvult(i, 5) => Inv(bvadd(i, 1), bvadd(sum, i))
    let i_plus_1 = ChcExpr::Op(
        ChcOp::BvAdd,
        vec![
            Arc::new(ChcExpr::var(i.clone())),
            Arc::new(ChcExpr::BitVec(1, 32)),
        ],
    );
    let sum_plus_i = ChcExpr::Op(
        ChcOp::BvAdd,
        vec![
            Arc::new(ChcExpr::var(sum.clone())),
            Arc::new(ChcExpr::var(i.clone())),
        ],
    );
    let i_lt_5 = ChcExpr::Op(
        ChcOp::BvULt,
        vec![
            Arc::new(ChcExpr::var(i.clone())),
            Arc::new(ChcExpr::BitVec(5, 32)),
        ],
    );
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(
                inv,
                vec![ChcExpr::var(i.clone()), ChcExpr::var(sum.clone())],
            )],
            Some(i_lt_5),
        ),
        ClauseHead::Predicate(inv, vec![i_plus_1, sum_plus_i]),
    ));

    // Query: Inv(i, sum) AND bvugt(sum, 100) => false
    // Safe: sum reaches at most 10, never exceeds 100.
    let sum_gt_100 = ChcExpr::Op(
        ChcOp::BvUGt,
        vec![
            Arc::new(ChcExpr::var(sum.clone())),
            Arc::new(ChcExpr::BitVec(100, 32)),
        ],
    );
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(i), ChcExpr::var(sum)])],
            Some(sum_gt_100),
        ),
        ClauseHead::False,
    ));

    let config = PortfolioConfig::default();
    let solver = testing::new_portfolio_solver(problem, config);
    let result = solver.solve();

    assert!(
        matches!(result, PortfolioResult::Safe(_)),
        "BV32 accumulator loop should be Safe via BV-to-Int abstraction, got {result:?}"
    );
}

/// Symbolic accumulator loop from zani issue #1753.
///
/// This is the reduced Int form of:
/// `while i < n { sum += i; i += 1; } assert(sum <= n*n);`
///
/// The regression exercises two pieces together:
/// 1. portfolio algebraic synthesis must analyze the original self-loop shape
///    (before LocalVarEliminator rewrites head vars into expressions), and
/// 2. the resulting quadratic invariant needs companion bounds like `0 <= i <= n`.
#[test]
#[timeout(30_000)]
fn portfolio_symbolic_accumulator_safe_via_algebraic_invariants_1753() {
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
    let problem = ChcParser::parse(input).expect("symbolic accumulator should parse");
    let solver = testing::new_portfolio_solver(problem, PortfolioConfig::default());
    let result = solver.solve();

    assert!(
        matches!(result, PortfolioResult::Safe(_)),
        "symbolic accumulator loop should be Safe via algebraic + bound synthesis, got {result:?}"
    );
}

/// Monotone-product factorial positivity loop from zani issue #1753.
///
/// Reduced Int form of:
/// `result = 1; for i in 1..=n { result *= i; } assert(result >= 1);`
#[test]
#[timeout(30_000)]
fn portfolio_factorial_positive_product_safe_1753() {
    let input = r#"
(set-logic HORN)
(declare-fun Inv (Int Int Int) Bool)

(assert (forall ((n Int) (i Int) (result Int))
  (=> (and (<= 0 n) (<= n 12) (= i 1) (= result 1))
      (Inv n i result))))

(assert (forall ((n Int) (i Int) (result Int) (i2 Int) (result2 Int))
  (=> (and (Inv n i result)
           (<= i n)
           (= i2 (+ i 1))
           (= result2 (* result i)))
      (Inv n i2 result2))))

(assert (forall ((n Int) (i Int) (result Int))
  (=> (and (Inv n i result)
           (< result 1))
      false)))

(check-sat)
"#;
    let problem = ChcParser::parse(input).expect("factorial positivity loop should parse");
    let solver = testing::new_portfolio_solver(problem, PortfolioConfig::default());
    let result = solver.solve();

    assert!(
        matches!(result, PortfolioResult::Safe(_)),
        "factorial positivity loop should be Safe via monotone-product invariant, got {result:?}"
    );
}

/// BV-to-Int spurious UNSAFE regression test (#6047).
///
/// Constructs a BV8 problem that uses `bvand` (bitwise AND) in the transition.
/// BV-to-Int maps `bvand` to an uninterpreted function, creating imprecision:
/// in BV8, `bvand(x, 15) <= 15` always holds, but in Int the over-approximation
/// cannot prove this bound. Engines operating on the Int-abstracted problem may
/// produce an UNSAFE result that is spurious (valid in Int, invalid in BV).
///
/// The `bv_abstracted` guard (commit a44a9a7, #6047) must prevent the portfolio
/// from reporting such a spurious UNSAFE. Expected: Safe or Unknown, never Unsafe.
///
/// Regression for: BV-to-Int over-approximation soundness
/// Related: W3:2009 (fix), P2:127 (regression test request)
#[test]
#[timeout(30_000)]
fn portfolio_bv_to_int_rejects_spurious_unsafe_6047() {
    // BV8 problem: Inv(x) with init x=0, trans Inv(x) => Inv(bvand(bvadd(x,1), 15)),
    // query Inv(x) AND bvugt(x, 15) => false.
    //
    // BV8 semantics: bvand(bvadd(x,1), 15) masks to low 4 bits. x ∈ {0..15} always.
    // Property x <= 15 is trivially safe.
    //
    // Int semantics after BV-to-Int: bvand becomes uninterpreted __bv2int_bvand.
    // Solver cannot prove __bv2int_bvand(x+1, 15) <= 15 without BV axioms.
    // This may cause spurious UNSAFE from trivial solver or engine result.
    let input = r#"
(set-logic HORN)
(declare-fun Inv ((_ BitVec 8)) Bool)

; Init: x = 0 => Inv(x)
(assert (forall ((x (_ BitVec 8)))
  (=> (= x #x00) (Inv x))))

; Trans: Inv(x) => Inv(bvand (bvadd x #x01) #x0F)
(assert (forall ((x (_ BitVec 8)))
  (=> (Inv x) (Inv (bvand (bvadd x #x01) #x0F)))))

; Query: Inv(x) AND bvugt(x, 15) => false
; Safe in BV8: bvand masks to 0..15, so x > 15 is unreachable.
(assert (forall ((x (_ BitVec 8)))
  (=> (and (Inv x) (bvugt x #x0F)) false)))

(check-sat)
"#;
    let problem = ChcParser::parse(input).expect("BV8 bvand problem should parse");
    // Use minimal engine config: PDR only, sequential, with per-engine timeout.
    // PDR on the Int-abstracted problem produces a spurious Unsafe quickly;
    // the sort-mismatch guard should reject it and return Unknown.
    let config = PortfolioConfig::with_engines(vec![EngineConfig::Pdr(PdrConfig::default())])
        .parallel(false)
        .timeout(Some(std::time::Duration::from_secs(5)));
    let solver = testing::new_portfolio_solver(problem, config);
    let result = solver.solve();

    // The problem is SAFE in BV8. After BV-to-Int, the bvand over-approximation
    // may cause engines to report Unsafe — the bv_abstracted guard must reject
    // such spurious results. Acceptable outcomes: Safe (if solver handles it)
    // or Unknown (if over-approximation prevents proof). Never Unsafe.
    assert!(
        !matches!(result, PortfolioResult::Unsafe(_)),
        "BV8 bvand-mask problem is SAFE but BV-to-Int over-approximation reported Unsafe.\n\
         The bv_abstracted guard should prevent spurious UNSAFE (#6047). Got: {result:?}"
    );
}

/// BV32 symbolic accumulator loop (#7931) -- the zani accumulator harness pattern.
///
/// Models `while i < n { sum += i; i += 1; } assert(sum <= n*n);`
/// with all variables as BitVec(32) and n symbolic (bounded by 100).
///
/// This is the exact pattern that blocks Z3 elimination from zani.
/// The invariant requires polynomial reasoning: sum = i*(i-1)/2 <= n*n.
/// The portfolio must apply BvToBool + BvToInt abstraction, then algebraic
/// synthesis discovers the quadratic closed form and derives the invariant.
#[test]
#[timeout(60_000)]
fn portfolio_bv32_symbolic_accumulator_safe_via_algebraic_7931() {
    use std::sync::Arc;
    use z4_chc::{ChcExpr, ChcOp, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause};

    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate(
        "Inv",
        vec![
            ChcSort::BitVec(32),
            ChcSort::BitVec(32),
            ChcSort::BitVec(32),
        ],
    );
    let n = ChcVar::new("n", ChcSort::BitVec(32));
    let i = ChcVar::new("i", ChcSort::BitVec(32));
    let sum = ChcVar::new("sum", ChcSort::BitVec(32));

    // Init: bvule(n, 100), i = 0, sum = 0 => Inv(n, i, sum)
    let n_le_100 = ChcExpr::Op(
        ChcOp::BvULe,
        vec![
            Arc::new(ChcExpr::var(n.clone())),
            Arc::new(ChcExpr::BitVec(100, 32)),
        ],
    );
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::Op(
            ChcOp::And,
            vec![
                Arc::new(n_le_100),
                Arc::new(ChcExpr::eq(ChcExpr::var(i.clone()), ChcExpr::BitVec(0, 32))),
                Arc::new(ChcExpr::eq(
                    ChcExpr::var(sum.clone()),
                    ChcExpr::BitVec(0, 32),
                )),
            ],
        )),
        ClauseHead::Predicate(
            inv,
            vec![
                ChcExpr::var(n.clone()),
                ChcExpr::var(i.clone()),
                ChcExpr::var(sum.clone()),
            ],
        ),
    ));

    // Trans: Inv(n, i, sum) AND bvult(i, n) => Inv(n, bvadd(i, 1), bvadd(sum, i))
    let i_plus_1 = ChcExpr::Op(
        ChcOp::BvAdd,
        vec![
            Arc::new(ChcExpr::var(i.clone())),
            Arc::new(ChcExpr::BitVec(1, 32)),
        ],
    );
    let sum_plus_i = ChcExpr::Op(
        ChcOp::BvAdd,
        vec![
            Arc::new(ChcExpr::var(sum.clone())),
            Arc::new(ChcExpr::var(i.clone())),
        ],
    );
    let i_lt_n = ChcExpr::Op(
        ChcOp::BvULt,
        vec![
            Arc::new(ChcExpr::var(i.clone())),
            Arc::new(ChcExpr::var(n.clone())),
        ],
    );
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(
                inv,
                vec![
                    ChcExpr::var(n.clone()),
                    ChcExpr::var(i.clone()),
                    ChcExpr::var(sum.clone()),
                ],
            )],
            Some(i_lt_n),
        ),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(n.clone()), i_plus_1, sum_plus_i]),
    ));

    // Query: Inv(n, i, sum) AND bvugt(sum, bvmul(n, n)) => false
    let n_times_n = ChcExpr::Op(
        ChcOp::BvMul,
        vec![
            Arc::new(ChcExpr::var(n.clone())),
            Arc::new(ChcExpr::var(n.clone())),
        ],
    );
    let sum_gt_n_sq = ChcExpr::Op(
        ChcOp::BvUGt,
        vec![Arc::new(ChcExpr::var(sum.clone())), Arc::new(n_times_n)],
    );
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(
                inv,
                vec![ChcExpr::var(n), ChcExpr::var(i), ChcExpr::var(sum)],
            )],
            Some(sum_gt_n_sq),
        ),
        ClauseHead::False,
    ));

    // Disable preprocessing: BvToBool bitblasting of BV32 (3 vars -> 96 Bool args)
    // is very expensive and not needed here. The algebraic prepass applies its own
    // BvToInt pipeline (without BvToBool) to the original problem. Part of #7931.
    let config = PortfolioConfig::default().preprocessing(false);
    let solver = testing::new_portfolio_solver(problem, config);
    let result = solver.solve();

    assert!(
        matches!(result, PortfolioResult::Safe(_)),
        "BV32 symbolic accumulator loop should be Safe via BV-to-Int + algebraic synthesis (#7931), got {result:?}"
    );
}

// test_preprocessing_reduces_clause_count moved to transform/clause_inlining.rs (#3627)
