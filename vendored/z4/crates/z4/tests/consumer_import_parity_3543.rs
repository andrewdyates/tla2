// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Downstream-shaped import parity canaries (#3543).
//!
//! Each test mirrors the concrete import set used by a consumer repo,
//! proving that all required types compile through the root `z4` facade
//! without reaching into internal crates (`z4_dpll`, `z4_core`, `z4_chc`,
//! `z4_frontend`).
//!
//! If a test here fails to compile, the facade is missing a re-export that
//! a downstream consumer depends on.

#![allow(deprecated)]

fn assert_public_type<T>() {}

// ---------------------------------------------------------------------------
// certus: z4_dpll::api + z4_core types
// Source: ~/certus/crates/certus-core/src/encoder/mod.rs:57-59
// ---------------------------------------------------------------------------

#[test]
fn certus_api_imports_compile() {
    use z4::api::{FuncDecl, Logic, Solver, Sort};
    use z4::ArraySort;

    assert_public_type::<ArraySort>();
    assert_public_type::<FuncDecl>();
    assert_public_type::<Solver>();
    assert_public_type::<Sort>();

    // Smoke: trivial SAT through the typed API
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let gt = solver.gt(x, zero);
    solver.assert_term(gt);
    assert!(solver.check_sat().is_sat());
}

// ---------------------------------------------------------------------------
// sunder: z4_dpll::api types (Model, SolveResult, Solver, Sort, Term)
// Source: ~/sunder/crates/sunder-z4/src/encoder/solver.rs:11-15
// ---------------------------------------------------------------------------

#[test]
fn sunder_api_imports_compile() {
    use z4::api::{Logic, Model, SolveResult, Solver, Sort, Term};

    assert_public_type::<Model>();
    assert_public_type::<SolveResult>();
    assert_public_type::<Solver>();
    assert_public_type::<Sort>();
    assert_public_type::<Term>();

    // Smoke: solve and extract model
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let one = solver.int_const(1);
    let eq = solver.eq(x, one);
    solver.assert_term(eq);
    assert!(solver.check_sat().is_sat());
    let model = solver.model().expect("SAT has model");
    assert_eq!(model.model().int_val_i64("x"), Some(1));
}

// ---------------------------------------------------------------------------
// tla2: z4_dpll::api + z4_chc (PdrConfig, PdrSolver) + z4_frontend (parse)
// Source: ~/tla2/crates/tla-z4/src/lib.rs:117-125
//         ~/tla2/crates/tla-z4/src/chc.rs:276-279
// ---------------------------------------------------------------------------

#[test]
fn tla2_api_and_chc_imports_compile() {
    use z4::api::{Logic, Model, SolveResult, Solver, Sort, Term};
    use z4::chc::{engines, ChcProblem, PdrConfig, PdrSolver};
    use z4::executor::Executor;
    use z4::parse;

    assert_public_type::<Logic>();
    assert_public_type::<Model>();
    assert_public_type::<SolveResult>();
    assert_public_type::<Solver>();
    assert_public_type::<Sort>();
    assert_public_type::<Term>();
    assert_public_type::<ChcProblem>();
    assert_public_type::<PdrConfig>();
    assert_public_type::<PdrSolver>();
    assert_public_type::<Executor>();

    // Verify engines module is accessible (new_pdr_solver constructor)
    let problem = ChcProblem::new();
    let config = PdrConfig::default();
    let _solver = engines::new_pdr_solver(problem, config);

    // Verify parse + Executor path
    let commands = parse("(set-logic QF_LIA)\n(check-sat)").expect("valid");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("ok");
    assert_eq!(outputs, vec!["sat"]);
}

// ---------------------------------------------------------------------------
// zani: z4_frontend (Command, parse, SExpr, sexp::*) + z4_dpll (Executor) +
//       z4_chc (SmtContext, SmtResult, PortfolioSolver, CHC types)
// Source: ~/zani/zani-driver/src/z4_direct.rs:42,117,264-265
//         ~/zani/zani-driver/src/z4_parse/chc.rs:7-8
//         ~/zani/zani-driver/src/call_z4/chc/proof_core/solve.rs:13-16
// ---------------------------------------------------------------------------

#[test]
fn zani_executor_chc_and_sexp_imports_compile() {
    use z4::chc::{ChcExpr, ChcProblem, PdrConfig, PortfolioSolver, SmtContext, SmtResult};
    use z4::executor::Executor;
    use z4::sexp::{parse_sexp, parse_sexps, SExpr};
    use z4::{parse, Command};

    assert_public_type::<Command>();
    assert_public_type::<Executor>();
    assert_public_type::<SExpr>();
    assert_public_type::<ChcExpr>();
    assert_public_type::<ChcProblem>();
    assert_public_type::<PdrConfig>();
    assert_public_type::<PortfolioSolver>();
    assert_public_type::<SmtContext>();
    assert_public_type::<SmtResult>();

    // Verify sexp parsing works through facade
    let expr = parse_sexp("(+ 1 2)").expect("valid s-expression");
    assert!(matches!(expr, SExpr::List(_)));

    let exprs = parse_sexps("(+ 1 2)\n(- 3 4)").expect("valid s-expressions");
    assert_eq!(exprs.len(), 2);

    // Verify parse + Executor path
    let commands = parse("(set-logic QF_LIA)\n(check-sat)").expect("valid");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("ok");
    assert_eq!(outputs, vec!["sat"]);
}

// ---------------------------------------------------------------------------
// ---------------------------------------------------------------------------
// zani: CHC try_solve through z4::chc facade
// Source: ~/zani/zani-driver/src/call_z4/chc.rs:99-118 (catch_unwind wrapper)
// ---------------------------------------------------------------------------

#[test]
fn zani_chc_try_solve_compiles() {
    use z4::chc::{
        AdaptiveConfig, AdaptivePortfolio, ChcError, ChcProblem, ChcResult, VerifiedChcResult,
    };

    assert_public_type::<AdaptiveConfig>();
    assert_public_type::<AdaptivePortfolio>();
    assert_public_type::<ChcProblem>();
    assert_public_type::<ChcResult<()>>();
    assert_public_type::<VerifiedChcResult>();
    assert_public_type::<ChcError>();

    // Verify try_solve returns ChcResult (= Result<_, ChcError>)
    let problem = ChcProblem::new();
    let config = AdaptiveConfig::default();
    let portfolio = AdaptivePortfolio::new(problem, config);
    let result: ChcResult<VerifiedChcResult> = portfolio.try_solve();
    // Empty problem should solve without panic
    assert!(result.is_ok());
}

// ---------------------------------------------------------------------------
// zani: CHC native panic-safe entrypoints (#6714)
// Source: ~/zani/zani-driver/src/call_z4/chc.rs:857-878, 935-938
// These are the methods zani actually calls; AdaptivePortfolio::try_solve()
// above is API completeness only.
// ---------------------------------------------------------------------------

#[test]
fn zani_chc_native_panic_safe_entrypoints_compile() {
    use z4::chc::{
        CexVerificationResult, ChcError, ChcResult, Counterexample, InvariantModel, PdrSolver,
        PortfolioResult, PortfolioSolver,
    };

    assert_public_type::<PortfolioSolver>();
    assert_public_type::<PdrSolver>();
    assert_public_type::<InvariantModel>();
    assert_public_type::<Counterexample>();
    assert_public_type::<PortfolioResult>();
    assert_public_type::<CexVerificationResult>();
    assert_public_type::<ChcResult<()>>();
    assert_public_type::<ChcError>();

    // Function-item type assertions prove method signatures match zani's expectations.
    // try_* methods return ChcResult<T> (= Result<T, ChcError>) instead of Result<T, String>.
    let _: fn(&PortfolioSolver) -> ChcResult<PortfolioResult> = PortfolioSolver::try_solve;
    let _: fn(&mut PdrSolver, &InvariantModel) -> ChcResult<bool> = PdrSolver::try_verify_model;
    let _: fn(&mut PdrSolver, &Counterexample) -> ChcResult<CexVerificationResult> =
        PdrSolver::try_verify_counterexample;
}

// ---------------------------------------------------------------------------
// gamma-crown: z4_frontend (parse, Command, SExpr) + z4_dpll (Executor)
// Source: ~/gamma-crown/crates/gamma-smt/src/verifier/solver.rs:17-19
// Note: gamma-crown also uses z4_proof and z4_tla_bridge as direct deps;
//       those are NOT tested here (intentionally outside the root facade).
// ---------------------------------------------------------------------------

#[test]
fn gamma_crown_parser_executor_imports_compile() {
    use z4::executor::Executor;
    use z4::{parse, Command, SExpr};

    assert_public_type::<Command>();
    assert_public_type::<Executor>();
    assert_public_type::<SExpr>();

    // Verify parse + Executor path (gamma-crown's primary z4 usage pattern)
    let commands = parse("(set-logic QF_LIA)\n(check-sat)").expect("valid");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("ok");
    assert_eq!(outputs, vec!["sat"]);
}

// ---------------------------------------------------------------------------
// tla2: z4::allsat (AllSatSolver, AllSatConfig) for solution enumeration
// Source: ~/tla2/crates/tla-z4/src/allsat.rs (planned #6712)
// ---------------------------------------------------------------------------

#[test]
fn tla2_allsat_imports_compile() {
    use z4::allsat::{AllSatConfig, AllSatSolver};

    assert_public_type::<AllSatConfig>();
    assert_public_type::<AllSatSolver>();

    // Smoke: enumerate solutions for a 2-variable SAT problem
    let mut solver = AllSatSolver::new();
    solver.add_clause(vec![1, 2]);
    solver.add_clause(vec![-1, -2]);
    let solutions: Vec<_> = solver.iter().collect();
    assert_eq!(solutions.len(), 2);
}

// ---------------------------------------------------------------------------
// zani: z4::chc PortfolioSolver::try_solve() + PdrSolver try_* wrappers (#6714)
// Source: ~/zani/zani-driver/src/call_z4/chc/proof_core/solve.rs:13-16
// ---------------------------------------------------------------------------

#[test]
fn zani_portfolio_pdr_try_wrappers_compile() {
    use z4::chc::{
        CexVerificationResult, ChcError, ChcResult, Counterexample, InvariantModel, PdrSolver,
        PortfolioResult, PortfolioSolver,
    };

    assert_public_type::<PortfolioResult>();
    assert_public_type::<PortfolioSolver>();
    assert_public_type::<CexVerificationResult>();
    assert_public_type::<ChcResult<()>>();
    assert_public_type::<PdrSolver>();

    // Verify PortfolioSolver::try_solve returns Result<_, ChcError>
    let _: fn(&PortfolioSolver) -> Result<PortfolioResult, ChcError> = PortfolioSolver::try_solve;

    // Verify PdrSolver::try_verify_model returns ChcResult
    let _: fn(&mut PdrSolver, &InvariantModel) -> ChcResult<bool> = PdrSolver::try_verify_model;

    // Verify PdrSolver::try_verify_counterexample returns ChcResult
    let _: fn(&mut PdrSolver, &Counterexample) -> ChcResult<CexVerificationResult> =
        PdrSolver::try_verify_counterexample;
}

#[test]
fn statistics_value_imports_compile() {
    use z4::api::StatValue as ApiStatValue;
    use z4::prelude::StatValue as PreludeStatValue;
    use z4::StatValue;

    assert_public_type::<StatValue>();
    assert_public_type::<ApiStatValue>();
    assert_public_type::<PreludeStatValue>();

    let _: StatValue = StatValue::Int(7);
    let _: ApiStatValue = ApiStatValue::Float(1.5);
    let _: PreludeStatValue = PreludeStatValue::String("facade".to_string());
}

#[test]
fn zani_chc_detail_type_imports_compile() {
    use z4::chc::{CounterexampleStep, PredicateInterpretation};

    assert_public_type::<CounterexampleStep>();
    assert_public_type::<PredicateInterpretation>();
}

// ---------------------------------------------------------------------------
// zani: LemmaHint API for auto-invariant injection
// Source: ~/zani/zani-driver/src/auto_invariants.rs (LemmaHintProvider impl)
// Zani implements LemmaHintProvider to inject range bounds and type-driven
// invariants into z4-chc PDR. This test proves the full trait + type surface
// is importable through the z4::chc facade.
// ---------------------------------------------------------------------------

#[test]
fn zani_lemma_hint_provider_api_compiles() {
    use std::sync::Arc;
    use z4::chc::{
        canonical_var_for_pred_arg, canonical_var_name, canonical_vars_for_pred, ChcProblem,
        HintProviders, HintRequest, HintStage, LemmaHint, LemmaHintProvider, PredicateId,
    };

    assert_public_type::<HintStage>();
    assert_public_type::<LemmaHint>();
    assert_public_type::<HintProviders>();

    // Verify canonical var helpers are callable
    let pred_id = PredicateId::new(0);
    let name = canonical_var_name(pred_id, 0);
    assert_eq!(name, "__p0_a0");

    // HintProviders can be constructed and populated
    struct TestProvider;
    impl LemmaHintProvider for TestProvider {
        fn collect(&self, request: &HintRequest<'_>, out: &mut Vec<LemmaHint>) {
            assert!(matches!(
                request.stage,
                HintStage::Startup | HintStage::Stuck
            ));
            // A real provider would construct ChcExpr formulas over canonical vars
            let _ = out;
        }
    }

    let providers = HintProviders(vec![Arc::new(TestProvider)]);
    assert_eq!(providers.0.len(), 1);

    // Verify canonical_var_for_pred_arg and canonical_vars_for_pred work
    // with an empty problem (returns None for unknown predicates)
    let problem = ChcProblem::new();
    let pred_id = PredicateId::new(0);
    assert!(canonical_var_for_pred_arg(&problem, pred_id, 0).is_none());
    assert!(canonical_vars_for_pred(&problem, pred_id).is_none());
}
