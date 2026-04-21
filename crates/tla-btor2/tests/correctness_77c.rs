// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression test for false positive on 77.c.btor2.
//!
//! This benchmark has states i=0, y=450, x=500 (15-bit unsigned).
//! Bad condition: (i < y) AND (i >= x) = (i < 450) AND (i >= 500) — impossible.
//! i only increments by 1 when i < y, so i can reach at most 449, never >= 500.
//! Correct answer: UNSAT (safe).

use std::sync::Arc;
use z4_chc::{ChcExpr, ChcOp, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause};

/// Test z4-chc directly with a hand-crafted CHC problem equivalent to 77.c.btor2.
/// This isolates whether the bug is in translation or in the solver.
#[test]
fn test_77c_direct_chc() {
    let bv15 = ChcSort::BitVec(15);
    let bv1 = ChcSort::BitVec(1);

    // State variables
    let i_var = ChcVar::new("i", bv15.clone());
    let y_var = ChcVar::new("y", bv15.clone());
    let x_var = ChcVar::new("x", bv15.clone());

    let i_prime = i_var.primed();
    let y_prime = y_var.primed();
    let x_prime = x_var.primed();

    // Input variables (free in clauses)
    let rst_var = ChcVar::new("rst", bv1.clone());
    let sel_var = ChcVar::new("sel", bv1.clone());

    // Expressions
    let i = ChcExpr::var(i_var.clone());
    let y = ChcExpr::var(y_var.clone());
    let x = ChcExpr::var(x_var.clone());
    let i_p = ChcExpr::var(i_prime.clone());
    let y_p = ChcExpr::var(y_prime.clone());
    let x_p = ChcExpr::var(x_prime.clone());
    let rst = ChcExpr::var(rst_var.clone());
    let sel = ChcExpr::var(sel_var.clone());

    let bv15_0 = ChcExpr::BitVec(0, 15);
    let bv15_1 = ChcExpr::BitVec(1, 15);
    let bv15_450 = ChcExpr::BitVec(450, 15);
    let bv15_500 = ChcExpr::BitVec(500, 15);
    let bv1_1 = ChcExpr::BitVec(1, 1);

    // Helper: bv_is_true(e) = eq(e, BV(1,1))
    let bv_is_true = |e: ChcExpr| ChcExpr::eq(e, bv1_1.clone());

    // i < y as 1-bit BV
    let i_lt_y = ChcExpr::ite(
        ChcExpr::Op(ChcOp::BvULt, vec![Arc::new(i.clone()), Arc::new(y.clone())]),
        bv1_1.clone(),
        ChcExpr::BitVec(0, 1),
    );

    // i >= x as 1-bit BV
    let i_ge_x = ChcExpr::ite(
        ChcExpr::Op(ChcOp::BvUGe, vec![Arc::new(i.clone()), Arc::new(x.clone())]),
        bv1_1.clone(),
        ChcExpr::BitVec(0, 1),
    );

    // bad = BvAnd(i_lt_y, i_ge_x)
    let bad_bv = ChcExpr::Op(
        ChcOp::BvAnd,
        vec![Arc::new(i_lt_y.clone()), Arc::new(i_ge_x.clone())],
    );

    // Next-state for i: ite(rst, 0, ite(sel, ite(i<y, i+1, i), i))
    let i_plus_1 = ChcExpr::Op(
        ChcOp::BvAdd,
        vec![Arc::new(i.clone()), Arc::new(bv15_1.clone())],
    );
    let inner_ite = ChcExpr::ite(bv_is_true(i_lt_y.clone()), i_plus_1, i.clone());
    let sel_ite = ChcExpr::ite(bv_is_true(sel.clone()), inner_ite, i.clone());
    let i_next = ChcExpr::ite(bv_is_true(rst.clone()), bv15_0.clone(), sel_ite);

    // Next-state for y: ite(rst, 450, y)
    let y_next = ChcExpr::ite(bv_is_true(rst.clone()), bv15_450.clone(), y.clone());

    // Next-state for x: ite(rst, 500, x)
    let x_next = ChcExpr::ite(bv_is_true(rst.clone()), bv15_500.clone(), x.clone());

    // Build CHC problem
    let mut problem = ChcProblem::new();
    let inv_pred = problem.declare_predicate("Inv", vec![bv15.clone(), bv15.clone(), bv15.clone()]);

    let curr_args = vec![i.clone(), y.clone(), x.clone()];
    let next_args = vec![i_p.clone(), y_p.clone(), x_p.clone()];

    // Init clause: (i=0 /\ y=450 /\ x=500) => Inv(i,y,x)
    let init_constraint = ChcExpr::and_all(vec![
        ChcExpr::eq(i.clone(), bv15_0.clone()),
        ChcExpr::eq(y.clone(), bv15_450.clone()),
        ChcExpr::eq(x.clone(), bv15_500.clone()),
    ]);
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(init_constraint),
        ClauseHead::Predicate(inv_pred, curr_args.clone()),
    ));

    // Transition clause: Inv(i,y,x) /\ (i'=next_i /\ y'=next_y /\ x'=next_x) => Inv(i',y',x')
    let trans_constraint = ChcExpr::and_all(vec![
        ChcExpr::eq(i_p.clone(), i_next),
        ChcExpr::eq(y_p.clone(), y_next),
        ChcExpr::eq(x_p.clone(), x_next),
    ]);
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(inv_pred, curr_args.clone())], Some(trans_constraint)),
        ClauseHead::Predicate(inv_pred, next_args),
    ));

    // Bad clause: Inv(i,y,x) /\ bad(i,y,x) => false
    let bad_constraint = bv_is_true(bad_bv);
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(inv_pred, curr_args)], Some(bad_constraint)),
        ClauseHead::False,
    ));

    // Solve
    let config = z4_chc::PortfolioConfig::default();
    let solver = z4_chc::testing::new_portfolio_solver(problem, config);
    let result = solver.solve();

    match &result {
        z4_chc::ChcEngineResult::Safe(_) => {
            // Expected: the system is safe
        }
        z4_chc::ChcEngineResult::Unsafe(cex) => {
            panic!(
                "FALSE POSITIVE: solver returned unsafe (SAT) but the system is safe.\n\
                 Bad = (i < 450) AND (i >= 500) is impossible.\n\
                 Counterexample steps: {}",
                cex.steps.len()
            );
        }
        other => {
            panic!("Unexpected solver result: {:?}", other);
        }
    }
}

/// Test 77.c.btor2 through the full parser + translator pipeline.
#[test]
fn test_77c_full_pipeline() {
    let btor2_src = r#"; BTOR description generated by Yosys
1 sort bitvec 1
2 input 1 clk
3 input 1 rst
4 input 1 selector
5 sort bitvec 15
6 const 5 000000000000000
7 state 5 i
8 init 5 7 6
9 const 5 000000111000010
10 state 5 y
11 init 5 10 9
12 ult 1 7 10
13 const 5 000000111110100
14 state 5 x
15 init 5 14 13
16 ugte 1 7 14
17 and 1 12 16
18 not 1 17
19 const 1 1
20 not 1 18
21 and 1 19 20
22 uext 5 19 14
23 add 5 7 22
24 ite 5 12 23 7
25 ite 5 4 24 7
26 ite 5 3 6 25
27 next 5 7 26
28 ite 5 3 9 10
29 next 5 10 28
30 ite 5 3 13 14
31 next 5 14 30
32 bad 21
"#;

    let program = tla_btor2::parse(btor2_src).expect("parse failed");
    assert_eq!(program.bad_properties.len(), 1);
    assert_eq!(program.num_states, 3);

    let results = tla_btor2::translate::check_btor2(&program).expect("check failed");
    assert_eq!(results.len(), 1);

    match &results[0] {
        tla_btor2::translate::Btor2CheckResult::Unsat => {
            // Expected: safe
        }
        tla_btor2::translate::Btor2CheckResult::Sat { trace } => {
            panic!(
                "FALSE POSITIVE via full pipeline: solver says SAT but system is safe.\n\
                 Trace has {} steps.",
                trace.len()
            );
        }
        tla_btor2::translate::Btor2CheckResult::Unknown { reason } => {
            panic!("Solver returned unknown: {}", reason);
        }
    }
}

/// Simpler test: trivially safe system — state starts at 0, never changes, bad = (state != 0).
#[test]
fn test_trivially_safe_direct_chc() {
    let bv8 = ChcSort::BitVec(8);

    let s_var = ChcVar::new("s", bv8.clone());
    let s_prime = s_var.primed();
    let s = ChcExpr::var(s_var.clone());
    let s_p = ChcExpr::var(s_prime.clone());

    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![bv8.clone()]);

    // Init: s = 0 => Inv(s)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(s.clone(), ChcExpr::BitVec(0, 8))),
        ClauseHead::Predicate(inv, vec![s.clone()]),
    ));

    // Trans: Inv(s) /\ s' = s => Inv(s')
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![s.clone()])],
            Some(ChcExpr::eq(s_p.clone(), s.clone())),
        ),
        ClauseHead::Predicate(inv, vec![s_p]),
    ));

    // Bad: Inv(s) /\ s != 0 => false
    let s_neq_0 = ChcExpr::Op(
        ChcOp::Not,
        vec![Arc::new(ChcExpr::eq(s.clone(), ChcExpr::BitVec(0, 8)))],
    );
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(inv, vec![s])], Some(s_neq_0)),
        ClauseHead::False,
    ));

    let config = z4_chc::PortfolioConfig::default();
    let solver = z4_chc::testing::new_portfolio_solver(problem, config);
    let result = solver.solve();

    match &result {
        z4_chc::ChcEngineResult::Safe(_) => {} // Expected
        other => panic!("Expected Safe, got: {:?}", other),
    }
}
