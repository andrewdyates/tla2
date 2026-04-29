// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Direct z4 incremental-solving coverage

// This test demonstrates z4 ALL-SAT directly at the solver level.
// Previously blocked by z4#294/z4#309: fixed in z4 commit 8ea188b6
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_z4_incremental_directly() {
    use std::collections::BTreeSet;
    use tla_z4::{Logic, SolveResult, Solver, Sort};

    let mut solver = Solver::new(Logic::QfLia);

    // Declare x and y
    let x = solver.declare_const("x", Sort::Int);
    let y = solver.declare_const("y", Sort::Int);

    let one = solver.int_const(1);
    let two = solver.int_const(2);
    let three = solver.int_const(3);

    // x in 1..3
    let x_ge_1 = solver.ge(x, one);
    let x_le_3 = solver.le(x, three);
    solver.assert_term(x_ge_1);
    solver.assert_term(x_le_3);

    // y in 1..2
    let y_ge_1 = solver.ge(y, one);
    let y_le_2 = solver.le(y, two);
    solver.assert_term(y_ge_1);
    solver.assert_term(y_le_2);

    let mut solutions = BTreeSet::new();

    for i in 0..10 {
        match solver.check_sat().result() {
            SolveResult::Sat => {
                let model = solver.get_model().unwrap().into_inner();
                let x_val: i64 = model
                    .int_val("x")
                    .expect("missing x")
                    .try_into()
                    .expect("x should fit in i64");
                let y_val: i64 = model
                    .int_val("y")
                    .expect("missing y")
                    .try_into()
                    .expect("y should fit in i64");
                eprintln!("Solution {}: x={}, y={}", i, x_val, y_val);
                assert!((1..=3).contains(&x_val), "x out of range: {x_val}");
                assert!((1..=2).contains(&y_val), "y out of range: {y_val}");
                assert!(
                    solutions.insert((x_val, y_val)),
                    "duplicate model: ({x_val}, {y_val})"
                );

                // Add blocking clause: (x != x_val) OR (y != y_val)
                let x_val_term = solver.int_const(x_val);
                let y_val_term = solver.int_const(y_val);
                let x_neq = solver.neq(x, x_val_term);
                let y_neq = solver.neq(y, y_val_term);
                let blocking = solver.or(x_neq, y_neq);
                solver.assert_term(blocking);
            }
            SolveResult::Unsat(_) => {
                eprintln!("UNSAT after {} solutions", i);
                break;
            }
            SolveResult::Unknown => {
                eprintln!("Unknown");
                break;
            }
            _ => {
                eprintln!("Unexpected solve result");
                break;
            }
        }
    }

    let expected: BTreeSet<(i64, i64)> = [(1, 1), (1, 2), (2, 1), (2, 2), (3, 1), (3, 2)]
        .into_iter()
        .collect();
    eprintln!(
        "Total solutions: {}, expected: {}",
        solutions.len(),
        expected.len()
    );
    assert_eq!(solutions, expected);
}

// Test z4 ALL-SAT directly with arithmetic constraints (x + y = 5).
//
// Regression test for z4#949: incremental solving + blocking clauses must not
// return UNSAT after the first model when arithmetic equalities are present.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_z4_incremental_arithmetic_directly() {
    use std::collections::BTreeSet;
    use tla_z4::{Logic, SolveResult, Solver, Sort};

    let mut solver = Solver::new(Logic::QfLia);

    // Declare x and y
    let x = solver.declare_const("x", Sort::Int);
    let y = solver.declare_const("y", Sort::Int);

    let one = solver.int_const(1);
    let five = solver.int_const(5);
    let ten = solver.int_const(10);

    // x in 1..10
    let x_ge_1 = solver.ge(x, one);
    let x_le_10 = solver.le(x, ten);
    solver.assert_term(x_ge_1);
    solver.assert_term(x_le_10);

    // y in 1..10
    let y_ge_1 = solver.ge(y, one);
    let y_le_10 = solver.le(y, ten);
    solver.assert_term(y_ge_1);
    solver.assert_term(y_le_10);

    // x + y = 5
    let sum = solver.add(x, y);
    let sum_eq_5 = solver.eq(sum, five);
    solver.assert_term(sum_eq_5);

    let mut solutions = BTreeSet::new();

    for i in 0..10 {
        match solver.check_sat().result() {
            SolveResult::Sat => {
                let model = solver.get_model().unwrap().into_inner();
                let x_val: i64 = model
                    .int_val("x")
                    .expect("missing x")
                    .try_into()
                    .expect("x should fit in i64");
                let y_val: i64 = model
                    .int_val("y")
                    .expect("missing y")
                    .try_into()
                    .expect("y should fit in i64");
                eprintln!("Solution {}: x={}, y={}", i, x_val, y_val);
                assert!((1..=10).contains(&x_val), "x out of range: {x_val}");
                assert!((1..=10).contains(&y_val), "y out of range: {y_val}");
                assert_eq!(
                    x_val + y_val,
                    5,
                    "model violates x + y = 5: ({x_val}, {y_val})"
                );
                assert!(
                    solutions.insert((x_val, y_val)),
                    "duplicate model: ({x_val}, {y_val})"
                );

                // Add blocking clause: (x != x_val) OR (y != y_val)
                let x_val_term = solver.int_const(x_val);
                let y_val_term = solver.int_const(y_val);
                let x_neq = solver.neq(x, x_val_term);
                let y_neq = solver.neq(y, y_val_term);
                let blocking = solver.or(x_neq, y_neq);
                solver.assert_term(blocking);
            }
            SolveResult::Unsat(_) => {
                eprintln!("UNSAT after {} solutions", i);
                break;
            }
            SolveResult::Unknown => {
                eprintln!("Unknown");
                break;
            }
            _ => {
                eprintln!("Unexpected solve result");
                break;
            }
        }
    }

    let expected: BTreeSet<(i64, i64)> = [(1, 4), (2, 3), (3, 2), (4, 1)].into_iter().collect();
    eprintln!(
        "Total solutions: {}, expected: {}",
        solutions.len(),
        expected.len()
    );
    assert_eq!(solutions, expected);
}
