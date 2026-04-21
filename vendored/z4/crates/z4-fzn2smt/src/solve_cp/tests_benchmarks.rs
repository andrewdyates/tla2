// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Phase 3 benchmark integration tests: classic CP problems solved via z4-cp.
// Benchmarks live in benchmarks/minizinc/*.fzn.

use super::tests::solve_cp_output;

#[test]
fn test_benchmark_nqueens_8() {
    let fzn = include_str!("../../../../benchmarks/minizinc/nqueens_8.fzn");
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("----------"),
        "should solve 8-queens: {output}"
    );
    assert!(
        output.contains("=========="),
        "should be complete: {output}"
    );
}

#[test]
fn test_benchmark_nqueens_12() {
    let fzn = include_str!("../../../../benchmarks/minizinc/nqueens_12.fzn");
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("----------"),
        "should solve 12-queens: {output}"
    );
}

#[test]
fn test_benchmark_nqueens_20() {
    let fzn = include_str!("../../../../benchmarks/minizinc/nqueens_20.fzn");
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("----------"),
        "should solve 20-queens: {output}"
    );
}

#[test]
fn test_benchmark_graph_color_petersen() {
    let fzn = include_str!("../../../../benchmarks/minizinc/graph_color_petersen.fzn");
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("----------"),
        "should 3-color Petersen graph: {output}"
    );
}

#[test]
fn test_benchmark_sudoku_4x4() {
    let fzn = include_str!("../../../../benchmarks/minizinc/sudoku_easy.fzn");
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("----------"),
        "should solve Sudoku: {output}"
    );
    // Verify given cells preserved
    assert!(
        output.contains("x11 = 1;"),
        "given: x11=1, output: {output}"
    );
    assert!(
        output.contains("x23 = 1;"),
        "given: x23=1, output: {output}"
    );
    assert!(
        output.contains("x32 = 3;"),
        "given: x32=3, output: {output}"
    );
    assert!(
        output.contains("x44 = 2;"),
        "given: x44=2, output: {output}"
    );
}

#[test]
fn test_benchmark_magic_square_3() {
    let fzn = include_str!("../../../../benchmarks/minizinc/magic_square_3.fzn");
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("----------"),
        "should solve 3x3 magic square: {output}"
    );
}

#[test]
fn test_benchmark_latin_square_5() {
    let fzn = include_str!("../../../../benchmarks/minizinc/latin_square_5.fzn");
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("----------"),
        "should solve 5x5 Latin square: {output}"
    );
}

#[test]
fn test_benchmark_send_more_money() {
    let fzn = include_str!("../../../../benchmarks/minizinc/send_more_money.fzn");
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("----------"),
        "should solve SEND+MORE=MONEY: {output}"
    );
    // The unique solution: s=9, e=5, n=6, d=7, m=1, o=0, r=8, y=2
    assert!(output.contains("s = 9;"), "s should be 9: {output}");
    assert!(output.contains("e = 5;"), "e should be 5: {output}");
    assert!(output.contains("m = 1;"), "m should be 1: {output}");
    assert!(output.contains("y = 2;"), "y should be 2: {output}");
}

#[test]
fn test_benchmark_knapsack_10() {
    let fzn = include_str!("../../../../benchmarks/minizinc/knapsack_10.fzn");
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("=========="),
        "should find optimal knapsack: {output}"
    );
    assert!(
        output.contains("profit = "),
        "should report profit: {output}"
    );
}

#[test]
fn test_benchmark_circuit_tsp_5() {
    let fzn = include_str!("../../../../benchmarks/minizinc/circuit_tsp_5.fzn");
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("=========="),
        "should find optimal TSP tour: {output}"
    );
    // Optimal is 85
    assert!(
        output.contains("total_dist = 85;"),
        "optimal TSP should be 85: {output}"
    );
}

#[test]
fn test_benchmark_cumulative_3tasks() {
    let fzn = include_str!("../../../../benchmarks/minizinc/cumulative_3tasks.fzn");
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("=========="),
        "should find optimal schedule: {output}"
    );
}

#[test]
fn test_benchmark_table_assignment() {
    let fzn = include_str!("../../../../benchmarks/minizinc/table_assignment.fzn");
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("=========="),
        "should find optimal assignment: {output}"
    );
}

#[test]
fn test_benchmark_golomb_ruler_7() {
    let fzn = include_str!("../../../../benchmarks/minizinc/golomb_ruler_7.fzn");
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("=========="),
        "should find optimal Golomb ruler: {output}"
    );
    // Known optimal 7-mark Golomb ruler has length 25
    assert!(
        output.contains("m7 = 25;"),
        "optimal ruler length should be 25: {output}"
    );
}
