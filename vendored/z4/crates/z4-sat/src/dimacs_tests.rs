// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_parse_simple() {
    let input = r"
c A simple CNF
p cnf 3 2
1 -2 3 0
-1 2 0
";
    let formula = parse_str(input).unwrap();
    assert_eq!(formula.num_vars, 3);
    assert_eq!(formula.num_clauses, 2);
    assert_eq!(formula.clauses.len(), 2);

    // First clause: x1 OR NOT x2 OR x3
    assert_eq!(formula.clauses[0].len(), 3);
    assert_eq!(formula.clauses[0][0], Literal::positive(Variable(0)));
    assert_eq!(formula.clauses[0][1], Literal::negative(Variable(1)));
    assert_eq!(formula.clauses[0][2], Literal::positive(Variable(2)));

    // Second clause: NOT x1 OR x2
    assert_eq!(formula.clauses[1].len(), 2);
    assert_eq!(formula.clauses[1][0], Literal::negative(Variable(0)));
    assert_eq!(formula.clauses[1][1], Literal::positive(Variable(1)));
}

#[test]
fn test_into_solver_dimacs_policy_defaults() {
    let formula = DimacsFormula {
        num_vars: 3,
        num_clauses: 1,
        clauses: vec![vec![
            Literal::positive(Variable(0)),
            Literal::negative(Variable(1)),
        ]],
    };

    let solver = formula.into_solver();
    assert!(
        solver.is_bve_enabled(),
        "DIMACS solver should enable BVE for SAT-only workloads"
    );
    assert!(
        solver.is_congruence_enabled(),
        "DIMACS solver should enable congruence closure for SAT-only workloads"
    );
    assert!(
        solver.is_subsume_enabled(),
        "DIMACS solver should enable subsumption (#4872 one-watch forward)"
    );
    assert!(
        solver.is_factor_enabled(),
        "DIMACS solver should keep factorization enabled for structured SAT workloads"
    );
    assert!(
        !solver.stable_only_enabled(),
        "DIMACS solver should use CaDiCaL-style focused/stable alternation"
    );
    // Small formulas (< 5K vars) get full BVE/subsumption effort.
    // Only large formulas (> DIMACS_PROOF_REDUCED_EFFORT_MIN_VARS = 5K)
    // get the reduced effort budgets (BVE=10, subsume=60).
    assert_eq!(
        solver.bve_effort_permille(),
        1000,
        "Small DIMACS formulas (<5K vars) should keep full BVE effort"
    );
    assert_eq!(
        solver.subsume_effort_permille(),
        1000,
        "Small DIMACS formulas (<5K vars) should keep full subsumption effort"
    );
    assert!(
        solver.is_full_preprocessing_enabled(),
        "small DIMACS formulas should keep full preprocessing enabled"
    );
}

#[test]
fn test_into_solver_large_dimacs_keeps_quick_preprocessing() {
    let formula = DimacsFormula {
        num_vars: 10_000,
        num_clauses: 5_000_001,
        clauses: vec![],
    };

    let solver = formula.into_solver();
    assert!(
        !solver.stable_only_enabled(),
        "DIMACS solver should use CaDiCaL-style focused/stable alternation on large formulas"
    );
    assert!(
        !solver.is_full_preprocessing_enabled(),
        "very large DIMACS formulas should stay on quick preprocessing"
    );
}

#[test]
fn test_parse_multiline_clause() {
    let input = r"
p cnf 5 1
1 2 3
4 5 0
";
    let formula = parse_str(input).unwrap();
    assert_eq!(formula.clauses.len(), 1);
    assert_eq!(formula.clauses[0].len(), 5);
}

#[test]
fn test_parse_empty_clause() {
    let input = r"
p cnf 3 3
1 2 0
0
-1 0
";
    let formula = parse_str(input).unwrap();
    // Empty clauses (just "0") ARE preserved — they signal UNSAT
    assert_eq!(formula.clauses.len(), 3);
    assert_eq!(formula.clauses[0].len(), 2); // {1, 2}
    assert!(formula.clauses[1].is_empty()); // empty clause
    assert_eq!(formula.clauses[2].len(), 1); // {-1}
}

#[test]
fn test_parse_trivially_unsat_empty_clause() {
    // p cnf 0 1 with one empty clause must yield UNSAT
    let input = "p cnf 0 1\n0\n";
    let formula = parse_str(input).unwrap();
    assert_eq!(formula.clauses.len(), 1);
    assert!(formula.clauses[0].is_empty());
    // Verify the solver returns UNSAT
    let mut solver = formula.into_solver();
    assert!(solver.solve().is_unsat());
}

#[test]
fn test_missing_problem_line() {
    let input = "1 2 0";
    let result = parse_str(input);
    assert!(matches!(result, Err(DimacsError::MissingProblemLine)));
}

#[test]
fn test_variable_out_of_range() {
    let input = r"
p cnf 3 1
1 2 4 0
";
    let result = parse_str(input);
    assert!(matches!(
        result,
        Err(DimacsError::VariableOutOfRange { var: 4, max: 3, .. })
    ));
}

#[test]
fn test_roundtrip() {
    let input = r"
p cnf 3 2
1 -2 3 0
-1 2 0
";
    let formula = parse_str(input).unwrap();

    let mut output = Vec::new();
    write_dimacs(&mut output, formula.num_vars, &formula.clauses).unwrap();

    let reparsed = parse(&output[..]).unwrap();
    assert_eq!(reparsed.num_vars, formula.num_vars);
    assert_eq!(reparsed.clauses.len(), formula.clauses.len());
}

#[test]
fn test_into_solver() {
    let input = r"
p cnf 3 2
1 -2 0
-1 2 0
";
    let formula = parse_str(input).unwrap();
    let solver = formula.into_solver();
    // Just verify it doesn't panic
    assert_eq!(solver.value(Variable(0)), None);
}

#[test]
fn test_percent_terminator() {
    // Some DIMACS files use '%' as end-of-file marker
    // This format is common in SAT competition benchmarks
    let input = r"
p cnf 3 2
1 -2 0
-1 2 0
%
0
";
    let formula = parse_str(input).unwrap();
    assert_eq!(formula.num_vars, 3);
    assert_eq!(formula.clauses.len(), 2);
}

#[test]
fn test_percent_terminates_parsing() {
    // '%' is an end-of-file marker; content after it is not parsed
    let input = r"
p cnf 3 2
1 -2 0
% end of file
-1 2 0
";
    let formula = parse_str(input).unwrap();
    // Only 1 clause before the '%' marker
    assert_eq!(formula.clauses.len(), 1);
}
