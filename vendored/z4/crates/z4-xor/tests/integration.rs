// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::panic)]

//! Integration tests for z4-xor with the SAT solver.
//!
//! These tests verify that XorExtension integrates correctly with z4-sat's
//! solve_with_extension() API.

use ntest::timeout;
use std::path::PathBuf;
use z4_sat::{parse_dimacs, Literal, SatResult, Solver, Variable};
use z4_xor::{XorConstraint, XorExtension, XorFinder};

/// Helper to create a literal.
fn lit(var: u32, positive: bool) -> Literal {
    if positive {
        Literal::positive(Variable::new(var))
    } else {
        Literal::negative(Variable::new(var))
    }
}

fn benchmark_path(relative: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(relative)
}

#[test]
#[timeout(10000)]
fn test_xor_extension_simple_sat() {
    // x0 XOR x1 = 1
    // This is satisfiable (e.g., x0=1, x1=0 or x0=0, x1=1)
    let mut solver = Solver::new(2);
    let constraints = vec![XorConstraint::new(vec![0, 1], true)];
    let mut ext = XorExtension::new(constraints);

    let result = solver.solve_with_extension(&mut ext).into_inner();

    match result {
        SatResult::Sat(model) => {
            // Verify the XOR is satisfied
            let v0 = model[0];
            let v1 = model[1];
            assert!(
                v0 != v1,
                "XOR constraint violated: x0={v0}, x1={v1}, but need x0 XOR x1 = 1"
            );
        }
        _ => panic!("Expected SAT, got {result:?}"),
    }
}

#[test]
#[timeout(10000)]
fn test_xor_extension_simple_unsat() {
    // x0 XOR x1 = 1 AND x0 XOR x1 = 0
    // This is unsatisfiable (contradiction)
    let mut solver = Solver::new(2);
    let constraints = vec![
        XorConstraint::new(vec![0, 1], true),
        XorConstraint::new(vec![0, 1], false),
    ];
    let mut ext = XorExtension::new(constraints);

    let result = solver.solve_with_extension(&mut ext).into_inner();

    // Fixed: empty clause DB + contradictory XOR extension correctly returns
    // Unsat (was Unknown due to #5806, fixed in #5823).
    assert!(
        matches!(result, SatResult::Unsat),
        "Expected UNSAT, got {result:?}"
    );
}

#[test]
#[timeout(10000)]
fn test_xor_extension_with_cnf_constraints() {
    // Mix XOR and CNF constraints
    // XOR: x0 XOR x1 = 1
    // CNF: x2 must be true
    let mut solver = Solver::new(3);

    // Add CNF constraint: x2 = true
    solver.add_clause(vec![lit(2, true)]);

    let constraints = vec![XorConstraint::new(vec![0, 1], true)];
    let mut ext = XorExtension::new(constraints);

    let result = solver.solve_with_extension(&mut ext).into_inner();

    match result {
        SatResult::Sat(model) => {
            let v0 = model[0];
            let v1 = model[1];
            let v2 = model[2];

            assert!(v0 != v1, "XOR constraint violated");
            assert!(v2, "CNF constraint violated: x2 should be true");
        }
        _ => panic!("Expected SAT, got {result:?}"),
    }
}

#[test]
#[timeout(10000)]
fn test_xor_extension_chain() {
    // Chain of XORs:
    // x0 XOR x1 = 1
    // x1 XOR x2 = 0
    // x2 XOR x3 = 1
    //
    // Solution must satisfy: x0 != x1, x1 == x2, x2 != x3
    // Example: x0=1, x1=0, x2=0, x3=1
    let mut solver = Solver::new(4);
    let constraints = vec![
        XorConstraint::new(vec![0, 1], true),
        XorConstraint::new(vec![1, 2], false),
        XorConstraint::new(vec![2, 3], true),
    ];
    let mut ext = XorExtension::new(constraints);

    let result = solver.solve_with_extension(&mut ext).into_inner();

    match result {
        SatResult::Sat(model) => {
            let v0 = model[0];
            let v1 = model[1];
            let v2 = model[2];
            let v3 = model[3];

            assert!(v0 != v1, "x0 XOR x1 = 1 violated");
            assert!(v1 == v2, "x1 XOR x2 = 0 violated");
            assert!(v2 != v3, "x2 XOR x3 = 1 violated");
        }
        _ => panic!("Expected SAT, got {result:?}"),
    }
}

#[test]
#[timeout(10000)]
fn test_xor_extension_unsat_chain() {
    // Unsatisfiable chain:
    // x0 XOR x1 = 1
    // x1 XOR x2 = 1
    // x0 XOR x2 = 1
    //
    // Adding all: (x0 XOR x1) XOR (x1 XOR x2) XOR (x0 XOR x2) = 1 XOR 1 XOR 1 = 1
    // But LHS = 0 (parity of x0, x0, x1, x1, x2, x2 = 0)
    // So 0 = 1, contradiction
    let mut solver = Solver::new(3);
    let constraints = vec![
        XorConstraint::new(vec![0, 1], true),
        XorConstraint::new(vec![1, 2], true),
        XorConstraint::new(vec![0, 2], true),
    ];
    let mut ext = XorExtension::new(constraints);

    let result = solver.solve_with_extension(&mut ext).into_inner();

    // Fixed: empty clause DB + contradictory XOR extension correctly returns
    // Unsat (was Unknown due to #5806, fixed in #5823).
    assert!(
        matches!(result, SatResult::Unsat),
        "Expected UNSAT for contradictory XOR chain, got {result:?}"
    );
}

#[test]
#[timeout(10000)]
fn test_xor_finder_and_extension_combined() {
    // Use XorFinder to detect XORs from CNF, then solve with XorExtension

    // CNF encoding of x0 XOR x1 = 1:
    // (-x0 OR -x1) forbids (1,1)
    // (x0 OR x1) forbids (0,0)
    let cnf_clauses = vec![
        vec![lit(0, false), lit(1, false)],
        vec![lit(0, true), lit(1, true)],
    ];

    // Detect XORs
    let mut finder = XorFinder::new();
    let xors = finder.find_xors(&cnf_clauses);
    assert_eq!(xors.len(), 1, "Should detect one XOR");

    // Create solver without the CNF clauses (XorExtension handles them)
    let mut solver = Solver::new(2);
    let mut ext = XorExtension::new(xors);

    let result = solver.solve_with_extension(&mut ext).into_inner();

    match result {
        SatResult::Sat(model) => {
            let v0 = model[0];
            let v1 = model[1];
            assert!(v0 != v1, "XOR constraint violated");
        }
        _ => panic!("Expected SAT, got {result:?}"),
    }
}

#[test]
#[timeout(10000)]
fn test_xor_extension_with_forced_values() {
    // x0 XOR x1 = 1
    // Force x0 = true via CNF
    // Should propagate x1 = false
    let mut solver = Solver::new(2);
    solver.add_clause(vec![lit(0, true)]); // Force x0 = true

    let constraints = vec![XorConstraint::new(vec![0, 1], true)];
    let mut ext = XorExtension::new(constraints);

    let result = solver.solve_with_extension(&mut ext).into_inner();

    match result {
        SatResult::Sat(model) => {
            let v0 = model[0];
            let v1 = model[1];

            assert!(v0, "x0 should be true (forced by CNF)");
            assert!(!v1, "x1 should be false (propagated by XOR)");
        }
        _ => panic!("Expected SAT, got {result:?}"),
    }
}

#[test]
#[timeout(10000)]
fn test_xor_extension_conflict_from_cnf() {
    // x0 XOR x1 = 1
    // Force x0 = true AND x1 = true via CNF
    // This conflicts with the XOR
    let mut solver = Solver::new(2);
    solver.add_clause(vec![lit(0, true)]); // Force x0 = true
    solver.add_clause(vec![lit(1, true)]); // Force x1 = true

    let constraints = vec![XorConstraint::new(vec![0, 1], true)];
    let mut ext = XorExtension::new(constraints);

    let result = solver.solve_with_extension(&mut ext).into_inner();

    assert!(
        matches!(result, SatResult::Unsat),
        "Expected UNSAT: x0=1, x1=1 violates x0 XOR x1 = 1"
    );
}

#[test]
#[timeout(10000)]
fn test_xor_extension_larger_xor() {
    // 4-variable XOR: x0 XOR x1 XOR x2 XOR x3 = 0
    // Satisfiable with even parity
    let mut solver = Solver::new(4);
    let constraints = vec![XorConstraint::new(vec![0, 1, 2, 3], false)];
    let mut ext = XorExtension::new(constraints);

    let result = solver.solve_with_extension(&mut ext).into_inner();

    match result {
        SatResult::Sat(model) => {
            let parity: u32 = model.iter().map(|&v| u32::from(v)).sum();
            assert!(
                parity.is_multiple_of(2),
                "XOR=0 violated: parity should be even, got {parity}"
            );
        }
        _ => panic!("Expected SAT, got {result:?}"),
    }
}

#[test]
#[timeout(10000)]
fn test_xor_extension_empty_constraints() {
    // No XOR constraints - should behave like normal SAT
    let mut solver = Solver::new(2);
    solver.add_clause(vec![lit(0, true), lit(1, true)]); // x0 OR x1

    let constraints = vec![];
    let mut ext = XorExtension::new(constraints);

    let result = solver.solve_with_extension(&mut ext).into_inner();

    assert!(
        matches!(result, SatResult::Sat(_)),
        "Expected SAT with empty XOR constraints"
    );
}

#[test]
#[timeout(10000)]
fn test_xor_extension_unit_initial_propagation() {
    // Single-variable XOR: x0 = 1
    // This should immediately propagate x0 = true
    let mut solver = Solver::new(2);
    solver.add_clause(vec![lit(1, true)]); // x1 must be true

    // x0 = 1 means x0 must be true
    let constraints = vec![XorConstraint::new(vec![0], true)];
    let mut ext = XorExtension::new(constraints);

    let result = solver.solve_with_extension(&mut ext).into_inner();

    match result {
        SatResult::Sat(model) => {
            assert!(model[0], "x0 should be true (unit XOR propagation)");
            assert!(model[1], "x1 should be true (CNF constraint)");
        }
        _ => panic!("Expected SAT, got {result:?}"),
    }
}

/// Generate CNF encoding of XOR: a XOR b = rhs
/// Uses standard 2-clause encoding for 2-var XOR
fn encode_xor_2var(a: u32, b: u32, rhs: bool) -> Vec<Vec<Literal>> {
    if rhs {
        // a XOR b = 1: forbid (0,0) and (1,1)
        vec![
            vec![lit(a, true), lit(b, true)],   // a OR b (forbids 0,0)
            vec![lit(a, false), lit(b, false)], // NOT a OR NOT b (forbids 1,1)
        ]
    } else {
        // a XOR b = 0: forbid (0,1) and (1,0)
        vec![
            vec![lit(a, true), lit(b, false)], // a OR NOT b (forbids 0,1)
            vec![lit(a, false), lit(b, true)], // NOT a OR b (forbids 1,0)
        ]
    }
}

/// Generate CNF encoding of XOR: a XOR b XOR c = rhs
/// Uses the standard 4-clause parity encoding for 3-variable XOR.
fn encode_xor_3var(a: u32, b: u32, c: u32, rhs: bool) -> Vec<Vec<Literal>> {
    let forbidden_assignments = if rhs {
        vec![
            [false, false, false],
            [true, true, false],
            [true, false, true],
            [false, true, true],
        ]
    } else {
        vec![
            [true, false, false],
            [false, true, false],
            [false, false, true],
            [true, true, true],
        ]
    };

    forbidden_assignments
        .into_iter()
        .map(|assignment| {
            [(a, assignment[0]), (b, assignment[1]), (c, assignment[2])]
                .into_iter()
                .map(|(var, value)| {
                    if value {
                        lit(var, false)
                    } else {
                        lit(var, true)
                    }
                })
                .collect()
        })
        .collect()
}

#[test]
#[timeout(10000)]
fn test_xor_finder_detects_five_constraints() {
    let mut clauses = Vec::new();
    clauses.extend(encode_xor_2var(0, 1, true));
    clauses.extend(encode_xor_2var(2, 3, false));
    clauses.extend(encode_xor_2var(4, 5, true));
    clauses.extend(encode_xor_3var(6, 7, 8, true));
    clauses.extend(encode_xor_3var(9, 10, 11, false));

    let mut finder = XorFinder::new();
    let (mut xors, used_indices) = finder.find_xors_with_indices(&clauses);

    xors.sort_by(|lhs, rhs| lhs.vars.cmp(&rhs.vars).then(lhs.rhs.cmp(&rhs.rhs)));

    assert_eq!(
        xors,
        vec![
            XorConstraint::new(vec![0, 1], true),
            XorConstraint::new(vec![2, 3], false),
            XorConstraint::new(vec![4, 5], true),
            XorConstraint::new(vec![6, 7, 8], true),
            XorConstraint::new(vec![9, 10, 11], false),
        ]
    );
    assert_eq!(used_indices.len(), 14, "all XOR clauses should be consumed");
}

#[test]
#[timeout(10000)]
fn test_xor_finder_classifies_mixed_xor_and_non_xor_clauses() {
    let mut clauses = Vec::new();
    clauses.extend(encode_xor_2var(0, 1, true));
    clauses.push(vec![lit(6, true)]);
    clauses.extend(encode_xor_3var(2, 3, 4, false));
    clauses.push(vec![lit(1, true), lit(5, false)]);
    clauses.push(vec![lit(0, false), lit(2, false), lit(6, true)]);

    let mut finder = XorFinder::new();
    let (mut xors, used_indices) = finder.find_xors_with_indices(&clauses);

    xors.sort_by(|lhs, rhs| lhs.vars.cmp(&rhs.vars).then(lhs.rhs.cmp(&rhs.rhs)));

    assert_eq!(
        xors,
        vec![
            XorConstraint::new(vec![0, 1], true),
            XorConstraint::new(vec![2, 3, 4], false),
        ]
    );

    assert_eq!(used_indices.len(), 6);
    assert!(used_indices.contains(&0));
    assert!(used_indices.contains(&1));
    assert!(used_indices.contains(&3));
    assert!(used_indices.contains(&4));
    assert!(used_indices.contains(&5));
    assert!(used_indices.contains(&6));
    assert!(!used_indices.contains(&2));
    assert!(!used_indices.contains(&7));
    assert!(!used_indices.contains(&8));
}

/// Test XOR preprocessing on crypto-style linear system
#[test]
#[timeout(10000)]
fn test_xor_preprocessing_crypto_style() {
    use z4_xor::{preprocess_clauses, solve_with_xor_detection_stats};

    // Create a crypto-style linear system:
    // Chain of XORs that forms a linear system over GF(2)
    // x0 XOR x1 = 1
    // x1 XOR x2 = 0
    // x2 XOR x3 = 1
    // ... etc
    // This is the kind of structure found in hash functions

    let num_vars = 20;
    let mut clauses = Vec::new();

    // Add XOR chain
    for i in 0..(num_vars - 1) {
        let rhs = i % 2 == 0; // alternating 1, 0, 1, 0, ...
        clauses.extend(encode_xor_2var(i as u32, (i + 1) as u32, rhs));
    }

    // Verify preprocessing detects all XORs
    let (remaining, xor_ext) = preprocess_clauses(&clauses);

    assert!(
        remaining.is_empty(),
        "All clauses should be consumed as XOR encoding"
    );
    let ext = xor_ext.expect("Should detect XOR constraints");
    assert_eq!(
        ext.num_constraints(),
        num_vars - 1,
        "Should detect {} XOR constraints",
        num_vars - 1
    );

    // Solve with XOR detection
    let xor_result = solve_with_xor_detection_stats(num_vars, &clauses);

    match xor_result.result.result() {
        SatResult::Sat(model) => {
            // Verify the XOR chain is satisfied
            for i in 0..(num_vars - 1) {
                let expected_xor = i % 2 == 0;
                let actual_xor = model[i] ^ model[i + 1];
                assert_eq!(
                    actual_xor,
                    expected_xor,
                    "XOR chain violated at position {}: x{}={}, x{}={}, expected XOR={}",
                    i,
                    i,
                    model[i],
                    i + 1,
                    model[i + 1],
                    expected_xor
                );
            }
        }
        _ => panic!("Expected SAT, got {:?}", xor_result.result),
    }

    // Verify stats
    assert_eq!(xor_result.stats.xors_detected, num_vars - 1);
    assert_eq!(xor_result.stats.clauses_consumed, (num_vars - 1) * 2);
}

/// Test larger XOR system (more stressful)
#[test]
#[timeout(10000)]
fn test_xor_preprocessing_larger_system() {
    use z4_xor::solve_with_xor_detection_stats;

    // 100 variables, 99 XOR constraints
    let num_vars = 100;
    let mut clauses = Vec::new();

    // Create XOR chain
    for i in 0..(num_vars - 1) {
        let rhs = i % 2 == 0;
        clauses.extend(encode_xor_2var(i as u32, (i + 1) as u32, rhs));
    }

    let xor_result = solve_with_xor_detection_stats(num_vars, &clauses);

    match xor_result.result.result() {
        SatResult::Sat(model) => {
            // Spot check a few constraints
            assert!(model[0] ^ model[1], "x0 XOR x1 should be 1");
            assert!(!(model[1] ^ model[2]), "x1 XOR x2 should be 0");
            assert!(model[98] ^ model[99], "x98 XOR x99 should be 1");
        }
        _ => panic!("Expected SAT, got {:?}", xor_result.result),
    }

    assert_eq!(xor_result.stats.xors_detected, 99);
}

#[test]
#[timeout(10000)]
fn test_two_trees_511v_preprocessing_shape_recovers_partial_xors() {
    use z4_xor::preprocess_clauses_with_stats;

    let content = std::fs::read_to_string(benchmark_path(
        "benchmarks/sat/satcomp2024-sample/16c5482d8e658b54e20d59cfd4b1d588-two-trees-511v.sanitized.cnf",
    ))
    .expect("failed to read two-trees benchmark");
    let formula = parse_dimacs(&content).expect("failed to parse two-trees benchmark");

    let (remaining, xor_ext, stats) = preprocess_clauses_with_stats(&formula.clauses);

    assert!(xor_ext.is_some(), "expected XOR preprocessing on two-trees");
    assert_eq!(stats.xors_detected, 509);
    assert_eq!(stats.clauses_consumed, 1960);
    assert_eq!(remaining.len(), 79);
}

/// Test XOR with additional CNF constraints
#[test]
#[timeout(10000)]
fn test_xor_preprocessing_with_cnf() {
    use z4_xor::solve_with_xor_detection_stats;

    let num_vars = 10;
    let mut clauses = Vec::new();

    // XOR constraints
    clauses.extend(encode_xor_2var(0, 1, true)); // x0 XOR x1 = 1
    clauses.extend(encode_xor_2var(2, 3, false)); // x2 XOR x3 = 0

    // Regular CNF constraints (not XOR patterns)
    clauses.push(vec![lit(0, true)]); // x0 must be true
    clauses.push(vec![lit(4, true), lit(5, false)]); // x4 OR NOT x5

    let xor_result = solve_with_xor_detection_stats(num_vars, &clauses);

    match xor_result.result.result() {
        SatResult::Sat(model) => {
            // x0 = true (from CNF)
            assert!(model[0], "x0 should be true");
            // x0 XOR x1 = 1, so x1 = false
            assert!(
                !model[1],
                "x1 should be false (since x0=true and x0 XOR x1 = 1)"
            );
            // x2 XOR x3 = 0
            assert_eq!(model[2], model[3], "x2 and x3 should be equal");
        }
        _ => panic!("Expected SAT, got {:?}", xor_result.result),
    }

    // Should detect 2 XORs (consuming 4 clauses)
    assert_eq!(xor_result.stats.xors_detected, 2);
    assert_eq!(xor_result.stats.clauses_consumed, 4);
}

/// Acceptance test for #7874: two-trees-511v must solve within the timeout budget.
///
/// This benchmark is a 511-variable, 2039-clause SAT instance dominated by XOR
/// constraints. With partial XOR recovery (binary clause support), the XOR finder
/// detects 509 constraints consuming 1960 clauses, leaving only 79 CNF clauses.
/// Gauss-Jordan elimination then solves the XOR system by pure propagation.
///
/// Prior to partial XOR recovery, the finder detected only 433 constraints (1732
/// consumed, 307 remaining), which left too many clauses for efficient XOR-driven
/// solving and the benchmark timed out at 20s.
#[test]
#[timeout(10000)]
fn test_two_trees_511v_solves_sat_7874() {
    use z4_xor::solve_with_xor_detection_stats;

    let content = std::fs::read_to_string(benchmark_path(
        "benchmarks/sat/satcomp2024-sample/16c5482d8e658b54e20d59cfd4b1d588-two-trees-511v.sanitized.cnf",
    ))
    .expect("failed to read two-trees benchmark");
    let formula = parse_dimacs(&content).expect("failed to parse two-trees benchmark");

    let xor_result = solve_with_xor_detection_stats(formula.num_vars, &formula.clauses);

    // Must solve to SAT
    let model = match xor_result.result.into_inner() {
        SatResult::Sat(model) => model,
        other => panic!(
            "two-trees-511v must be SAT, got {other:?} (XOR stats: {} detected, {} consumed)",
            xor_result.stats.xors_detected, xor_result.stats.clauses_consumed,
        ),
    };

    // Verify the model satisfies all original clauses
    for (clause_idx, clause) in formula.clauses.iter().enumerate() {
        let satisfied = clause.iter().any(|lit| {
            let var_idx = lit.variable().id() as usize;
            let val = model[var_idx];
            if lit.is_positive() {
                val
            } else {
                !val
            }
        });
        assert!(
            satisfied,
            "Model violates original clause {clause_idx}: {clause:?}"
        );
    }
}

/// Test UNSAT detection through XOR preprocessing
#[test]
#[timeout(10000)]
fn test_xor_preprocessing_unsat() {
    use z4_xor::solve_with_xor_detection;

    // Create contradictory XOR system:
    // x0 XOR x1 = 1
    // x1 XOR x2 = 1
    // x0 XOR x2 = 1
    // Chain implies x0 XOR x2 = 0, but we say = 1 -> contradiction
    let mut clauses = Vec::new();
    clauses.extend(encode_xor_2var(0, 1, true)); // x0 XOR x1 = 1
    clauses.extend(encode_xor_2var(1, 2, true)); // x1 XOR x2 = 1
    clauses.extend(encode_xor_2var(0, 2, true)); // x0 XOR x2 = 1 (contradicts chain)

    let result = solve_with_xor_detection(3, &clauses);

    // Fixed: empty clause DB + contradictory XOR extension correctly returns
    // Unsat (was Unknown due to #5806, fixed in #5823).
    assert!(
        result.is_unsat(),
        "Contradictory XOR system should be UNSAT, got {result:?}"
    );
}
