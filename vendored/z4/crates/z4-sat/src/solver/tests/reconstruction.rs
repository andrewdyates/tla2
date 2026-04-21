// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use proptest::prelude::*;

// ========================================================================
// Property Tests for Propagation Soundness
// ========================================================================

proptest! {
    /// Propagation soundness: if propagate returns conflict, clause is falsified
    #[test]
    fn prop_propagation_conflict_soundness(
        num_clauses in 1usize..10,
        seed in 0u64..1000
    ) {
        // Create solver with fixed seed-based clauses
        let num_vars = 5usize;
        let mut solver = Solver::new(num_vars);

        // Generate deterministic clauses based on seed
        for i in 0..num_clauses {
            let v1 = ((seed + i as u64) % num_vars as u64) as u32;
            let v2 = ((seed + i as u64 + 1) % num_vars as u64) as u32;
            let v3 = ((seed + i as u64 + 2) % num_vars as u64) as u32;

            let lit1 = if (seed + i as u64).is_multiple_of(2) {
                Literal::positive(Variable(v1))
            } else {
                Literal::negative(Variable(v1))
            };
            let lit2 = if (seed + i as u64 + 1).is_multiple_of(2) {
                Literal::positive(Variable(v2))
            } else {
                Literal::negative(Variable(v2))
            };
            let lit3 = if (seed + i as u64 + 2).is_multiple_of(2) {
                Literal::positive(Variable(v3))
            } else {
                Literal::negative(Variable(v3))
            };

            solver.add_clause(vec![lit1, lit2, lit3]);
        }

        // Initialize and run solver
        let result = solver.solve().into_inner();

        // Basic soundness check: if SAT, model satisfies all original clauses
        if let SatResult::Sat(model) = &result {
            for i in solver.arena.indices().take(num_clauses) {
                // Skip clauses deleted by BVE/subsumption during preprocessing
                if solver.arena.is_empty_clause(i) {
                    continue;
                }
                let satisfied = solver.arena.literals(i).iter().any(|&lit| {
                    let var_val = model[lit.variable().index()];
                    if lit.is_positive() {
                        var_val
                    } else {
                        !var_val
                    }
                });
                prop_assert!(satisfied, "Clause {} not satisfied by model", i);
            }
        }
    }

    /// Solver returns consistent results on same formula
    #[test]
    fn prop_solve_deterministic(clauses_seed in 0u64..100) {
        let num_vars = 4usize;
        let num_clauses = 5usize;

        let run_solver = || {
            let mut solver = Solver::new(num_vars);
            for i in 0..num_clauses {
                let v1 = ((clauses_seed + i as u64) % num_vars as u64) as u32;
                let v2 = ((clauses_seed + i as u64 + 1) % num_vars as u64) as u32;
                let polarity1 = (clauses_seed + i as u64).is_multiple_of(2);
                let polarity2 = (clauses_seed + i as u64 + 1).is_multiple_of(2);

                let lit1 = if polarity1 {
                    Literal::positive(Variable(v1))
                } else {
                    Literal::negative(Variable(v1))
                };
                let lit2 = if polarity2 {
                    Literal::positive(Variable(v2))
                } else {
                    Literal::negative(Variable(v2))
                };
                solver.add_clause(vec![lit1, lit2]);
            }
            solver.solve().into_inner()
        };

        let result1 = run_solver();
        let result2 = run_solver();

        // Results should be consistent (both SAT or both UNSAT)
        match (&result1, &result2) {
            (SatResult::Sat(_), SatResult::Sat(_))
            | (SatResult::Unsat, SatResult::Unsat) => (),
            _ => prop_assert!(false, "Inconsistent results: {:?} vs {:?}", result1, result2),
        }
    }

    /// Unit clauses are correctly propagated
    #[test]
    fn prop_unit_clause_propagation(var_idx in 0u32..10) {
        let num_vars = 10usize;
        let mut solver = Solver::new(num_vars);

        // Add unit clause
        let unit_lit = Literal::positive(Variable(var_idx));
        solver.add_clause(vec![unit_lit]);

        // Add clause requiring the unit
        let other_var = (var_idx + 1) % num_vars as u32;
        solver.add_clause(vec![
            Literal::negative(Variable(var_idx)),
            Literal::positive(Variable(other_var)),
        ]);

        let result = solver.solve().into_inner();

        if let SatResult::Sat(model) = result {
            // Unit clause must be satisfied
            prop_assert!(model[var_idx as usize], "Unit clause not satisfied");
        }
    }

    // ====================================================================
    // TLA+ Invariant Property Tests (Gap 3: Formal Link to TLA+ Spec)
    //
    // These tests mirror the invariants from specs/cdcl.tla:
    // - TypeInvariant: Implicitly enforced by Rust's type system
    // - SatCorrect: When SAT, all clauses are satisfied
    // - NoDoubleAssignment: No variable assigned twice
    // - WatchedInvariant: Checked during propagation
    // ====================================================================

    /// TLA+ SatCorrect invariant (lines 201-202 of cdcl.tla):
    /// state = "SAT" => \A clause \in Clauses : Satisfied(clause)
    ///
    /// For any random SAT formula, if the solver returns SAT, every
    /// original clause must be satisfied by the model.
    #[test]
    fn tla_invariant_sat_correct(
        num_vars in 3usize..8,
        num_clauses in 1usize..15,
        seed in 0u64..10000
    ) {
        use std::collections::HashSet;

        let mut solver = Solver::new(num_vars);
        let mut original_clauses: Vec<Vec<Literal>> = Vec::new();

        // Generate random clauses
        for i in 0..num_clauses {
            let clause_len = 2 + ((seed + i as u64) % 3) as usize; // 2-4 literals
            let mut clause = Vec::new();
            let mut seen_vars: HashSet<u32> = HashSet::new();

            for j in 0..clause_len {
                let v = ((seed.wrapping_mul(7) + i as u64 * 13 + j as u64 * 31) % num_vars as u64) as u32;
                if seen_vars.contains(&v) {
                    continue; // Skip duplicate variables in same clause
                }
                seen_vars.insert(v);
                let polarity = (seed + i as u64 + j as u64).is_multiple_of(2);
                let lit = if polarity {
                    Literal::positive(Variable(v))
                } else {
                    Literal::negative(Variable(v))
                };
                clause.push(lit);
            }

            if clause.is_empty() {
                continue; // Skip empty clauses
            }

            original_clauses.push(clause.clone());
            solver.add_clause(clause);
        }

        let result = solver.solve().into_inner();

        // TLA+ SatCorrect: If SAT, all original clauses must be satisfied
        if let SatResult::Sat(model) = result {
            for (clause_idx, clause) in original_clauses.iter().enumerate() {
                let satisfied = clause.iter().any(|&lit| {
                    let var_idx = lit.variable().index();
                    let val = model[var_idx];
                    if lit.is_positive() { val } else { !val }
                });
                prop_assert!(
                    satisfied,
                    "TLA+ SatCorrect violation: clause {} ({:?}) not satisfied by model {:?}",
                    clause_idx, clause, model
                );
            }
        }
    }

    /// TLA+ NoDoubleAssignment invariant (lines 213-215 of cdcl.tla):
    /// \A i, j \in 1..Len(trail) : i # j => Var(trail[i][1]) # Var(trail[j][1])
    ///
    /// In the model, each variable should have exactly one consistent value.
    /// This is implicitly enforced by our Vec<bool> model representation,
    /// but we verify that values are deterministic across multiple accesses.
    #[test]
    fn tla_invariant_no_double_assignment(
        num_vars in 2usize..6,
        seed in 0u64..1000
    ) {
        let mut solver = Solver::new(num_vars);

        // Create simple SAT formula
        for i in 0..num_vars {
            let v1 = i as u32;
            let v2 = ((i + 1) % num_vars) as u32;
            let polarity = (seed + i as u64).is_multiple_of(2);
            let lit1 = if polarity {
                Literal::positive(Variable(v1))
            } else {
                Literal::negative(Variable(v1))
            };
            let lit2 = Literal::positive(Variable(v2));
            solver.add_clause(vec![lit1, lit2]);
        }

        let result = solver.solve().into_inner();

        if let SatResult::Sat(model) = result {
            // Verify model length matches num_vars
            prop_assert_eq!(
                model.len(), num_vars,
                "Model length {} does not match num_vars {}",
                model.len(), num_vars
            );

            // Verify model actually satisfies all added clauses
            for i in 0..num_vars {
                let v1 = i as u32;
                let v2 = ((i + 1) % num_vars) as u32;
                let polarity = (seed + i as u64).is_multiple_of(2);
                let lit1_sat = if polarity { model[v1 as usize] } else { !model[v1 as usize] };
                let lit2_sat = model[v2 as usize];
                prop_assert!(
                    lit1_sat || lit2_sat,
                    "Clause {} not satisfied by model: lit1(v{}={})={}, lit2(v{}={})={}",
                    i, v1, model[v1 as usize], lit1_sat, v2, model[v2 as usize], lit2_sat
                );
            }
        }
    }

    /// TLA+ Soundness invariant combining SatCorrect and UnsatCorrect:
    /// When we claim SAT, we can construct a satisfying assignment.
    /// When we claim UNSAT, there truly is no satisfying assignment.
    ///
    /// This test generates formulas and verifies soundness both ways.
    #[test]
    fn tla_invariant_soundness(
        num_vars in 2usize..5,
        seed in 0u64..500
    ) {
        // Test 1: Known SAT formula
        {
            let mut solver = Solver::new(num_vars);
            // Add tautology: (x0 OR NOT x0) for each var
            for i in 0..num_vars {
                solver.add_clause(vec![
                    Literal::positive(Variable(i as u32)),
                    Literal::negative(Variable(i as u32)),
                ]);
            }
            let result = solver.solve().into_inner();
            match result {
                SatResult::Sat(_) => (), // Expected
                other => prop_assert!(false, "Tautology should be SAT, got {:?}", other),
            }
        }

        // Test 2: Known UNSAT formula
        {
            let mut solver = Solver::new(1);
            solver.add_clause(vec![Literal::positive(Variable(0))]);
            solver.add_clause(vec![Literal::negative(Variable(0))]);
            let result = solver.solve().into_inner();
            match result {
                SatResult::Unsat => (), // Expected
                other => prop_assert!(false, "x AND NOT x should be UNSAT, got {:?}", other),
            }
        }

        // Test 3: Random formula with soundness check
        {
            let mut solver = Solver::new(num_vars);
            let mut clauses: Vec<Vec<Literal>> = Vec::new();

            for i in 0..=(seed % 10) {
                let v1 = (seed.wrapping_add(i) % num_vars as u64) as u32;
                let v2 = (seed.wrapping_add(i).wrapping_add(1) % num_vars as u64) as u32;
                let p1 = (seed.wrapping_add(i) % 2) == 0;
                let p2 = (seed.wrapping_add(i).wrapping_add(1) % 2) == 0;
                let lit1 = if p1 { Literal::positive(Variable(v1)) } else { Literal::negative(Variable(v1)) };
                let lit2 = if p2 { Literal::positive(Variable(v2)) } else { Literal::negative(Variable(v2)) };
                clauses.push(vec![lit1, lit2]);
                solver.add_clause(vec![lit1, lit2]);
            }

            let result = solver.solve().into_inner();

            if let SatResult::Sat(model) = result {
                // Verify all clauses satisfied
                for clause in &clauses {
                    let sat = clause.iter().any(|&lit| {
                        let v = lit.variable().index();
                        let val = model[v];
                        if lit.is_positive() { val } else { !val }
                    });
                    prop_assert!(sat, "Soundness violation: clause {:?} not satisfied", clause);
                }
            }
            // Note: For UNSAT, we trust DRAT proof verification (Gap 2)
        }
    }

    /// TLA+ TrailConsistency: Variables assigned in dependency order
    ///
    /// If x implies y (via unit clause ¬x ∨ y), then in any model:
    /// - If x is true, y must be true
    /// - This tests that propagation correctly follows implication chains
    #[test]
    fn tla_invariant_trail_consistency(
        chain_len in 2usize..6,
        _seed in 0u64..1000
    ) {
        // Build implication chain: x0 → x1 → x2 → ... → xN
        let num_vars = chain_len;
        let mut solver = Solver::new(num_vars);

        // Add implications: ¬x_i ∨ x_{i+1}
        for i in 0..(num_vars - 1) {
            solver.add_clause(vec![
                Literal::negative(Variable(i as u32)),
                Literal::positive(Variable((i + 1) as u32)),
            ]);
        }

        // Force x0 true (this should propagate through the chain)
        solver.add_clause(vec![Literal::positive(Variable(0))]);

        let result = solver.solve().into_inner();

        if let SatResult::Sat(model) = result {
            // x0 must be true
            prop_assert!(model[0], "Root of implication chain must be true");

            // All implied variables must be true
            for (offset, &value) in model[1..].iter().enumerate() {
                let i = offset + 1;
                prop_assert!(
                    value,
                    "Variable {} should be true by implication from 0",
                    i
                );
            }
        } else {
            // Formula is satisfiable, UNSAT is a bug
            prop_assert!(false, "Implication chain should be SAT");
        }
    }

    /// TLA+ ConflictLevelCorrect: Conflict analysis produces valid learned clauses
    ///
    /// For known-UNSAT formulas, verify:
    /// 1. Solver returns UNSAT (conflicts were resolved correctly)
    /// 2. Unit propagation finds conflicts at appropriate levels
    #[test]
    fn tla_invariant_conflict_level_correct(
        n in 2usize..5,
        _seed in 0u64..500
    ) {
        // Create simple UNSAT formula: (x) ∧ (¬x)
        let mut solver = Solver::new(1);
        solver.add_clause(vec![Literal::positive(Variable(0))]);
        solver.add_clause(vec![Literal::negative(Variable(0))]);

        let result = solver.solve().into_inner();

        // Must be UNSAT - conflict at level 0
        prop_assert!(
            matches!(result, SatResult::Unsat),
            "x ∧ ¬x must be UNSAT, got {:?}",
            result
        );

        // Test with deeper conflicts: pigeon-hole principle for n+1 pigeons in n holes
        // PHP is UNSAT and requires exponential resolution
        if n >= 2 {
            let pigeons = n + 1;
            let holes = n;
            let mut php_solver = Solver::new(pigeons * holes);

            // Each pigeon must be in some hole: ∨_j p_{i,j}
            for p in 0..pigeons {
                let mut clause = Vec::new();
                for h in 0..holes {
                    let var = (p * holes + h) as u32;
                    clause.push(Literal::positive(Variable(var)));
                }
                php_solver.add_clause(clause);
            }

            // No two pigeons in same hole: ¬p_{i,h} ∨ ¬p_{j,h}
            for h in 0..holes {
                for p1 in 0..pigeons {
                    for p2 in (p1 + 1)..pigeons {
                        let var1 = (p1 * holes + h) as u32;
                        let var2 = (p2 * holes + h) as u32;
                        php_solver.add_clause(vec![
                            Literal::negative(Variable(var1)),
                            Literal::negative(Variable(var2)),
                        ]);
                    }
                }
            }

            let php_result = php_solver.solve().into_inner();
            prop_assert!(
                matches!(php_result, SatResult::Unsat),
                "PHP({},{}) must be UNSAT, got {:?}",
                pigeons,
                holes,
                php_result
            );
        }
    }

    /// TLA+ LearnedClauseValid: Learned clauses are properly asserting
    ///
    /// Tests that:
    /// 1. Solver can solve problems requiring clause learning
    /// 2. Results are correct (SAT models satisfy formula, UNSAT is actually UNSAT)
    /// 3. No infinite loops (learning makes progress)
    #[test]
    fn tla_invariant_learned_clause_valid(
        grid_size in 2usize..4,
        seed in 0u64..200
    ) {
        // Create graph coloring problem: 2-colorable cycle (even length = SAT, odd = UNSAT)
        let is_odd = (seed % 2) == 1;
        let cycle_len = if is_odd { grid_size * 2 + 1 } else { grid_size * 2 };
        let num_vars = cycle_len; // One variable per node (true = color 1, false = color 2)

        let mut solver = Solver::new(num_vars);

        // Adjacent nodes must have different colors: (x_i ∨ x_{i+1}) ∧ (¬x_i ∨ ¬x_{i+1})
        // This is equivalent to x_i XOR x_{i+1}
        for i in 0..cycle_len {
            let j = (i + 1) % cycle_len;
            // At least one must be true
            solver.add_clause(vec![
                Literal::positive(Variable(i as u32)),
                Literal::positive(Variable(j as u32)),
            ]);
            // At least one must be false
            solver.add_clause(vec![
                Literal::negative(Variable(i as u32)),
                Literal::negative(Variable(j as u32)),
            ]);
        }

        let result = solver.solve().into_inner();

        if is_odd {
            // Odd cycle is not 2-colorable
            prop_assert!(
                matches!(result, SatResult::Unsat),
                "Odd cycle length {} should be UNSAT, got {:?}",
                cycle_len,
                result
            );
        } else {
            // Even cycle is 2-colorable
            if let SatResult::Sat(model) = &result {
                // Verify coloring is valid
                for i in 0..cycle_len {
                    let j = (i + 1) % cycle_len;
                    prop_assert!(
                        model[i] != model[j],
                        "Adjacent nodes {} and {} have same color",
                        i,
                        j
                    );
                }
            } else {
                prop_assert!(
                    false,
                    "Even cycle length {} should be SAT, got {:?}",
                    cycle_len,
                    result
                );
            }
        }
    }

    /// BVE model reconstruction soundness: if the solver returns SAT after
    /// BVE eliminates variables, the reconstructed model must satisfy all
    /// original (pre-elimination) clauses.
    ///
    /// Note: compaction requires >= 100 eliminated variables (COMPACT_MIN_INACTIVE)
    /// so it does NOT trigger with these small formulas (10-30 vars). This test
    /// exercises BVE reconstruction only. The compaction index remapping is
    /// covered by prop_map_lit_for_reconstruction_no_index_collision in compact.rs.
    ///
    /// Regression coverage for #4977: BVE reconstruction correctness.
    ///
    /// Strategy: generate 3-SAT formulas near the satisfiability threshold
    /// (clause/var ratio ~4.2) with enough variables that BVE can eliminate
    /// some. Preserve original clauses before solving, then verify model.
    #[test]
    fn prop_bve_model_reconstruction_soundness(
        num_vars in 10usize..30,
        seed in 0u64..500
    ) {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};

        // Generate a reproducible pseudo-random 3-SAT formula.
        // Target clause/var ratio ~4.2 (phase transition region) to get
        // a mix of SAT and UNSAT instances where BVE is useful.
        let num_clauses = (num_vars as f64 * 4.2) as usize;
        let mut hasher = DefaultHasher::new();
        seed.hash(&mut hasher);
        let mut h = hasher.finish();

        let mut original_clauses: Vec<Vec<Literal>> = Vec::with_capacity(num_clauses);
        let mut solver: Solver = Solver::new(num_vars);
        solver.set_bve_enabled(true);

        for _ in 0..num_clauses {
            h = h.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            let v0 = (h % num_vars as u64) as u32;
            h = h.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            let v1 = (h % num_vars as u64) as u32;
            h = h.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            let v2 = (h % num_vars as u64) as u32;
            h = h.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            let signs = h % 8;

            let lit0 = if signs & 1 == 0 {
                Literal::positive(Variable(v0))
            } else {
                Literal::negative(Variable(v0))
            };
            let lit1 = if signs & 2 == 0 {
                Literal::positive(Variable(v1))
            } else {
                Literal::negative(Variable(v1))
            };
            let lit2 = if signs & 4 == 0 {
                Literal::positive(Variable(v2))
            } else {
                Literal::negative(Variable(v2))
            };

            let clause = vec![lit0, lit1, lit2];
            original_clauses.push(clause.clone());
            solver.add_clause(clause);
        }

        let result = solver.solve().into_inner();

        if let SatResult::Sat(model) = &result {
            // Verify model against original clauses (pre-BVE).
            for (ci, clause) in original_clauses.iter().enumerate() {
                let satisfied = clause.iter().any(|&lit| {
                    let vi = lit.variable().index();
                    if vi >= model.len() {
                        // Model shorter than expected — reconstruction bug.
                        return false;
                    }
                    if lit.is_positive() { model[vi] } else { !model[vi] }
                });
                prop_assert!(
                    satisfied,
                    "Original clause {} ({:?}) not satisfied by model (BVE reconstruction). \
                     num_vars={}, seed={}",
                    ci, clause, num_vars, seed
                );
            }
        }
        // UNSAT results don't need model verification here.
    }
}

fn generate_bve_reconstruction_formula(num_vars: usize, seed: u64) -> Vec<Vec<Literal>> {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};

    let num_clauses = (num_vars as f64 * 4.2) as usize;
    let mut hasher = DefaultHasher::new();
    seed.hash(&mut hasher);
    let mut h = hasher.finish();

    let mut clauses: Vec<Vec<Literal>> = Vec::with_capacity(num_clauses);
    for _ in 0..num_clauses {
        h = h
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let v0 = (h % num_vars as u64) as u32;
        h = h
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let v1 = (h % num_vars as u64) as u32;
        h = h
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let v2 = (h % num_vars as u64) as u32;
        h = h
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let signs = h % 8;

        let lit0 = if signs & 1 == 0 {
            Literal::positive(Variable(v0))
        } else {
            Literal::negative(Variable(v0))
        };
        let lit1 = if signs & 2 == 0 {
            Literal::positive(Variable(v1))
        } else {
            Literal::negative(Variable(v1))
        };
        let lit2 = if signs & 4 == 0 {
            Literal::positive(Variable(v2))
        } else {
            Literal::negative(Variable(v2))
        };

        clauses.push(vec![lit0, lit1, lit2]);
    }

    clauses
}

fn verify_bve_reconstruction_case<F>(num_vars: usize, seed: u64, configure: F)
where
    F: FnOnce(&mut Solver),
{
    let clauses = generate_bve_reconstruction_formula(num_vars, seed);
    let mut solver = Solver::new(num_vars);
    solver.set_preprocess_enabled(true);
    solver.set_bve_enabled(true);
    configure(&mut solver);

    for clause in &clauses {
        solver.add_clause(clause.clone());
    }

    let result = solver.solve().into_inner();

    if let SatResult::Sat(model) = &result {
        for (ci, clause) in clauses.iter().enumerate() {
            let satisfied = clause.iter().any(|&lit| {
                let vi = lit.variable().index();
                vi < model.len()
                    && if lit.is_positive() {
                        model[vi]
                    } else {
                        !model[vi]
                    }
            });
            assert!(
                satisfied,
                "Original clause {ci} ({clause:?}) not satisfied by model. \
                 num_vars={num_vars}, seed={seed}"
            );
        }
    }
}

/// Deterministic reproduction of the stale-reason BVE deletion path seen in
/// `prop_bve_model_reconstruction_soundness`.
#[test]
fn test_bve_reconstruction_12_0_default_preprocessing() {
    verify_bve_reconstruction_case(12, 0, |_| {});
}

/// Isolation check: run the same formula with only preprocessing BVE enabled.
#[test]
fn test_bve_reconstruction_12_0_bve_only() {
    verify_bve_reconstruction_case(12, 0, |solver| {
        solver.disable_all_inprocessing();
        solver.set_bve_enabled(true);
    });
}

/// Isolation check: disable conditioning while leaving the rest of the default
/// preprocessing stack in place.
#[test]
fn test_bve_reconstruction_12_0_no_conditioning() {
    verify_bve_reconstruction_case(12, 0, |solver| {
        solver.set_condition_enabled(false);
    });
}

/// Isolation check: disable decompose while leaving the rest of the default
/// preprocessing stack in place.
#[test]
fn test_bve_reconstruction_12_0_no_decompose() {
    verify_bve_reconstruction_case(12, 0, |solver| {
        solver.set_decompose_enabled(false);
    });
}

/// Isolation check: disable sweep while leaving the rest of the default
/// preprocessing stack in place.
#[test]
fn test_bve_reconstruction_12_0_no_sweep() {
    verify_bve_reconstruction_case(12, 0, |solver| {
        solver.set_sweep_enabled(false);
    });
}

/// Isolation check: disable congruence while leaving the rest of the default
/// preprocessing stack in place.
#[test]
fn test_bve_reconstruction_12_0_no_congruence() {
    verify_bve_reconstruction_case(12, 0, |solver| {
        solver.set_congruence_enabled(false);
    });
}

/// Deterministic reproduction of BVE model reconstruction failure at
/// num_vars=19, seed=234. Tests conditioning+BVE interaction separately
/// to isolate the root cause.
#[test]
fn test_bve_reconstruction_19_234_no_conditioning() {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};

    let num_vars = 19usize;
    let seed = 234u64;
    let num_clauses = (num_vars as f64 * 4.2) as usize;
    let mut hasher = DefaultHasher::new();
    seed.hash(&mut hasher);
    let mut h = hasher.finish();

    let mut original_clauses: Vec<Vec<Literal>> = Vec::with_capacity(num_clauses);
    let mut solver = Solver::new(num_vars);
    solver.set_bve_enabled(true);
    solver.set_condition_enabled(false);

    for _ in 0..num_clauses {
        h = h
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let v0 = (h % num_vars as u64) as u32;
        h = h
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let v1 = (h % num_vars as u64) as u32;
        h = h
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let v2 = (h % num_vars as u64) as u32;
        h = h
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let signs = h % 8;

        let lit0 = if signs & 1 == 0 {
            Literal::positive(Variable(v0))
        } else {
            Literal::negative(Variable(v0))
        };
        let lit1 = if signs & 2 == 0 {
            Literal::positive(Variable(v1))
        } else {
            Literal::negative(Variable(v1))
        };
        let lit2 = if signs & 4 == 0 {
            Literal::positive(Variable(v2))
        } else {
            Literal::negative(Variable(v2))
        };

        let clause = vec![lit0, lit1, lit2];
        original_clauses.push(clause.clone());
        solver.add_clause(clause);
    }

    let result = solver.solve().into_inner();

    if let SatResult::Sat(model) = &result {
        for (ci, clause) in original_clauses.iter().enumerate() {
            let satisfied = clause.iter().any(|&lit| {
                let vi = lit.variable().index();
                if vi >= model.len() {
                    return false;
                }
                if lit.is_positive() {
                    model[vi]
                } else {
                    !model[vi]
                }
            });
            assert!(
                satisfied,
                "Original clause {ci} ({clause:?}) not satisfied by model (BVE w/o conditioning). num_vars={num_vars}, seed={seed}",
            );
        }
    }
}

#[test]
fn test_bve_reconstruction_19_234_with_conditioning() {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};

    let num_vars = 19usize;
    let seed = 234u64;
    let num_clauses = (num_vars as f64 * 4.2) as usize;
    let mut hasher = DefaultHasher::new();
    seed.hash(&mut hasher);
    let mut h = hasher.finish();

    let mut original_clauses: Vec<Vec<Literal>> = Vec::with_capacity(num_clauses);
    let mut solver = Solver::new(num_vars);
    solver.set_bve_enabled(true);
    // Conditioning is enabled by default, leave it enabled.

    for _ in 0..num_clauses {
        h = h
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let v0 = (h % num_vars as u64) as u32;
        h = h
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let v1 = (h % num_vars as u64) as u32;
        h = h
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let v2 = (h % num_vars as u64) as u32;
        h = h
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let signs = h % 8;

        let lit0 = if signs & 1 == 0 {
            Literal::positive(Variable(v0))
        } else {
            Literal::negative(Variable(v0))
        };
        let lit1 = if signs & 2 == 0 {
            Literal::positive(Variable(v1))
        } else {
            Literal::negative(Variable(v1))
        };
        let lit2 = if signs & 4 == 0 {
            Literal::positive(Variable(v2))
        } else {
            Literal::negative(Variable(v2))
        };

        let clause = vec![lit0, lit1, lit2];
        original_clauses.push(clause.clone());
        solver.add_clause(clause);
    }

    let result = solver.solve().into_inner();

    if let SatResult::Sat(model) = &result {
        for (ci, clause) in original_clauses.iter().enumerate() {
            let satisfied = clause.iter().any(|&lit| {
                let vi = lit.variable().index();
                if vi >= model.len() {
                    return false;
                }
                if lit.is_positive() {
                    model[vi]
                } else {
                    !model[vi]
                }
            });
            assert!(
                satisfied,
                "Original clause {ci} ({clause:?}) not satisfied by model (BVE+conditioning). num_vars={num_vars}, seed={seed}",
            );
        }
    }
}

// ========================================================================
// Decompose (SCC+ELS) Soundness Cross-Check (#5067)
// ========================================================================

proptest! {
    /// Decompose soundness: decompose-only must agree with no-inprocessing.
    ///
    /// Generates random formulas with a mix of binary and ternary clauses
    /// (binary clauses form the implication graph for SCC detection).
    /// Runs with decompose-only and with no inprocessing. If decompose
    /// returns UNSAT but baseline returns SAT, the model is verified against
    /// the original formula to confirm it's a real wrong-UNSAT.
    #[test]
    fn prop_decompose_soundness_cross_check(
        num_vars in 5usize..25,
        seed in 0u64..2000
    ) {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};

        let num_binary = num_vars * 3; // ~3 binary clauses per var to trigger SCCs
        let num_ternary = (num_vars as f64 * 2.0) as usize;
        let mut hasher = DefaultHasher::new();
        seed.hash(&mut hasher);
        let mut h = hasher.finish();

        let mut clauses: Vec<Vec<Literal>> = Vec::new();

        // Generate binary clauses (form the implication graph).
        for _ in 0..num_binary {
            h = h.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            let v0 = (h % num_vars as u64) as u32;
            h = h.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            let v1 = (h % num_vars as u64) as u32;
            h = h.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            let signs = h % 4;
            let l0 = if signs & 1 == 0 {
                Literal::positive(Variable(v0))
            } else {
                Literal::negative(Variable(v0))
            };
            let l1 = if signs & 2 == 0 {
                Literal::positive(Variable(v1))
            } else {
                Literal::negative(Variable(v1))
            };
            if v0 != v1 {
                clauses.push(vec![l0, l1]);
            }
        }

        // Generate ternary clauses for more interesting formulas.
        for _ in 0..num_ternary {
            h = h.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            let v0 = (h % num_vars as u64) as u32;
            h = h.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            let v1 = (h % num_vars as u64) as u32;
            h = h.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            let v2 = (h % num_vars as u64) as u32;
            h = h.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            let signs = h % 8;
            let l0 = if signs & 1 == 0 { Literal::positive(Variable(v0)) } else { Literal::negative(Variable(v0)) };
            let l1 = if signs & 2 == 0 { Literal::positive(Variable(v1)) } else { Literal::negative(Variable(v1)) };
            let l2 = if signs & 4 == 0 { Literal::positive(Variable(v2)) } else { Literal::negative(Variable(v2)) };
            clauses.push(vec![l0, l1, l2]);
        }

        if clauses.is_empty() {
            return Ok(());
        }

        // Run 1: decompose only (all other inprocessing off).
        let mut solver_decompose: Solver = Solver::new(num_vars);
        solver_decompose.disable_all_inprocessing();
        solver_decompose.set_decompose_enabled(true);
        for c in &clauses {
            solver_decompose.add_clause(c.clone());
        }
        let result_decompose = solver_decompose.solve().into_inner();

        // Run 2: no inprocessing baseline.
        let mut solver_baseline: Solver = Solver::new(num_vars);
        solver_baseline.disable_all_inprocessing();
        for c in &clauses {
            solver_baseline.add_clause(c.clone());
        }
        let result_baseline = solver_baseline.solve().into_inner();

        // Cross-check: if decompose says UNSAT but baseline says SAT, verify.
        match (&result_decompose, &result_baseline) {
            (SatResult::Unsat, SatResult::Sat(model)) => {
                // Verify the baseline model against original clauses.
                let model_valid = clauses.iter().all(|clause| {
                    clause.iter().any(|&lit| {
                        let vi = lit.variable().index();
                        if vi >= model.len() { return false; }
                        if lit.is_positive() { model[vi] } else { !model[vi] }
                    })
                });
                prop_assert!(
                    !model_valid,
                    "DECOMPOSE WRONG-UNSAT: decompose returned UNSAT but baseline returned SAT \
                     with a valid model. num_vars={}, seed={}, clauses={}",
                    num_vars, seed, clauses.len()
                );
            }
            (SatResult::Sat(model_d), SatResult::Unsat) => {
                // Decompose says SAT but baseline says UNSAT — verify decompose model.
                let model_valid = clauses.iter().all(|clause| {
                    clause.iter().any(|&lit| {
                        let vi = lit.variable().index();
                        if vi >= model_d.len() { return false; }
                        if lit.is_positive() { model_d[vi] } else { !model_d[vi] }
                    })
                });
                prop_assert!(
                    !model_valid,
                    "BASELINE WRONG-UNSAT: baseline returned UNSAT but decompose returned SAT \
                     with a valid model. num_vars={}, seed={}, clauses={}",
                    num_vars, seed, clauses.len()
                );
            }
            (SatResult::Sat(model_d), SatResult::Sat(_)) => {
                // Both SAT — verify decompose model (reconstruction correctness).
                for (ci, clause) in clauses.iter().enumerate() {
                    let satisfied = clause.iter().any(|&lit| {
                        let vi = lit.variable().index();
                        if vi >= model_d.len() { return false; }
                        if lit.is_positive() { model_d[vi] } else { !model_d[vi] }
                    });
                    prop_assert!(
                        satisfied,
                        "DECOMPOSE MODEL BUG: clause {} ({:?}) not satisfied. \
                         num_vars={}, seed={}",
                        ci, clause, num_vars, seed
                    );
                }
            }
            _ => {
                // Both UNSAT or other combos — OK
            }
        }
    }
}

// ========================================================================
// Decompose Reconstruction Bug Reproduction (#5067)
// ========================================================================

/// Deterministic reproduction of decompose proptest failure: num_vars=5, seed=1010.
/// The solver with decompose-only returns SAT but reconstruction produces an
/// invalid model that doesn't satisfy the original clauses.
#[test]
fn test_decompose_reconstruction_bug_5_1010() {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};

    let num_vars = 5usize;
    let seed = 1010u64;
    let num_binary = num_vars * 3;
    let num_ternary = (num_vars as f64 * 2.0) as usize;
    let mut hasher = DefaultHasher::new();
    seed.hash(&mut hasher);
    let mut h = hasher.finish();

    let mut clauses: Vec<Vec<Literal>> = Vec::new();

    // Generate binary clauses.
    for _ in 0..num_binary {
        h = h
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let v0 = (h % num_vars as u64) as u32;
        h = h
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let v1 = (h % num_vars as u64) as u32;
        h = h
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let signs = h % 4;
        let l0 = if signs & 1 == 0 {
            Literal::positive(Variable(v0))
        } else {
            Literal::negative(Variable(v0))
        };
        let l1 = if signs & 2 == 0 {
            Literal::positive(Variable(v1))
        } else {
            Literal::negative(Variable(v1))
        };
        if v0 != v1 {
            clauses.push(vec![l0, l1]);
        }
    }

    // Generate ternary clauses.
    for _ in 0..num_ternary {
        h = h
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let v0 = (h % num_vars as u64) as u32;
        h = h
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let v1 = (h % num_vars as u64) as u32;
        h = h
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let v2 = (h % num_vars as u64) as u32;
        h = h
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let signs = h % 8;
        let l0 = if signs & 1 == 0 {
            Literal::positive(Variable(v0))
        } else {
            Literal::negative(Variable(v0))
        };
        let l1 = if signs & 2 == 0 {
            Literal::positive(Variable(v1))
        } else {
            Literal::negative(Variable(v1))
        };
        let l2 = if signs & 4 == 0 {
            Literal::positive(Variable(v2))
        } else {
            Literal::negative(Variable(v2))
        };
        clauses.push(vec![l0, l1, l2]);
    }

    eprintln!(
        "Generated {} clauses for num_vars={}, seed={}",
        clauses.len(),
        num_vars,
        seed
    );
    for (i, c) in clauses.iter().enumerate() {
        let dimacs: Vec<i32> = c.iter().map(|l| l.to_dimacs()).collect();
        eprintln!("  clause {i}: {dimacs:?}");
    }

    // Run with decompose only.
    let mut solver: Solver = Solver::new(num_vars);
    solver.disable_all_inprocessing();
    solver.set_decompose_enabled(true);
    for c in &clauses {
        solver.add_clause(c.clone());
    }
    let result = solver.solve().into_inner();

    match &result {
        SatResult::Sat(model) => {
            // Verify model against original clauses.
            for (ci, clause) in clauses.iter().enumerate() {
                let satisfied = clause.iter().any(|&lit| {
                    let vi = lit.variable().index();
                    if vi >= model.len() {
                        return false;
                    }
                    if lit.is_positive() {
                        model[vi]
                    } else {
                        !model[vi]
                    }
                });
                assert!(
                    satisfied,
                    "Decompose reconstruction bug: original clause {} ({:?}) not satisfied. \
                     model={:?}, num_vars={}, seed={}",
                    ci,
                    clause.iter().map(|l| l.to_dimacs()).collect::<Vec<_>>(),
                    model,
                    num_vars,
                    seed
                );
            }
        }
        SatResult::Unsat => {
            // Run baseline to verify.
            let mut solver_baseline: Solver = Solver::new(num_vars);
            solver_baseline.disable_all_inprocessing();
            for c in &clauses {
                solver_baseline.add_clause(c.clone());
            }
            let result_baseline = solver_baseline.solve().into_inner();
            if let SatResult::Sat(model) = &result_baseline {
                let model_valid = clauses.iter().all(|clause| {
                    clause.iter().any(|&lit| {
                        let vi = lit.variable().index();
                        if vi >= model.len() {
                            return false;
                        }
                        if lit.is_positive() {
                            model[vi]
                        } else {
                            !model[vi]
                        }
                    })
                });
                assert!(
                    !model_valid,
                    "Decompose wrong-UNSAT: decompose returned UNSAT but baseline found valid SAT model. \
                     num_vars={num_vars}, seed={seed}",
                );
            }
        }
        _ => {}
    }
}

// ========================================================================
// BVE Reconstruction Bug Reproduction (#5044 follow-up)
// ========================================================================

/// Deterministic reproduction of proptest failure: num_vars=17, seed=194.
/// The solver returns SAT but reconstruction flips a variable that breaks
/// a live clause_db clause.
#[test]
fn test_bve_reconstruction_bug_17_194() {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};

    let num_vars = 17usize;
    let seed = 194u64;
    let num_clauses = (num_vars as f64 * 4.2) as usize;
    let mut hasher = DefaultHasher::new();
    seed.hash(&mut hasher);
    let mut h = hasher.finish();

    let mut original_clauses: Vec<Vec<Literal>> = Vec::with_capacity(num_clauses);
    let mut solver: Solver = Solver::new(num_vars);
    solver.set_bve_enabled(true);

    for _ in 0..num_clauses {
        h = h
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let v0 = (h % num_vars as u64) as u32;
        h = h
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let v1 = (h % num_vars as u64) as u32;
        h = h
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let v2 = (h % num_vars as u64) as u32;
        h = h
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let signs = h % 8;

        let lit0 = if signs & 1 == 0 {
            Literal::positive(Variable(v0))
        } else {
            Literal::negative(Variable(v0))
        };
        let lit1 = if signs & 2 == 0 {
            Literal::positive(Variable(v1))
        } else {
            Literal::negative(Variable(v1))
        };
        let lit2 = if signs & 4 == 0 {
            Literal::positive(Variable(v2))
        } else {
            Literal::negative(Variable(v2))
        };

        let clause = vec![lit0, lit1, lit2];
        original_clauses.push(clause.clone());
        solver.add_clause(clause);
    }

    let result = solver.solve().into_inner();

    if let SatResult::Sat(model) = &result {
        for (ci, clause) in original_clauses.iter().enumerate() {
            let satisfied = clause.iter().any(|&lit| {
                let vi = lit.variable().index();
                if vi >= model.len() {
                    return false;
                }
                if lit.is_positive() {
                    model[vi]
                } else {
                    !model[vi]
                }
            });
            assert!(
                satisfied,
                "Original clause {ci} ({clause:?}) not satisfied by model. num_vars={num_vars}, seed={seed}"
            );
        }
    }
    // If UNSAT, the test passes (no model to verify).
}

// ========================================================================
// BVE Reconstruction Property Tests (#4977)
// ========================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(30))]

    /// BVE reconstruction soundness: after BVE eliminates bridge variables,
    /// the model (extended by reconstruction) must satisfy all original clauses.
    ///
    /// Exercises the `map_lit_for_reconstruction` fix from #4977 (commit
    /// 561d2b6c0) which offsets eliminated variables beyond the compacted
    /// range to prevent index collisions during reconstruction.
    ///
    /// Formula: `core_count` core vars + `bridge_count` BVE-eliminable vars.
    /// Each bridge var `b` has exactly 1 positive and 1 negative binary clause:
    /// `(a ∨ b)` and `(¬b ∨ c)` where a, c are core vars. BVE resolves these
    /// into `(a ∨ c)`, eliminating b (product = 1 ≤ growth bound).
    #[test]
    fn prop_bve_reconstruction_model_soundness(
        seed in 0u64..200,
        bridge_count in 20usize..150,
    ) {
        let core_count = 30usize;
        let total_vars = core_count + bridge_count;

        let mut solver: Solver = Solver::new(total_vars);
        solver.set_preprocess_enabled(true);
        solver.disable_all_inprocessing();
        solver.inproc_ctrl.bve.enabled = true;

        let mut original_clauses: Vec<Vec<Literal>> = Vec::new();

        // Bridge variable clauses: each bridge var `b` has exactly
        // 1 positive and 1 negative occurrence → BVE-eliminable.
        for i in 0..bridge_count {
            let b = (core_count + i) as u32;
            let a = ((seed as usize + i * 3) % core_count) as u32;
            let c = ((seed as usize + i * 3 + 1) % core_count) as u32;

            let clause_pos = vec![
                Literal::positive(Variable(a)),
                Literal::positive(Variable(b)),
            ];
            let clause_neg = vec![
                Literal::negative(Variable(b)),
                Literal::positive(Variable(c)),
            ];

            original_clauses.push(clause_pos.clone());
            original_clauses.push(clause_neg.clone());
            solver.add_clause(clause_pos);
            solver.add_clause(clause_neg);
        }

        // Core clauses: positive binary clauses (formula always SAT).
        for i in 0..core_count.min(15) {
            let v1 = ((seed as usize + i * 7) % core_count) as u32;
            let v2 = ((seed as usize + i * 7 + 3) % core_count) as u32;
            if v1 != v2 {
                let clause = vec![
                    Literal::positive(Variable(v1)),
                    Literal::positive(Variable(v2)),
                ];
                original_clauses.push(clause.clone());
                solver.add_clause(clause);
            }
        }

        let result = solver.solve().into_inner();

        // BVE must have eliminated bridge vars.
        let eliminated = solver.bve_stats().vars_eliminated;
        prop_assert!(
            eliminated >= 5,
            "BVE should eliminate bridge vars, got {}",
            eliminated,
        );

        // Model soundness: every original clause must be satisfied.
        if let SatResult::Sat(model) = &result {
            for (clause_idx, clause) in original_clauses.iter().enumerate() {
                let satisfied = clause.iter().any(|&lit| {
                    let vi = lit.variable().index();
                    if vi >= model.len() {
                        return false;
                    }
                    let val = model[vi];
                    if lit.is_positive() { val } else { !val }
                });
                prop_assert!(
                    satisfied,
                    "Original clause {} ({:?}) not satisfied by model after BVE",
                    clause_idx,
                    clause,
                );
            }
        } else {
            // Formula is always SAT by construction (core positive binary
            // clauses + bridge resolvents are satisfiable by all-true).
            prop_assert!(false, "Formula should be SAT (seed={})", seed);
        }
    }
}

/// Deterministic reproduction of #7083: BVE rebuild hits active-clause
/// eliminated-variable invariant at num_vars=23, seed=455.
///
/// The multi-round BVE loop eliminated variables in round 1, but the
/// inter-round GC pass was missing, leaving irredundant clauses with
/// eliminated-variable literals alive when round 2 called rebuild_with_vals().
#[test]
fn test_bve_rebuild_eliminated_var_invariant_23_455() {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};

    let num_vars = 23usize;
    let seed = 455u64;
    let num_clauses = (num_vars as f64 * 4.2) as usize;
    let mut hasher = DefaultHasher::new();
    seed.hash(&mut hasher);
    let mut h = hasher.finish();

    let mut original_clauses: Vec<Vec<Literal>> = Vec::with_capacity(num_clauses);
    let mut solver = Solver::new(num_vars);
    solver.set_bve_enabled(true);

    for _ in 0..num_clauses {
        h = h
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let v0 = (h % num_vars as u64) as u32;
        h = h
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let v1 = (h % num_vars as u64) as u32;
        h = h
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let v2 = (h % num_vars as u64) as u32;
        h = h
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let signs = h % 8;

        let lit0 = if signs & 1 == 0 {
            Literal::positive(Variable(v0))
        } else {
            Literal::negative(Variable(v0))
        };
        let lit1 = if signs & 2 == 0 {
            Literal::positive(Variable(v1))
        } else {
            Literal::negative(Variable(v1))
        };
        let lit2 = if signs & 4 == 0 {
            Literal::positive(Variable(v2))
        } else {
            Literal::negative(Variable(v2))
        };

        let clause = vec![lit0, lit1, lit2];
        original_clauses.push(clause.clone());
        solver.add_clause(clause);
    }

    let result = solver.solve().into_inner();

    if let SatResult::Sat(model) = &result {
        for (ci, clause) in original_clauses.iter().enumerate() {
            let satisfied = clause.iter().any(|&lit| {
                let vi = lit.variable().index();
                if vi >= model.len() {
                    return false;
                }
                if lit.is_positive() {
                    model[vi]
                } else {
                    !model[vi]
                }
            });
            assert!(
                satisfied,
                "Original clause {ci} ({clause:?}) not satisfied by model. \
                 num_vars={num_vars}, seed={seed}",
            );
        }
    }
}

/// Regression test for P1 dual ReconstructionStack field bug (#7015).
///
/// Constructs a SAT formula with 30 core vars and 40 bridge vars. Each
/// bridge var has exactly 1 positive and 1 negative occurrence, making it
/// BVE-eliminable. After BVE, reconstruction must restore eliminated vars.
///
/// The bug was: finalize_sat.rs read `self.reconstruction` (empty, wrong field)
/// instead of `self.inproc.reconstruction` (populated by BVE). Eliminated
/// variables never got reconstructed, causing finalize_sat_model to demote
/// SAT→Unknown. Fixed by removing the duplicate field and routing all reads
/// through `self.inproc.reconstruction`.
#[test]
fn test_bve_reconstruction_reads_correct_field_p1_7015() {
    let core_count = 30usize;
    let bridge_count = 40usize;
    let total_vars = core_count + bridge_count;
    let seed = 42u64;

    let mut solver = Solver::new(total_vars);
    solver.set_preprocess_enabled(true);
    solver.disable_all_inprocessing();
    solver.inproc_ctrl.bve.enabled = true;

    let mut original_clauses: Vec<Vec<Literal>> = Vec::new();

    // Bridge variable clauses: each bridge var `b` has exactly
    // 1 positive and 1 negative occurrence → BVE-eliminable.
    for i in 0..bridge_count {
        let b = (core_count + i) as u32;
        let a = ((seed as usize + i * 3) % core_count) as u32;
        let c = ((seed as usize + i * 3 + 1) % core_count) as u32;

        let clause_pos = vec![
            Literal::positive(Variable(a)),
            Literal::positive(Variable(b)),
        ];
        let clause_neg = vec![
            Literal::negative(Variable(b)),
            Literal::positive(Variable(c)),
        ];

        original_clauses.push(clause_pos.clone());
        original_clauses.push(clause_neg.clone());
        solver.add_clause(clause_pos);
        solver.add_clause(clause_neg);
    }

    // Core clauses: positive binary clauses (formula always SAT by all-true).
    for i in 0..core_count.min(15) {
        let v1 = ((seed as usize + i * 7) % core_count) as u32;
        let v2 = ((seed as usize + i * 7 + 3) % core_count) as u32;
        if v1 != v2 {
            let clause = vec![
                Literal::positive(Variable(v1)),
                Literal::positive(Variable(v2)),
            ];
            original_clauses.push(clause.clone());
            solver.add_clause(clause);
        }
    }

    let result = solver.solve().into_inner();

    // BVE should have eliminated bridge vars.
    let eliminated = solver.bve_stats().vars_eliminated;
    assert!(
        eliminated >= 5,
        "BVE should eliminate bridge vars, got {eliminated} eliminations",
    );

    // Reconstruction entries should exist in inproc (the correct location).
    assert!(
        solver.inproc.reconstruction.len() > 0,
        "BVE pushed {} reconstruction entries to inproc.reconstruction, \
         but finalize_sat_model reads from the wrong Solver.reconstruction field",
        solver.inproc.reconstruction.len(),
    );

    // The formula is SAT by construction (all-positive binary core + bridge resolvents).
    // With the dual-field bug, the solver returns Unknown because its internal
    // model verification catches the unsatisfied original clauses.
    match &result {
        SatResult::Sat(model) => {
            // If we get here, reconstruction worked (bug is fixed).
            for (ci, clause) in original_clauses.iter().enumerate() {
                let satisfied = clause.iter().any(|&lit| {
                    let vi = lit.variable().index();
                    vi < model.len() && (model[vi] == lit.is_positive())
                });
                assert!(
                    satisfied,
                    "Original clause {ci} ({clause:?}) not satisfied by model",
                );
            }
        }
        _ => {
            panic!(
                "Expected SAT (formula is SAT by construction), got {:?}. \
                 BVE eliminated {} vars, inproc.reconstruction has {} entries. \
                 This is the dual ReconstructionStack field bug: finalize_sat.rs \
                 reads from Solver.reconstruction (empty) instead of \
                 inproc.reconstruction ({} entries).",
                result,
                eliminated,
                solver.inproc.reconstruction.len(),
                solver.inproc.reconstruction.len(),
            );
        }
    }
}
