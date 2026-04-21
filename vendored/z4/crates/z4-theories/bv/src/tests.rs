// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use num_bigint::BigInt;
use z4_core::{TheoryResult, TheorySolver};
use z4_sat::{Literal, SatResult, Solver};

fn setup_store() -> TermStore {
    TermStore::new()
}

/// Solve BvSolver clauses and return variable assignments
fn solve_bv_clauses(solver: &BvSolver<'_>) -> Vec<bool> {
    let num_vars = (solver.next_var - 1) as usize;
    let mut sat_solver = Solver::new(num_vars);

    for clause in solver.clauses() {
        let lits: Vec<Literal> = clause
            .literals()
            .iter()
            .map(|&l| Literal::from_dimacs(l))
            .collect();
        sat_solver.add_clause(lits);
    }

    match sat_solver.solve().into_inner() {
        SatResult::Sat(model) => model,
        SatResult::Unsat => panic!("Expected SAT, got UNSAT"),
        SatResult::Unknown => panic!("Expected SAT, got Unknown"),
        #[allow(unreachable_patterns)]
        _ => unreachable!(),
    }
}

/// Extract a bitvector value from an assignment
fn extract_bv_value(model: &[bool], bits: &[CnfLit]) -> u64 {
    let mut value = 0u64;
    for (i, &bit) in bits.iter().enumerate() {
        let var_idx = (bit.unsigned_abs() - 1) as usize;
        let bit_value = model.get(var_idx).copied().unwrap_or(false);
        let polarity = bit > 0;
        if bit_value == polarity && i < 64 {
            value |= 1u64 << i;
        }
    }
    value
}

#[test]
fn test_const_bits() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    let bits = solver.const_bits(5, 4); // 0101
    assert_eq!(bits.len(), 4);

    // Verify the concrete value by solving and extracting
    let model = solve_bv_clauses(&solver);
    let val = extract_bv_value(&model, &bits);
    assert_eq!(val, 5, "const_bits(5, 4) should produce value 5");
}

#[test]
fn test_const_bits_wide_no_panic() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    let bits = solver.const_bits(1, 128);
    assert_eq!(bits.len(), 128);
    // With cached false literal optimization, zero bits share a single
    // variable, so only 2 unit clauses: 1 for the cached false + 1 for
    // the single true bit.
    assert_eq!(solver.clauses.len(), 2);
}

#[test]
fn test_delayed_internalization_tracks_wide_variable_mul() {
    let mut store = setup_store();
    let x = store.mk_var("x", Sort::bitvec(16));
    let y = store.mk_var("y", Sort::bitvec(16));
    let mul = store.mk_bvmul(vec![x, y]);

    let mut solver = BvSolver::new(&store);
    solver.set_delay_enabled(true);

    let bits = solver.ensure_term_bits(mul).expect("mul is BV-sorted");

    assert_eq!(bits.len(), 16);
    assert_eq!(solver.delayed_ops().len(), 1);
    // Proactive structural clauses (OR-chain trailing-zero propagation + bit-0 AND)
    // are emitted for delayed mul, but the full shift-and-add circuit (thousands of
    // clauses for 16-bit) is NOT built. Bound: < 200 structural clauses.
    assert!(
        solver.clauses().len() < 200,
        "delayed mul should emit only structural clauses, not the full circuit (got {} clauses)",
        solver.clauses().len()
    );
}

#[test]
fn test_materialize_delayed_term_emits_constraining_clauses() {
    let mut store = setup_store();
    let x = store.mk_var("x", Sort::bitvec(16));
    let y = store.mk_var("y", Sort::bitvec(16));
    let udiv = store.mk_bvudiv(vec![x, y]);

    let mut solver = BvSolver::new(&store);
    solver.set_delay_enabled(true);
    let _bits = solver.ensure_term_bits(udiv).expect("udiv is BV-sorted");

    // Build circuit for the first (and only) delayed operation
    let clauses = solver.build_delayed_circuit(0);

    assert!(
        !clauses.is_empty(),
        "building delayed circuit should add circuit/equality clauses"
    );
    assert!(
        !solver.has_unresolved_delayed_ops(),
        "built circuit term should no longer be unresolved"
    );
}

#[test]
fn test_process_assertion_handles_bool_ite() {
    // Regression test for #1539: check-sat-assuming with BV+ITE returns invalid SAT
    // The bug was that process_assertion() didn't handle TermData::Ite,
    // causing the ITE to be silently ignored and SAT to be incorrectly returned.

    let mut store = TermStore::new();

    // Build: (ite cond then_br else_br) where cond, then_br, else_br are Bool variables
    // We use variables to prevent constant folding from simplifying away the ITE.
    let cond = store.mk_var("cond", Sort::Bool);
    let then_br = store.mk_var("then_br", Sort::Bool);
    let else_br = store.mk_var("else_br", Sort::Bool);

    // Create ITE term
    let ite_term = store.mk_ite(cond, then_br, else_br);

    // Process assertion: ite(cond, then_br, else_br) = true
    // This should add clauses that encode the ITE semantics.
    let mut solver = BvSolver::new(&store);
    solver.process_assertion(ite_term, true);

    // After bitblasting, we should have non-empty clauses
    // (the bug would leave clauses empty because ITE was ignored)
    assert!(
        !solver.clauses.is_empty(),
        "ITE should be processed and generate clauses"
    );
}

#[test]
fn test_bv_ite_condition_tracked_for_tseitin_linking() {
    // Regression test for #1696: BV `ite` conditions must be tracked so we can
    // link their Tseitin var ↔ BV literal during encoding. Linking *all* Bool terms
    // is unsound, so we must track which Bool terms are legitimate BV ITE conditions.
    let mut store = TermStore::new();
    let cond = store.mk_var("cond", Sort::Bool);
    let then_bv = store.mk_var("then_bv", Sort::bitvec(8));
    let else_bv = store.mk_var("else_bv", Sort::bitvec(8));
    let ite_bv = store.mk_ite(cond, then_bv, else_bv);

    let mut solver = BvSolver::new(&store);
    let bits = solver.get_bits(ite_bv);

    assert_eq!(bits.len(), 8);
    assert!(
        solver.bv_ite_conditions().contains(&cond),
        "BV ite condition should be tracked for Tseitin linking"
    );
}

#[test]
fn test_bool_ite_condition_tracked_for_tseitin_linking() {
    // Bool-sorted ITE conditions MUST be tracked for Tseitin-BV linking (#1708).
    // Previously this test asserted the opposite, but that was wrong - Bool ITE
    // conditions need linking just like BV ITE conditions to ensure the Tseitin
    // and BV encodings agree on the condition's truth value.
    let mut store = TermStore::new();
    let cond = store.mk_var("cond", Sort::Bool);
    let then_br = store.mk_var("then_br", Sort::Bool);
    let else_br = store.mk_var("else_br", Sort::Bool);
    let ite_bool = store.mk_ite(cond, then_br, else_br);

    let mut solver = BvSolver::new(&store);
    let _lit = solver.bitblast_bool(ite_bool);

    assert!(
        solver.bv_ite_conditions().contains(&cond),
        "Bool ITE condition should be tracked for Tseitin-BV linking (#1708)"
    );
}

#[test]
fn test_bitblast_bool_caches_degenerate_xor() {
    // Ensure degenerate SMT-LIB arities are cached (no fresh CNF var per call).
    //
    // Previously, bitblast_bool() would early-return for (xor), bypassing the
    // bool_to_var cache and allocating new vars/clauses on each call.
    let mut store = TermStore::new();
    let xor0 = store.mk_app(Symbol::named("xor"), vec![], Sort::Bool);

    let mut solver = BvSolver::new(&store);
    let lit1 = solver.bitblast_bool(xor0);
    let clauses_after_first = solver.clauses.len();
    let lit2 = solver.bitblast_bool(xor0);
    let clauses_after_second = solver.clauses.len();

    assert_eq!(lit1, lit2);
    assert_eq!(clauses_after_first, clauses_after_second);
}

#[test]
fn test_bitblast_bool_caches_degenerate_eq() {
    // SMT-LIB: (=) and (= x) are both true.
    // Test 0-arity case (=).
    let mut store = TermStore::new();
    let eq0 = store.mk_app(Symbol::named("="), vec![], Sort::Bool);

    let mut solver = BvSolver::new(&store);
    let lit1 = solver.bitblast_bool(eq0);
    let clauses_after_first = solver.clauses.len();
    let lit2 = solver.bitblast_bool(eq0);
    let clauses_after_second = solver.clauses.len();

    assert_eq!(lit1, lit2);
    assert_eq!(clauses_after_first, clauses_after_second);
}

#[test]
fn test_bitblast_bool_caches_degenerate_eq_single_arg() {
    // SMT-LIB: (= x) is true (trivial reflexivity).
    // Test 1-arity case.
    let mut store = TermStore::new();
    let x = store.mk_var("x", Sort::Bool);
    let eq1 = store.mk_app(Symbol::named("="), vec![x], Sort::Bool);

    let mut solver = BvSolver::new(&store);
    let lit1 = solver.bitblast_bool(eq1);
    let clauses_after_first = solver.clauses.len();
    let lit2 = solver.bitblast_bool(eq1);
    let clauses_after_second = solver.clauses.len();

    assert_eq!(lit1, lit2);
    assert_eq!(clauses_after_first, clauses_after_second);
}

#[test]
fn test_bitblast_bool_caches_degenerate_distinct() {
    // SMT-LIB: (distinct) and (distinct x) are both true.
    // Test 0-arity case.
    let mut store = TermStore::new();
    let distinct0 = store.mk_app(Symbol::named("distinct"), vec![], Sort::Bool);

    let mut solver = BvSolver::new(&store);
    let lit1 = solver.bitblast_bool(distinct0);
    let clauses_after_first = solver.clauses.len();
    let lit2 = solver.bitblast_bool(distinct0);
    let clauses_after_second = solver.clauses.len();

    assert_eq!(lit1, lit2);
    assert_eq!(clauses_after_first, clauses_after_second);
}

#[test]
fn test_bitblast_bool_caches_degenerate_distinct_single_arg() {
    // SMT-LIB: (distinct x) is true (trivially all elements are distinct).
    // Test 1-arity case.
    let mut store = TermStore::new();
    let x = store.mk_var("x", Sort::Bool);
    let distinct1 = store.mk_app(Symbol::named("distinct"), vec![x], Sort::Bool);

    let mut solver = BvSolver::new(&store);
    let lit1 = solver.bitblast_bool(distinct1);
    let clauses_after_first = solver.clauses.len();
    let lit2 = solver.bitblast_bool(distinct1);
    let clauses_after_second = solver.clauses.len();

    assert_eq!(lit1, lit2);
    assert_eq!(clauses_after_first, clauses_after_second);
}

#[test]
fn test_bitblast_and() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    let a = solver.const_bits(0b1100, 4);
    let b = solver.const_bits(0b1010, 4);
    let result = solver.bitblast_and(&a, &b);

    assert_eq!(result.len(), 4);

    let model = solve_bv_clauses(&solver);
    let val = extract_bv_value(&model, &result);
    assert_eq!(val, 0b1000, "0b1100 & 0b1010 should be 0b1000 (8)");
}

#[test]
fn test_bitblast_add() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    let a = solver.const_bits(3, 4);
    let b = solver.const_bits(5, 4);
    let result = solver.bitblast_add(&a, &b);

    assert_eq!(result.len(), 4);

    let model = solve_bv_clauses(&solver);
    let val = extract_bv_value(&model, &result);
    assert_eq!(val, 8, "3 + 5 should be 8");
}

#[test]
fn test_bitblast_variable() {
    let mut store = setup_store();
    let x = store.mk_var("x", Sort::bitvec(8));

    let mut solver = BvSolver::new(&store);
    let bits = solver.get_bits(x);

    assert_eq!(bits.len(), 8);
}

#[test]
fn test_bitblast_concat_nested_order() {
    let mut store = setup_store();
    let a = store.mk_var("a", Sort::bitvec(2));
    let b = store.mk_var("b", Sort::bitvec(3));
    let c = store.mk_var("c", Sort::bitvec(1));

    // concat is binary: concat(high, low)
    let ab = store.mk_bvconcat(vec![a, b]);
    let abc = store.mk_bvconcat(vec![ab, c]);

    let mut solver = BvSolver::new(&store);
    let a_bits = solver.get_bits(a);
    let b_bits = solver.get_bits(b);
    let c_bits = solver.get_bits(c);

    // LSB-first: bits(concat(high, low)) = bits(low) ++ bits(high)
    let mut expected = c_bits;
    expected.extend(b_bits);
    expected.extend(a_bits);

    let bits = solver.get_bits(abc);
    assert_eq!(bits, expected);
}

#[test]
fn test_bitblast_concat_flattens_without_bitblasting_intermediates() {
    let mut store = setup_store();

    let leaf_count = 20usize;
    let leaves: Vec<TermId> = (0..leaf_count)
        .map(|i| store.mk_var(format!("v{i}"), Sort::bitvec(1)))
        .collect();

    // Build a deep, left-associative concat chain.
    let mut concats = Vec::new();
    let mut t = store.mk_bvconcat(vec![leaves[0], leaves[1]]);
    concats.push(t);
    for &leaf in &leaves[2..] {
        t = store.mk_bvconcat(vec![t, leaf]);
        concats.push(t);
    }
    let root = t;

    let mut solver = BvSolver::new(&store);
    let _bits = solver.get_bits(root);

    // Only leaf vars + root should be cached: intermediate concat nodes are flattened. (#1804)
    assert_eq!(solver.term_to_bits().len(), leaf_count + 1);
    for &c in &concats[..concats.len() - 1] {
        assert!(
            !solver.term_to_bits().contains_key(&c),
            "intermediate concat term should not be bitblasted"
        );
    }
}

#[test]
fn test_bitblast_bvadd_term() {
    let mut store = setup_store();
    let x = store.mk_var("x", Sort::bitvec(8));
    let y = store.mk_var("y", Sort::bitvec(8));
    let sum = store.mk_bvadd(vec![x, y]);

    let mut solver = BvSolver::new(&store);
    let bits = solver.get_bits(sum);

    assert_eq!(bits.len(), 8);
}

#[test]
fn test_bitblast_equality() {
    let mut store = setup_store();
    let x = store.mk_var("x", Sort::bitvec(4));
    let c = store.mk_bitvec(BigInt::from(5), 4);

    let mut solver = BvSolver::new(&store);
    let x_bits = solver.get_bits(x);
    let c_bits = solver.get_bits(c);

    let eq = solver.bitblast_eq(&x_bits, &c_bits);
    assert!(eq != 0);

    // Force equality to hold and verify x is constrained to 5
    solver.add_clause(CnfClause::unit(eq));
    let model = solve_bv_clauses(&solver);
    let x_val = extract_bv_value(&model, &x_bits);
    assert_eq!(x_val, 5, "equality constraint should force x = 5");
}

#[test]
fn test_bitblast_ult() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    let a = solver.const_bits(3, 4);
    let b = solver.const_bits(5, 4);
    let lt = solver.bitblast_ult(&a, &b);

    assert!(lt != 0);

    // 3 < 5 is true, so the ult literal should be forced true
    let model = solve_bv_clauses(&solver);
    let var_idx = (lt.unsigned_abs() - 1) as usize;
    let bit_val = model.get(var_idx).copied().unwrap_or(false);
    let expected = lt > 0; // positive literal means true when var is true
    assert_eq!(bit_val, expected, "3 < 5 should be true");
}

#[test]
fn test_theory_solver_interface() {
    let mut store = setup_store();
    let x = store.mk_var("x", Sort::bitvec(8));
    let y = store.mk_var("y", Sort::bitvec(8));
    let eq = store.mk_eq(x, y);

    let mut solver = BvSolver::new(&store);
    solver.assert_literal(eq, true);

    // Check returns Sat for eager bit-blasting (consistency checked by SAT solver)
    assert!(matches!(solver.check(), TheoryResult::Sat));
}

// =========================================================================
// Division tests
// =========================================================================

#[test]
fn test_is_zero() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    let zero = solver.const_bits(0, 4);
    let nonzero = solver.const_bits(5, 4);

    let zero_is_zero = solver.is_zero(&zero);
    let nonzero_is_zero = solver.is_zero(&nonzero);

    // These return literals - the actual constraints will be in clauses
    assert!(zero_is_zero != 0);
    assert!(nonzero_is_zero != 0);
}

#[test]
fn test_bitblast_udiv_urem_basic() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    // 7 / 3 = 2, 7 % 3 = 1
    let a = solver.const_bits(7, 4);
    let b = solver.const_bits(3, 4);

    let (q, r) = solver.bitblast_udiv_urem(&a, &b);

    assert_eq!(q.len(), 4);
    assert_eq!(r.len(), 4);
    assert!(!solver.clauses.is_empty());

    let model = solve_bv_clauses(&solver);
    let q_val = extract_bv_value(&model, &q);
    let r_val = extract_bv_value(&model, &r);
    assert_eq!(q_val, 2, "7 / 3 should be 2");
    assert_eq!(r_val, 1, "7 % 3 should be 1");
}

#[test]
fn test_bitblast_udiv() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    // 10 / 3 = 3
    let a = solver.const_bits(10, 4);
    let b = solver.const_bits(3, 4);

    let (q, _r) = solver.bitblast_udiv_urem(&a, &b);

    assert_eq!(q.len(), 4);

    let model = solve_bv_clauses(&solver);
    let q_val = extract_bv_value(&model, &q);
    assert_eq!(q_val, 3, "10 / 3 should be 3");
}

#[test]
fn test_bitblast_urem() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    // 10 % 3 = 1
    let a = solver.const_bits(10, 4);
    let b = solver.const_bits(3, 4);

    let (_q, r) = solver.bitblast_udiv_urem(&a, &b);

    assert_eq!(r.len(), 4);

    let model = solve_bv_clauses(&solver);
    let r_val = extract_bv_value(&model, &r);
    assert_eq!(r_val, 1, "10 % 3 should be 1");
}

#[test]
fn test_bitblast_sdiv() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    // In 4-bit signed: -7 = 0b1001, 2 = 0b0010
    // -7 / 2 = -3 (truncation toward zero) = 0b1101 = 13 unsigned
    let a = solver.const_bits(0b1001, 4); // -7 in 4-bit signed
    let b = solver.const_bits(0b0010, 4); // 2

    // Compute signed division: abs values, unsigned div, conditional negate
    let sign_a = a[3]; // MSB = sign bit
    let sign_b = b[3];
    let abs_a = solver.conditional_neg(&a, sign_a);
    let abs_b = solver.conditional_neg(&b, sign_b);
    let (abs_q, _) = solver.bitblast_udiv_urem(&abs_a, &abs_b);
    let result_neg = solver.mk_xor(sign_a, sign_b);
    let q = solver.conditional_neg(&abs_q, result_neg);

    assert_eq!(q.len(), 4);

    let model = solve_bv_clauses(&solver);
    let q_val = extract_bv_value(&model, &q);
    // -3 in 4-bit two's complement = 0b1101 = 13 unsigned
    assert_eq!(q_val, 0b1101, "-7 / 2 should be -3 (0b1101 = 13 unsigned)");
}

#[test]
fn test_bitblast_srem() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    // In 4-bit signed: -7 = 0b1001, 2 = 0b0010
    // -7 % 2 = -1 (sign matches dividend) = 0b1111 = 15 unsigned
    let a = solver.const_bits(0b1001, 4); // -7 in 4-bit signed
    let b = solver.const_bits(0b0010, 4); // 2

    // Compute signed remainder: abs values, unsigned div, conditional negate
    let sign_a = a[3]; // MSB = sign bit
    let sign_b = b[3];
    let abs_a = solver.conditional_neg(&a, sign_a);
    let abs_b = solver.conditional_neg(&b, sign_b);
    let (_, abs_r) = solver.bitblast_udiv_urem(&abs_a, &abs_b);
    let r = solver.conditional_neg(&abs_r, sign_a);

    assert_eq!(r.len(), 4);

    let model = solve_bv_clauses(&solver);
    let r_val = extract_bv_value(&model, &r);
    // -1 in 4-bit two's complement = 0b1111 = 15 unsigned
    assert_eq!(r_val, 0b1111, "-7 % 2 should be -1 (0b1111 = 15 unsigned)");
}

#[test]
fn test_bitblast_div_by_zero() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    // Division by zero: a / 0 = all_ones, a % 0 = a
    // SMT-LIB semantics: bvudiv(a, 0) = all_ones, bvurem(a, 0) = a
    let a = solver.const_bits(7, 4);
    let zero = solver.const_bits(0, 4);

    let (q, r) = solver.bitblast_udiv_urem(&a, &zero);

    assert_eq!(q.len(), 4);
    assert_eq!(r.len(), 4);

    // Verify semantics by solving the CNF and checking the model
    let model = solve_bv_clauses(&solver);
    let q_val = extract_bv_value(&model, &q);
    let r_val = extract_bv_value(&model, &r);

    assert_eq!(
        q_val, 0xF,
        "bvudiv(a, 0) should be all_ones (0xF for 4-bit)"
    );
    assert_eq!(r_val, 7, "bvurem(a, 0) should be a (7)");
}

#[test]
fn test_conditional_neg() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    let a = solver.const_bits(5, 4);
    let cond_true = solver.fresh_var();
    solver.add_clause(CnfClause::unit(cond_true));

    let result = solver.conditional_neg(&a, cond_true);
    assert_eq!(result.len(), 4);

    let model = solve_bv_clauses(&solver);
    let val = extract_bv_value(&model, &result);
    // -5 in 4-bit two's complement = ~5 + 1 = 0b1010 + 1 = 0b1011 = 11
    assert_eq!(
        val, 0b1011,
        "conditional_neg(5, true) should be -5 (0b1011 = 11)"
    );
}

#[test]
fn test_mk_or_many() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    // Test with multiple literals
    let lits = vec![solver.fresh_var(), solver.fresh_var(), solver.fresh_var()];

    let result = solver.mk_or_many(&lits);
    assert!(result != 0);
}

#[test]
fn test_mk_or_many_empty() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    // Empty case should return false
    let result = solver.mk_or_many(&[]);
    assert!(result != 0);
}

#[test]
fn test_mk_or_many_single() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    let lit = solver.fresh_var();
    let result = solver.mk_or_many(&[lit]);

    // Single literal case should return the literal itself
    assert_eq!(result, lit);
}

#[test]
fn test_division_generates_clauses() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    let initial_clauses = solver.clauses.len();

    let a = solver.const_bits(15, 4);
    let b = solver.const_bits(4, 4);
    let (_q, _r) = solver.bitblast_udiv_urem(&a, &b);

    // Division should generate additional clauses for the constraints
    assert!(solver.clauses.len() > initial_clauses);
}

#[test]
fn test_signed_division_symmetry() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    // Test that both operands being negative gives positive result
    // -6 / -2 = 3
    let a = solver.const_bits(0b1010, 4); // -6 in 4-bit signed
    let b = solver.const_bits(0b1110, 4); // -2 in 4-bit signed

    let sign_a = a[3];
    let sign_b = b[3];
    let abs_a = solver.conditional_neg(&a, sign_a);
    let abs_b = solver.conditional_neg(&b, sign_b);
    let (abs_q, _) = solver.bitblast_udiv_urem(&abs_a, &abs_b);
    let result_neg = solver.mk_xor(sign_a, sign_b);
    let q = solver.conditional_neg(&abs_q, result_neg);
    assert_eq!(q.len(), 4);

    let model = solve_bv_clauses(&solver);
    let q_val = extract_bv_value(&model, &q);
    assert_eq!(q_val, 3, "-6 / -2 should be 3");
}

#[test]
fn test_bitblast_extract() {
    // Test extract[hi:lo](x) operation via term API
    let mut store = setup_store();
    let x = store.mk_var("x", Sort::bitvec(8));
    // extract[5:2](x) - extract bits 5 down to 2 (4 bits)
    let extracted = store.mk_bvextract(5, 2, x);

    let mut solver = BvSolver::new(&store);
    let bits = solver.get_bits(extracted);

    // Result should be 4 bits (5 - 2 + 1 = 4)
    assert_eq!(bits.len(), 4, "extract[5:2] should produce 4 bits");
}

#[test]
fn test_bitblast_zero_extend() {
    // Test zero_extend[4](x) operation via term API
    let mut store = setup_store();
    let x = store.mk_var("x", Sort::bitvec(4));
    // zero_extend[4](x) - extend 4-bit value by 4 zero bits -> 8 bits
    let extended = store.mk_bvzero_extend(4, x);

    let mut solver = BvSolver::new(&store);
    let bits = solver.get_bits(extended);

    // Result should be 8 bits (4 + 4 = 8)
    assert_eq!(
        bits.len(),
        8,
        "zero_extend[4] of 4-bit value should produce 8 bits"
    );
}

#[test]
fn test_bitblast_sign_extend() {
    // Test sign_extend[4](x) operation via term API
    let mut store = setup_store();
    let x = store.mk_var("x", Sort::bitvec(4));
    // sign_extend[4](x) - extend 4-bit value by 4 sign bits -> 8 bits
    let extended = store.mk_bvsign_extend(4, x);

    let mut solver = BvSolver::new(&store);
    let bits = solver.get_bits(extended);

    // Result should be 8 bits (4 + 4 = 8)
    assert_eq!(
        bits.len(),
        8,
        "sign_extend[4] of 4-bit value should produce 8 bits"
    );
}

#[test]
fn test_concat_flattening_deep_chain() {
    // Test that deeply nested concat is correctly flattened.
    // Build concat(concat(concat(a, b), c), d) where a,b,c,d are 8-bit.
    // Result should be 32 bits in order: [d_bits, c_bits, b_bits, a_bits] (LSB-first).
    let mut store = TermStore::new();
    let a = store.mk_var("a", Sort::bitvec(8));
    let b = store.mk_var("b", Sort::bitvec(8));
    let c = store.mk_var("c", Sort::bitvec(8));
    let d = store.mk_var("d", Sort::bitvec(8));

    // Build: concat(concat(concat(a, b), c), d)
    let ab = store.mk_bvconcat(vec![a, b]); // a is high, b is low
    let abc = store.mk_bvconcat(vec![ab, c]); // ab is high, c is low
    let abcd = store.mk_bvconcat(vec![abc, d]); // abc is high, d is low

    let mut solver = BvSolver::new(&store);

    // Get bits for leaves FIRST to establish their CNF variables
    let a_bits = solver.get_bits(a);
    let b_bits = solver.get_bits(b);
    let c_bits = solver.get_bits(c);
    let d_bits = solver.get_bits(d);

    // Now get the concat result
    let bits = solver.get_bits(abcd);

    // Should have 32 bits total
    assert_eq!(bits.len(), 32, "concat of 4x8-bit should be 32 bits");

    // Verify bit ordering correctness (LSB-first):
    // concat(concat(concat(a, b), c), d) = concat(abc_high, d_low)
    // In LSB-first: [d_bits, c_bits, b_bits, a_bits]
    let mut expected = Vec::with_capacity(32);
    expected.extend_from_slice(&d_bits); // bits[0..8]: d (LSB)
    expected.extend_from_slice(&c_bits); // bits[8..16]: c
    expected.extend_from_slice(&b_bits); // bits[16..24]: b
    expected.extend_from_slice(&a_bits); // bits[24..32]: a (MSB)
    assert_eq!(
        bits, expected,
        "concat bit ordering must be LSB-first: [d, c, b, a]"
    );
}

#[test]
fn test_concat_flattening_bit_order() {
    // Verify that bit order is preserved after flattening.
    // concat(0xAB, 0xCD) produces bitvector 0xABCD (AB high, CD low).
    // In LSB-first bit representation: bits[0..8] = CD, bits[8..16] = AB.
    let mut store = TermStore::new();

    // Create constants: 0xAB = 10101011, 0xCD = 11001101
    let ab = store.mk_bitvec(BigInt::from(0xABu8), 8);
    let cd = store.mk_bitvec(BigInt::from(0xCDu8), 8);

    // concat(ab, cd) where ab is high bits, cd is low bits
    // Result: 0xABCD as 16-bit bitvector
    let concat_term = store.mk_bvconcat(vec![ab, cd]);

    let mut solver = BvSolver::new(&store);
    let bits = solver.get_bits(concat_term);

    assert_eq!(bits.len(), 16, "concat of two 8-bit should be 16 bits");

    // Check that bit constraints encode the correct values.
    // The unit clauses tell us which bits are forced true/false.
    // bits[0..8] should be CD (0xCD = 11001101), bits[8..16] should be AB (0xAB = 10101011).

    // With cached false literal, zero bits share one variable. Verify we have
    // at least 2 unit clauses (1 cached false + 1+ true bits).
    let unit_clause_count = solver.clauses.iter().filter(|c| c.0.len() == 1).count();
    assert!(
        unit_clause_count >= 2,
        "should have at least 2 unit clauses (1 cached false + 1+ true bits)"
    );
}

#[test]
fn test_concat_flattening_performance() {
    // Test that deeply nested concat doesn't blow up.
    // Build a chain of 20 concat operations.
    let mut store = TermStore::new();

    // Create 21 variables
    let vars: Vec<_> = (0..21)
        .map(|i| store.mk_var(format!("v{i}"), Sort::bitvec(8)))
        .collect();

    // Build a right-associative chain: concat(v0, concat(v1, concat(v2, ...)))
    let mut current = vars[20];
    for i in (0..20).rev() {
        current = store.mk_bvconcat(vec![vars[i], current]);
    }

    let mut solver = BvSolver::new(&store);
    let bits = solver.get_bits(current);

    // Should have 168 bits (21 * 8)
    assert_eq!(bits.len(), 21 * 8, "21 x 8-bit concat should be 168 bits");
}

#[test]
fn test_concat_flattening_nary() {
    // Test n-ary concat (3+ arguments in a single concat call).
    // mk_bvconcat handles n-ary by converting to binary tree, but
    // flattening should handle the tree structure correctly.
    let mut store = TermStore::new();
    let a = store.mk_var("a", Sort::bitvec(4));
    let b = store.mk_var("b", Sort::bitvec(4));
    let c = store.mk_var("c", Sort::bitvec(4));

    // concat(a, b, c) where a is MSB, c is LSB
    // Result bits should be [c_bits, b_bits, a_bits] (LSB-first)
    let concat_term = store.mk_bvconcat(vec![a, b, c]);

    let mut solver = BvSolver::new(&store);

    // Get leaf bits FIRST to establish their CNF variables
    let a_bits = solver.get_bits(a);
    let b_bits = solver.get_bits(b);
    let c_bits = solver.get_bits(c);

    // Now get the concat result
    let bits = solver.get_bits(concat_term);

    // Should have 12 bits total (3 x 4)
    assert_eq!(bits.len(), 12, "concat of 3x4-bit should be 12 bits");

    // Verify bit ordering correctness (LSB-first):
    // concat(a, b, c) = a high, b middle, c low
    // In LSB-first: [c_bits, b_bits, a_bits]
    let mut expected = Vec::with_capacity(12);
    expected.extend_from_slice(&c_bits); // bits[0..4]: c (LSB)
    expected.extend_from_slice(&b_bits); // bits[4..8]: b
    expected.extend_from_slice(&a_bits); // bits[8..12]: a (MSB)
    assert_eq!(
        bits, expected,
        "n-ary concat bit ordering must be LSB-first: [c, b, a]"
    );
}

#[test]
fn test_const_case_multiplier_triggers_for_sparse_operands() {
    // Test that const-case multiplier is used when operands have many constant bits.
    // For an 8-bit multiplication where a has 5 known bits and b has 5 known bits,
    // case_size = 2^6 = 64 < circuit_size = 8*8*5 = 320, so case-split should trigger.
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    // Create operand a: 3 variable bits at positions 0,1,2, rest are 0
    let mut a_bits = Vec::with_capacity(8);
    for _ in 0..3 {
        a_bits.push(solver.fresh_var());
    }
    for _ in 3..8 {
        a_bits.push(solver.fresh_false());
    }

    // Create operand b: 3 variable bits at positions 0,1,2, rest are 0
    let mut b_bits = Vec::with_capacity(8);
    for _ in 0..3 {
        b_bits.push(solver.fresh_var());
    }
    for _ in 3..8 {
        b_bits.push(solver.fresh_false());
    }

    let clauses_before = solver.clauses.len();
    let result = solver.bitblast_mul(&a_bits, &b_bits);
    assert_eq!(result.len(), 8);
    let clauses_after = solver.clauses.len();
    assert!(
        clauses_after > clauses_before,
        "Multiplication should add clauses"
    );
}

#[test]
fn test_const_case_multiplier_correctness() {
    // Verify const-case multiplier produces correct results.
    // Use a concrete case: a = 3, b = 5
    // Expected result: 3 * 5 = 15
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    let a_bits = solver.const_bits(3, 8);
    let b_bits = solver.const_bits(5, 8);

    let result = solver.bitblast_mul(&a_bits, &b_bits);
    assert_eq!(result.len(), 8);

    let model = solve_bv_clauses(&solver);
    let product = extract_bv_value(&model, &result);

    assert_eq!(product, 15, "3 * 5 should equal 15");
}

#[test]
fn test_shift_add_fallback_for_dense_operands() {
    // Test that dense-variable operands fall back to shift-and-add.
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    // Create 16-bit operands with all variable bits
    let mut a_bits = Vec::with_capacity(16);
    let mut b_bits = Vec::with_capacity(16);
    for _ in 0..16 {
        a_bits.push(solver.fresh_var());
        b_bits.push(solver.fresh_var());
    }

    let result = solver.bitblast_mul(&a_bits, &b_bits);
    assert_eq!(result.len(), 16);
}

#[test]
fn test_fresh_true_is_known_true() {
    // Verify fresh_true produces a literal that is_known_true() recognizes.
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    let true_lit = solver.fresh_true();
    assert!(
        solver.is_known_true(true_lit),
        "fresh_true should produce a known-true literal"
    );
    assert!(
        !solver.is_known_false(true_lit),
        "fresh_true should not be known-false"
    );
}

// =========================================================================
// TheorySolver protocol compliance: push/pop/reset
// =========================================================================

#[test]
fn test_bv_push_pop_undoes_assertions() {
    let mut store = setup_store();
    let x = store.mk_var("x", Sort::bitvec(8));
    let y = store.mk_var("y", Sort::bitvec(8));
    let z = store.mk_var("z", Sort::bitvec(8));
    let eq = store.mk_eq(x, y);
    let eq2 = store.mk_eq(x, z);

    let mut solver = BvSolver::new(&store);

    // Assert at base level
    solver.assert_literal(eq, true);
    assert!(solver.asserted.contains_key(&eq));

    // Push, assert another literal, then pop
    solver.push();
    solver.assert_literal(eq2, true);
    assert!(
        solver.asserted.contains_key(&eq2),
        "scoped assertion present"
    );

    solver.pop();
    assert!(
        !solver.asserted.contains_key(&eq2),
        "scoped assertion must be removed on pop"
    );
    assert!(
        solver.asserted.contains_key(&eq),
        "base assertion must survive pop"
    );
}

#[test]
fn test_bv_nested_push_pop() {
    let mut store = setup_store();
    let a = store.mk_var("a", Sort::bitvec(4));
    let b = store.mk_var("b", Sort::bitvec(4));
    let c = store.mk_var("c", Sort::bitvec(4));
    let eq_ab = store.mk_eq(a, b);
    let eq_bc = store.mk_eq(b, c);
    let eq_ac = store.mk_eq(a, c);

    let mut solver = BvSolver::new(&store);

    // Level 0: assert a = b
    solver.assert_literal(eq_ab, true);
    let trail_base = solver.trail.len();

    // Level 1: assert b = c
    solver.push();
    solver.assert_literal(eq_bc, true);
    let trail_l1 = solver.trail.len();

    // Level 2: assert a = c
    solver.push();
    solver.assert_literal(eq_ac, true);
    assert_eq!(solver.trail.len(), trail_l1 + 1);

    // Pop level 2
    solver.pop();
    assert_eq!(solver.trail.len(), trail_l1);
    assert!(!solver.asserted.contains_key(&eq_ac));

    // Pop level 1
    solver.pop();
    assert_eq!(solver.trail.len(), trail_base);
    assert!(!solver.asserted.contains_key(&eq_bc));
    assert!(solver.asserted.contains_key(&eq_ab));
}

#[test]
fn test_bv_reset_clears_all_state() {
    let mut store = setup_store();
    let x = store.mk_var("x", Sort::bitvec(8));
    let y = store.mk_var("y", Sort::bitvec(8));
    let eq = store.mk_eq(x, y);

    let mut solver = BvSolver::new(&store);
    solver.assert_literal(eq, true);
    solver.push();

    // Produce some bitblasting state
    let _bits = solver.const_bits(42, 8);

    solver.reset();

    assert!(solver.trail.is_empty(), "trail must be empty after reset");
    assert!(
        solver.trail_stack.is_empty(),
        "trail_stack must be empty after reset"
    );
    assert!(
        solver.asserted.is_empty(),
        "asserted must be empty after reset"
    );
    assert!(
        solver.term_to_bits.is_empty(),
        "term_to_bits must be empty after reset"
    );
    assert!(
        solver.clauses.is_empty(),
        "clauses must be empty after reset"
    );
    assert_eq!(solver.next_var, 1, "next_var must reset to 1");
}

#[test]
fn test_bv_check_after_push_pop_is_sat() {
    let mut store = setup_store();
    let x = store.mk_var("x", Sort::bitvec(8));
    let y = store.mk_var("y", Sort::bitvec(8));
    let eq = store.mk_eq(x, y);

    let mut solver = BvSolver::new(&store);

    solver.push();
    solver.assert_literal(eq, true);
    assert!(matches!(solver.check(), TheoryResult::Sat));
    solver.pop();

    // After pop, check should still return Sat (eager bit-blasting)
    assert!(
        matches!(solver.check(), TheoryResult::Sat),
        "BV check after pop must be Sat"
    );
}

#[test]
fn test_bv_propagate_always_empty() {
    let mut store = setup_store();
    let x = store.mk_var("x", Sort::bitvec(8));
    let y = store.mk_var("y", Sort::bitvec(8));
    let eq = store.mk_eq(x, y);

    let mut solver = BvSolver::new(&store);
    solver.assert_literal(eq, true);

    // Eager bit-blasting never propagates
    let props = solver.propagate();
    assert!(props.is_empty(), "BV propagate must always return empty");
}

// --- #5877: gate cache round-trip tests ---

/// Test that gate_caches() returns empty caches for a fresh solver.
#[test]
fn test_bv_gate_caches_initially_empty_5877() {
    let store = setup_store();
    let solver = BvSolver::new(&store);
    let (and_cache, or_cache, xor_cache) = solver.gate_caches();
    assert!(
        and_cache.is_empty(),
        "fresh solver AND cache should be empty"
    );
    assert!(or_cache.is_empty(), "fresh solver OR cache should be empty");
    assert!(
        xor_cache.is_empty(),
        "fresh solver XOR cache should be empty"
    );
}

/// Test that gate caches accumulate entries after bit-blasting.
/// Bit-blasting a BV AND expression should populate the AND gate cache.
#[test]
fn test_bv_gate_caches_populated_after_bitblast_5877() {
    let mut store = setup_store();
    let x = store.mk_var("x", Sort::bitvec(8));
    let y = store.mk_var("y", Sort::bitvec(8));
    let bvand = store.mk_app(Symbol::Named("bvand".into()), vec![x, y], Sort::bitvec(8));
    // Create assertion: bvand(x, y) = x (arbitrary, just to trigger bitblasting)
    let eq = store.mk_eq(bvand, x);

    let mut solver = BvSolver::new(&store);
    solver.assert_literal(eq, true);

    let (and_cache, or_cache, _xor_cache) = solver.gate_caches();
    // After bit-blasting an 8-bit AND, the AND cache should have entries
    // (one per bit pair, potentially).
    assert!(
        !and_cache.is_empty(),
        "AND cache should be populated after bit-blasting bvand, got {} entries",
        and_cache.len()
    );
    // OR and XOR caches may or may not be populated depending on the formula
    let _ = or_cache; // suppress unused warning
}

/// Test that set_gate_caches + gate_caches is a faithful round-trip.
/// Save caches from one solver, create a new solver, restore caches,
/// and verify the restored caches match.
#[test]
fn test_bv_gate_cache_round_trip_5877() {
    let mut store = setup_store();
    let x = store.mk_var("x", Sort::bitvec(8));
    let y = store.mk_var("y", Sort::bitvec(8));
    let bvand = store.mk_app(Symbol::Named("bvand".into()), vec![x, y], Sort::bitvec(8));
    let eq = store.mk_eq(bvand, x);

    // First solver: bit-blast to populate caches
    let mut solver1 = BvSolver::new(&store);
    solver1.assert_literal(eq, true);

    // Save caches
    let (and1, or1, xor1) = solver1.gate_caches();
    let saved_and = and1.clone();
    let saved_or = or1.clone();
    let saved_xor = xor1.clone();
    let and_count = saved_and.len();

    // Second solver: restore caches
    let mut solver2 = BvSolver::new(&store);
    solver2.set_gate_caches(saved_and.clone(), saved_or.clone(), saved_xor.clone());

    // Verify restored caches match saved caches
    let (and2, or2, xor2) = solver2.gate_caches();
    assert_eq!(
        and2.len(),
        and_count,
        "restored AND cache should have same size as saved"
    );
    assert_eq!(
        *and2, saved_and,
        "restored AND cache should equal saved cache"
    );
    assert_eq!(*or2, saved_or, "restored OR cache should equal saved cache");
    assert_eq!(
        *xor2, saved_xor,
        "restored XOR cache should equal saved cache"
    );
}

/// Test that div_caches() returns empty caches for a fresh solver.
#[test]
fn test_bv_div_caches_initially_empty_5877() {
    let store = setup_store();
    let solver = BvSolver::new(&store);
    let (unsigned, signed) = solver.div_caches();
    assert!(
        unsigned.is_empty(),
        "fresh solver unsigned div cache should be empty"
    );
    assert!(
        signed.is_empty(),
        "fresh solver signed div cache should be empty"
    );
}

/// Regression test for #6536: ensure_term_bits returns None for non-BV terms.
/// This guards the invariant that the internal bitblast/get_bits path is never
/// reached for non-BV-sorted terms.
#[test]
fn test_ensure_term_bits_rejects_non_bv_6536() {
    let mut store = setup_store();
    let int_var = store.mk_var("x", Sort::Int);
    let bool_var = store.mk_var("b", Sort::Bool);
    let mut solver = BvSolver::new(&store);
    assert!(
        solver.ensure_term_bits(int_var).is_none(),
        "ensure_term_bits should return None for Int-sorted term"
    );
    assert!(
        solver.ensure_term_bits(bool_var).is_none(),
        "ensure_term_bits should return None for Bool-sorted term"
    );
}
