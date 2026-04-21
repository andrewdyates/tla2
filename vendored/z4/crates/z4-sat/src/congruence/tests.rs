// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::collections::HashSet;

use super::union_find::{MergeResult, UnionFind};
use super::*;
use crate::test_util::lit;

#[test]
fn test_union_find_basic() {
    let mut uf = UnionFind::new(10);

    assert_eq!(uf.find(0), 0);
    assert_eq!(uf.find(5), 5);

    // union_lits merges literal pairs (positive + negative together)
    assert_eq!(uf.union_lits(0, 4), MergeResult::Merged);
    assert_eq!(uf.find(0), uf.find(4));
    // Complements must also be merged
    assert_eq!(uf.find(1), uf.find(5));

    assert_eq!(uf.union_lits(2, 6), MergeResult::Merged);
    assert_eq!(uf.find(2), uf.find(6));
}

#[test]
fn test_find_units_complementary_pair() {
    // Binary clauses (x, y) and (x, -y) → x is a forced unit.
    // Variables: x=0, y=1
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true), lit(1, true)], false); // (x, y)
    clauses.add(&[lit(0, true), lit(1, false)], false); // (x, -y)

    let mut cc = CongruenceClosure::new(2);
    cc.build_binary_adjacency_cached(&clauses);
    let units = cc.find_units_cached();

    // x (positive, literal index 0) should be discovered as a unit.
    assert!(
        units.contains(&lit(0, true)),
        "find_units should discover x as unit from (x,y) and (x,-y), got: {units:?}"
    );
}

#[test]
fn test_find_units_no_complementary_pair() {
    // Binary clauses (x, y) and (x, z) — no complementary pair.
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true), lit(1, true)], false); // (x, y)
    clauses.add(&[lit(0, true), lit(2, true)], false); // (x, z)

    let mut cc = CongruenceClosure::new(3);
    cc.build_binary_adjacency_cached(&clauses);
    let units = cc.find_units_cached();

    assert!(
        units.is_empty(),
        "find_units should find no units without complementary pairs, got: {units:?}"
    );
}

#[test]
fn test_find_equivalences_basic() {
    // Binary clauses: (x, -y) and (-x, y) → x ≡ y
    // (x, -y) means ¬x → ¬y, (-x, y) means x → y
    // Combined: x → y and ¬x → ¬y, so x ≡ y
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true), lit(1, false)], false); // (x, -y)
    clauses.add(&[lit(0, false), lit(1, true)], false); // (-x, y)

    let mut cc = CongruenceClosure::new(2);
    cc.build_binary_adjacency_cached(&clauses);
    let num_lits = 2 * 2;
    let mut uf = UnionFind::new(num_lits);
    let mut edges = Vec::new();

    let result = cc.find_equivalences_cached(&mut uf, &mut edges);
    assert!(result.is_ok());
    assert!(result.unwrap(), "should find x ≡ y equivalence");

    // x and y should now be in the same equivalence class.
    assert_eq!(
        uf.find(lit(0, true).index()),
        uf.find(lit(1, true).index()),
        "x and y should be equivalent"
    );
}

#[test]
fn test_find_equivalences_no_match() {
    // Binary clauses: (x, y) and (-x, y) — not an equivalence pattern.
    // (x, y) means ¬x → y, (-x, y) means x → y → y is unit, not equivalence.
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true), lit(1, true)], false); // (x, y)
    clauses.add(&[lit(0, false), lit(1, true)], false); // (-x, y)

    let mut cc = CongruenceClosure::new(2);
    cc.build_binary_adjacency_cached(&clauses);
    let num_lits = 2 * 2;
    let mut uf = UnionFind::new(num_lits);
    let mut edges = Vec::new();

    let result = cc.find_equivalences_cached(&mut uf, &mut edges);
    assert!(result.is_ok());
    assert!(
        !result.unwrap(),
        "should not find equivalences from non-matching pattern"
    );
}

#[test]
fn test_no_gates_no_change() {
    // Simple clauses with no gate structure
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true), lit(1, true)], false);
    clauses.add(&[lit(1, false), lit(2, true)], false);

    let mut cc = CongruenceClosure::new(3);
    let result = cc.run(&mut clauses, None, &[]);

    assert!(!result.found_equivalences);
}

#[test]
fn test_identical_and_gates() {
    // Two AND gates with identical inputs:
    // y1 = AND(a, b): (¬y1 ∨ a), (¬y1 ∨ b), (y1 ∨ ¬a ∨ ¬b)
    // y2 = AND(a, b): (¬y2 ∨ a), (¬y2 ∨ b), (y2 ∨ ¬a ∨ ¬b)
    // Variables: y1=0, y2=1, a=2, b=3

    let mut clauses = ClauseArena::new();
    // y1 = AND(a, b)
    clauses.add(&[lit(0, false), lit(2, true)], false); // (¬y1 ∨ a)
    clauses.add(&[lit(0, false), lit(3, true)], false); // (¬y1 ∨ b)
    clauses.add(&[lit(0, true), lit(2, false), lit(3, false)], false); // (y1 ∨ ¬a ∨ ¬b)
                                                                       // y2 = AND(a, b)
    clauses.add(&[lit(1, false), lit(2, true)], false); // (¬y2 ∨ a)
    clauses.add(&[lit(1, false), lit(3, true)], false); // (¬y2 ∨ b)
    clauses.add(&[lit(1, true), lit(2, false), lit(3, false)], false); // (y2 ∨ ¬a ∨ ¬b)

    let mut cc = CongruenceClosure::new(4);
    let result = cc.run(&mut clauses, None, &[]);

    // Should detect that y1 ≡ y2
    assert!(result.found_equivalences);
    assert!(cc.stats.equivalences_found > 0);
}

#[test]
fn test_equivalence_gates() {
    // Two EQUIV gates:
    // y1 ↔ a: (y1 ∨ ¬a), (¬y1 ∨ a)
    // y2 ↔ a: (y2 ∨ ¬a), (¬y2 ∨ a)
    // Variables: y1=0, y2=1, a=2

    let mut clauses = ClauseArena::new();
    // y1 ↔ a
    clauses.add(&[lit(0, true), lit(2, false)], false); // (y1 ∨ ¬a)
    clauses.add(&[lit(0, false), lit(2, true)], false); // (¬y1 ∨ a)
                                                        // y2 ↔ a
    clauses.add(&[lit(1, true), lit(2, false)], false); // (y2 ∨ ¬a)
    clauses.add(&[lit(1, false), lit(2, true)], false); // (¬y2 ∨ a)

    let mut cc = CongruenceClosure::new(3);
    let result = cc.run(&mut clauses, None, &[]);

    // Should detect that y1 ≡ y2
    assert!(result.found_equivalences);
}

#[test]
fn test_cascading_congruence() {
    // Test that eager rewriting finds cascading equivalences.
    // y1 = AND(a, b), y2 = AND(a, b) => y1 ≡ y2
    // z1 = AND(y1, c), z2 = AND(y2, c) => after y1≡y2, z1 ≡ z2
    // Variables: y1=0, y2=1, z1=2, z2=3, a=4, b=5, c=6

    let mut clauses = ClauseArena::new();
    // y1 = AND(a, b)
    clauses.add(&[lit(0, false), lit(4, true)], false);
    clauses.add(&[lit(0, false), lit(5, true)], false);
    clauses.add(&[lit(0, true), lit(4, false), lit(5, false)], false);
    // y2 = AND(a, b)
    clauses.add(&[lit(1, false), lit(4, true)], false);
    clauses.add(&[lit(1, false), lit(5, true)], false);
    clauses.add(&[lit(1, true), lit(4, false), lit(5, false)], false);
    // z1 = AND(y1, c)
    clauses.add(&[lit(2, false), lit(0, true)], false);
    clauses.add(&[lit(2, false), lit(6, true)], false);
    clauses.add(&[lit(2, true), lit(0, false), lit(6, false)], false);
    // z2 = AND(y2, c)
    clauses.add(&[lit(3, false), lit(1, true)], false);
    clauses.add(&[lit(3, false), lit(6, true)], false);
    clauses.add(&[lit(3, true), lit(1, false), lit(6, false)], false);

    let mut cc = CongruenceClosure::new(7);
    let result = cc.run(&mut clauses, None, &[]);

    assert!(result.found_equivalences);
    // Should find at least 2 equivalences: y1≡y2 and z1≡z2
    assert!(cc.stats.equivalences_found >= 2);

    // Verify z1 and z2 are in the same equivalence class.
    // With the CaDiCaL-parity refactor (#5237), congruence returns
    // equivalence_edges rather than a full lit_map. Check that edges
    // connect z1 and z2 (directly or transitively via y1≡y2).
    let z1_pos = Literal::positive(Variable(2));
    let z2_pos = Literal::positive(Variable(3));
    let has_z_equiv = result
        .equivalence_edges
        .iter()
        .any(|&(a, b)| (a == z1_pos && b == z2_pos) || (a == z2_pos && b == z1_pos));
    assert!(
        has_z_equiv,
        "Expected z1≡z2 in equivalence_edges, got: {:?}",
        result.equivalence_edges
    );
}

#[test]
fn test_stats_tracking() {
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true), lit(1, true)], false);

    let mut cc = CongruenceClosure::new(2);
    cc.run(&mut clauses, None, &[]);

    assert_eq!(cc.stats.rounds, 1);
}

#[test]
fn test_hyper_ternary_resolution() {
    // Hyper-ternary resolution: binary (-a, b) + ternary (a, b, c) => (b, c)
    //
    // Setup:
    //   binary: (¬a ∨ b) means a → b
    //   ternary: (a ∨ b ∨ c)
    // Derive: (b ∨ c)
    //   if ¬a: (b ∨ c) from ternary
    //   if a: b from binary, so (b ∨ c) trivially
    //
    // Variables: a=0, b=1, c=2
    let mut clauses = ClauseArena::new();
    // Binary: (¬a ∨ b)
    clauses.add(&[lit(0, false), lit(1, true)], false);
    // Ternary: (a ∨ b ∨ c)
    clauses.add(&[lit(0, true), lit(1, true), lit(2, true)], false);

    let mut cc = CongruenceClosure::new(3);
    let result = cc.run(&mut clauses, None, &[]);

    // Should have derived new binary clause (b ∨ c)
    assert_eq!(result.new_binary_clauses.len(), 1);
    let (_, l0, l1) = result.new_binary_clauses[0];
    let lits: HashSet<Literal> = [l0, l1].into_iter().collect();
    assert!(lits.contains(&lit(1, true)));
    assert!(lits.contains(&lit(2, true)));
}

#[test]
fn test_hyper_ternary_no_derivation() {
    // No hyper-ternary derivation possible.
    // Binary: (a ∨ d) — unrelated variable, doesn't enable resolution
    // Ternary: (a ∨ b ∨ c)
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true), lit(3, true)], false); // (a ∨ d)
    clauses.add(&[lit(0, true), lit(1, true), lit(2, true)], false); // (a ∨ b ∨ c)

    let mut cc = CongruenceClosure::new(4);
    let result = cc.run(&mut clauses, None, &[]);

    assert_eq!(result.new_binary_clauses.len(), 0);
}

#[test]
fn test_union_find_contradiction_detection() {
    let mut uf = UnionFind::new(4);
    // Merging a literal with its complement is a contradiction.
    assert!(matches!(
        uf.union_lits(0, 1),
        MergeResult::Contradiction { .. }
    ));

    // Indirect: merge a->b+, then a->b- forces b+ ≡ b-.
    let mut uf2 = UnionFind::new(4);
    assert_eq!(uf2.union_lits(0, 2), MergeResult::Merged);
    assert!(matches!(
        uf2.union_lits(0, 3),
        MergeResult::Contradiction { .. }
    ));
}

#[test]
fn test_congruence_no_unsat_on_satisfiable() {
    // Verify is_unsat is false for a satisfiable formula with AND gates.
    //   G1: y = AND(a, b)
    //   G2: z = AND(a, b)
    // Congruence merges y ≡ z; formula is still satisfiable.
    let mut clauses = ClauseArena::new();

    // G1: y = AND(a, b) => (¬y ∨ a), (¬y ∨ b), (y ∨ ¬a ∨ ¬b)
    clauses.add(&[lit(2, false), lit(0, true)], false);
    clauses.add(&[lit(2, false), lit(1, true)], false);
    clauses.add(&[lit(2, true), lit(0, false), lit(1, false)], false);

    // G2: z = AND(a, b) => (¬z ∨ a), (¬z ∨ b), (z ∨ ¬a ∨ ¬b)
    clauses.add(&[lit(3, false), lit(0, true)], false);
    clauses.add(&[lit(3, false), lit(1, true)], false);
    clauses.add(&[lit(3, true), lit(0, false), lit(1, false)], false);

    let mut cc = CongruenceClosure::new(4);
    let result = cc.run(&mut clauses, None, &[]);

    assert!(result.found_equivalences, "Should find y ≡ z");
    assert!(!result.is_unsat, "Satisfiable formula should not be UNSAT");
}

/// Build a vals array for the given assignments.
/// Each entry is (literal_index, value) where value is 1 (true) or -1 (false).
fn make_vals(num_vars: usize, assignments: &[(usize, i8)]) -> Vec<i8> {
    let mut vals = vec![0i8; num_vars * 2];
    for &(lit_idx, val) in assignments {
        vals[lit_idx] = val;
        vals[lit_idx ^ 1] = -val;
    }
    vals
}

fn add_and_gate(clauses: &mut ClauseArena, output_var: usize, input_vars: &[usize]) {
    let output_var = u32::try_from(output_var).expect("test output var fits in u32");
    for &input_var in input_vars {
        let input_var = u32::try_from(input_var).expect("test input var fits in u32");
        clauses.add(&[lit(output_var, false), lit(input_var, true)], false);
    }
    let mut long_clause = Vec::with_capacity(input_vars.len() + 1);
    long_clause.push(lit(output_var, true));
    long_clause.extend(input_vars.iter().map(|&input_var| {
        let input_var = u32::try_from(input_var).expect("test input var fits in u32");
        lit(input_var, false)
    }));
    clauses.add(&long_clause, false);
}

fn add_xnor3_gate(clauses: &mut ClauseArena, output_var: usize, input_vars: [usize; 3]) {
    let output_var = u32::try_from(output_var).expect("test output var fits in u32");
    let [x0, x1, x2] = input_vars
        .map(|input_var| u32::try_from(input_var).expect("test XOR input var fits in u32"));
    let clause_patterns = [
        [
            lit(output_var, true),
            lit(x0, true),
            lit(x1, true),
            lit(x2, true),
        ],
        [
            lit(output_var, true),
            lit(x0, true),
            lit(x1, false),
            lit(x2, false),
        ],
        [
            lit(output_var, true),
            lit(x0, false),
            lit(x1, true),
            lit(x2, false),
        ],
        [
            lit(output_var, true),
            lit(x0, false),
            lit(x1, false),
            lit(x2, true),
        ],
        [
            lit(output_var, false),
            lit(x0, true),
            lit(x1, true),
            lit(x2, false),
        ],
        [
            lit(output_var, false),
            lit(x0, true),
            lit(x1, false),
            lit(x2, true),
        ],
        [
            lit(output_var, false),
            lit(x0, false),
            lit(x1, true),
            lit(x2, true),
        ],
        [
            lit(output_var, false),
            lit(x0, false),
            lit(x1, false),
            lit(x2, false),
        ],
    ];
    for clause in clause_patterns {
        clauses.add(&clause, false);
    }
}

fn add_equivalence(clauses: &mut ClauseArena, lhs_var: usize, rhs_var: usize) {
    let lhs_var = u32::try_from(lhs_var).expect("test lhs var fits in u32");
    let rhs_var = u32::try_from(rhs_var).expect("test rhs var fits in u32");
    clauses.add(&[lit(lhs_var, false), lit(rhs_var, true)], false);
    clauses.add(&[lit(lhs_var, true), lit(rhs_var, false)], false);
}

fn add_negated_equivalence(clauses: &mut ClauseArena, lhs_var: usize, rhs_var: usize) {
    let lhs_var = u32::try_from(lhs_var).expect("test lhs var fits in u32");
    let rhs_var = u32::try_from(rhs_var).expect("test rhs var fits in u32");
    clauses.add(&[lit(lhs_var, false), lit(rhs_var, false)], false);
    clauses.add(&[lit(lhs_var, true), lit(rhs_var, true)], false);
}

fn edge_connects(edges: &[(Literal, Literal)], lhs: Literal, rhs: Literal) -> bool {
    edges.iter().any(|&(a, b)| {
        (a == lhs && b == rhs)
            || (a == rhs && b == lhs)
            || (a == lhs.negated() && b == rhs.negated())
            || (a == rhs.negated() && b == lhs.negated())
    })
}

#[test]
fn test_vals_and_gate_true_input_reduces_arity() {
    // AND gate: y = AND(a, b, c) with a=true simplifies to AND(b, c).
    // Another gate z = AND(b, c) should collide → y ≡ z.
    // Variables: y=0, z=1, a=2, b=3, c=4
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, false), lit(2, true)], false);
    clauses.add(&[lit(0, false), lit(3, true)], false);
    clauses.add(&[lit(0, false), lit(4, true)], false);
    clauses.add(
        &[lit(0, true), lit(2, false), lit(3, false), lit(4, false)],
        false,
    );
    clauses.add(&[lit(1, false), lit(3, true)], false);
    clauses.add(&[lit(1, false), lit(4, true)], false);
    clauses.add(&[lit(1, true), lit(3, false), lit(4, false)], false);
    let vals = make_vals(5, &[(4, 1)]); // var 2 positive = true
    let mut cc = CongruenceClosure::new(5);
    let result = cc.run(&mut clauses, Some(&vals), &[]);
    assert!(
        result.found_equivalences,
        "vals-aware simplification should expose y ≡ z"
    );
}

#[test]
fn test_vals_and_gate_false_input_kills_gate() {
    // AND(a, b) with a=false → output forced false, gate killed.
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, false), lit(1, true)], false);
    clauses.add(&[lit(0, false), lit(2, true)], false);
    clauses.add(&[lit(0, true), lit(1, false), lit(2, false)], false);
    let vals = make_vals(3, &[(2, -1)]); // var 1 positive = false
    let mut cc = CongruenceClosure::new(3);
    let result = cc.run(&mut clauses, Some(&vals), &[]);
    assert!(!result.is_unsat);
    assert!(
        result.units.contains(&lit(0, false)),
        "forced-false AND must emit unit ¬y, got {:?}",
        result.units
    );
}

#[test]
fn test_vals_and_gate_all_true_inputs_emit_output_unit() {
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, false), lit(1, true)], false);
    clauses.add(&[lit(0, false), lit(2, true)], false);
    clauses.add(&[lit(0, true), lit(1, false), lit(2, false)], false);
    let vals = make_vals(3, &[(2, 1), (4, 1)]);
    let mut cc = CongruenceClosure::new(3);
    let result = cc.run(&mut clauses, Some(&vals), &[]);
    assert!(
        result.units.contains(&lit(0, true)),
        "all-true AND must emit unit y, got {:?}",
        result.units
    );
}

#[test]
fn test_identical_wide_and_gates_merge() {
    let mut clauses = ClauseArena::new();
    let shared_inputs = [2, 3, 4, 5, 6, 7];
    add_and_gate(&mut clauses, 0, &shared_inputs);
    add_and_gate(&mut clauses, 1, &shared_inputs);

    let mut cc = CongruenceClosure::new(8);
    let result = cc.run(&mut clauses, None, &[]);

    assert!(
        result.found_equivalences,
        "identical 6-input AND gates should merge"
    );
    let y0 = lit(0, true);
    let y1 = lit(1, true);
    assert!(
        result
            .equivalence_edges
            .iter()
            .any(|&(a, b)| (a == y0 && b == y1) || (a == y1 && b == y0)),
        "expected direct equivalence for identical wide AND gates, got {:?}",
        result.equivalence_edges
    );
}

#[test]
fn test_wide_and_gates_with_distinct_tail_do_not_merge() {
    let mut clauses = ClauseArena::new();
    add_and_gate(&mut clauses, 0, &[2, 3, 4, 5, 6, 7]);
    add_and_gate(&mut clauses, 1, &[2, 3, 4, 5, 6, 8]);

    let mut cc = CongruenceClosure::new(9);
    let result = cc.run(&mut clauses, None, &[]);

    assert!(
        !result.found_equivalences,
        "wide AND gates that differ after the fifth input must not merge, got {:?}",
        result.equivalence_edges
    );
    assert!(
        result.equivalence_edges.is_empty(),
        "unexpected equivalence edges from distinct wide AND gates: {:?}",
        result.equivalence_edges
    );
}

#[test]
fn test_vals_and_gate_single_input_creates_equiv() {
    // AND(a, b) with a=true → y≡b. z≡b also exists → y≡z.
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, false), lit(2, true)], false);
    clauses.add(&[lit(0, false), lit(3, true)], false);
    clauses.add(&[lit(0, true), lit(2, false), lit(3, false)], false);
    clauses.add(&[lit(1, true), lit(3, false)], false);
    clauses.add(&[lit(1, false), lit(3, true)], false);
    let vals = make_vals(4, &[(4, 1)]); // var 2 positive = true
    let mut cc = CongruenceClosure::new(4);
    let result = cc.run(&mut clauses, Some(&vals), &[]);
    assert!(
        result.found_equivalences,
        "AND with one input should create equiv that cascades"
    );
}

#[test]
fn test_vals_xor_assigned_input() {
    // Gate pattern encodes XNOR: XNOR(a, b) with a=true → y ≡ b.
    // z ≡ b also (binary clauses) → y ≡ z via congruence cascade.
    let mut clauses = ClauseArena::new();
    // XOR gate y = XNOR(a, b): 4 ternary clauses on vars 0(y), 2(a), 3(b)
    clauses.add(&[lit(0, true), lit(2, true), lit(3, true)], false);
    clauses.add(&[lit(0, true), lit(2, false), lit(3, false)], false);
    clauses.add(&[lit(0, false), lit(2, false), lit(3, true)], false);
    clauses.add(&[lit(0, false), lit(2, true), lit(3, false)], false);
    // z ≡ b: (¬z ∨ b) and (z ∨ ¬b) on vars 1(z), 3(b)
    clauses.add(&[lit(1, false), lit(3, true)], false);
    clauses.add(&[lit(1, true), lit(3, false)], false);
    let vals = make_vals(4, &[(4, 1)]); // var 2 positive = true
    let mut cc = CongruenceClosure::new(4);
    let result = cc.run(&mut clauses, Some(&vals), &[]);
    assert!(
        result.found_equivalences,
        "XNOR with assigned true input should find y ≡ b, then y ≡ z"
    );
    // XNOR(true, b) = b → y ≡ b (same polarity).
    // With output-sign-carries-parity (#7137), the XNOR gate stores
    // -y as output. The merge edge is -y ≡ -z (negative literals),
    // and the binary clause gave +z ≡ +b. Together these mean y ≡ z ≡ b.
    // Edges imply their complements: (a, b) → (¬a, ¬b). So +z ≡ +b
    // implies -z ≡ -b, giving transitive: -y ≡ -z ≡ -b → y ≡ b. ✓
    let edges = &result.equivalence_edges;
    // Helper: edge (a,b) or its complement (¬a,¬b) connects l1↔l2
    let edge_connects = |l1: Literal, l2: Literal| -> bool {
        edges.iter().any(|&(a, b)| {
            (a == l1 && b == l2)
                || (b == l1 && a == l2)
                || (a == l1.negated() && b == l2.negated())
                || (b == l1.negated() && a == l2.negated())
        })
    };
    let y_pos = Literal::positive(Variable(0));
    let z_pos = Literal::positive(Variable(1));
    let b_pos = Literal::positive(Variable(3));
    let b_neg = Literal::negative(Variable(3));
    let y_eq_b =
        edge_connects(y_pos, b_pos) || (edge_connects(y_pos, z_pos) && edge_connects(z_pos, b_pos));
    assert!(
        y_eq_b,
        "XNOR(true, b) must produce y ≡ b (same polarity), got edges: {edges:?}"
    );
    // Verify NO wrong-polarity: y ≡ ¬b
    let y_eq_neg_b =
        edge_connects(y_pos, b_neg) || (edge_connects(y_pos, z_pos) && edge_connects(z_pos, b_neg));
    assert!(
        !y_eq_neg_b,
        "XNOR(true, b) must NOT produce y ≡ ¬b, got edges: {edges:?}"
    );
}

#[test]
fn test_vals_xor_false_input() {
    // XNOR(a, b) with a=false → y ≡ ¬b (since XNOR(F,b) = NOT(b)).
    let mut clauses = ClauseArena::new();
    // Same XNOR gate encoding: y = XNOR(a, b)
    clauses.add(&[lit(0, true), lit(2, true), lit(3, true)], false);
    clauses.add(&[lit(0, true), lit(2, false), lit(3, false)], false);
    clauses.add(&[lit(0, false), lit(2, false), lit(3, true)], false);
    clauses.add(&[lit(0, false), lit(2, true), lit(3, false)], false);
    let vals = make_vals(4, &[(5, 1)]); // var 2 negative = true → var 2 = false
    let mut cc = CongruenceClosure::new(4);
    let result = cc.run(&mut clauses, Some(&vals), &[]);
    assert!(
        result.found_equivalences,
        "XNOR with false input should find y ≡ ¬b"
    );
    // XNOR(false, b) = NOT(b), so y ≡ ¬b.
    // With output-sign-carries-parity (#7137), the XNOR gate stores
    // -y as output. The merge edge is -y ≡ +b (since XOR(false,b)=b
    // and gate says -y = XOR(a,b)), meaning y ≡ -b. ✓
    let y_neg = Literal::negative(Variable(0));
    let y_pos = Literal::positive(Variable(0));
    let b_pos = Literal::positive(Variable(3));
    let b_neg = Literal::negative(Variable(3));
    // Check: -y ≡ +b (or transitively via z), OR +y ≡ -b
    let has_correct = result.equivalence_edges.iter().any(|&(a, c)| {
        (a == y_neg && c == b_pos)
            || (a == b_pos && c == y_neg)
            || (a == y_pos && c == b_neg)
            || (a == b_neg && c == y_pos)
    }) || {
        // Transitively via z: -y ≡ +z and +z ≡ +b
        let z_pos = Literal::positive(Variable(1));
        let neg_y_to_z = result
            .equivalence_edges
            .iter()
            .any(|&(a, c)| (a == y_neg && c == z_pos) || (a == z_pos && c == y_neg));
        let z_to_b = result
            .equivalence_edges
            .iter()
            .any(|&(a, c)| (a == z_pos && c == b_pos) || (a == b_pos && c == z_pos));
        neg_y_to_z && z_to_b
    };
    assert!(
        has_correct,
        "XNOR(false, b) must produce y ≡ ¬b, got edges: {:?}",
        result.equivalence_edges
    );
}

#[test]
fn test_xnor_complementary_inputs_collapse_to_negative_unit() {
    // Binary equivalence x ≡ ¬y plus XNOR(x, y) forces the output false:
    // XNOR(x, ¬x) = false.
    //
    // This exercises the UF-rewrite path where a positive-normalized XOR/XNOR
    // input becomes the complemented representative of another input.
    // Congruence must cancel the complementary pair and flip parity instead of
    // leaving a spurious 2-input XOR gate alive.
    let mut clauses = ClauseArena::new();

    // z = XNOR(x, y)
    clauses.add(&[lit(0, true), lit(1, true), lit(2, true)], false);
    clauses.add(&[lit(0, true), lit(1, false), lit(2, false)], false);
    clauses.add(&[lit(0, false), lit(1, false), lit(2, true)], false);
    clauses.add(&[lit(0, false), lit(1, true), lit(2, false)], false);

    // x ≡ ¬y
    clauses.add(&[lit(1, true), lit(2, true)], false);
    clauses.add(&[lit(1, false), lit(2, false)], false);

    let mut cc = CongruenceClosure::new(3);
    let result = cc.run(&mut clauses, None, &[]);

    assert!(
        !result.is_unsat,
        "x ≡ ¬y with XNOR(x, y) is satisfiable and should force only ¬z"
    );
    assert!(
        result.units.contains(&lit(0, false)),
        "XNOR(x, y) with x ≡ ¬y must force ¬z, got units {:?} and edges {:?}",
        result.units,
        result.equivalence_edges
    );
    assert!(
        !result.units.contains(&lit(0, true)),
        "XNOR(x, y) with x ≡ ¬y must not force z"
    );
}

#[test]
fn test_xnor_duplicate_pair_reorders_after_uf_canonicalization() {
    // The initial XNOR simplification path sees raw inputs [a, b, c], but UF
    // rewrites them to [t, b, t]. Sorting before canonicalization leaves the
    // duplicate pair non-adjacent and misses y ≡ ¬b.
    let mut clauses = ClauseArena::new();
    add_xnor3_gate(&mut clauses, 0, [1, 2, 3]);
    add_equivalence(&mut clauses, 1, 4);
    add_equivalence(&mut clauses, 3, 4);

    let mut cc = CongruenceClosure::new(5);
    let result = cc.run(&mut clauses, None, &[]);

    let y_pos = Literal::positive(Variable(0));
    let b_pos = Literal::positive(Variable(2));
    let b_neg = Literal::negative(Variable(2));
    assert!(
        edge_connects(&result.equivalence_edges, y_pos, b_neg),
        "XNOR(t, b, t) must collapse to y ≡ ¬b, got edges {:?}",
        result.equivalence_edges
    );
    assert!(
        !edge_connects(&result.equivalence_edges, y_pos, b_pos),
        "XNOR(t, b, t) must not collapse to y ≡ b, got edges {:?}",
        result.equivalence_edges
    );
}

#[test]
fn test_xnor_complementary_pair_reorders_after_uf_canonicalization() {
    // The initial XNOR simplification path sees raw inputs [a, b, c], but UF
    // rewrites them to [t, b, ¬t]. Sorting before canonicalization leaves the
    // complementary pair non-adjacent and misses y ≡ b.
    let mut clauses = ClauseArena::new();
    add_xnor3_gate(&mut clauses, 0, [1, 2, 3]);
    add_equivalence(&mut clauses, 1, 4);
    add_negated_equivalence(&mut clauses, 3, 4);

    let mut cc = CongruenceClosure::new(5);
    let result = cc.run(&mut clauses, None, &[]);

    let y_pos = Literal::positive(Variable(0));
    let b_pos = Literal::positive(Variable(2));
    let b_neg = Literal::negative(Variable(2));
    assert!(
        edge_connects(&result.equivalence_edges, y_pos, b_pos),
        "XNOR(t, b, ¬t) must collapse to y ≡ b, got edges {:?}",
        result.equivalence_edges
    );
    assert!(
        !edge_connects(&result.equivalence_edges, y_pos, b_neg),
        "XNOR(t, b, ¬t) must not collapse to y ≡ ¬b, got edges {:?}",
        result.equivalence_edges
    );
}

#[test]
fn test_vals_ite_condition_assigned() {
    // ITE(c, t, e) with c=true → y ≡ t.
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true), lit(1, true), lit(3, false)], false);
    clauses.add(&[lit(0, true), lit(1, false), lit(2, false)], false);
    clauses.add(&[lit(0, false), lit(1, true), lit(3, true)], false);
    clauses.add(&[lit(0, false), lit(1, false), lit(2, true)], false);
    let vals = make_vals(4, &[(2, 1)]); // var 1 positive = true
    let mut cc = CongruenceClosure::new(4);
    let result = cc.run(&mut clauses, Some(&vals), &[]);
    assert!(
        result.found_equivalences,
        "ITE with assigned condition should create equivalence"
    );
    assert!(cc.stats().equivalences_found > 0);
}

#[test]
fn test_vals_ite_then_true_else_false_merges_output_with_condition() {
    // ITE(c, t, e) = y with t=true, e=false → y ≡ c (Case C).
    // gate_rewriting.rs:244-255: when then-branch is true and else-branch
    // is false, ITE reduces to the identity: output equals condition.
    // Variables: y=0 (output), c=1 (condition), t=2 (then), e=3 (else).
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true), lit(1, true), lit(3, false)], false);
    clauses.add(&[lit(0, true), lit(1, false), lit(2, false)], false);
    clauses.add(&[lit(0, false), lit(1, true), lit(3, true)], false);
    clauses.add(&[lit(0, false), lit(1, false), lit(2, true)], false);
    // then-branch (var 2 positive, lit_idx 4) = true,
    // else-branch (var 3 positive, lit_idx 6) = false.
    let vals = make_vals(4, &[(4, 1), (6, -1)]);
    let mut cc = CongruenceClosure::new(4);
    let result = cc.run(&mut clauses, Some(&vals), &[]);
    assert!(
        result.found_equivalences,
        "ITE(c, true, false) should merge output with condition"
    );
    assert!(cc.stats().equivalences_found > 0);
}

#[test]
fn test_vals_ite_then_false_else_true_merges_output_with_neg_condition() {
    // ITE(c, t, e) = y with t=false, e=true → y ≡ ¬c (Case D).
    // gate_rewriting.rs:256-268: when then-branch is false and else-branch
    // is true, ITE reduces to the negation: output equals NOT condition.
    // Variables: y=0 (output), c=1 (condition), t=2 (then), e=3 (else).
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true), lit(1, true), lit(3, false)], false);
    clauses.add(&[lit(0, true), lit(1, false), lit(2, false)], false);
    clauses.add(&[lit(0, false), lit(1, true), lit(3, true)], false);
    clauses.add(&[lit(0, false), lit(1, false), lit(2, true)], false);
    // then-branch (var 2 positive, lit_idx 4) = false,
    // else-branch (var 3 positive, lit_idx 6) = true.
    let vals = make_vals(4, &[(4, -1), (6, 1)]);
    let mut cc = CongruenceClosure::new(4);
    let result = cc.run(&mut clauses, Some(&vals), &[]);
    assert!(
        result.found_equivalences,
        "ITE(c, false, true) should merge output with negated condition"
    );
    assert!(cc.stats().equivalences_found > 0);
}

#[test]
fn test_vals_xor_all_inputs_assigned_emit_output_unit() {
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true), lit(1, true), lit(2, true)], false);
    clauses.add(&[lit(0, true), lit(1, false), lit(2, false)], false);
    clauses.add(&[lit(0, false), lit(1, false), lit(2, true)], false);
    clauses.add(&[lit(0, false), lit(1, true), lit(2, false)], false);
    let vals = make_vals(3, &[(2, 1), (4, 1)]);
    let mut cc = CongruenceClosure::new(3);
    let result = cc.run(&mut clauses, Some(&vals), &[]);
    assert!(
        result.units.contains(&lit(0, true)),
        "XNOR(true, true) must emit unit y, got {:?}",
        result.units
    );
}

#[test]
fn test_vals_ite_both_branches_same_polarity_kills_gate_no_merge() {
    // ITE(c, t, e) = y with t=true, e=true → gate killed, no merge (Case A).
    // gate_rewriting.rs:240-243: both branches assigned to same value means
    // the output is forced to that value. BCP handles the unit; congruence
    // just kills the gate without creating an equivalence.
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true), lit(1, true), lit(3, false)], false);
    clauses.add(&[lit(0, true), lit(1, false), lit(2, false)], false);
    clauses.add(&[lit(0, false), lit(1, true), lit(3, true)], false);
    clauses.add(&[lit(0, false), lit(1, false), lit(2, true)], false);
    // Both branches true: then (lit_idx 4) = true, else (lit_idx 6) = true.
    let vals = make_vals(4, &[(4, 1), (6, 1)]);
    let mut cc = CongruenceClosure::new(4);
    let result = cc.run(&mut clauses, Some(&vals), &[]);
    assert!(
        !result.found_equivalences,
        "ITE with both branches same polarity should not create equivalence"
    );
    assert!(!result.is_unsat);
    assert!(
        result.units.contains(&lit(0, true)),
        "ITE(true, true) branches must emit unit y, got {:?}",
        result.units
    );
}

#[test]
fn test_vals_equiv_assigned_input_emits_output_unit() {
    let mut clauses = ClauseArena::new();
    add_equivalence(&mut clauses, 0, 1);
    let vals = make_vals(2, &[(2, 1)]);
    let mut cc = CongruenceClosure::new(2);
    let result = cc.run(&mut clauses, Some(&vals), &[]);
    assert!(
        result.units.contains(&lit(0, true)),
        "equiv with assigned input must emit unit y, got {:?}",
        result.units
    );
}

#[test]
fn test_vals_none_matches_original_behavior() {
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, false), lit(2, true)], false);
    clauses.add(&[lit(0, false), lit(3, true)], false);
    clauses.add(&[lit(0, true), lit(2, false), lit(3, false)], false);
    clauses.add(&[lit(1, false), lit(2, true)], false);
    clauses.add(&[lit(1, false), lit(3, true)], false);
    clauses.add(&[lit(1, true), lit(2, false), lit(3, false)], false);
    let mut cc = CongruenceClosure::new(4);
    let result = cc.run(&mut clauses, None, &[]);
    assert!(result.found_equivalences);
    assert!(!result.is_unsat);
}

#[test]
fn congruence_skips_frozen_gate_outputs() {
    // AND gate: x1 = x2 ∧ x3
    // Clauses: (¬x1 ∨ x2), (¬x1 ∨ x3), (x1 ∨ ¬x2 ∨ ¬x3)
    // Plus a duplicate gate: x0 = x2 ∧ x3
    // Clauses: (¬x0 ∨ x2), (¬x0 ∨ x3), (x0 ∨ ¬x2 ∨ ¬x3)
    //
    // Without freeze: congruence detects x0 ≡ x1.
    // With x1 frozen: x1 is excluded from gate extraction, no equivalence found.
    let mut clauses = ClauseArena::new();
    // Gate for x0 = x2 ∧ x3
    clauses.add(&[lit(0, false), lit(2, true)], false);
    clauses.add(&[lit(0, false), lit(3, true)], false);
    clauses.add(&[lit(0, true), lit(2, false), lit(3, false)], false);
    // Gate for x1 = x2 ∧ x3
    clauses.add(&[lit(1, false), lit(2, true)], false);
    clauses.add(&[lit(1, false), lit(3, true)], false);
    clauses.add(&[lit(1, true), lit(2, false), lit(3, false)], false);

    // Without freeze: equivalence found
    let mut cc = CongruenceClosure::new(4);
    let result = cc.run(&mut clauses, None, &[]);
    assert!(result.found_equivalences);

    // With x1 frozen: x1 excluded from gate extraction, no equivalence
    let frozen = vec![false, true, false, false]; // x1 frozen
    let mut cc2 = CongruenceClosure::new(4);
    let result2 = cc2.run(&mut clauses, None, &frozen);
    // x1's gate is not extracted, so it cannot be merged with x0.
    // x0's gate still exists but has no partner to merge with.
    assert!(!result2.found_equivalences);
}

#[test]
fn test_forward_subsume_with_equivalences_is_disabled_without_reconstruction() {
    let mut clauses = ClauseArena::new();
    let subsumer = clauses.add(&[lit(0, true), lit(2, true)], false);
    let candidate = clauses.add(&[lit(1, true), lit(2, true), lit(3, true)], false);
    let edges = [(lit(0, true), lit(1, true))];

    let mut cc = CongruenceClosure::new(4);
    let subsumed = cc.forward_subsume_with_equivalences(&mut clauses, &edges);

    assert_eq!(
        subsumed, 0,
        "representative-based clause deletion stays disabled until congruence records reconstruction"
    );
    assert!(
        clauses.is_active(subsumer),
        "subsuming clause must stay active while the deletion path is disabled"
    );
    assert!(
        clauses.is_active(candidate),
        "candidate clause must stay active while the deletion path is disabled"
    );
}
