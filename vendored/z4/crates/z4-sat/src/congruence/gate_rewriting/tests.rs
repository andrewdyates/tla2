// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::CongruenceClosure;
use crate::clause_arena::ClauseArena;
use crate::literal::{Literal, Variable};
use crate::test_util::lit;

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
fn test_xnor_complementary_inputs_collapse_to_negative_unit() {
    let mut clauses = ClauseArena::new();

    clauses.add(&[lit(0, true), lit(1, true), lit(2, true)], false);
    clauses.add(&[lit(0, true), lit(1, false), lit(2, false)], false);
    clauses.add(&[lit(0, false), lit(1, false), lit(2, true)], false);
    clauses.add(&[lit(0, false), lit(1, true), lit(2, false)], false);

    add_negated_equivalence(&mut clauses, 1, 2);

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
