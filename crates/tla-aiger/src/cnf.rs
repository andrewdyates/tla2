// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! AIG to CNF conversion via Tseitin transformation.
//!
//! Converts an `AigerCircuit` into Conjunctive Normal Form suitable for SAT
//! solving. Each AND gate becomes a set of clauses encoding the equivalence
//! `out <-> in0 AND in1`. Structural optimization detects XOR and ITE patterns
//! that arise from the AIG encoding and produces tighter clause sets.
//!
//! Reference: rIC3 `deps/aig-rs/src/cnf.rs` (121 lines) — Tseitin encoding
//! with XOR/ITE detection over the cone of influence.

use rustc_hash::FxHashSet;

use crate::sat_types::{Lit, Var};
use crate::types::{aiger_is_negated, aiger_var, AigerCircuit};

/// A CNF formula produced by Tseitin transformation of an AIGER circuit.
#[derive(Debug, Clone)]
pub struct CnfFormula {
    /// Total number of CNF variables (max var index + 1).
    pub num_vars: usize,
    /// Clauses: each clause is a disjunction of literals.
    pub clauses: Vec<Vec<Lit>>,
    /// Mapping from AIGER variable index to CNF `Var`.
    /// `var_map[aiger_var]` is `Some(cnf_var)` if the AIGER variable is in
    /// the cone of influence, `None` otherwise.
    pub var_map: Vec<Option<Var>>,
}

/// Map an AIGER literal through the variable mapping, returning a SAT `Lit`.
///
/// Handles constant literals (0 = FALSE, 1 = TRUE) by mapping them to Var(0)
/// with appropriate polarity. Returns `None` if the AIGER variable is not in
/// the `var_map`.
fn map_aiger_lit(aiger_lit: u64, var_map: &[Option<Var>]) -> Option<Lit> {
    let avar = aiger_var(aiger_lit) as usize;
    if avar >= var_map.len() {
        return None;
    }
    let cnf_var = var_map[avar]?;
    let negated = aiger_is_negated(aiger_lit);
    Some(if negated {
        Lit::neg(cnf_var)
    } else {
        Lit::pos(cnf_var)
    })
}

/// Detect XOR pattern: both children of an AND gate are themselves AND gates
/// with complementary inputs. Structure:
///   node = AND(NOT(AND(a, b)), NOT(AND(NOT(a), NOT(b))))
///   => node = XOR(a, b)
///
/// Returns (a_lit, b_lit) as AIGER literals if the pattern matches.
fn detect_xor(
    node_idx: usize,
    ands_by_var: &[Option<usize>],
    circuit: &AigerCircuit,
) -> Option<(u64, u64)> {
    let gate = &circuit.ands[ands_by_var[node_idx]?];

    // Both children must be negated AND gates
    if !aiger_is_negated(gate.rhs0) || !aiger_is_negated(gate.rhs1) {
        return None;
    }

    let child0_var = aiger_var(gate.rhs0) as usize;
    let child1_var = aiger_var(gate.rhs1) as usize;

    let child0_gate = &circuit.ands[ands_by_var.get(child0_var).copied().flatten()?];
    let child1_gate = &circuit.ands[ands_by_var.get(child1_var).copied().flatten()?];

    let (c0r0, c0r1) = (child0_gate.rhs0, child0_gate.rhs1);
    let (c1r0, c1r1) = (child1_gate.rhs0, child1_gate.rhs1);

    // Check: child0 = AND(a, b), child1 = AND(NOT(a), NOT(b))
    if c0r0 == (c1r0 ^ 1) && c0r1 == (c1r1 ^ 1) {
        // Avoid degenerate case where both inputs are the same variable
        if aiger_var(c0r0) == aiger_var(c0r1) {
            return None;
        }
        return Some((c0r0, c0r1));
    }

    None
}

/// Detect ITE (if-then-else) pattern. Structure:
///   node = AND(NOT(AND(c, t')), NOT(AND(NOT(c), e')))
///   => node = ITE(c, NOT(t'), NOT(e'))
///
/// Returns (condition, then_branch, else_branch) as AIGER literals.
fn detect_ite(
    node_idx: usize,
    ands_by_var: &[Option<usize>],
    circuit: &AigerCircuit,
) -> Option<(u64, u64, u64)> {
    let gate = &circuit.ands[ands_by_var[node_idx]?];

    if !aiger_is_negated(gate.rhs0) || !aiger_is_negated(gate.rhs1) {
        return None;
    }

    let child0_var = aiger_var(gate.rhs0) as usize;
    let child1_var = aiger_var(gate.rhs1) as usize;

    let child0_gate = &circuit.ands[ands_by_var.get(child0_var).copied().flatten()?];
    let child1_gate = &circuit.ands[ands_by_var.get(child1_var).copied().flatten()?];

    let (c0r0, c0r1) = (child0_gate.rhs0, child0_gate.rhs1);
    let (c1r0, c1r1) = (child1_gate.rhs0, child1_gate.rhs1);

    // Look for a complementary pair in the four inputs
    let try_ite = |cond: u64, then_val: u64, else_val: u64| -> Option<(u64, u64, u64)> {
        let cv = aiger_var(cond);
        let tv = aiger_var(then_val);
        let ev = aiger_var(else_val);
        // All three variables must be distinct
        if cv == tv || cv == ev || tv == ev {
            return None;
        }
        Some((cond, then_val ^ 1, else_val ^ 1))
    };

    if c0r0 == (c1r0 ^ 1) {
        return try_ite(c0r0, c0r1, c1r1);
    }
    if c0r0 == (c1r1 ^ 1) {
        return try_ite(c0r0, c0r1, c1r0);
    }
    if c0r1 == (c1r0 ^ 1) {
        return try_ite(c0r1, c0r0, c1r1);
    }
    if c0r1 == (c1r1 ^ 1) {
        return try_ite(c0r1, c0r0, c1r0);
    }

    None
}

/// Convert an `AigerCircuit` to CNF via Tseitin transformation.
///
/// Only gates in the cone of influence (reachable from bad-state properties,
/// constraints, and next-state functions) are encoded. XOR and ITE patterns
/// are detected and encoded with specialized clause sets.
pub fn aiger_to_cnf(circuit: &AigerCircuit) -> CnfFormula {
    let max_aiger_var = circuit.maxvar as usize;

    // Build lookup: aiger_var -> index in circuit.ands
    let mut ands_by_var: Vec<Option<usize>> = vec![None; max_aiger_var + 1];
    for (idx, gate) in circuit.ands.iter().enumerate() {
        let v = aiger_var(gate.lhs) as usize;
        if v <= max_aiger_var {
            ands_by_var[v] = Some(idx);
        }
    }

    // Compute cone of influence: start from bad properties, constraints,
    // outputs, and next-state functions, then walk backwards through AND gates.
    let mut in_coi = FxHashSet::default();

    let seed_coi = |lit: u64, coi: &mut FxHashSet<usize>| {
        let v = aiger_var(lit) as usize;
        if v > 0 {
            coi.insert(v);
        }
    };

    for b in &circuit.bad {
        seed_coi(b.lit, &mut in_coi);
    }
    for o in &circuit.outputs {
        seed_coi(o.lit, &mut in_coi);
    }
    for c in &circuit.constraints {
        seed_coi(c.lit, &mut in_coi);
    }
    for l in &circuit.latches {
        seed_coi(l.next, &mut in_coi);
    }

    // Backwards walk: for each AND gate in COI, add its children.
    let mut worklist: Vec<usize> = in_coi.iter().copied().collect();
    while let Some(v) = worklist.pop() {
        if let Some(Some(gate_idx)) = ands_by_var.get(v) {
            let gate = &circuit.ands[*gate_idx];
            let child0 = aiger_var(gate.rhs0) as usize;
            let child1 = aiger_var(gate.rhs1) as usize;
            if child0 > 0 && in_coi.insert(child0) {
                worklist.push(child0);
            }
            if child1 > 0 && in_coi.insert(child1) {
                worklist.push(child1);
            }
        }
    }

    // Allocate CNF variables for AIGER variables in COI.
    // Variable 0 is reserved for the constant FALSE node.
    let mut var_map: Vec<Option<Var>> = vec![None; max_aiger_var + 1];
    var_map[0] = Some(Var::CONST); // Constant FALSE
    let mut next_cnf_idx: u32 = 1;

    for v in 1..=max_aiger_var {
        if in_coi.contains(&v) {
            var_map[v] = Some(Var(next_cnf_idx));
            next_cnf_idx += 1;
        }
    }

    let num_vars = next_cnf_idx as usize;
    let mut clauses: Vec<Vec<Lit>> = Vec::new();

    // Constant FALSE node: In our encoding, Lit::TRUE = pos(Var::CONST) = Lit(0).
    // The unit clause [Lit::TRUE] constrains the constant variable.
    // The transys module handles constant semantics independently via
    // direct AIGER-to-Lit mapping, so the CNF only needs structural
    // consistency for the Tseitin encoding to work.
    clauses.push(vec![Lit::TRUE]);

    // Encode each AND gate in the COI via Tseitin transformation.
    // Process in reverse variable order (higher first) matching rIC3 convention.
    let mut sorted_coi: Vec<usize> = in_coi.iter().copied().collect();
    sorted_coi.sort_unstable();

    for &v in sorted_coi.iter().rev() {
        if ands_by_var.get(v).and_then(|x| *x).is_none() {
            continue; // Not an AND gate (input or latch)
        }

        let out_var = match var_map[v] {
            Some(cv) => cv,
            None => continue,
        };

        // Try XOR optimization
        if let Some((xor_a, xor_b)) = detect_xor(v, &ands_by_var, circuit) {
            if let (Some(a), Some(b)) = (
                map_aiger_lit(xor_a, &var_map),
                map_aiger_lit(xor_b, &var_map),
            ) {
                let n = Lit::pos(out_var);
                // XOR encoding: n <-> (a XOR b)
                // 4 clauses:
                //   (!n, !a, !b), (!n, a, b), (n, !a, b), (n, a, !b)
                clauses.push(vec![!n, !a, !b]);
                clauses.push(vec![!n, a, b]);
                clauses.push(vec![n, !a, b]);
                clauses.push(vec![n, a, !b]);
                continue;
            }
        }

        // Try ITE optimization
        if let Some((cond, then_br, else_br)) = detect_ite(v, &ands_by_var, circuit) {
            if let (Some(c), Some(t), Some(e)) = (
                map_aiger_lit(cond, &var_map),
                map_aiger_lit(then_br, &var_map),
                map_aiger_lit(else_br, &var_map),
            ) {
                let n = Lit::pos(out_var);
                // ITE encoding: n <-> ITE(c, t, e)
                // 4 clauses (conditional equivalence):
                //   (!c, !n, t), (!c, n, !t), (c, !n, e), (c, n, !e)
                clauses.push(vec![!c, !n, t]);
                clauses.push(vec![!c, n, !t]);
                clauses.push(vec![c, !n, e]);
                clauses.push(vec![c, n, !e]);
                continue;
            }
        }

        // Standard AND encoding: out <-> (in0 AND in1)
        // 3 Tseitin clauses:
        //   (out, !in0, !in1)   — if both inputs true, output must be true
        //   (!out, in0)         — if output true, in0 must be true
        //   (!out, in1)         — if output true, in1 must be true
        let gate = &circuit.ands[ands_by_var[v].unwrap()];
        let in0 = match map_aiger_lit(gate.rhs0, &var_map) {
            Some(l) => l,
            None => continue,
        };
        let in1 = match map_aiger_lit(gate.rhs1, &var_map) {
            Some(l) => l,
            None => continue,
        };

        let out = Lit::pos(out_var);
        clauses.push(vec![out, !in0, !in1]);
        clauses.push(vec![!out, in0]);
        clauses.push(vec![!out, in1]);
    }

    CnfFormula {
        num_vars,
        clauses,
        var_map,
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse_aag;

    #[test]
    fn test_cnf_empty_circuit() {
        let c = parse_aag("aag 0 0 0 0 0\n").unwrap();
        let cnf = aiger_to_cnf(&c);
        // Only the constant FALSE clause
        assert_eq!(cnf.num_vars, 1);
        assert_eq!(cnf.clauses.len(), 1); // just ~v0
    }

    #[test]
    fn test_cnf_single_and_gate() {
        // M=3, I=2, L=0, O=1, A=1: out=6, AND(6, 2, 4)
        let c = parse_aag("aag 3 2 0 1 1\n2\n4\n6\n6 2 4\n").unwrap();
        let cnf = aiger_to_cnf(&c);
        // Variables: const(0), input1(1), input2(2), and_out(3) => 4 vars
        assert_eq!(cnf.num_vars, 4);
        // Clauses: 1 (const FALSE) + 3 (Tseitin AND) = 4
        assert_eq!(cnf.clauses.len(), 4);
    }

    #[test]
    fn test_cnf_var_map() {
        let c = parse_aag("aag 3 2 0 1 1\n2\n4\n6\n6 2 4\n").unwrap();
        let cnf = aiger_to_cnf(&c);
        // AIGER var 0 -> CNF Var(0) (constant)
        assert_eq!(cnf.var_map[0], Some(Var::CONST));
        // AIGER var 1 (input) -> some CNF var
        assert!(cnf.var_map[1].is_some());
        // AIGER var 2 (input) -> some CNF var
        assert!(cnf.var_map[2].is_some());
        // AIGER var 3 (AND output) -> some CNF var
        assert!(cnf.var_map[3].is_some());
    }

    #[test]
    fn test_cnf_with_latch() {
        // Toggle flip-flop: latch starts at 0, next = NOT(current)
        let c = parse_aag("aag 1 0 1 2 0\n2 3\n2\n3\n").unwrap();
        let cnf = aiger_to_cnf(&c);
        // Latch variable should be in the COI
        assert!(cnf.var_map[1].is_some());
    }

    #[test]
    fn test_cnf_constant_output() {
        // Output is constant FALSE (lit 0)
        let c = parse_aag("aag 0 0 0 1 0\n0\n").unwrap();
        let cnf = aiger_to_cnf(&c);
        assert_eq!(cnf.num_vars, 1);
    }

    #[test]
    fn test_cnf_bad_property() {
        // M=3, I=2, L=0, O=0, A=1, B=1: bad=6, AND(6, 2, 4)
        let c = parse_aag("aag 3 2 0 0 1 1\n2\n4\n6\n6 2 4\n").unwrap();
        let cnf = aiger_to_cnf(&c);
        assert_eq!(cnf.num_vars, 4);
        assert_eq!(cnf.clauses.len(), 4);
    }

    #[test]
    fn test_cnf_half_adder_xor_detection() {
        // Half adder: sum = XOR(x, y), carry = AND(x, y)
        // 6 13 15 => AND(NOT(12), NOT(14)) — XOR structure
        // 12 2 4  => AND(x, y)
        // 14 3 5  => AND(NOT(x), NOT(y))
        let src = "aag 7 2 0 2 3\n2\n4\n6\n12\n6 13 15\n12 2 4\n14 3 5\n";
        let c = parse_aag(src).unwrap();
        let cnf = aiger_to_cnf(&c);
        // Should produce clauses — exact count depends on XOR detection
        assert!(cnf.clauses.len() >= 4);
        // All referenced variables should be mapped
        assert!(cnf.var_map[1].is_some()); // input x
        assert!(cnf.var_map[2].is_some()); // input y
    }

    #[test]
    fn test_map_aiger_lit_constants() {
        let var_map = vec![Some(Var::CONST)]; // only constant
                                              // AIGER lit 0 = FALSE = var 0, positive
        let lit0 = map_aiger_lit(0, &var_map).unwrap();
        assert_eq!(lit0.var(), Var::CONST);
        assert!(lit0.is_positive());

        // AIGER lit 1 = TRUE = var 0, negated
        let lit1 = map_aiger_lit(1, &var_map).unwrap();
        assert_eq!(lit1.var(), Var::CONST);
        assert!(lit1.is_negated());
    }

    #[test]
    fn test_cnf_tseitin_correctness() {
        // Verify that the Tseitin encoding is correct for a simple AND gate.
        // AND gate: out = in0 AND in1
        // For all 4 input combinations, assert that the CNF is satisfiable
        // iff out matches the AND of in0 and in1.
        let c = parse_aag("aag 3 2 0 1 1\n2\n4\n6\n6 2 4\n").unwrap();
        let cnf = aiger_to_cnf(&c);

        let in0_var = cnf.var_map[1].unwrap(); // AIGER var 1 = input 0
        let in1_var = cnf.var_map[2].unwrap(); // AIGER var 2 = input 1
        let out_var = cnf.var_map[3].unwrap(); // AIGER var 3 = AND output

        // Check all 8 assignments of 3 variables
        for a in [false, true] {
            for b in [false, true] {
                for c_val in [false, true] {
                    let expected_out = a && b;
                    let consistent = c_val == expected_out;

                    // Check if all clauses are satisfied under this assignment
                    let model = |lit: Lit| -> bool {
                        let var = lit.var();
                        let val = if var == Var::CONST {
                            false // constant FALSE
                        } else if var == in0_var {
                            a
                        } else if var == in1_var {
                            b
                        } else if var == out_var {
                            c_val
                        } else {
                            false
                        };
                        if lit.is_negated() {
                            !val
                        } else {
                            val
                        }
                    };

                    let all_satisfied = cnf
                        .clauses
                        .iter()
                        .all(|clause| clause.iter().any(|&lit| model(lit)));

                    assert_eq!(
                        all_satisfied, consistent,
                        "in0={a}, in1={b}, out={c_val}: expected consistent={consistent}, got all_satisfied={all_satisfied}"
                    );
                }
            }
        }
    }
}
