// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! XOR-pattern detection and arithmetic-structure analysis for AIGs.
//!
//! Detects the standard half-adder XOR encoding:
//! - `t1 = AND(a, !b)`
//! - `t2 = AND(!a, b)`
//! - `g = AND(!t1, !t2)`
//!
//! In this pattern, `!g = XOR(a, b)`.

use rustc_hash::{FxHashMap, FxHashSet};

use crate::sat_types::{Lit, Var};
use crate::transys::Transys;

/// Analysis of circuit structure for strategy selection.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct CircuitAnalysis {
    pub xor_count: usize,
    pub xor_depth: usize,
    pub max_logic_depth: usize,
    pub has_carry_chain: bool,
    pub is_arithmetic: bool,
}

/// Detect XOR patterns in the AIG and compute circuit structure metrics.
///
/// Arithmetic detection heuristic (#4072):
/// A circuit is classified as arithmetic if any of:
/// 1. XOR count exceeds 25% of latch count (standard half-adder detection)
/// 2. Has a carry chain (ripple-carry adder structure detected)
/// 3. High logic depth relative to latch count (deep combinational logic
///    typical of multipliers, ALUs, and differential equation circuits)
///
/// The third condition catches arithmetic circuits that don't use XOR
/// (e.g., multipliers using only AND gates, or circuits like `diffeq`
/// that compute difference equations with deep combinational networks).
pub(crate) fn analyze_circuit(ts: &Transys) -> CircuitAnalysis {
    let xor_gates = detect_xor_gates(ts);
    let xor_count = xor_gates.len();
    let max_logic_depth = compute_logic_depth(ts);
    let has_carry_chain = detect_carry_chains(ts, &xor_gates);

    // Arithmetic if: many XOR gates, carry chain detected, or
    // deep logic relative to circuit size (>= 3x depth-to-latch ratio
    // with at least 8 latches and depth >= 10).
    let high_xor = ts.num_latches > 0 && xor_count > ts.num_latches / 4;
    let deep_logic = ts.num_latches >= 8
        && max_logic_depth >= 10
        && max_logic_depth >= ts.num_latches * 3;
    let is_arithmetic = high_xor || has_carry_chain || deep_logic;

    CircuitAnalysis {
        xor_count,
        xor_depth: compute_xor_depth(&xor_gates),
        max_logic_depth,
        has_carry_chain,
        is_arithmetic,
    }
}

/// Detect XOR gates in the AIG.
///
/// Returns a map from the AND gate output var whose negation is the XOR output
/// to the `(a, b)` XOR inputs.
pub(crate) fn detect_xor_gates(ts: &Transys) -> FxHashMap<Var, (Lit, Lit)> {
    let mut xor_gates = FxHashMap::default();

    for (&gate, &(rhs0, rhs1)) in &ts.and_defs {
        if !rhs0.is_negated() || !rhs1.is_negated() {
            continue;
        }
        if rhs0.var() == Var::CONST || rhs1.var() == Var::CONST || rhs0.var() == rhs1.var() {
            continue;
        }

        let Some(&child0) = ts.and_defs.get(&rhs0.var()) else {
            continue;
        };
        let Some(&child1) = ts.and_defs.get(&rhs1.var()) else {
            continue;
        };

        let inputs =
            match_half_adder_xor(child0, child1).or_else(|| match_half_adder_xor(child1, child0));
        if let Some((a, b)) = inputs {
            xor_gates.insert(gate, canonical_lit_pair(a, b));
        }
    }

    xor_gates
}

/// Compute the maximum combinational logic depth.
///
/// Depth is measured from latch next-state functions through `and_defs`. If the
/// transition system has no latches, bad-state and constraint literals are used
/// as fallback roots so pure combinational test fixtures still report depth.
fn compute_logic_depth(ts: &Transys) -> usize {
    let input_vars: FxHashSet<Var> = ts.input_vars.iter().copied().collect();
    let latch_vars: FxHashSet<Var> = ts.latch_vars.iter().copied().collect();
    let mut memo = FxHashMap::default();
    let mut visiting = FxHashSet::default();

    let mut roots: Vec<Lit> = ts.next_state.values().copied().collect();
    if roots.is_empty() {
        roots.extend(ts.bad_lits.iter().copied());
        roots.extend(ts.constraint_lits.iter().copied());
    }

    roots
        .into_iter()
        .map(|lit| logic_depth_of_lit(lit, ts, &input_vars, &latch_vars, &mut memo, &mut visiting))
        .max()
        .unwrap_or(0)
}

/// Detect carry chain patterns: XOR feeding into AND with carry-in.
fn detect_carry_chains(ts: &Transys, xor_gates: &FxHashMap<Var, (Lit, Lit)>) -> bool {
    if xor_gates.len() < 2 {
        return false;
    }

    let mut gates_by_inputs: FxHashMap<(Lit, Lit), Vec<Var>> = FxHashMap::default();
    for (&out, &(rhs0, rhs1)) in &ts.and_defs {
        gates_by_inputs
            .entry(canonical_lit_pair(rhs0, rhs1))
            .or_default()
            .push(out);
    }

    let mut carry_stages = FxHashSet::default();

    for (&xor_var, &(a, b)) in xor_gates {
        let Some(generate_gates) = gates_by_inputs.get(&canonical_lit_pair(a, b)) else {
            continue;
        };
        let xor_out = Lit::neg(xor_var);

        for (&mix_var, &(rhs0, rhs1)) in &ts.and_defs {
            let cin = if rhs0 == xor_out {
                Some(rhs1)
            } else if rhs1 == xor_out {
                Some(rhs0)
            } else {
                None
            };
            let Some(cin) = cin else {
                continue;
            };
            if cin.var() == Var::CONST {
                continue;
            }

            for &generate_var in generate_gates {
                let or_key = canonical_lit_pair(Lit::neg(generate_var), Lit::neg(mix_var));
                let Some(carry_gates) = gates_by_inputs.get(&or_key) else {
                    continue;
                };
                for &carry_gate in carry_gates {
                    carry_stages.insert((cin, Lit::neg(carry_gate)));
                }
            }
        }
    }

    if carry_stages.len() < 2 {
        return false;
    }

    let carry_outputs: FxHashSet<Lit> = carry_stages.iter().map(|&(_, cout)| cout).collect();
    carry_stages
        .iter()
        .any(|&(cin, _)| carry_outputs.contains(&cin))
}

fn canonical_lit_pair(a: Lit, b: Lit) -> (Lit, Lit) {
    if a <= b {
        (a, b)
    } else {
        (b, a)
    }
}

fn match_half_adder_xor(left: (Lit, Lit), right: (Lit, Lit)) -> Option<(Lit, Lit)> {
    let left_lits = [left.0, left.1];
    let right_lits = [right.0, right.1];

    for left_idx in 0..2 {
        let a = left_lits[left_idx];
        let not_b = left_lits[1 - left_idx];

        for right_idx in 0..2 {
            let not_a = right_lits[right_idx];
            let b = right_lits[1 - right_idx];

            if not_a == !a && not_b == !b && a.var() != b.var() {
                return Some((a, b));
            }
        }
    }

    None
}

fn compute_xor_depth(xor_gates: &FxHashMap<Var, (Lit, Lit)>) -> usize {
    let mut memo = FxHashMap::default();
    let mut visiting = FxHashSet::default();

    xor_gates
        .keys()
        .copied()
        .map(|var| xor_depth_of_var(var, xor_gates, &mut memo, &mut visiting))
        .max()
        .unwrap_or(0)
}

fn xor_depth_of_var(
    var: Var,
    xor_gates: &FxHashMap<Var, (Lit, Lit)>,
    memo: &mut FxHashMap<Var, usize>,
    visiting: &mut FxHashSet<Var>,
) -> usize {
    if let Some(&depth) = memo.get(&var) {
        return depth;
    }
    if !visiting.insert(var) {
        return 0;
    }

    let depth = xor_gates.get(&var).map_or(0, |&(a, b)| {
        1 + xor_depth_of_lit(a, xor_gates, memo, visiting)
            .max(xor_depth_of_lit(b, xor_gates, memo, visiting))
    });

    visiting.remove(&var);
    memo.insert(var, depth);
    depth
}

fn xor_depth_of_lit(
    lit: Lit,
    xor_gates: &FxHashMap<Var, (Lit, Lit)>,
    memo: &mut FxHashMap<Var, usize>,
    visiting: &mut FxHashSet<Var>,
) -> usize {
    if xor_gates.contains_key(&lit.var()) {
        xor_depth_of_var(lit.var(), xor_gates, memo, visiting)
    } else {
        0
    }
}

fn logic_depth_of_var(
    var: Var,
    ts: &Transys,
    input_vars: &FxHashSet<Var>,
    latch_vars: &FxHashSet<Var>,
    memo: &mut FxHashMap<Var, usize>,
    visiting: &mut FxHashSet<Var>,
) -> usize {
    if var == Var::CONST || input_vars.contains(&var) || latch_vars.contains(&var) {
        return 0;
    }
    if let Some(&depth) = memo.get(&var) {
        return depth;
    }
    if !visiting.insert(var) {
        return 0;
    }

    let depth = ts.and_defs.get(&var).map_or(0, |&(rhs0, rhs1)| {
        1 + logic_depth_of_lit(rhs0, ts, input_vars, latch_vars, memo, visiting).max(
            logic_depth_of_lit(rhs1, ts, input_vars, latch_vars, memo, visiting),
        )
    });

    visiting.remove(&var);
    memo.insert(var, depth);
    depth
}

fn logic_depth_of_lit(
    lit: Lit,
    ts: &Transys,
    input_vars: &FxHashSet<Var>,
    latch_vars: &FxHashSet<Var>,
    memo: &mut FxHashMap<Var, usize>,
    visiting: &mut FxHashSet<Var>,
) -> usize {
    logic_depth_of_var(lit.var(), ts, input_vars, latch_vars, memo, visiting)
}

#[cfg(test)]
mod tests {
    use rustc_hash::FxHashMap;

    use crate::preprocess::substitution::rebuild_trans_clauses;
    use crate::sat_types::{Clause, Lit, Var};
    use crate::transys::Transys;

    use super::{analyze_circuit, compute_logic_depth, detect_carry_chains, detect_xor_gates};

    fn build_ts(
        max_var: u32,
        latch_vars: Vec<Var>,
        input_vars: Vec<Var>,
        next_state: FxHashMap<Var, Lit>,
        bad_lits: Vec<Lit>,
        constraint_lits: Vec<Lit>,
        and_defs: FxHashMap<Var, (Lit, Lit)>,
    ) -> Transys {
        Transys {
            max_var,
            num_latches: latch_vars.len(),
            num_inputs: input_vars.len(),
            latch_vars,
            input_vars,
            next_state,
            init_clauses: Vec::<Clause>::new(),
            trans_clauses: rebuild_trans_clauses(&and_defs),
            bad_lits,
            constraint_lits,
            and_defs,
            internal_signals: Vec::new(),
        }
    }

    fn fresh_var(next_var: &mut u32) -> Var {
        let var = Var(*next_var);
        *next_var += 1;
        var
    }

    fn insert_and(
        and_defs: &mut FxHashMap<Var, (Lit, Lit)>,
        next_var: &mut u32,
        lhs0: Lit,
        lhs1: Lit,
    ) -> Var {
        let out = fresh_var(next_var);
        and_defs.insert(out, (lhs0, lhs1));
        out
    }

    fn insert_or(
        and_defs: &mut FxHashMap<Var, (Lit, Lit)>,
        next_var: &mut u32,
        lhs0: Lit,
        lhs1: Lit,
    ) -> Var {
        insert_and(and_defs, next_var, !lhs0, !lhs1)
    }

    fn insert_xor(
        and_defs: &mut FxHashMap<Var, (Lit, Lit)>,
        next_var: &mut u32,
        a: Lit,
        b: Lit,
    ) -> Var {
        let t1 = insert_and(and_defs, next_var, a, !b);
        let t2 = insert_and(and_defs, next_var, !a, b);
        insert_and(and_defs, next_var, Lit::neg(t1), Lit::neg(t2))
    }

    #[test]
    fn detects_basic_half_adder_xor() {
        let a = Var(1);
        let b = Var(2);
        let sum = Var(3);
        let mut next_var = 4;
        let mut and_defs = FxHashMap::default();

        let xor_gate = insert_xor(&mut and_defs, &mut next_var, Lit::pos(a), Lit::pos(b));

        let mut next_state = FxHashMap::default();
        next_state.insert(sum, Lit::neg(xor_gate));

        let ts = build_ts(
            next_var - 1,
            vec![sum],
            vec![a, b],
            next_state,
            Vec::new(),
            Vec::new(),
            and_defs,
        );

        let xor_gates = detect_xor_gates(&ts);
        assert_eq!(xor_gates.len(), 1);
        assert_eq!(
            xor_gates.get(&xor_gate).copied(),
            Some((Lit::pos(a), Lit::pos(b)))
        );

        let analysis = analyze_circuit(&ts);
        assert_eq!(analysis.xor_count, 1);
        assert_eq!(analysis.xor_depth, 1);
        assert_eq!(analysis.max_logic_depth, 2);
        assert!(!analysis.has_carry_chain);
        assert!(analysis.is_arithmetic);
    }

    #[test]
    fn detects_xor_when_child_order_is_swapped() {
        let a = Var(1);
        let b = Var(2);
        let g = Var(5);
        let t1 = Var(3);
        let t2 = Var(4);

        let mut and_defs = FxHashMap::default();
        and_defs.insert(t1, (Lit::neg(b), Lit::pos(a)));
        and_defs.insert(t2, (Lit::pos(b), Lit::neg(a)));
        and_defs.insert(g, (Lit::neg(t1), Lit::neg(t2)));

        let ts = build_ts(
            5,
            Vec::new(),
            vec![a, b],
            FxHashMap::default(),
            vec![Lit::neg(g)],
            Vec::new(),
            and_defs,
        );

        let xor_gates = detect_xor_gates(&ts);
        assert_eq!(xor_gates.len(), 1);
        assert!(matches!(
            xor_gates.get(&g).copied(),
            Some((lhs, rhs))
                if (lhs, rhs) == (Lit::pos(a), Lit::pos(b))
                    || (lhs, rhs) == (Lit::neg(a), Lit::neg(b))
        ));
    }

    #[test]
    fn rejects_non_xor_patterns() {
        let a = Var(1);
        let b = Var(2);
        let g = Var(5);
        let t1 = Var(3);
        let t2 = Var(4);

        let mut and_defs = FxHashMap::default();
        and_defs.insert(t1, (Lit::pos(a), Lit::neg(b)));
        and_defs.insert(t2, (Lit::pos(a), Lit::pos(b)));
        and_defs.insert(g, (Lit::neg(t1), Lit::neg(t2)));

        let ts = build_ts(
            5,
            Vec::new(),
            vec![a, b],
            FxHashMap::default(),
            vec![Lit::neg(g)],
            Vec::new(),
            and_defs,
        );

        assert!(detect_xor_gates(&ts).is_empty());
        assert_eq!(analyze_circuit(&ts).xor_count, 0);
    }

    #[test]
    fn computes_nested_xor_depth_and_logic_depth() {
        let a = Var(1);
        let b = Var(2);
        let cin = Var(3);
        let sum = Var(4);
        let mut next_var = 5;
        let mut and_defs = FxHashMap::default();

        let xor_ab = insert_xor(&mut and_defs, &mut next_var, Lit::pos(a), Lit::pos(b));
        let xor_sum = insert_xor(
            &mut and_defs,
            &mut next_var,
            Lit::neg(xor_ab),
            Lit::pos(cin),
        );

        let mut next_state = FxHashMap::default();
        next_state.insert(sum, Lit::neg(xor_sum));

        let ts = build_ts(
            next_var - 1,
            vec![sum],
            vec![a, b, cin],
            next_state,
            Vec::new(),
            Vec::new(),
            and_defs,
        );

        let analysis = analyze_circuit(&ts);
        assert_eq!(analysis.xor_count, 2);
        assert_eq!(analysis.xor_depth, 2);
        assert_eq!(analysis.max_logic_depth, 4);
        assert!(!analysis.has_carry_chain);
    }

    #[test]
    fn single_full_adder_stage_is_not_a_chain() {
        let a = Var(1);
        let b = Var(2);
        let cin = Var(3);
        let carry = Var(4);
        let mut next_var = 5;
        let mut and_defs = FxHashMap::default();

        let xor_ab = insert_xor(&mut and_defs, &mut next_var, Lit::pos(a), Lit::pos(b));
        let mix = insert_and(
            &mut and_defs,
            &mut next_var,
            Lit::neg(xor_ab),
            Lit::pos(cin),
        );
        let generate = insert_and(&mut and_defs, &mut next_var, Lit::pos(a), Lit::pos(b));
        let carry_gate = insert_or(
            &mut and_defs,
            &mut next_var,
            Lit::pos(generate),
            Lit::pos(mix),
        );

        let mut next_state = FxHashMap::default();
        next_state.insert(carry, Lit::neg(carry_gate));

        let ts = build_ts(
            next_var - 1,
            vec![carry],
            vec![a, b, cin],
            next_state,
            Vec::new(),
            Vec::new(),
            and_defs,
        );

        let xor_gates = detect_xor_gates(&ts);
        assert!(!detect_carry_chains(&ts, &xor_gates));
        assert!(!analyze_circuit(&ts).has_carry_chain);
    }

    #[test]
    fn detects_two_stage_ripple_carry_chain() {
        let a0 = Var(1);
        let b0 = Var(2);
        let cin = Var(3);
        let a1 = Var(4);
        let b1 = Var(5);
        let sum = Var(6);
        let cout = Var(7);
        let mut next_var = 8;
        let mut and_defs = FxHashMap::default();

        let xor0 = insert_xor(&mut and_defs, &mut next_var, Lit::pos(a0), Lit::pos(b0));
        let mix0 = insert_and(&mut and_defs, &mut next_var, Lit::neg(xor0), Lit::pos(cin));
        let gen0 = insert_and(&mut and_defs, &mut next_var, Lit::pos(a0), Lit::pos(b0));
        let carry0_gate = insert_or(&mut and_defs, &mut next_var, Lit::pos(gen0), Lit::pos(mix0));
        let carry0 = Lit::neg(carry0_gate);

        let xor1 = insert_xor(&mut and_defs, &mut next_var, Lit::pos(a1), Lit::pos(b1));
        let mix1 = insert_and(&mut and_defs, &mut next_var, Lit::neg(xor1), carry0);
        let gen1 = insert_and(&mut and_defs, &mut next_var, Lit::pos(a1), Lit::pos(b1));
        let carry1_gate = insert_or(&mut and_defs, &mut next_var, Lit::pos(gen1), Lit::pos(mix1));
        let sum1 = insert_xor(&mut and_defs, &mut next_var, Lit::neg(xor1), carry0);

        let mut next_state = FxHashMap::default();
        next_state.insert(sum, Lit::neg(sum1));
        next_state.insert(cout, Lit::neg(carry1_gate));

        let ts = build_ts(
            next_var - 1,
            vec![sum, cout],
            vec![a0, b0, cin, a1, b1],
            next_state,
            Vec::new(),
            Vec::new(),
            and_defs,
        );

        let analysis = analyze_circuit(&ts);
        assert_eq!(analysis.xor_count, 3);
        assert_eq!(analysis.xor_depth, 2);
        assert_eq!(analysis.max_logic_depth, 6);
        assert!(analysis.has_carry_chain);
        assert!(analysis.is_arithmetic);
    }

    #[test]
    fn logic_depth_falls_back_to_bad_literals_for_combinational_circuits() {
        let a = Var(1);
        let b = Var(2);
        let mut next_var = 3;
        let mut and_defs = FxHashMap::default();

        let xor_gate = insert_xor(&mut and_defs, &mut next_var, Lit::pos(a), Lit::pos(b));
        let ts = build_ts(
            next_var - 1,
            Vec::new(),
            vec![a, b],
            FxHashMap::default(),
            vec![Lit::neg(xor_gate)],
            Vec::new(),
            and_defs,
        );

        assert_eq!(compute_logic_depth(&ts), 2);
    }
}
