// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Internal-signal latch promotion ("inn-proper", FMCAD'21).
//!
//! Promotes AND-gate outputs that are pure functions of latches (i.e., do not
//! depend on primary inputs) to first-class latches. The transition relation
//! is extended with a 1-step unrolled definition so the new latches have
//! proper next-state functions.
//!
//! This is structurally different from the cube-extension variant of `--inn`
//! (see `Transys::select_internal_signals`), which keeps internal signals as
//! gates but exposes them to MIC for cube generalization only. With
//! `inn-proper`, IC3 frames are clauses over the richer state basis
//! `latches ∪ promoted_signals`, producing structurally smaller inductive
//! invariants on arithmetic-heavy circuits.
//!
//! Reference: rIC3 `src/transys/unroll.rs:301-338` (`internal_signals()`).
//! Issue: #4308.

use rustc_hash::{FxHashMap, FxHashSet};

use crate::sat_types::{Clause, Lit, Var};
use crate::transys::Transys;

/// Build a new `Transys` where internal signals (AND-gate outputs that do not
/// depend on primary inputs) become first-class latches with a next-state
/// derived from the 1-step unrolled relation.
///
/// Returns the transformed Transys. If no signals qualify for promotion, the
/// original Transys is returned unchanged.
pub(crate) fn promote_internal_signals_to_latches(ts: &Transys) -> Transys {
    // 1. Compute input_fanout: vars reachable forward from inputs via and_defs.
    //    Anything NOT in this set is a pure function of latches and constants.
    let input_fanout = compute_input_fanout(ts);

    // 2. Identify AND-gate outputs to promote: in and_defs but not input_fanout
    //    and not already a latch. We keep constants out.
    let latch_set: FxHashSet<Var> = ts.latch_vars.iter().copied().collect();
    let mut to_promote: Vec<Var> = Vec::new();
    for &g in ts.and_defs.keys() {
        if input_fanout.contains(&g) {
            continue;
        }
        if latch_set.contains(&g) {
            continue;
        }
        if g == Var::CONST {
            continue;
        }
        to_promote.push(g);
    }
    to_promote.sort_by_key(|v| v.0);

    // Early exit if nothing to promote.
    if to_promote.is_empty() {
        return ts.clone();
    }

    // 3. Build step-1 variable mapping:
    //    - Var(0) / constants: map to themselves (constants are invariant).
    //    - Inputs: fresh variables (inputs at step 1 are unconstrained).
    //    - Input-fanout gates: fresh variables (computed from step-1 inputs).
    //    - Latches: map to their next-state literal's var (with polarity tracked on lit).
    //    - Promoted (non-input-fanout) gates: map to themselves (pure function of latches; at step 1 equals g evaluated with latches' next-state, which is just g's original definition evaluated at next-state latch values — but since the AND-gate Tseitin already defines g in terms of its inputs, and those inputs at step 1 are either step-1 input vars, step-1 fanout gates, or next-state latch lits, the step-1 definition of g needs fresh Tseitin clauses).
    //
    //    For simplicity and to match rIC3 structure, we allocate fresh vars for
    //    ALL non-latch variables at step 1, then emit Tseitin clauses that link
    //    the step-1 copies to the step-1 definitions.

    let mut max_var = ts.max_var;
    // step1_var[v] = step-1 variable for var v. For latches, we use the next-state
    //                literal's var (polarity handled via step1_lit()).
    // For constants, step1_var[0] = Var(0).
    let mut step1_var: FxHashMap<Var, Var> = FxHashMap::default();
    // step1_polarity_flip[v] = true if step-1 version of var v has inverted polarity
    //                          relative to the step-0 var (only possible for latches
    //                          whose next-state literal is negated).
    let mut step1_polarity_flip: FxHashMap<Var, bool> = FxHashMap::default();

    step1_var.insert(Var::CONST, Var::CONST);
    step1_polarity_flip.insert(Var::CONST, false);

    // Latches: map to their next-state literal's var.
    for &latch in &ts.latch_vars {
        if let Some(&next_lit) = ts.next_state.get(&latch) {
            step1_var.insert(latch, next_lit.var());
            step1_polarity_flip.insert(latch, next_lit.is_negated());
        } else {
            // Latch without next-state: self-map (shouldn't happen for
            // well-formed AIGER circuits, but handle defensively).
            step1_var.insert(latch, latch);
            step1_polarity_flip.insert(latch, false);
        }
    }

    // Inputs: allocate fresh step-1 variables.
    for &inp in &ts.input_vars {
        max_var += 1;
        step1_var.insert(inp, Var(max_var));
        step1_polarity_flip.insert(inp, false);
    }

    // All remaining vars in the circuit (AND-gate outputs, including those to promote):
    // allocate fresh step-1 variables. The Tseitin clauses linking step-1 vars to
    // their step-1 definitions are emitted next.
    for &g in ts.and_defs.keys() {
        if step1_var.contains_key(&g) {
            continue;
        }
        max_var += 1;
        step1_var.insert(g, Var(max_var));
        step1_polarity_flip.insert(g, false);
    }

    // Helper: rename a step-0 literal to its step-1 equivalent.
    let step1_lit = |l: Lit| -> Lit {
        if l == Lit::FALSE {
            return Lit::FALSE;
        }
        if l == Lit::TRUE {
            return Lit::TRUE;
        }
        let v = l.var();
        let new_var = step1_var.get(&v).copied().unwrap_or(v);
        let new_flip = step1_polarity_flip.get(&v).copied().unwrap_or(false);
        // Effective polarity: original polarity XOR polarity_flip.
        let negated = l.is_negated() ^ new_flip;
        if negated {
            Lit::neg(new_var)
        } else {
            Lit::pos(new_var)
        }
    };

    // 4. Build the new transys.
    let mut new_trans_clauses = ts.trans_clauses.clone();
    let mut new_and_defs = ts.and_defs.clone();
    let mut new_next_state = ts.next_state.clone();
    let mut new_latch_vars = ts.latch_vars.clone();

    // Emit step-1 Tseitin clauses for each AND-gate g to define step1_lit(g):
    //   step1(g) <=> step1(rhs0) AND step1(rhs1)
    // Skip latches (their step-1 is already defined via next_state linking, which
    // is implicit in the existing trans_clauses).
    //
    // For input-fanout gates, we need these Tseitin clauses because step1(g) is a
    // fresh variable used by the promoted signals' next-state via transitive deps.
    // For non-input-fanout gates (promoted or otherwise), we also need them.
    for (&g, &(rhs0, rhs1)) in &ts.and_defs {
        let g_step1 = step1_lit(Lit::pos(g));
        let a_step1 = step1_lit(rhs0);
        let b_step1 = step1_lit(rhs1);
        // Tseitin: g <=> a AND b
        //   (!g OR a), (!g OR b), (!a OR !b OR g)
        new_trans_clauses.push(Clause::binary(!g_step1, a_step1));
        new_trans_clauses.push(Clause::binary(!g_step1, b_step1));
        new_trans_clauses.push(Clause::new(vec![!a_step1, !b_step1, g_step1]));
    }

    // Track promoted signals in and_defs: add step-1 versions as new AND defs if
    // they are fresh allocated vars (this keeps and_defs accurate for downstream
    // analysis like COI).
    for (&g, &(rhs0, rhs1)) in &ts.and_defs {
        let g_s1_var = step1_var[&g];
        if g_s1_var == g {
            continue;
        }
        // Only insert if not already present (latches may share var space with gates
        // via next_state mapping).
        new_and_defs.entry(g_s1_var).or_insert_with(|| {
            let a_s1 = step1_lit(rhs0);
            let b_s1 = step1_lit(rhs1);
            // step1_polarity_flip on g may have inverted polarity — but since
            // we allocated fresh vars here (not coming from latch next-state),
            // the flip is false and the step-1 definition is direct AND.
            (a_s1, b_s1)
        });
    }

    // Promote: for each signal to promote, add it as a latch with next = step1_lit(g).
    for &g in &to_promote {
        new_latch_vars.push(g);
        let next = step1_lit(Lit::pos(g));
        new_next_state.insert(g, next);
    }

    // Initial state: the promoted signals' initial values are determined by their
    // AND-gate definitions evaluated at the initial latch values. The existing
    // trans_clauses already contain these Tseitin definitions at step 0, so IC3's
    // init query (Init ∧ Trans) will correctly bind g to its AND value.
    //
    // No explicit init clauses are added for promoted signals (matches rIC3).

    let num_latches = new_latch_vars.len();
    Transys {
        max_var,
        num_latches,
        num_inputs: ts.num_inputs,
        latch_vars: new_latch_vars,
        input_vars: ts.input_vars.clone(),
        next_state: new_next_state,
        init_clauses: ts.init_clauses.clone(),
        trans_clauses: new_trans_clauses,
        bad_lits: ts.bad_lits.clone(),
        constraint_lits: ts.constraint_lits.clone(),
        and_defs: new_and_defs,
        internal_signals: Vec::new(),
    }
}

/// Compute the set of variables reachable forward from primary inputs via
/// the AND-gate dependency graph. This is rIC3's `rel.fanouts(input())`:
/// a variable `v` is in the result iff `v` is an input, or `v` is an AND-gate
/// output and at least one of its operands (or transitively) is in the result.
///
/// Runs in O((V + E) * iterations) where iterations is bounded by the circuit
/// depth. Uses iterative worklist until fixpoint.
fn compute_input_fanout(ts: &Transys) -> FxHashSet<Var> {
    let mut in_fanout: FxHashSet<Var> = ts.input_vars.iter().copied().collect();

    // Build reverse-edge map: for each operand var, which AND gates consume it?
    let mut consumers: FxHashMap<Var, Vec<Var>> = FxHashMap::default();
    for (&out, &(rhs0, rhs1)) in &ts.and_defs {
        consumers.entry(rhs0.var()).or_default().push(out);
        consumers.entry(rhs1.var()).or_default().push(out);
    }

    // BFS from inputs forward through consumers.
    let mut worklist: Vec<Var> = in_fanout.iter().copied().collect();
    while let Some(v) = worklist.pop() {
        if let Some(consumers_of_v) = consumers.get(&v) {
            for &out in consumers_of_v {
                if in_fanout.insert(out) {
                    worklist.push(out);
                }
            }
        }
    }

    in_fanout
}

/// Count the number of internal signals eligible for promotion without
/// actually building the promoted transys. Useful for diagnostics and
/// portfolio config heuristics.
#[allow(dead_code)]
pub(crate) fn count_promotable_signals(ts: &Transys) -> usize {
    let input_fanout = compute_input_fanout(ts);
    let latch_set: FxHashSet<Var> = ts.latch_vars.iter().copied().collect();
    ts.and_defs
        .keys()
        .filter(|&&g| !input_fanout.contains(&g) && !latch_set.contains(&g) && g != Var::CONST)
        .count()
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse_aag;

    #[test]
    fn test_promote_no_candidates_returns_clone() {
        // Simple circuit: 1 input, 1 latch, 1 AND gate (g = input AND latch).
        // The AND gate depends on input, so it's in input_fanout — no promotion.
        let aag = "aag 3 1 1 0 1 1\n2\n4 6\n6\n6 2 4\n";
        let circuit = parse_aag(aag).unwrap();
        let ts = Transys::from_aiger(&circuit);
        let original_max_var = ts.max_var;
        let original_latches = ts.num_latches;

        let promoted = promote_internal_signals_to_latches(&ts);
        assert_eq!(promoted.max_var, original_max_var);
        assert_eq!(promoted.num_latches, original_latches);
    }

    #[test]
    fn test_promote_promotes_latch_only_gate() {
        // Circuit: 0 inputs, 2 latches (l1, l2), 1 AND gate g = l1 AND l2.
        // Bad = g. The AND gate depends only on latches, so it's promotable.
        //
        // AAG header: M=3 I=0 L=2 O=0 A=1 B=1
        // Latch 1 (lit 2): next = lit 3 (= !l1). Initial = 0.
        // Latch 2 (lit 4): next = lit 5 (= !l2). Initial = 0.
        // AND gate: lhs=6 (var 3), rhs0=2, rhs1=4.
        // Bad: lit 6.
        let aag = "aag 3 0 2 0 1 1\n2 3\n4 5\n6\n6 2 4\n";
        let circuit = parse_aag(aag).unwrap();
        let ts = Transys::from_aiger(&circuit);
        assert_eq!(ts.num_latches, 2);
        assert_eq!(ts.and_defs.len(), 1);
        assert_eq!(count_promotable_signals(&ts), 1);

        let promoted = promote_internal_signals_to_latches(&ts);
        assert_eq!(promoted.num_latches, 3); // 2 original + 1 promoted signal
        assert!(promoted.latch_vars.contains(&Var(3))); // g = var 3
        assert!(promoted.next_state.contains_key(&Var(3)));
        // Next-state for g should not be the same var as g itself (it's the step-1 rewrite).
        let g_next = promoted.next_state[&Var(3)];
        assert_ne!(g_next.var(), Var(3));
        // Max var must have grown (fresh step-1 vars were allocated for inputs/gates).
        assert!(promoted.max_var > ts.max_var);
        // trans_clauses must have grown (step-1 Tseitin clauses were added).
        assert!(promoted.trans_clauses.len() > ts.trans_clauses.len());
    }

    #[test]
    fn test_compute_input_fanout_includes_input_derived_gates() {
        // Circuit: 1 input, 1 latch, 1 AND gate g = input AND latch.
        let aag = "aag 3 1 1 0 1 1\n2\n4 6\n6\n6 2 4\n";
        let circuit = parse_aag(aag).unwrap();
        let ts = Transys::from_aiger(&circuit);
        let fanout = compute_input_fanout(&ts);
        assert!(fanout.contains(&Var(1))); // input
        assert!(fanout.contains(&Var(3))); // AND gate (depends on input)
    }

    #[test]
    fn test_compute_input_fanout_excludes_pure_latch_gates() {
        // Circuit: 0 inputs, 2 latches, 1 AND gate g = l1 AND l2.
        let aag = "aag 3 0 2 0 1 1\n2 3\n4 5\n6\n6 2 4\n";
        let circuit = parse_aag(aag).unwrap();
        let ts = Transys::from_aiger(&circuit);
        let fanout = compute_input_fanout(&ts);
        assert!(!fanout.contains(&Var(3))); // g doesn't depend on any input (there are none)
    }

    #[test]
    fn test_promote_transys_preserves_bad_and_constraints() {
        let aag = "aag 3 0 2 0 1 1\n2 3\n4 5\n6\n6 2 4\n";
        let circuit = parse_aag(aag).unwrap();
        let ts = Transys::from_aiger(&circuit);
        let promoted = promote_internal_signals_to_latches(&ts);
        assert_eq!(promoted.bad_lits, ts.bad_lits);
        assert_eq!(promoted.constraint_lits, ts.constraint_lits);
        assert_eq!(promoted.init_clauses, ts.init_clauses);
        assert_eq!(promoted.num_inputs, ts.num_inputs);
    }
}
