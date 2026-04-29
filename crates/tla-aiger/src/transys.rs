// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Transition system: CNF encoding of an AIGER circuit for SAT-based
//! model checking (BMC, k-induction, IC3).
//!
//! Converts an `AigerCircuit` into a `Transys` with:
//! - `init_clauses`: CNF encoding of initial state constraints
//! - `trans_clauses`: CNF encoding of the transition relation (AND gates + latch next-state)
//! - `bad_lits`: literals representing bad-state properties
//! - Variable mappings for time-step unrolling

use rustc_hash::FxHashMap;

use crate::sat_types::{Clause, Lit, SatSolver, Var};
use crate::types::{aiger_is_negated, aiger_var, AigerCircuit};

/// A transition system in CNF form, derived from an AIGER circuit.
#[derive(Debug, Clone)]
pub struct Transys {
    /// Maximum variable index used (all vars are in 1..=max_var).
    pub max_var: u32,

    /// Number of state (latch) variables.
    pub num_latches: usize,

    /// Number of input variables.
    pub num_inputs: usize,

    /// Latch variables (current state).
    pub latch_vars: Vec<Var>,

    /// Input variables.
    pub input_vars: Vec<Var>,

    /// Mapping from latch current-state var to next-state literal.
    pub next_state: FxHashMap<Var, Lit>,

    /// Initial-state clauses: constraints on latch values at time 0.
    pub init_clauses: Vec<Clause>,

    /// Transition relation clauses: AND gate definitions + next-state wiring.
    /// These are the Tseitin encoding of the combinational logic.
    pub trans_clauses: Vec<Clause>,

    /// Bad-state literals (properties to check). If any is reachable, circuit is UNSAFE.
    pub bad_lits: Vec<Lit>,

    /// Constraint literals (environment assumptions). Conjoined with transition relation.
    pub constraint_lits: Vec<Lit>,

    /// AND gate variable definitions: maps AND output var to (rhs0_lit, rhs1_lit).
    /// Used for cone-of-influence analysis and unrolling.
    pub and_defs: FxHashMap<Var, (Lit, Lit)>,

    /// Internal signals: AND gate outputs selected for use in IC3 cubes/lemmas.
    ///
    /// From FMCAD'21: using AND gate outputs as additional cube variables
    /// improves generalization — cubes over internal signals are shorter and
    /// more general than cubes over latches alone.
    pub(crate) internal_signals: Vec<Var>,
}

impl Transys {
    /// Build a transition system from a parsed AIGER circuit.
    pub fn from_aiger(circuit: &AigerCircuit) -> Self {
        let max_var = circuit.maxvar as u32;

        // Map AIGER literal to our Lit type.
        // AIGER: var = lit/2, negated = lit%2. Var 0 = constant.
        // Our Lit: same encoding (var*2 + sign), but Var is 1-indexed for variables,
        // and Var(0) is constant FALSE.
        let aiger_to_lit = |aiger_lit: u64| -> Lit {
            if aiger_lit == 0 {
                return Lit::FALSE; // constant 0
            }
            if aiger_lit == 1 {
                return Lit::TRUE; // constant 1 (negated FALSE var)
            }
            let var = aiger_var(aiger_lit) as u32;
            if aiger_is_negated(aiger_lit) {
                Lit::neg(Var(var))
            } else {
                Lit::pos(Var(var))
            }
        };

        // Collect variables
        let input_vars: Vec<Var> = circuit
            .inputs
            .iter()
            .map(|inp| Var(aiger_var(inp.lit) as u32))
            .collect();

        let latch_vars: Vec<Var> = circuit
            .latches
            .iter()
            .map(|l| Var(aiger_var(l.lit) as u32))
            .collect();

        // Next-state mapping
        let mut next_state = FxHashMap::default();
        for latch in &circuit.latches {
            let curr_var = Var(aiger_var(latch.lit) as u32);
            let next_lit = aiger_to_lit(latch.next);
            next_state.insert(curr_var, next_lit);
        }

        // Initial state clauses
        let mut init_clauses = Vec::new();
        for latch in &circuit.latches {
            let curr_var = Var(aiger_var(latch.lit) as u32);
            if latch.reset == latch.lit {
                // Nondeterministic reset: no constraint
                continue;
            }
            if latch.reset == 0 {
                // Reset to 0: assert !latch
                init_clauses.push(Clause::unit(Lit::neg(curr_var)));
            } else if latch.reset == 1 {
                // Reset to 1: assert latch
                init_clauses.push(Clause::unit(Lit::pos(curr_var)));
            } else {
                // Reset to another literal's value
                let reset_lit = aiger_to_lit(latch.reset);
                // curr_var <=> reset_lit
                // Encoded as: (curr_var -> reset_lit) AND (reset_lit -> curr_var)
                // = (!curr_var OR reset_lit) AND (!reset_lit OR curr_var)
                init_clauses.push(Clause::binary(Lit::neg(curr_var), reset_lit));
                init_clauses.push(Clause::binary(!reset_lit, Lit::pos(curr_var)));
            }
        }

        // Transition relation: Tseitin encoding of AND gates
        let mut trans_clauses = Vec::new();
        let mut and_defs = FxHashMap::default();

        for gate in &circuit.ands {
            let out_var = Var(aiger_var(gate.lhs) as u32);
            let rhs0 = aiger_to_lit(gate.rhs0);
            let rhs1 = aiger_to_lit(gate.rhs1);

            and_defs.insert(out_var, (rhs0, rhs1));

            let out = Lit::pos(out_var);

            // Tseitin encoding of out = rhs0 AND rhs1:
            // (out -> rhs0): !out OR rhs0
            // (out -> rhs1): !out OR rhs1
            // (rhs0 AND rhs1 -> out): !rhs0 OR !rhs1 OR out
            trans_clauses.push(Clause::binary(!out, rhs0));
            trans_clauses.push(Clause::binary(!out, rhs1));
            trans_clauses.push(Clause::new(vec![!rhs0, !rhs1, out]));
        }

        // Bad-state literals
        let bad_lits: Vec<Lit> = if !circuit.bad.is_empty() {
            circuit.bad.iter().map(|b| aiger_to_lit(b.lit)).collect()
        } else {
            circuit
                .outputs
                .iter()
                .map(|o| aiger_to_lit(o.lit))
                .collect()
        };

        // Constraint literals
        let constraint_lits: Vec<Lit> = circuit
            .constraints
            .iter()
            .map(|c| aiger_to_lit(c.lit))
            .collect();

        Transys {
            max_var,
            num_latches: latch_vars.len(),
            num_inputs: input_vars.len(),
            latch_vars,
            input_vars,
            next_state,
            init_clauses,
            trans_clauses,
            bad_lits,
            constraint_lits,
            and_defs,
            internal_signals: Vec::new(),
        }
    }

    /// Select AND gate outputs as internal signals for IC3 cubes.
    ///
    /// An AND gate output is selected if it appears in at least 2 different
    /// latch next-state functions (fanout >= 2). Gates with high fanout to
    /// next-state logic capture "interesting" state shared across latches.
    ///
    /// Capped at `max(50, num_latches / 2)` to avoid blowup.
    pub(crate) fn select_internal_signals(&mut self) {
        // Skip for small circuits — overhead outweighs benefit.
        if self.num_latches < 20 {
            return;
        }

        use rustc_hash::FxHashSet;

        let latch_set: FxHashSet<Var> = self.latch_vars.iter().copied().collect();
        let mut fanout_count: FxHashMap<Var, usize> = FxHashMap::default();

        for &next_lit in self.next_state.values() {
            let mut seen = FxHashSet::default();
            let mut stack = vec![next_lit.var()];
            while let Some(v) = stack.pop() {
                if !seen.insert(v) {
                    continue;
                }
                if latch_set.contains(&v) {
                    continue;
                }
                if self.and_defs.contains_key(&v) {
                    *fanout_count.entry(v).or_insert(0) += 1;
                    if let Some(&(rhs0, rhs1)) = self.and_defs.get(&v) {
                        stack.push(rhs0.var());
                        stack.push(rhs1.var());
                    }
                }
            }
        }

        let mut candidates: Vec<(Var, usize)> = fanout_count
            .into_iter()
            .filter(|&(_, count)| count >= 2)
            .collect();
        candidates.sort_by(|a, b| b.1.cmp(&a.1));

        let cap = 50usize.max(self.num_latches / 2);
        candidates.truncate(cap);

        self.internal_signals = candidates.into_iter().map(|(v, _)| v).collect();
    }

    /// Load initial state clauses into a SAT solver.
    pub fn load_init(&self, solver: &mut dyn SatSolver) {
        solver.ensure_vars(self.max_var);
        for clause in &self.init_clauses {
            solver.add_clause(&clause.lits);
        }
    }

    /// Load transition relation clauses into a SAT solver with variable renaming.
    /// `rename` maps a Lit from the base encoding to the target time step.
    ///
    /// Uses a reusable buffer to avoid per-clause allocation. The transition
    /// relation has 3 clauses per AND gate (2 binary + 1 ternary), so for
    /// circuits with hundreds of gates this saves thousands of allocations
    /// per BMC step.
    pub fn load_trans_renamed(&self, solver: &mut dyn SatSolver, rename: &dyn Fn(Lit) -> Lit) {
        let mut buf = Vec::with_capacity(8); // most clauses are 2-3 lits
        for clause in &self.trans_clauses {
            buf.clear();
            buf.extend(clause.lits.iter().map(|&l| rename(l)));
            solver.add_clause(&buf);
        }
        // Also add constraint literals as unit clauses
        for &c in &self.constraint_lits {
            solver.add_clause(&[rename(c)]);
        }
    }

    /// Get the combined bad-state literal (OR of all bad properties).
    /// If there's one bad lit, returns it directly.
    /// If there are multiple, creates auxiliary variables in the solver.
    pub fn get_bad_lit(&self, solver: &mut dyn SatSolver) -> Lit {
        match self.bad_lits.len() {
            0 => Lit::FALSE, // No bad states
            1 => self.bad_lits[0],
            _ => {
                // Create OR of all bad lits: bad_combined = bad_0 OR bad_1 OR ...
                // Tseitin: bad_combined -> (bad_0 OR bad_1 OR ...)
                //          each bad_i -> bad_combined
                let combined = solver.new_var();
                let combined_lit = Lit::pos(combined);

                // combined -> (bad_0 OR ... OR bad_n)
                let mut disj = self.bad_lits.clone();
                disj.push(!combined_lit);
                solver.add_clause(&disj);

                // each bad_i -> combined
                for &bad in &self.bad_lits {
                    solver.add_clause(&[!bad, combined_lit]);
                }

                combined_lit
            }
        }
    }

    /// Verify a BMC witness trace against the transition system.
    ///
    /// Simulates the circuit step by step using the given trace of latch and
    /// input values. Returns `Ok(())` if the trace is a valid counterexample
    /// (reaches a bad state), or `Err(reason)` if the trace is invalid.
    ///
    /// This is a soundness check: if BMC claims UNSAFE with a witness, we can
    /// verify the witness by pure simulation without the SAT solver.
    pub fn verify_witness(&self, trace: &[FxHashMap<String, bool>]) -> Result<(), String> {
        if trace.is_empty() {
            return Err("empty trace".into());
        }

        // Build variable assignment from latch/input values at a given step
        let build_assignment = |step: &FxHashMap<String, bool>| -> FxHashMap<Var, bool> {
            let mut assign = FxHashMap::default();
            // Var(0) is always false (constant)
            assign.insert(Var(0), false);
            for (idx, &latch_var) in self.latch_vars.iter().enumerate() {
                if let Some(&val) = step.get(&format!("l{idx}")) {
                    assign.insert(latch_var, val);
                }
            }
            for (idx, &input_var) in self.input_vars.iter().enumerate() {
                if let Some(&val) = step.get(&format!("i{idx}")) {
                    assign.insert(input_var, val);
                }
            }
            assign
        };

        // Evaluate a literal given an assignment
        let eval_lit = |lit: Lit, assign: &FxHashMap<Var, bool>| -> Option<bool> {
            if lit == Lit::FALSE {
                return Some(false);
            }
            if lit == Lit::TRUE {
                return Some(true);
            }
            let val = assign.get(&lit.var()).copied()?;
            if lit.is_negated() {
                Some(!val)
            } else {
                Some(val)
            }
        };

        // Evaluate all AND gates given current assignments, adding results.
        // Uses topological evaluation: iterate until fixpoint.
        let eval_gates = |assign: &mut FxHashMap<Var, bool>| {
            let mut changed = true;
            while changed {
                changed = false;
                for (&out_var, &(rhs0, rhs1)) in &self.and_defs {
                    if assign.contains_key(&out_var) {
                        continue;
                    }
                    if let (Some(v0), Some(v1)) = (eval_lit(rhs0, assign), eval_lit(rhs1, assign)) {
                        assign.insert(out_var, v0 && v1);
                        changed = true;
                    }
                }
            }
        };

        // Step 0: verify init constraints
        let mut assign = build_assignment(&trace[0]);
        eval_gates(&mut assign);
        for clause in &self.init_clauses {
            let satisfied = clause
                .lits
                .iter()
                .any(|&lit| eval_lit(lit, &assign).unwrap_or(false));
            if !satisfied {
                return Err(format!("init clause violated at step 0: {:?}", clause));
            }
        }

        // For each step, evaluate gates and check constraints
        for k in 0..trace.len() {
            let mut assign = build_assignment(&trace[k]);
            eval_gates(&mut assign);

            // Check transition relation clauses at this step (#4103).
            //
            // This is a stronger check than eval_gates alone: after BVE
            // preprocessing, trans_clauses may contain resolved clauses that
            // don't correspond to any single AND gate in and_defs. Checking
            // all trans_clauses ensures the witness is consistent with the
            // full CNF encoding, not just the structural AND-gate definitions.
            for (ci, clause) in self.trans_clauses.iter().enumerate() {
                // A clause is satisfied if at least one literal evaluates to true.
                // If a literal's variable is unassigned (not in the trace and not
                // evaluable via AND gates), we conservatively treat the clause as
                // potentially satisfied — only flag a violation when ALL literals
                // are definitively false.
                let all_determined = clause
                    .lits
                    .iter()
                    .all(|&lit| eval_lit(lit, &assign).is_some());
                if all_determined {
                    let satisfied = clause
                        .lits
                        .iter()
                        .any(|&lit| eval_lit(lit, &assign).unwrap_or(false));
                    if !satisfied {
                        return Err(format!(
                            "trans clause {} violated at step {k}: {:?} \
                             (all lits evaluable but none true)",
                            ci, clause
                        ));
                    }
                }
            }

            // Check constraints at this step
            for &constraint_lit in &self.constraint_lits {
                let val = eval_lit(constraint_lit, &assign).unwrap_or(false);
                if !val {
                    return Err(format!(
                        "constraint violated at step {k}: {constraint_lit:?} is false"
                    ));
                }
            }

            // At the last step, check if bad is true
            if k == trace.len() - 1 {
                let bad_true = self
                    .bad_lits
                    .iter()
                    .any(|&bad_lit| eval_lit(bad_lit, &assign).unwrap_or(false));
                if !bad_true {
                    return Err(format!("bad state NOT reached at final step {k}"));
                }
            }

            // If not the last step, verify latch values at step k+1 match
            // the next-state function evaluated at step k
            if k + 1 < trace.len() {
                let next_assign = build_assignment(&trace[k + 1]);
                for (idx, &latch_var) in self.latch_vars.iter().enumerate() {
                    if let Some(&next_lit) = self.next_state.get(&latch_var) {
                        let expected = eval_lit(next_lit, &assign);
                        let actual = next_assign.get(&latch_var).copied();
                        if let (Some(exp), Some(act)) = (expected, actual) {
                            if exp != act {
                                return Err(format!(
                                    "latch l{idx} (Var({})) at step {} has value {}, \
                                     but next-state from step {} evaluates to {}",
                                    latch_var.0,
                                    k + 1,
                                    act,
                                    k,
                                    exp
                                ));
                            }
                        }
                    }
                }
            }
        }

        Ok(())
    }

    /// Verify an inductive invariant for the safety property (#4216).
    ///
    /// Given a set of CNF lemmas claimed to form an inductive invariant, this
    /// method independently checks the three standard conditions:
    ///
    /// 1. **Init => Inv** — every initial state satisfies the invariant.
    /// 2. **Inv AND T => Inv'** — the invariant is preserved by the transition relation.
    /// 3. **Inv => !Bad** — the invariant implies safety (no bad state is reachable).
    ///
    /// This is a standalone portfolio-level defense-in-depth check. It uses
    /// fresh solvers completely independent of the IC3 engine that produced the
    /// lemmas. If any check fails, the invariant is unsound and the Safe result
    /// should be demoted to Unknown.
    ///
    /// Returns `Ok(())` if all checks pass, or `Err(reason)` describing the failure.
    pub fn verify_safe_invariant(&self, lemmas: &[Vec<Lit>]) -> Result<(), String> {
        use crate::sat_types::{SatResult, SimpleSolver};

        if lemmas.is_empty() {
            // Degenerate case: no lemmas means the property is trivially true
            // (bad = constant FALSE or no bad lits). Nothing to validate.
            return Ok(());
        }

        // Build next-state variable mapping (mirrors IC3 engine construction).
        let mut next_var_id = self.max_var + 1;
        let mut next_vars: FxHashMap<Var, Var> = FxHashMap::default();
        for &latch_var in &self.latch_vars {
            next_vars.insert(latch_var, Var(next_var_id));
            next_var_id += 1;
        }

        // Build next-state linking clauses: next_var <=> next_state_expr.
        let mut next_link_clauses: Vec<Vec<Lit>> = Vec::new();
        for &latch_var in &self.latch_vars {
            if let (Some(&next_var), Some(&next_expr)) =
                (next_vars.get(&latch_var), self.next_state.get(&latch_var))
            {
                let nv_pos = Lit::pos(next_var);
                let nv_neg = Lit::neg(next_var);
                next_link_clauses.push(vec![nv_neg, next_expr]);
                next_link_clauses.push(vec![nv_pos, !next_expr]);
            }
        }

        // Check 1: Init => Inv
        // For each lemma, verify that Init AND !lemma is UNSAT.
        {
            let mut init_solver = SimpleSolver::new();
            init_solver.add_clause(&[Lit::TRUE]);
            for clause in &self.init_clauses {
                init_solver.add_clause(&clause.lits);
            }
            for clause in &self.trans_clauses {
                init_solver.add_clause(&clause.lits);
            }
            for &constraint in &self.constraint_lits {
                init_solver.add_clause(&[constraint]);
            }

            for (i, lemma) in lemmas.iter().enumerate() {
                let neg_lits: Vec<Lit> = lemma.iter().map(|l| !*l).collect();
                if init_solver.solve(&neg_lits) == SatResult::Sat {
                    return Err(format!(
                        "Init => Inv FAILED: initial state does not satisfy lemma {} ({} lits)",
                        i,
                        lemma.len(),
                    ));
                }
            }
        }

        // Check 2: Inv AND T => Inv'
        // Build solver with: Trans + constraints + next-linking + all lemmas.
        // For each lemma, verify that Inv AND T AND !lemma' is UNSAT.
        {
            let mut trans_solver = SimpleSolver::new();
            trans_solver.add_clause(&[Lit::TRUE]);
            for clause in &self.trans_clauses {
                trans_solver.add_clause(&clause.lits);
            }
            for &constraint in &self.constraint_lits {
                trans_solver.add_clause(&[constraint]);
            }
            for clause in &next_link_clauses {
                trans_solver.add_clause(clause);
            }
            // Assert all lemmas in the current state.
            for lemma in lemmas {
                trans_solver.add_clause(lemma);
            }

            for (i, lemma) in lemmas.iter().enumerate() {
                // Negate the primed version of this lemma.
                let neg_primed: Vec<Lit> = lemma
                    .iter()
                    .map(|l| {
                        let var = l.var();
                        if let Some(&next_var) = next_vars.get(&var) {
                            if l.is_positive() {
                                Lit::neg(next_var)
                            } else {
                                Lit::pos(next_var)
                            }
                        } else {
                            // Variable not a latch — negate directly.
                            !*l
                        }
                    })
                    .collect();

                if trans_solver.solve(&neg_primed) == SatResult::Sat {
                    return Err(format!(
                        "Inv AND T => Inv' FAILED: transition does not preserve lemma {} ({} lits)",
                        i,
                        lemma.len(),
                    ));
                }
            }
        }

        // Check 3: Inv => !Bad
        // Build solver with: Trans + constraints + all lemmas.
        // For each bad lit, verify that Inv AND bad is UNSAT.
        {
            let mut bad_solver = SimpleSolver::new();
            bad_solver.add_clause(&[Lit::TRUE]);
            for clause in &self.trans_clauses {
                bad_solver.add_clause(&clause.lits);
            }
            for &constraint in &self.constraint_lits {
                bad_solver.add_clause(&[constraint]);
            }
            for lemma in lemmas {
                bad_solver.add_clause(lemma);
            }

            for &bad_lit in &self.bad_lits {
                if bad_solver.solve(&[bad_lit]) == SatResult::Sat {
                    return Err(format!(
                        "Inv => !Bad FAILED: invariant allows bad state (bad_lit={:?})",
                        bad_lit,
                    ));
                }
            }
        }

        Ok(())
    }
}

// ---------------------------------------------------------------------------
// Variable renaming for time-step unrolling
// ---------------------------------------------------------------------------

/// Maps variables from the base (time-0) encoding to a specific time step.
/// Each time step gets fresh variables for inputs and AND-gate outputs.
/// Latch variables at step k map to next-state literals from step k-1.
///
/// Uses a Vec<Var> per step instead of FxHashMap for O(1) indexed lookup.
/// Since variables are a dense range 0..=max_var, Vec is both faster
/// (no hash computation) and more memory-efficient.
#[derive(Debug, Clone)]
pub struct VarRenamer {
    /// For each time step, mapping from base Var index to renamed Var.
    /// step_maps[k][v] = renamed variable for Var(v) at step k.
    step_maps: Vec<Vec<Var>>,
    /// Next fresh variable to allocate.
    next_var: u32,
    /// Reference to the transition system.
    max_var: u32,
}

impl VarRenamer {
    pub fn new(ts: &Transys) -> Self {
        VarRenamer {
            step_maps: Vec::new(),
            next_var: ts.max_var + 1,
            max_var: ts.max_var,
        }
    }

    /// Allocate variables for time step `k`.
    /// Step 0 uses the original variables (identity mapping).
    pub fn ensure_step(&mut self, k: usize) {
        while self.step_maps.len() <= k {
            let step = self.step_maps.len();
            if step == 0 {
                // Step 0: identity mapping
                let map: Vec<Var> = (0..=self.max_var).map(Var).collect();
                self.step_maps.push(map);
            } else {
                // Step k > 0: fresh variables
                let mut map = Vec::with_capacity((self.max_var + 1) as usize);
                // Var(0) always maps to itself (constant)
                map.push(Var(0));
                for _v in 1..=self.max_var {
                    let fresh = Var(self.next_var);
                    self.next_var += 1;
                    map.push(fresh);
                }
                self.step_maps.push(map);
            }
        }
    }

    /// Get the maximum variable index allocated so far.
    pub fn max_allocated(&self) -> u32 {
        self.next_var.saturating_sub(1)
    }

    /// Allocate a fresh auxiliary variable from the same namespace as
    /// time-step variables. Use this for accumulator variables, activation
    /// literals, etc. to avoid collisions with `ensure_step()` allocations.
    pub fn alloc_aux_var(&mut self) -> Var {
        let v = Var(self.next_var);
        self.next_var += 1;
        v
    }

    /// Rename a literal to time step `k`.
    #[inline]
    pub fn rename_lit(&self, lit: Lit, step: usize) -> Lit {
        let var_idx = lit.var().0 as usize;
        let map = &self.step_maps[step];
        let renamed_var = if var_idx < map.len() {
            map[var_idx]
        } else {
            lit.var()
        };
        if lit.is_negated() {
            Lit::neg(renamed_var)
        } else {
            Lit::pos(renamed_var)
        }
    }

    /// Get the renamed variable for a base variable at a given step.
    #[inline]
    pub fn rename_var(&self, var: Var, step: usize) -> Var {
        let var_idx = var.0 as usize;
        let map = &self.step_maps[step];
        if var_idx < map.len() {
            map[var_idx]
        } else {
            var
        }
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
    fn test_transys_from_trivially_safe() {
        // output=0 (constant FALSE) => never bad => SAFE
        let circuit = parse_aag("aag 0 0 0 1 0\n0\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        assert_eq!(ts.bad_lits.len(), 1);
        // bad lit should be constant FALSE
        assert_eq!(ts.bad_lits[0], Lit::FALSE);
    }

    #[test]
    fn test_transys_from_trivially_unsafe() {
        // output=1 (constant TRUE) => always bad => UNSAFE
        let circuit = parse_aag("aag 0 0 0 1 0\n1\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        assert_eq!(ts.bad_lits.len(), 1);
        // bad lit should be constant TRUE
        assert_eq!(ts.bad_lits[0], Lit::TRUE);
    }

    #[test]
    fn test_transys_toggle_flip_flop() {
        // Latch starts at 0, next = !latch. Bad = latch.
        // Step 0: latch=0 (safe), Step 1: latch=1 (bad)
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        assert_eq!(ts.num_latches, 1);
        assert_eq!(ts.latch_vars, vec![Var(1)]);
        assert_eq!(ts.init_clauses.len(), 1); // latch = 0
        assert_eq!(ts.bad_lits.len(), 1);
    }

    #[test]
    fn test_transys_and_gate_encoding() {
        // M=3 I=2 L=0 O=0 A=1 B=1: inputs 2,4; AND 6=2&4; bad=6
        let circuit = parse_aag("aag 3 2 0 0 1 1\n2\n4\n6\n6 2 4\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        assert_eq!(ts.num_inputs, 2);
        assert_eq!(ts.trans_clauses.len(), 3); // Tseitin for one AND gate
        assert_eq!(ts.bad_lits.len(), 1);
        // AND gate output var is 3 (lit 6 / 2)
        assert!(ts.and_defs.contains_key(&Var(3)));
    }

    #[test]
    fn test_transys_latch_stays_zero() {
        // Latch with next=0 (stuck at 0). Bad = latch (lit 2).
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        assert_eq!(ts.num_latches, 1);
        // Next state of latch var(1) should be constant FALSE
        assert_eq!(*ts.next_state.get(&Var(1)).unwrap(), Lit::FALSE);
    }

    #[test]
    fn test_var_renamer() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let mut renamer = VarRenamer::new(&ts);

        renamer.ensure_step(0);
        // Step 0: identity
        assert_eq!(renamer.rename_var(Var(1), 0), Var(1));

        renamer.ensure_step(1);
        // Step 1: fresh variable
        let v1_at_1 = renamer.rename_var(Var(1), 1);
        assert_ne!(v1_at_1, Var(1));
    }

    #[test]
    fn test_load_init() {
        use crate::sat_types::SimpleSolver;

        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let mut solver = SimpleSolver::new();
        ts.load_init(&mut solver);
        // After loading init, latch (var 1) should be forced to false
        let result = solver.solve(&[]);
        assert_eq!(result, crate::sat_types::SatResult::Sat);
        assert_eq!(solver.value(Lit::pos(Var(1))), Some(false));
    }
}
