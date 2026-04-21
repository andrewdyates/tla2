// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Cone of Influence (COI) reduction for AIGER circuits.
//!
//! Eliminates variables and gates not in the transitive fanin cone of the
//! bad-state properties and constraints. This is standard preprocessing that
//! all competitive HWMCC solvers perform (rIC3, ABC, super-prove, etc.).
//!
//! The algorithm:
//! 1. Start with the set of variables referenced by bad-state and constraint
//!    literals.
//! 2. For each variable in the set:
//!    - If it's an AND gate output, add both input variables.
//!    - If it's a latch, add variables referenced by its next-state function.
//!    - Also trace through init clause dependencies (e.g., non-constant resets).
//! 3. Repeat until no new variables are added (fixpoint).
//! 4. Filter the transition system to only include variables in the COI.
//!
//! Reference: rIC3 `src/transys/simp.rs` `coi_refine()` traces through
//! `self.next`, `self.init`, and `self.rel.dep(v)` (AND gate dependencies).

use rustc_hash::{FxHashMap, FxHashSet};

use crate::sat_types::{Clause, Lit, Var};
use crate::transys::Transys;

/// Statistics from a COI reduction pass.
#[derive(Debug, Clone)]
pub struct CoiStats {
    /// Original counts before reduction.
    pub orig_latches: usize,
    pub orig_inputs: usize,
    pub orig_and_gates: usize,
    pub orig_trans_clauses: usize,
    /// Counts after reduction.
    pub reduced_latches: usize,
    pub reduced_inputs: usize,
    pub reduced_and_gates: usize,
    pub reduced_trans_clauses: usize,
}

impl std::fmt::Display for CoiStats {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "COI: latches {}->{} inputs {}->{} gates {}->{} clauses {}->{}",
            self.orig_latches,
            self.reduced_latches,
            self.orig_inputs,
            self.reduced_inputs,
            self.orig_and_gates,
            self.reduced_and_gates,
            self.orig_trans_clauses,
            self.reduced_trans_clauses,
        )
    }
}

impl Transys {
    /// Reduce the transition system to only include variables in the
    /// cone of influence of the bad-state properties.
    ///
    /// Returns a new `Transys` with only the relevant variables, gates,
    /// and constraints. The variable numbering is preserved (no renumbering)
    /// to keep literal encodings consistent.
    pub fn coi_reduce(&self) -> Transys {
        self.coi_reduce_with_stats().0
    }

    /// Like `coi_reduce` but also returns reduction statistics.
    pub fn coi_reduce_with_stats(&self) -> (Transys, CoiStats) {
        let coi_vars = self.compute_coi();

        // Filter latch vars
        let latch_vars: Vec<Var> = self
            .latch_vars
            .iter()
            .copied()
            .filter(|v| coi_vars.contains(v))
            .collect();

        // Filter input vars
        let input_vars: Vec<Var> = self
            .input_vars
            .iter()
            .copied()
            .filter(|v| coi_vars.contains(v))
            .collect();

        // Filter next_state
        let next_state: FxHashMap<Var, Lit> = self
            .next_state
            .iter()
            .filter(|(k, _)| coi_vars.contains(k))
            .map(|(&k, &v)| (k, v))
            .collect();

        // Filter init_clauses: keep only those mentioning COI variables
        let init_clauses: Vec<Clause> = self
            .init_clauses
            .iter()
            .filter(|c| c.lits.iter().any(|l| coi_vars.contains(&l.var())))
            .cloned()
            .collect();

        // Filter trans_clauses: keep only those where at least one variable is in COI.
        // A Tseitin clause for an AND gate has 3 literals involving the gate output
        // and its two inputs. If the gate output is in COI, all three literals'
        // variables will be in COI (since we traced through and_defs). If the gate
        // output is NOT in COI, the clause is irrelevant.
        let trans_clauses: Vec<Clause> = self
            .trans_clauses
            .iter()
            .filter(|c| c.lits.iter().any(|l| coi_vars.contains(&l.var())))
            .cloned()
            .collect();

        // Filter and_defs
        let and_defs: FxHashMap<Var, (Lit, Lit)> = self
            .and_defs
            .iter()
            .filter(|(k, _)| coi_vars.contains(k))
            .map(|(&k, &v)| (k, v))
            .collect();

        // Filter constraint_lits: keep only those in COI (constants always kept)
        let constraint_lits: Vec<Lit> = self
            .constraint_lits
            .iter()
            .copied()
            .filter(|l| l.var() == Var(0) || coi_vars.contains(&l.var()))
            .collect();

        let stats = CoiStats {
            orig_latches: self.num_latches,
            orig_inputs: self.num_inputs,
            orig_and_gates: self.and_defs.len(),
            orig_trans_clauses: self.trans_clauses.len(),
            reduced_latches: latch_vars.len(),
            reduced_inputs: input_vars.len(),
            reduced_and_gates: and_defs.len(),
            reduced_trans_clauses: trans_clauses.len(),
        };

        let ts = Transys {
            max_var: self.max_var,
            num_latches: latch_vars.len(),
            num_inputs: input_vars.len(),
            latch_vars,
            input_vars,
            next_state,
            init_clauses,
            trans_clauses,
            bad_lits: self.bad_lits.clone(),
            constraint_lits,
            and_defs,
            internal_signals: Vec::new(),
        };

        (ts, stats)
    }

    /// Compute the set of variables in the cone of influence of the bad
    /// properties and constraints.
    ///
    /// Traces backwards through:
    /// - AND gate definitions (both inputs of each gate)
    /// - Latch next-state functions
    /// - Init clause dependencies (non-constant reset values)
    ///
    /// This matches rIC3's `coi_refine` which traces through `next`, `init`,
    /// and `rel.dep(v)`.
    fn compute_coi(&self) -> FxHashSet<Var> {
        let mut coi = FxHashSet::default();
        let mut worklist: Vec<Var> = Vec::new();

        // Helper: add a variable to the COI set and worklist if not already present.
        let enqueue = |coi: &mut FxHashSet<Var>, worklist: &mut Vec<Var>, v: Var| {
            if v != Var(0) && coi.insert(v) {
                worklist.push(v);
            }
        };

        // Seed with variables from bad literals.
        for &bad_lit in &self.bad_lits {
            enqueue(&mut coi, &mut worklist, bad_lit.var());
        }

        // Seed with variables from constraint literals.
        for &c_lit in &self.constraint_lits {
            enqueue(&mut coi, &mut worklist, c_lit.var());
        }

        // Pre-compute a map from latch var to the set of variables referenced
        // in its init clauses. This handles non-constant resets like
        // `latch_var <=> reset_lit` which create binary init clauses.
        let init_deps = self.compute_init_deps();

        // Fixpoint: expand backwards through AND gates, latch next-state,
        // and init dependencies.
        while let Some(var) = worklist.pop() {
            // If var is an AND gate output, add its inputs.
            if let Some(&(rhs0, rhs1)) = self.and_defs.get(&var) {
                enqueue(&mut coi, &mut worklist, rhs0.var());
                enqueue(&mut coi, &mut worklist, rhs1.var());
            }

            // If var is a latch, add variables from its next-state function.
            if let Some(&next_lit) = self.next_state.get(&var) {
                enqueue(&mut coi, &mut worklist, next_lit.var());
            }

            // If var has init dependencies (non-constant reset), add them.
            if let Some(deps) = init_deps.get(&var) {
                for &dep_var in deps {
                    enqueue(&mut coi, &mut worklist, dep_var);
                }
            }
        }

        coi
    }

    /// Compute dependencies from init clauses: for each variable that appears
    /// in an init clause, record the other variables in that clause.
    ///
    /// This handles the case where a latch has a non-constant reset value
    /// (e.g., `reset = other_literal`), which generates binary init clauses
    /// like `(!latch_var OR reset_lit) AND (!reset_lit OR latch_var)`.
    fn compute_init_deps(&self) -> FxHashMap<Var, Vec<Var>> {
        let mut deps: FxHashMap<Var, Vec<Var>> = FxHashMap::default();
        for clause in &self.init_clauses {
            // For each variable in the clause, the other variables are deps.
            let vars: Vec<Var> = clause
                .lits
                .iter()
                .map(|l| l.var())
                .filter(|&v| v != Var(0))
                .collect();
            for &v in &vars {
                for &other in &vars {
                    if other != v {
                        deps.entry(v).or_default().push(other);
                    }
                }
            }
        }
        deps
    }

    /// Compact variable numbering after COI reduction.
    ///
    /// After COI removes irrelevant variables, the remaining variable IDs
    /// may have large gaps (e.g., vars 1, 5, 100 out of max_var=1000).
    /// This wastes memory in SAT solver arrays and hurts cache locality.
    ///
    /// Compaction remaps all variables to a contiguous range [1..n],
    /// reducing max_var and improving SAT solver performance.
    ///
    /// Reference: rIC3 `rearrange()` in `src/transys/simp.rs` does this
    /// after COI refinement, prioritizing latches, inputs, and bad/constraint
    /// variables in the renumbering to improve SAT solver variable ordering.
    pub fn compact_vars(&self) -> Transys {
        // Collect all variables actually in use.
        let mut used_vars = FxHashSet::default();
        // Always include Var(0) (constant).
        used_vars.insert(Var(0));

        for &v in &self.latch_vars {
            used_vars.insert(v);
        }
        for &v in &self.input_vars {
            used_vars.insert(v);
        }
        for &lit in &self.bad_lits {
            used_vars.insert(lit.var());
        }
        for &lit in &self.constraint_lits {
            used_vars.insert(lit.var());
        }
        for clause in &self.init_clauses {
            for &lit in &clause.lits {
                used_vars.insert(lit.var());
            }
        }
        for clause in &self.trans_clauses {
            for &lit in &clause.lits {
                used_vars.insert(lit.var());
            }
        }
        for (&var, &(rhs0, rhs1)) in &self.and_defs {
            used_vars.insert(var);
            used_vars.insert(rhs0.var());
            used_vars.insert(rhs1.var());
        }
        for (&_latch, &next_lit) in &self.next_state {
            used_vars.insert(next_lit.var());
        }

        // Build sorted list and create remapping.
        // Priority order (like rIC3 rearrange): latches, inputs, bad/constraint vars first,
        // then AND gate internals. Lower IDs get better cache behavior in SAT solvers.
        let mut priority_vars: Vec<Var> = Vec::new();
        priority_vars.push(Var(0)); // constant always ID 0
                                    // Latches first (most important for IC3 cubes).
        for &v in &self.latch_vars {
            if !priority_vars.contains(&v) {
                priority_vars.push(v);
            }
        }
        // Inputs next.
        for &v in &self.input_vars {
            if !priority_vars.contains(&v) {
                priority_vars.push(v);
            }
        }
        // Bad/constraint vars.
        for &lit in &self.bad_lits {
            if !priority_vars.contains(&lit.var()) {
                priority_vars.push(lit.var());
            }
        }
        for &lit in &self.constraint_lits {
            if !priority_vars.contains(&lit.var()) {
                priority_vars.push(lit.var());
            }
        }
        // Remaining AND gate and other vars.
        let mut remaining: Vec<Var> = used_vars
            .iter()
            .copied()
            .filter(|v| !priority_vars.contains(v))
            .collect();
        remaining.sort_by_key(|v| v.0);
        priority_vars.extend(remaining);

        // Build the remapping: old_var -> new_var.
        let mut remap = FxHashMap::default();
        for (new_id, &old_var) in priority_vars.iter().enumerate() {
            remap.insert(old_var, Var(new_id as u32));
        }

        let remap_lit = |lit: Lit| -> Lit {
            let new_var = remap.get(&lit.var()).copied().unwrap_or(lit.var());
            if lit.is_positive() {
                Lit::pos(new_var)
            } else {
                Lit::neg(new_var)
            }
        };

        let new_max_var = if priority_vars.is_empty() {
            0
        } else {
            (priority_vars.len() - 1) as u32
        };

        // Only compact if it would actually reduce max_var meaningfully.
        if new_max_var >= self.max_var {
            return self.clone();
        }

        let latch_vars: Vec<Var> = self.latch_vars.iter().map(|v| remap[v]).collect();
        let input_vars: Vec<Var> = self.input_vars.iter().map(|v| remap[v]).collect();
        let bad_lits: Vec<Lit> = self.bad_lits.iter().map(|&l| remap_lit(l)).collect();
        let constraint_lits: Vec<Lit> =
            self.constraint_lits.iter().map(|&l| remap_lit(l)).collect();

        let init_clauses: Vec<Clause> = self
            .init_clauses
            .iter()
            .map(|c| Clause::new(c.lits.iter().map(|&l| remap_lit(l)).collect()))
            .collect();

        let trans_clauses: Vec<Clause> = self
            .trans_clauses
            .iter()
            .map(|c| Clause::new(c.lits.iter().map(|&l| remap_lit(l)).collect()))
            .collect();

        let next_state: FxHashMap<Var, Lit> = self
            .next_state
            .iter()
            .map(|(&k, &v)| (remap[&k], remap_lit(v)))
            .collect();

        let and_defs: FxHashMap<Var, (Lit, Lit)> = self
            .and_defs
            .iter()
            .map(|(&k, &(r0, r1))| (remap[&k], (remap_lit(r0), remap_lit(r1))))
            .collect();

        Transys {
            max_var: new_max_var,
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

    /// Full preprocessing pipeline: COI + trivial simplification + constant
    /// latch elimination + structural hashing + SCORR + forward reduction +
    /// variable compaction.
    ///
    /// This is the standard preprocessing applied before all engines.
    /// Returns the preprocessed transition system and COI statistics.
    ///
    /// Pipeline order (matching rIC3's `preproc()`):
    /// 1. COI reduction (remove variables outside cone of influence)
    /// 2. Trivial simplification (constant folding, identity/complement gates)
    /// 3. Constant latch elimination (iterative fixpoint: remove latches stuck
    ///    at their init value because their next-state function always produces
    ///    the same constant)
    /// 4. Structural hashing (merge AND gates with identical inputs after
    ///    constant propagation)
    /// 5. SCORR (sequential latch equivalence merging via simulation + SAT)
    /// 6. Forward reduction (combinational signal merging)
    /// 7. Variable compaction (renumber to dense range)
    pub fn preprocess(&self) -> (Transys, CoiStats) {
        self.preprocess_configured(&crate::preprocess::PreprocessConfig::default())
    }

    /// Full preprocessing pipeline with custom configuration.
    ///
    /// Like [`preprocess`] but allows portfolio configs to customize
    /// which passes are enabled and how many iterations to run.
    pub fn preprocess_configured(
        &self,
        config: &crate::preprocess::PreprocessConfig,
    ) -> (Transys, CoiStats) {
        let (reduced, stats) = self.coi_reduce_with_stats();

        // Run the preprocessing pipeline with the given config.
        let (preprocessed, preproc_stats) =
            crate::preprocess::preprocess_with_config(&reduced, config);
        eprintln!("{preproc_stats}");

        let compacted = preprocessed.compact_vars();
        eprintln!(
            "Compaction: max_var {}->{} ({}% reduction)",
            preprocessed.max_var,
            compacted.max_var,
            if preprocessed.max_var > 0 {
                100 - (compacted.max_var * 100 / preprocessed.max_var)
            } else {
                0
            },
        );
        (compacted, stats)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse_aag;

    #[test]
    fn test_coi_trivial_safe() {
        // output=0 (constant FALSE) => nothing in COI
        let circuit = parse_aag("aag 0 0 0 1 0\n0\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let reduced = ts.coi_reduce();
        assert_eq!(reduced.latch_vars.len(), 0);
        assert_eq!(reduced.input_vars.len(), 0);
        assert_eq!(reduced.trans_clauses.len(), 0);
    }

    #[test]
    fn test_coi_toggle() {
        // Toggle: latch starts at 0, next = !latch. Bad = latch.
        // COI includes latch variable.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let reduced = ts.coi_reduce();
        assert_eq!(reduced.latch_vars.len(), 1);
        assert_eq!(reduced.num_latches, 1);
    }

    #[test]
    fn test_coi_removes_irrelevant_input() {
        // Two inputs, AND gate on first input only, bad = AND output.
        // Second input should be removed by COI.
        // aag 3 2 0 0 1 1
        // inputs: 2, 4
        // bad: 6
        // AND: 6 = 2 & 2 (self-AND, just uses input 1)
        let circuit = parse_aag("aag 3 2 0 0 1 1\n2\n4\n6\n6 2 2\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        assert_eq!(ts.input_vars.len(), 2);
        let reduced = ts.coi_reduce();
        // Only input 1 (var 1) should remain, not input 2 (var 2)
        assert_eq!(reduced.input_vars.len(), 1);
        assert_eq!(reduced.input_vars[0], Var(1));
    }

    #[test]
    fn test_coi_keeps_chain() {
        // Chain: input -> AND -> latch -> bad
        // All should be in COI.
        // aag 3 1 1 0 1 1
        // input: 2 (var 1)
        // latch: 4 next=6 (var 2, next = AND output var 3)
        // AND: 6 = 2 & 4 (var 3 = var 1 AND var 2)
        // bad: 4 (latch)
        let circuit = parse_aag("aag 3 1 1 0 1 1\n2\n4 6\n4\n6 2 4\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let reduced = ts.coi_reduce();
        // All variables should be in COI: input var 1, latch var 2, AND var 3
        assert_eq!(reduced.input_vars.len(), 1);
        assert_eq!(reduced.latch_vars.len(), 1);
        assert!(reduced.and_defs.contains_key(&Var(3)));
    }

    #[test]
    fn test_coi_preserves_full_circuit() {
        // When everything is connected, nothing gets removed.
        let circuit = parse_aag("aag 3 2 0 0 1 1\n2\n4\n6\n6 2 4\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let reduced = ts.coi_reduce();
        assert_eq!(reduced.input_vars.len(), 2);
        assert_eq!(reduced.trans_clauses.len(), ts.trans_clauses.len());
    }

    #[test]
    fn test_coi_stats() {
        // Verify the stats capture original and reduced counts.
        let circuit = parse_aag("aag 3 2 0 0 1 1\n2\n4\n6\n6 2 2\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let (reduced, stats) = ts.coi_reduce_with_stats();
        assert_eq!(stats.orig_inputs, 2);
        assert_eq!(stats.reduced_inputs, 1);
        assert_eq!(reduced.input_vars.len(), 1);
        // Verify Display impl works
        let s = format!("{stats}");
        assert!(s.contains("COI:"));
    }

    #[test]
    fn test_coi_removes_irrelevant_latch() {
        // Two latches, only one feeds into bad. The other should be removed.
        // aag 2 0 2 0 0 1
        // latch 1 (var 1): lit 2, next=0 (stuck at 0)
        // latch 2 (var 2): lit 4, next=0 (stuck at 0)
        // bad: lit 2 (latch 1)
        // Only latch 1 should be in COI.
        let circuit = parse_aag("aag 2 0 2 0 0 1\n2 0\n4 0\n2\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        assert_eq!(ts.latch_vars.len(), 2);
        let reduced = ts.coi_reduce();
        assert_eq!(reduced.latch_vars.len(), 1);
        assert_eq!(reduced.latch_vars[0], Var(1));
        assert_eq!(reduced.num_latches, 1);
    }

    #[test]
    fn test_coi_constant_bad_empty_cone() {
        // Bad = constant TRUE (lit 1). No variables in COI since Var(0) is constant.
        let circuit = parse_aag("aag 1 1 0 1 0\n2\n1\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let reduced = ts.coi_reduce();
        // Input var 1 not referenced by bad (which is constant TRUE), so removed.
        assert_eq!(reduced.input_vars.len(), 0);
    }

    #[test]
    fn test_coi_with_constraints() {
        // Constraint references an input; that input must stay in COI.
        // Header: aag M=2 I=2 L=0 O=0 A=0 B=1 C=1
        // inputs: 2, 4 (var 1, var 2)
        // bad: 2 (var 1)
        // constraint: 4 (var 2)
        // Both inputs should be in COI: var 1 from bad, var 2 from constraint.
        let circuit = parse_aag("aag 2 2 0 0 0 1 1\n2\n4\n2\n4\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let reduced = ts.coi_reduce();
        assert_eq!(reduced.input_vars.len(), 2);
        assert_eq!(reduced.constraint_lits.len(), 1);
    }

    #[test]
    fn test_coi_multi_level_and_chain() {
        // Chain of AND gates: g1 = i1 & i2, g2 = g1 & i3, bad = g2.
        // All three inputs and both gates should be in COI.
        // Header: aag M=5 I=3 L=0 O=0 A=2 B=1
        // inputs: 2, 4, 6 (vars 1, 2, 3)
        // bad: 10 (var 5)
        // AND: 8 = 2 & 4 (var 4 = var 1 & var 2)
        // AND: 10 = 8 & 6 (var 5 = var 4 & var 3)
        let circuit = parse_aag("aag 5 3 0 0 2 1\n2\n4\n6\n10\n8 2 4\n10 8 6\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let reduced = ts.coi_reduce();
        assert_eq!(reduced.input_vars.len(), 3);
        assert_eq!(reduced.and_defs.len(), 2);
    }

    #[test]
    fn test_coi_idempotent() {
        // Applying COI reduction twice should give the same result.
        let circuit = parse_aag("aag 3 2 0 0 1 1\n2\n4\n6\n6 2 2\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let reduced1 = ts.coi_reduce();
        let reduced2 = reduced1.coi_reduce();
        assert_eq!(reduced1.latch_vars, reduced2.latch_vars);
        assert_eq!(reduced1.input_vars, reduced2.input_vars);
        assert_eq!(reduced1.num_latches, reduced2.num_latches);
        assert_eq!(reduced1.num_inputs, reduced2.num_inputs);
        assert_eq!(reduced1.trans_clauses.len(), reduced2.trans_clauses.len());
    }

    #[test]
    fn test_compact_vars_reduces_max_var() {
        // After COI removes var 2, compact should reduce max_var.
        // aag 3 2 0 0 1 1: 2 inputs, AND on first only, bad=AND.
        // COI removes input var 2. compact_vars should renumber.
        let circuit = parse_aag("aag 3 2 0 0 1 1\n2\n4\n6\n6 2 2\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let reduced = ts.coi_reduce();
        assert_eq!(reduced.max_var, 3); // original max_var preserved (gap at var 2)
        let compacted = reduced.compact_vars();
        assert!(
            compacted.max_var <= reduced.max_var,
            "compact should reduce max_var: {} <= {}",
            compacted.max_var,
            reduced.max_var
        );
        // Structural integrity checks.
        assert_eq!(compacted.input_vars.len(), reduced.input_vars.len());
        assert_eq!(compacted.latch_vars.len(), reduced.latch_vars.len());
        assert_eq!(compacted.trans_clauses.len(), reduced.trans_clauses.len());
        assert_eq!(compacted.bad_lits.len(), reduced.bad_lits.len());
    }

    #[test]
    fn test_compact_vars_noop_when_dense() {
        // When variables are already dense, compact is a no-op.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let compacted = ts.compact_vars();
        // Should not increase max_var.
        assert!(compacted.max_var <= ts.max_var);
    }

    #[test]
    fn test_preprocess_pipeline() {
        // Full preprocess (COI + compact) should produce a valid transition system.
        let circuit = parse_aag("aag 3 2 0 0 1 1\n2\n4\n6\n6 2 2\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let (preprocessed, stats) = ts.preprocess();
        assert_eq!(stats.orig_inputs, 2);
        assert_eq!(stats.reduced_inputs, 1);
        assert!(preprocessed.max_var <= ts.max_var);
        // The preprocessed system should still be structurally valid.
        assert_eq!(preprocessed.input_vars.len(), 1);
        assert_eq!(preprocessed.bad_lits.len(), 1);
    }

    #[test]
    fn test_compact_preserves_ic3_correctness() {
        // Ensure that IC3 on a compacted system gives the same result.
        use crate::ic3;
        // Toggle: unsafe at depth 1.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let result = ic3::check_ic3(&circuit);
        assert!(
            matches!(result, ic3::Ic3Result::Unsafe { .. }),
            "IC3 with preprocessing should find Unsafe, got {result:?}"
        );
        // Stuck-at-zero: always safe.
        let circuit2 = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let result2 = ic3::check_ic3(&circuit2);
        assert!(
            matches!(result2, ic3::Ic3Result::Safe { .. }),
            "IC3 with preprocessing should find Safe, got {result2:?}"
        );
    }
}
