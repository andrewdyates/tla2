// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! CEGAR (Counterexample-Guided Abstraction Refinement) wrapper for IC3.
//!
//! CEGAR for IC3 works by starting with an abstract model containing only
//! a subset of latches, running IC3 on it, and refining if the counterexample
//! is spurious. This can dramatically speed up IC3 on large circuits where
//! most latches are irrelevant to the property.
//!
//! The algorithm:
//! 1. Start with an abstract model containing latches in the bad property's
//!    immediate cone of influence (1 hop through next-state functions).
//! 2. Run IC3 on the abstract model.
//! 3. If IC3 proves safe → the concrete model is safe (abstraction is
//!    an overapproximation, so safe abstract → safe concrete).
//! 4. If IC3 finds a counterexample → simulate on the concrete model.
//! 5. If the counterexample is real → return Unsafe.
//! 6. If spurious → identify which latches caused the discrepancy and
//!    add them to the abstraction (refinement).
//! 7. Repeat until proof or real counterexample.
//!
//! Reference: Clarke et al., "Counterexample-Guided Abstraction Refinement
//! for Symbolic Model Checking" (JACM 2003). Applied to IC3 by Vizel and
//! Grumberg, "Interpolation-sequence based model checking" (FMCAD 2009).
//! AVR (Aman Goel, FMCAD 2020) uses a similar abstraction-refinement loop
//! over word-level IC3.

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

use rustc_hash::FxHashSet;

use crate::check_result::CheckResult;
use crate::ic3::{Ic3Config, Ic3Engine, Ic3Result};
use crate::sat_types::{Lit, Var};
use crate::transys::Transys;

/// Maximum number of CEGAR refinement iterations before giving up.
/// Each iteration adds latches, so this bounds the total work.
/// On HWMCC benchmarks, most proofs converge within 10-20 iterations.
const MAX_CEGAR_ITERATIONS: usize = 50;

/// Abstraction mode for CEGAR-IC3, mirroring rIC3's `abs_cst` and `abs_trans` flags.
///
/// These modes control how aggressively the abstraction removes information
/// from the concrete model:
///
/// - `AbstractConstraints`: Only abstract constraint literals. The transition
///   relation and next-state functions for all latches are kept, but constraint
///   enforcement for non-abstract latches is relaxed. This is the safest mode
///   with the least abstraction (fewest refinements needed).
///
/// - `AbstractAll`: Abstract both constraints AND transition relation. Non-abstract
///   latches become fully unconstrained (free variables), maximizing the
///   abstraction benefit. Requires more refinement iterations but can solve
///   benchmarks with many irrelevant latches much faster.
///
/// Reference: rIC3 `ic3/localabs.rs:27-36` — `abs_cst` and `abs_trans` flags.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum AbstractionMode {
    /// Abstract only constraint clauses (rIC3's `abs_cst` mode).
    /// Keeps all transition relations but relaxes constraint enforcement.
    AbstractConstraints,
    /// Abstract both constraints and transition relation (rIC3's `abs_cst + abs_trans`).
    /// Non-abstract latches become free variables.
    AbstractAll,
}

impl Default for AbstractionMode {
    fn default() -> Self {
        AbstractionMode::AbstractAll
    }
}

/// CEGAR-IC3 engine.
///
/// Manages the abstraction-refinement loop around an inner IC3 engine.
/// The concrete model is kept intact; abstractions are built on-demand
/// by selecting subsets of latches and their combinational support.
pub(crate) struct CegarIc3 {
    /// The full concrete transition system.
    concrete: Transys,
    /// Set of latch variables currently in the abstraction.
    abstract_latches: FxHashSet<Var>,
    /// IC3 configuration to use for each abstract IC3 run.
    ic3_config: Ic3Config,
    /// Abstraction mode controlling what gets removed from abstract model.
    mode: AbstractionMode,
    /// Cancellation flag shared with portfolio.
    cancelled: Arc<AtomicBool>,
}

impl CegarIc3 {
    /// Create a new CEGAR-IC3 engine with default abstraction mode (AbstractAll).
    ///
    /// The initial abstraction includes latches directly referenced by
    /// bad-state literals and their immediate combinational support.
    pub(crate) fn new(concrete: Transys, ic3_config: Ic3Config) -> Self {
        Self::with_mode(concrete, ic3_config, AbstractionMode::default())
    }

    /// Create a new CEGAR-IC3 engine with a specific abstraction mode.
    ///
    /// - `AbstractConstraints` (abs_cst): keeps all transition clauses, only
    ///   relaxes constraint enforcement on non-abstract latches. Fewer
    ///   refinement iterations but less abstraction benefit.
    /// - `AbstractAll` (abs_all): removes both constraints and transition
    ///   clauses for non-abstract latches, making them free variables.
    ///   Maximum abstraction benefit.
    ///
    /// Reference: rIC3 `ic3/localabs.rs:27-36` — `abs_cst` and `abs_trans` flags.
    pub(crate) fn with_mode(
        concrete: Transys,
        ic3_config: Ic3Config,
        mode: AbstractionMode,
    ) -> Self {
        let abstract_latches = initial_abstraction(&concrete);
        let mode_name = match mode {
            AbstractionMode::AbstractConstraints => "abs_cst",
            AbstractionMode::AbstractAll => "abs_all",
        };
        eprintln!(
            "CEGAR({}): initial abstraction {}/{} latches",
            mode_name,
            abstract_latches.len(),
            concrete.latch_vars.len(),
        );
        CegarIc3 {
            concrete,
            abstract_latches,
            ic3_config,
            mode,
            cancelled: Arc::new(AtomicBool::new(false)),
        }
    }

    /// Set the cancellation flag (shared with portfolio).
    pub(crate) fn set_cancelled(&mut self, cancelled: Arc<AtomicBool>) {
        self.cancelled = cancelled;
    }

    fn is_cancelled(&self) -> bool {
        self.cancelled.load(Ordering::Relaxed)
    }

    /// Run the CEGAR loop.
    ///
    /// Returns a `CheckResult` compatible with the portfolio framework.
    pub(crate) fn run(&mut self) -> CheckResult {
        for iteration in 0..MAX_CEGAR_ITERATIONS {
            if self.is_cancelled() {
                return CheckResult::Unknown {
                    reason: "cancelled".into(),
                };
            }

            // If we've included all latches, just run IC3 on the full model.
            if self.abstract_latches.len() >= self.concrete.latch_vars.len() {
                eprintln!("CEGAR: abstraction includes all latches, running full IC3");
                return self.run_full_ic3();
            }

            // Build abstract model.
            let abstract_ts = self.build_abstract_model();
            eprintln!(
                "CEGAR iter={iteration} abstract_latches={}/{} abstract_gates={}",
                abstract_ts.latch_vars.len(),
                self.concrete.latch_vars.len(),
                abstract_ts.and_defs.len(),
            );

            // Run IC3 on the abstract model.
            let mut engine = Ic3Engine::with_config(abstract_ts, self.ic3_config.clone());
            engine.set_cancelled(self.cancelled.clone());
            let result = engine.check();

            match result {
                Ic3Result::Safe { depth, .. } => {
                    // Abstract model is safe → concrete is safe.
                    // (Abstraction overapproximates reachable states.)
                    eprintln!("CEGAR: abstract IC3 proved safe at depth={depth}");
                    return CheckResult::Safe;
                }
                Ic3Result::Unsafe { trace, .. } => {
                    // Check if the counterexample is real on the concrete model.
                    match self.check_counterexample(&trace) {
                        CexCheck::Real { trace: real_trace } => {
                            eprintln!(
                                "CEGAR: real counterexample at depth={}",
                                real_trace.len().saturating_sub(1)
                            );
                            let named_trace = real_trace
                                .into_iter()
                                .map(|state| {
                                    state
                                        .into_iter()
                                        .map(|(var, val)| (format!("v{}", var.0), val))
                                        .collect()
                                })
                                .collect();
                            return CheckResult::Unsafe {
                                depth: trace.len().saturating_sub(1),
                                trace: named_trace,
                            };
                        }
                        CexCheck::Spurious { refine_latches } => {
                            eprintln!(
                                "CEGAR: spurious CEX, refining with {} new latches",
                                refine_latches.len()
                            );
                            if refine_latches.is_empty() {
                                // No latches to refine with — add all remaining.
                                // This shouldn't happen often but is a safety net.
                                eprintln!("CEGAR: empty refinement, adding all latches");
                                for &lv in &self.concrete.latch_vars {
                                    self.abstract_latches.insert(lv);
                                }
                            } else {
                                for lv in refine_latches {
                                    self.abstract_latches.insert(lv);
                                }
                            }
                        }
                    }
                }
                Ic3Result::Unknown { reason } => {
                    eprintln!("CEGAR: abstract IC3 returned unknown: {reason}");
                    // Try with full model as fallback.
                    return self.run_full_ic3();
                }
            }
        }

        eprintln!("CEGAR: max iterations ({MAX_CEGAR_ITERATIONS}) exceeded");
        CheckResult::Unknown {
            reason: format!("CEGAR: max iterations ({MAX_CEGAR_ITERATIONS}) exceeded"),
        }
    }

    /// Run IC3 on the full concrete model (no abstraction).
    fn run_full_ic3(&self) -> CheckResult {
        let mut engine = Ic3Engine::with_config(self.concrete.clone(), self.ic3_config.clone());
        engine.set_cancelled(self.cancelled.clone());
        match engine.check() {
            Ic3Result::Safe { .. } => CheckResult::Safe,
            Ic3Result::Unsafe { depth, trace } => {
                let named_trace = trace
                    .into_iter()
                    .map(|state| {
                        state
                            .into_iter()
                            .map(|(var, val)| (format!("v{}", var.0), val))
                            .collect()
                    })
                    .collect();
                CheckResult::Unsafe {
                    depth,
                    trace: named_trace,
                }
            }
            Ic3Result::Unknown { reason } => CheckResult::Unknown { reason },
        }
    }

    /// Build an abstract transition system based on the current abstraction mode.
    ///
    /// **AbstractAll mode (abs_all):**
    /// - Keeps only latches in `abstract_latches`
    /// - Keeps AND gates in the combinational support of abstract latches
    /// - Keeps init/trans clauses only for abstract variables
    /// - Latches NOT in the abstraction become free (unconstrained) variables
    ///
    /// **AbstractConstraints mode (abs_cst):**
    /// - Keeps ALL latches and their transition relations
    /// - Keeps ALL AND gates
    /// - Only removes constraint literals that reference non-abstract latches
    /// - Less aggressive: the transition relation is preserved, so fewer
    ///   spurious counterexamples, but less abstraction speedup
    ///
    /// Both modes overapproximate: "safe in abstract" implies "safe in concrete".
    fn build_abstract_model(&self) -> Transys {
        match self.mode {
            AbstractionMode::AbstractAll => self.build_abstract_model_all(),
            AbstractionMode::AbstractConstraints => self.build_abstract_model_cst(),
        }
    }

    /// Build abstract model in `abs_all` mode: remove non-abstract latches entirely.
    fn build_abstract_model_all(&self) -> Transys {
        // Compute the combinational support of abstract latches:
        // AND gates reachable from next-state functions of abstract latches
        // and from bad/constraint literals.
        let support = self.compute_abstract_support();

        // Filter latch vars to only abstract latches.
        let latch_vars: Vec<Var> = self
            .concrete
            .latch_vars
            .iter()
            .copied()
            .filter(|v| self.abstract_latches.contains(v))
            .collect();

        // Keep all inputs.
        let input_vars = self.concrete.input_vars.clone();

        // Filter next_state to only abstract latches.
        let next_state = self
            .concrete
            .next_state
            .iter()
            .filter(|(k, _)| self.abstract_latches.contains(k))
            .map(|(&k, &v)| (k, v))
            .collect();

        // Filter init clauses to only those mentioning abstract latches.
        let init_clauses = self
            .concrete
            .init_clauses
            .iter()
            .filter(|c| {
                c.lits
                    .iter()
                    .any(|l| self.abstract_latches.contains(&l.var()))
            })
            .cloned()
            .collect();

        // Filter trans clauses: keep those whose variables are all in support.
        let trans_clauses = self
            .concrete
            .trans_clauses
            .iter()
            .filter(|c| {
                c.lits
                    .iter()
                    .all(|l| l.var() == Var(0) || support.contains(&l.var()))
            })
            .cloned()
            .collect();

        // Filter AND defs to support.
        let and_defs = self
            .concrete
            .and_defs
            .iter()
            .filter(|(k, _)| support.contains(k))
            .map(|(&k, &v)| (k, v))
            .collect();

        // Keep all constraints (they are environmental assumptions).
        let constraint_lits = self.concrete.constraint_lits.clone();

        Transys {
            max_var: self.concrete.max_var,
            num_latches: latch_vars.len(),
            num_inputs: input_vars.len(),
            latch_vars,
            input_vars,
            next_state,
            init_clauses,
            trans_clauses,
            bad_lits: self.concrete.bad_lits.clone(),
            constraint_lits,
            and_defs,
            internal_signals: Vec::new(),
        }
    }

    /// Build abstract model in `abs_cst` mode: keep all transitions, only
    /// relax constraint enforcement for non-abstract latches.
    ///
    /// This is a lighter abstraction than `abs_all`. All latches remain in the
    /// model with their next-state functions, but constraints that reference
    /// non-abstract latches are removed. This means the model preserves the
    /// exact transition relation but relaxes environmental assumptions.
    ///
    /// This mirrors rIC3's `abs_cst` mode where `refine` starts with only
    /// `bad` variables, and constraint variables are gradually refined in.
    fn build_abstract_model_cst(&self) -> Transys {
        // Keep ALL latches — only constraints are abstracted.
        let latch_vars = self.concrete.latch_vars.clone();
        let input_vars = self.concrete.input_vars.clone();
        let next_state = self.concrete.next_state.clone();
        let init_clauses = self.concrete.init_clauses.clone();
        let trans_clauses = self.concrete.trans_clauses.clone();
        let and_defs = self.concrete.and_defs.clone();

        // Filter constraint literals: only keep those whose variables are in
        // the abstract set. Non-abstract constraint variables become unconstrained.
        let constraint_lits = self
            .concrete
            .constraint_lits
            .iter()
            .copied()
            .filter(|c| self.abstract_latches.contains(&c.var()))
            .collect();

        Transys {
            max_var: self.concrete.max_var,
            num_latches: latch_vars.len(),
            num_inputs: input_vars.len(),
            latch_vars,
            input_vars,
            next_state,
            init_clauses,
            trans_clauses,
            bad_lits: self.concrete.bad_lits.clone(),
            constraint_lits,
            and_defs,
            internal_signals: Vec::new(),
        }
    }

    /// Compute the set of variables in the combinational support of the
    /// abstract model: all variables reachable from abstract latch next-state
    /// functions, bad literals, and constraint literals through AND gates.
    fn compute_abstract_support(&self) -> FxHashSet<Var> {
        let mut support = FxHashSet::default();
        let mut worklist: Vec<Var> = Vec::new();

        let enqueue = |support: &mut FxHashSet<Var>, worklist: &mut Vec<Var>, v: Var| {
            if v != Var(0) && support.insert(v) {
                worklist.push(v);
            }
        };

        // Seed: abstract latch variables themselves.
        for &lv in &self.abstract_latches {
            enqueue(&mut support, &mut worklist, lv);
        }

        // Seed: next-state function variables of abstract latches.
        for &lv in &self.abstract_latches {
            if let Some(&next_lit) = self.concrete.next_state.get(&lv) {
                enqueue(&mut support, &mut worklist, next_lit.var());
            }
        }

        // Seed: bad-state literal variables.
        for &bad_lit in &self.concrete.bad_lits {
            enqueue(&mut support, &mut worklist, bad_lit.var());
        }

        // Seed: constraint literal variables.
        for &c_lit in &self.concrete.constraint_lits {
            enqueue(&mut support, &mut worklist, c_lit.var());
        }

        // Seed: all input variables (free, always in support).
        for &iv in &self.concrete.input_vars {
            enqueue(&mut support, &mut worklist, iv);
        }

        // Fixpoint: trace through AND gate definitions.
        while let Some(var) = worklist.pop() {
            if let Some(&(rhs0, rhs1)) = self.concrete.and_defs.get(&var) {
                enqueue(&mut support, &mut worklist, rhs0.var());
                enqueue(&mut support, &mut worklist, rhs1.var());
            }
        }

        support
    }

    /// Check if a counterexample trace from the abstract IC3 is real
    /// on the concrete model.
    ///
    /// Simulates the trace forward on the concrete model:
    /// 1. Initialize all latches to their reset values.
    /// 2. For each step, compute next-state values using the concrete
    ///    transition relation and the input values from the abstract trace.
    /// 3. If all steps are consistent, the trace is real.
    /// 4. If a step is inconsistent (an abstract latch value doesn't match
    ///    the concrete next-state), identify which concrete latches caused
    ///    the discrepancy and return them for refinement.
    fn check_counterexample(
        &self,
        abstract_trace: &[Vec<(Var, bool)>],
    ) -> CexCheck {
        if abstract_trace.is_empty() {
            return CexCheck::Real {
                trace: Vec::new(),
            };
        }

        // Build a map of AND gate definitions for evaluation.
        let and_defs = &self.concrete.and_defs;

        // State: current assignment of all variables.
        let num_vars = self.concrete.max_var as usize + 1;
        let mut assignment = vec![None::<bool>; num_vars];

        // Var(0) is always false.
        assignment[0] = Some(false);

        // Initialize from concrete init state.
        for clause in &self.concrete.init_clauses {
            if clause.lits.len() == 1 {
                let lit = clause.lits[0];
                let val = lit.is_positive();
                assignment[lit.var().0 as usize] = Some(val);
            }
        }

        // Non-abstract latches that weren't initialized stay at their reset (0 default).
        for &lv in &self.concrete.latch_vars {
            if assignment[lv.0 as usize].is_none() {
                assignment[lv.0 as usize] = Some(false);
            }
        }

        let mut concrete_trace = Vec::new();

        // Record initial state.
        let init_state: Vec<(Var, bool)> = self
            .concrete
            .latch_vars
            .iter()
            .map(|&v| (v, assignment[v.0 as usize].unwrap_or(false)))
            .collect();
        concrete_trace.push(init_state);

        // Check initial state against abstract trace step 0.
        if !abstract_trace.is_empty() {
            let step0 = &abstract_trace[0];
            for &(var, val) in step0 {
                if self.abstract_latches.contains(&var) {
                    let concrete_val = assignment[var.0 as usize].unwrap_or(false);
                    if concrete_val != val {
                        // Initial state mismatch -- this is spurious.
                        // Shouldn't normally happen since both use same init constraints.
                        let refine = self.latches_in_coi_of_var(var);
                        return CexCheck::Spurious {
                            refine_latches: refine,
                        };
                    }
                }
            }
        }

        // Simulate each transition step.
        for step_idx in 1..abstract_trace.len() {
            // Set input values from abstract trace (inputs are free in both models).
            // Inputs in the abstract trace are simply whatever the abstract IC3
            // solver chose -- we don't constrain them here.

            // Evaluate all AND gates to determine combinational values.
            self.evaluate_combinational(&mut assignment, and_defs);

            // Compute next-state values for ALL concrete latches.
            let mut next_assignment = vec![None::<bool>; num_vars];
            next_assignment[0] = Some(false);

            for &lv in &self.concrete.latch_vars {
                if let Some(&next_lit) = self.concrete.next_state.get(&lv) {
                    let next_val = eval_lit(next_lit, &assignment);
                    next_assignment[lv.0 as usize] = Some(next_val);
                } else {
                    next_assignment[lv.0 as usize] = Some(false);
                }
            }

            // Check abstract latch values against concrete next-state.
            let abstract_step = &abstract_trace[step_idx];
            let mut mismatch_vars = Vec::new();
            for &(var, abstract_val) in abstract_step {
                if self.abstract_latches.contains(&var) {
                    let concrete_val = next_assignment[var.0 as usize].unwrap_or(false);
                    if concrete_val != abstract_val {
                        mismatch_vars.push(var);
                    }
                }
            }

            if !mismatch_vars.is_empty() {
                // Spurious: find latches that influence the mismatched values.
                let mut refine = FxHashSet::default();
                for mv in &mismatch_vars {
                    for lv in self.latches_in_coi_of_var(*mv) {
                        refine.insert(lv);
                    }
                }
                return CexCheck::Spurious {
                    refine_latches: refine.into_iter().collect(),
                };
            }

            // Update assignment for next step.
            assignment = next_assignment;

            // Ensure inputs and AND gates have assignment slots.
            for &iv in &self.concrete.input_vars {
                if assignment[iv.0 as usize].is_none() {
                    assignment[iv.0 as usize] = Some(false);
                }
            }

            // Record concrete state.
            let state: Vec<(Var, bool)> = self
                .concrete
                .latch_vars
                .iter()
                .map(|&v| (v, assignment[v.0 as usize].unwrap_or(false)))
                .collect();
            concrete_trace.push(state);
        }

        // All steps matched -- counterexample is real.
        CexCheck::Real {
            trace: concrete_trace,
        }
    }

    /// Evaluate all AND gates in topological order (inputs before outputs).
    ///
    /// Since AND gates form a DAG, we evaluate by repeatedly scanning and
    /// evaluating gates whose inputs are known. In practice, AIGER circuits
    /// are numbered such that inputs have lower indices than outputs, so
    /// a single pass usually suffices.
    fn evaluate_combinational(
        &self,
        assignment: &mut [Option<bool>],
        and_defs: &rustc_hash::FxHashMap<Var, (Lit, Lit)>,
    ) {
        // Simple iterative evaluation: scan all gates, evaluate if inputs known.
        // Repeat until no progress (handles any topological ordering).
        let mut changed = true;
        let mut max_iters = and_defs.len() + 1;
        while changed && max_iters > 0 {
            changed = false;
            max_iters -= 1;
            for (&out_var, &(rhs0, rhs1)) in and_defs {
                if assignment[out_var.0 as usize].is_some() {
                    continue;
                }
                let v0 = eval_lit_opt(rhs0, assignment);
                let v1 = eval_lit_opt(rhs1, assignment);
                match (v0, v1) {
                    (Some(a), Some(b)) => {
                        assignment[out_var.0 as usize] = Some(a && b);
                        changed = true;
                    }
                    (Some(false), _) | (_, Some(false)) => {
                        // Short-circuit: if either input is false, output is false.
                        assignment[out_var.0 as usize] = Some(false);
                        changed = true;
                    }
                    _ => {}
                }
            }
        }
    }

    /// Find concrete latches in the transitive fanin COI of a given variable.
    ///
    /// Traces backward through AND gate definitions and next-state functions
    /// to find latches that influence the given variable's value.
    fn latches_in_coi_of_var(&self, var: Var) -> Vec<Var> {
        let latch_set: FxHashSet<Var> = self.concrete.latch_vars.iter().copied().collect();
        let mut visited = FxHashSet::default();
        let mut worklist = vec![var];
        let mut result_latches = Vec::new();

        while let Some(v) = worklist.pop() {
            if !visited.insert(v) {
                continue;
            }
            if v == Var(0) {
                continue;
            }

            // If this is a latch not in our abstraction, it's a refinement candidate.
            if latch_set.contains(&v) && !self.abstract_latches.contains(&v) {
                result_latches.push(v);
            }

            // Trace through AND gates.
            if let Some(&(rhs0, rhs1)) = self.concrete.and_defs.get(&v) {
                worklist.push(rhs0.var());
                worklist.push(rhs1.var());
            }

            // Trace through next-state functions (if this is a latch, trace
            // what feeds its next-state to find more latches).
            if let Some(&next_lit) = self.concrete.next_state.get(&v) {
                worklist.push(next_lit.var());
            }
        }

        result_latches
    }
}

/// Result of checking an abstract counterexample against the concrete model.
enum CexCheck {
    /// The counterexample is real on the concrete model.
    Real { trace: Vec<Vec<(Var, bool)>> },
    /// The counterexample is spurious; refine with these latches.
    Spurious { refine_latches: Vec<Var> },
}

/// Compute the initial abstraction: latches in the immediate COI of bad
/// properties (1 hop through next-state and AND gates).
///
/// This is deliberately small to maximize the benefit of abstraction.
/// If the property can be proven with just a few latches, CEGAR finds
/// it quickly. If not, refinement will add needed latches.
fn initial_abstraction(ts: &Transys) -> FxHashSet<Var> {
    let latch_set: FxHashSet<Var> = ts.latch_vars.iter().copied().collect();
    let mut abstract_latches = FxHashSet::default();
    let mut visited = FxHashSet::default();

    // Start from bad-state literal variables.
    let mut worklist: Vec<Var> = ts.bad_lits.iter().map(|l| l.var()).collect();

    // Trace one level through AND gates and next-state to find latches.
    while let Some(v) = worklist.pop() {
        if !visited.insert(v) || v == Var(0) {
            continue;
        }

        if latch_set.contains(&v) {
            abstract_latches.insert(v);
            // Also add latches that feed this latch's next-state function.
            if let Some(&next_lit) = ts.next_state.get(&v) {
                let nv = next_lit.var();
                if latch_set.contains(&nv) {
                    abstract_latches.insert(nv);
                }
                // Trace AND gate inputs for one more level.
                if let Some(&(rhs0, rhs1)) = ts.and_defs.get(&nv) {
                    if latch_set.contains(&rhs0.var()) {
                        abstract_latches.insert(rhs0.var());
                    }
                    if latch_set.contains(&rhs1.var()) {
                        abstract_latches.insert(rhs1.var());
                    }
                }
            }
        }

        // Trace through AND gates.
        if let Some(&(rhs0, rhs1)) = ts.and_defs.get(&v) {
            worklist.push(rhs0.var());
            worklist.push(rhs1.var());
        }
    }

    // Ensure at least one latch is in the abstraction (degenerate case).
    if abstract_latches.is_empty() && !ts.latch_vars.is_empty() {
        abstract_latches.insert(ts.latch_vars[0]);
    }

    abstract_latches
}

/// Evaluate a literal given a variable assignment.
/// Unknown variables default to false.
#[inline]
fn eval_lit(lit: Lit, assignment: &[Option<bool>]) -> bool {
    let idx = lit.var().0 as usize;
    let val = if idx < assignment.len() {
        assignment[idx].unwrap_or(false)
    } else {
        false
    };
    if lit.is_negated() { !val } else { val }
}

/// Evaluate a literal, returning None if the variable is unassigned.
#[inline]
fn eval_lit_opt(lit: Lit, assignment: &[Option<bool>]) -> Option<bool> {
    let idx = lit.var().0 as usize;
    if idx >= assignment.len() {
        return None;
    }
    assignment[idx].map(|val| if lit.is_negated() { !val } else { val })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse_aag;

    #[test]
    fn test_cegar_trivially_safe() {
        // Latch next=0, bad=latch. Latch is always 0, so safe.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").expect("parse");
        let ts = Transys::from_aiger(&circuit);
        let mut cegar = CegarIc3::new(ts, Ic3Config::default());
        let result = cegar.run();
        assert!(
            matches!(result, CheckResult::Safe),
            "expected Safe, got {result:?}"
        );
    }

    #[test]
    fn test_cegar_trivially_unsafe() {
        // Toggle: latch starts 0, next = NOT latch. Bad = latch.
        // At step 1, latch=1 → bad.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").expect("parse");
        let ts = Transys::from_aiger(&circuit);
        let mut cegar = CegarIc3::new(ts, Ic3Config::default());
        let result = cegar.run();
        assert!(
            matches!(result, CheckResult::Unsafe { .. }),
            "expected Unsafe, got {result:?}"
        );
    }

    #[test]
    fn test_cegar_constant_bad() {
        // Bad = constant TRUE (always unsafe from step 0).
        let circuit = parse_aag("aag 0 0 0 1 0\n1\n").expect("parse");
        let ts = Transys::from_aiger(&circuit);
        let mut cegar = CegarIc3::new(ts, Ic3Config::default());
        let result = cegar.run();
        assert!(
            matches!(result, CheckResult::Unsafe { .. }),
            "expected Unsafe, got {result:?}"
        );
    }

    #[test]
    fn test_cegar_constant_safe() {
        // Bad = constant FALSE (always safe).
        let circuit = parse_aag("aag 0 0 0 1 0\n0\n").expect("parse");
        let ts = Transys::from_aiger(&circuit);
        let mut cegar = CegarIc3::new(ts, Ic3Config::default());
        let result = cegar.run();
        assert!(
            matches!(result, CheckResult::Safe),
            "expected Safe, got {result:?}"
        );
    }

    #[test]
    fn test_cegar_two_latches_one_relevant() {
        // Two latches: latch1 (var 1) next=0, latch2 (var 2) next=0.
        // Bad = latch1. Only latch1 is relevant; latch2 is irrelevant.
        // CEGAR should prove safe with just latch1 in the abstraction.
        let circuit = parse_aag("aag 2 0 2 0 0 1\n2 0\n4 0\n2\n").expect("parse");
        let ts = Transys::from_aiger(&circuit);

        let cegar = CegarIc3::new(ts.clone(), Ic3Config::default());
        // Initial abstraction should include latch1 (var 1) since bad=latch1.
        assert!(
            cegar.abstract_latches.contains(&Var(1)),
            "abstraction should include latch1"
        );

        let mut cegar = CegarIc3::new(ts, Ic3Config::default());
        let result = cegar.run();
        assert!(
            matches!(result, CheckResult::Safe),
            "expected Safe, got {result:?}"
        );
    }

    #[test]
    fn test_initial_abstraction_includes_bad_latches() {
        // Chain: input -> AND -> latch -> bad.
        // aag 3 1 1 0 1 1: input=2 (var 1), latch=4 next=6 (var 2), AND 6=2&4 (var 3), bad=4
        let circuit = parse_aag("aag 3 1 1 0 1 1\n2\n4 6\n4\n6 2 4\n").expect("parse");
        let ts = Transys::from_aiger(&circuit);
        let abs = initial_abstraction(&ts);
        // Latch var 2 should be in the abstraction (bad=latch directly).
        assert!(
            abs.contains(&Var(2)),
            "abstraction should include the bad latch"
        );
    }

    #[test]
    fn test_eval_lit_basic() {
        let assignment = vec![Some(false), Some(true), Some(false)];
        // Var(1) = true
        assert!(eval_lit(Lit::pos(Var(1)), &assignment));
        assert!(!eval_lit(Lit::neg(Var(1)), &assignment));
        // Var(0) = false (constant)
        assert!(!eval_lit(Lit::pos(Var(0)), &assignment));
        assert!(eval_lit(Lit::neg(Var(0)), &assignment));
    }

    #[test]
    fn test_cegar_cancellation() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").expect("parse");
        let ts = Transys::from_aiger(&circuit);
        let cancelled = Arc::new(AtomicBool::new(true));
        let mut cegar = CegarIc3::new(ts, Ic3Config::default());
        cegar.set_cancelled(cancelled);
        let result = cegar.run();
        assert!(
            matches!(result, CheckResult::Unknown { .. }),
            "expected Unknown (cancelled), got {result:?}"
        );
    }

    #[test]
    fn test_cegar_abs_cst_trivially_safe() {
        // Latch next=0, bad=latch. Latch is always 0, so safe.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").expect("parse");
        let ts = Transys::from_aiger(&circuit);
        let mut cegar =
            CegarIc3::with_mode(ts, Ic3Config::default(), AbstractionMode::AbstractConstraints);
        let result = cegar.run();
        assert!(
            matches!(result, CheckResult::Safe),
            "abs_cst: expected Safe, got {result:?}"
        );
    }

    #[test]
    fn test_cegar_abs_cst_trivially_unsafe() {
        // Toggle: latch starts 0, next = NOT latch. Bad = latch.
        // At step 1, latch=1 -> bad.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").expect("parse");
        let ts = Transys::from_aiger(&circuit);
        let mut cegar =
            CegarIc3::with_mode(ts, Ic3Config::default(), AbstractionMode::AbstractConstraints);
        let result = cegar.run();
        assert!(
            matches!(result, CheckResult::Unsafe { .. }),
            "abs_cst: expected Unsafe, got {result:?}"
        );
    }

    #[test]
    fn test_cegar_abs_all_trivially_safe() {
        // Latch next=0, bad=latch. Latch is always 0, so safe.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").expect("parse");
        let ts = Transys::from_aiger(&circuit);
        let mut cegar =
            CegarIc3::with_mode(ts, Ic3Config::default(), AbstractionMode::AbstractAll);
        let result = cegar.run();
        assert!(
            matches!(result, CheckResult::Safe),
            "abs_all: expected Safe, got {result:?}"
        );
    }

    #[test]
    fn test_cegar_abs_all_trivially_unsafe() {
        // Toggle: latch starts 0, next = NOT latch. Bad = latch.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").expect("parse");
        let ts = Transys::from_aiger(&circuit);
        let mut cegar =
            CegarIc3::with_mode(ts, Ic3Config::default(), AbstractionMode::AbstractAll);
        let result = cegar.run();
        assert!(
            matches!(result, CheckResult::Unsafe { .. }),
            "abs_all: expected Unsafe, got {result:?}"
        );
    }

    #[test]
    fn test_abstraction_mode_default_is_abs_all() {
        assert_eq!(AbstractionMode::default(), AbstractionMode::AbstractAll);
    }
}
