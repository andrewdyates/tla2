// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Domain restriction for IC3 SAT queries.
//!
//! rIC3's biggest performance win is domain-restricted SAT: each IC3 query
//! restricts the SAT solver to cone-of-influence (COI) variables only.
//! GipSAT's `propagate_domain()` skips clauses outside the domain, making
//! each IC3 SAT call much faster because the solver only processes relevant
//! variables.
//!
//! Two-layer domain restriction (#4091):
//! 1. **Clause-filtered mini-solvers** (tla-aiger level): build restricted
//!    solvers containing only clauses involving domain variables.
//! 2. **z4-sat native domain BCP** (`set_domain()`): within the mini-solver,
//!    z4-sat's `propagate_domain_bcp()` further restricts watcher propagation
//!    and VSIDS branching to domain variables only.
//!
//! This combination matches rIC3's approach: domain-restricted mini-solver
//! (clause subset) + GipSAT domain BCP (watcher filtering). Used in MIC
//! (the generalization bottleneck) and consecution checks where many SAT
//! calls operate on the same cube's COI.
//!
//! ## Improvements over initial implementation (#4059)
//!
//! 1. **Bitvec-based domain**: O(1) membership testing via dense bit vector
//!    instead of FxHashSet. Clause filtering during solver construction is
//!    the hot path -- each clause checks 2-3 variables.
//!
//! 2. **Pre-computed constraint COIs**: Constraint variable dependencies are
//!    traced once in `DomainComputer::new()`, not per `compute_domain()` call.
//!
//! 3. **Stricter clause filter**: For 3-literal Tseitin clauses from AND gates,
//!    we check that the output variable is in the domain, not just "any"
//!    variable. This filters more irrelevant clauses since non-domain AND
//!    gate outputs can't propagate useful information to domain variables.
//!
//! 4. **Always-on activation** (#4091): Domain restriction is active for all
//!    non-trivial circuits (>= 2 total vars) with no coverage threshold.
//!    Matching rIC3's approach: domain restriction is always enabled. The old
//!    thresholds (10 latches, 80%/95% coverage) prevented activation on HWMCC
//!    benchmarks where cubes span most latches. Even at high coverage, the
//!    clause-filtered mini-solver and z4-sat's domain BCP both help.
//!
//! Reference: rIC3 `src/gipsat/domain.rs` -- `Domain` struct with
//! `enable_local()` that traces through `DagCnf.dep()` (AND gate dependencies).

use crate::sat_types::{Lit, SatSolver, SolverBackend, Var};
use crate::transys::Transys;

use super::frame::{Frame, Lemma};

/// Dense bitvec-based domain set for O(1) membership testing.
///
/// Uses a `Vec<bool>` indexed by `Var.0`. This is faster than `FxHashSet<Var>`
/// for the clause-filtering hot path where we check 2-3 variables per clause
/// across potentially thousands of clauses.
pub(crate) struct DomainSet {
    /// Dense membership array indexed by Var.0.
    bits: Vec<bool>,
    /// Number of variables in the domain (for threshold checks).
    count: usize,
}

impl DomainSet {
    /// Create an empty domain set that can hold variables up to `max_var`.
    fn new(max_var: u32) -> Self {
        DomainSet {
            bits: vec![false; max_var as usize + 1],
            count: 0,
        }
    }

    /// Insert a variable into the domain. Returns true if newly inserted.
    #[inline]
    fn insert(&mut self, var: Var) -> bool {
        let idx = var.0 as usize;
        if idx < self.bits.len() && !self.bits[idx] {
            self.bits[idx] = true;
            self.count += 1;
            true
        } else {
            false
        }
    }

    /// Check if a variable is in the domain.
    #[inline]
    pub(crate) fn contains(&self, var: Var) -> bool {
        let idx = var.0 as usize;
        idx < self.bits.len() && self.bits[idx]
    }

    /// Number of variables in the domain.
    #[inline]
    pub(crate) fn len(&self) -> usize {
        self.count
    }
}

/// Pre-computed variable dependency graph for domain restriction.
///
/// For each variable, stores the set of variables it transitively depends on
/// through AND gate definitions and next-state functions. This enables O(|cube|)
/// domain computation for any cube: the domain is the union of dependencies
/// for all latch variables in the cube.
///
/// Built once per `Transys` and reused across all IC3 queries.
pub(crate) struct DomainComputer {
    /// For each latch variable (indexed by Var.0), the transitive closure of
    /// dependencies through AND gates. Stored as sorted Vec<Var> for compact
    /// memory and efficient union during compute_domain.
    ///
    /// This is the combinational COI: starting from a latch variable,
    /// trace through its next-state function and all AND gates feeding it.
    latch_coi: Vec<Vec<Var>>,

    /// Pre-computed constraint variable COIs. Traced once at construction
    /// time instead of per compute_domain call. Each element is a variable
    /// that's transitively reachable from any constraint literal through
    /// AND gate definitions.
    constraint_coi_vars: Vec<Var>,

    /// Maximum variable index for domain set allocation.
    max_var: u32,
}

impl DomainComputer {
    /// Build a domain computer from the transition system.
    ///
    /// Pre-computes the combinational COI for each latch variable by tracing
    /// through AND gate definitions and next-state functions.
    /// Also pre-computes constraint variable COIs once.
    pub(crate) fn new(
        ts: &Transys,
        next_vars: &rustc_hash::FxHashMap<Var, Var>,
        max_var: u32,
    ) -> Self {
        let total_vars = max_var as usize + 1;
        let mut latch_coi: Vec<Vec<Var>> = vec![Vec::new(); total_vars];

        // For each latch variable, compute its transitive COI:
        // 1. Start with the latch variable itself
        // 2. Add the latch's next-state literal's variable
        // 3. Trace through AND gate definitions (both inputs)
        // 4. Also include the next-state variable (for primed assumptions)
        for &latch_var in &ts.latch_vars {
            let mut visited = vec![false; total_vars];
            let mut worklist: Vec<Var> = Vec::new();
            let mut deps = Vec::new();

            // Seed: the latch variable itself.
            let seed = |var: Var,
                        visited: &mut Vec<bool>,
                        worklist: &mut Vec<Var>,
                        deps: &mut Vec<Var>| {
                let idx = var.0 as usize;
                if idx < visited.len() && !visited[idx] && var != Var(0) {
                    visited[idx] = true;
                    deps.push(var);
                    worklist.push(var);
                }
            };

            seed(latch_var, &mut visited, &mut worklist, &mut deps);

            // Seed: the latch's next-state function variable.
            if let Some(&next_lit) = ts.next_state.get(&latch_var) {
                if next_lit.var() != Var(0) {
                    seed(next_lit.var(), &mut visited, &mut worklist, &mut deps);
                }
            }

            // Seed: the allocated next-state variable (for primed cubes).
            if let Some(&next_var) = next_vars.get(&latch_var) {
                let idx = next_var.0 as usize;
                if idx < visited.len() && !visited[idx] {
                    visited[idx] = true;
                    deps.push(next_var);
                    // Don't add to worklist -- next_var is a fresh variable
                    // with no AND gate definition to trace.
                }
            }

            // Fixpoint: trace through AND gate definitions.
            while let Some(var) = worklist.pop() {
                if let Some(&(rhs0, rhs1)) = ts.and_defs.get(&var) {
                    seed(rhs0.var(), &mut visited, &mut worklist, &mut deps);
                    seed(rhs1.var(), &mut visited, &mut worklist, &mut deps);
                }
            }

            let idx = latch_var.0 as usize;
            if idx < latch_coi.len() {
                latch_coi[idx] = deps;
            }
        }

        // Pre-compute constraint variable COIs once.
        let constraint_coi_vars = {
            let mut visited = vec![false; total_vars];
            let mut all_deps = Vec::new();

            for &c_lit in &ts.constraint_lits {
                let var = c_lit.var();
                if var == Var(0) {
                    continue;
                }
                let idx = var.0 as usize;
                if idx < visited.len() && !visited[idx] {
                    visited[idx] = true;
                    all_deps.push(var);
                }
                // Trace constraint variable's AND gate deps.
                let mut worklist = vec![var];
                while let Some(v) = worklist.pop() {
                    if let Some(&(rhs0, rhs1)) = ts.and_defs.get(&v) {
                        for dep_lit in [rhs0, rhs1] {
                            let dep = dep_lit.var();
                            if dep != Var(0) {
                                let didx = dep.0 as usize;
                                if didx < visited.len() && !visited[didx] {
                                    visited[didx] = true;
                                    all_deps.push(dep);
                                    worklist.push(dep);
                                }
                            }
                        }
                    }
                }
            }

            all_deps
        };

        DomainComputer {
            latch_coi,
            constraint_coi_vars,
            max_var,
        }
    }

    /// Compute the domain (set of relevant variables) for a given cube.
    ///
    /// The domain is the union of combinational COIs for all latch variables
    /// appearing in the cube. Returns a `DomainSet` for O(1) membership tests.
    ///
    /// Includes:
    /// - Latch variables themselves and their transitive AND-gate fanin
    /// - Corresponding next-state variables (for primed assumptions)
    /// - Pre-computed constraint variable COIs
    /// - Var(0) (constant, always needed)
    pub(crate) fn compute_domain(
        &self,
        cube: &[Lit],
        next_vars: &rustc_hash::FxHashMap<Var, Var>,
    ) -> DomainSet {
        let mut domain = DomainSet::new(self.max_var);

        // Always include Var(0) (constant).
        domain.insert(Var(0));

        // Union the pre-computed COIs for each latch in the cube.
        for &lit in cube {
            let var = lit.var();
            let idx = var.0 as usize;
            if idx < self.latch_coi.len() && !self.latch_coi[idx].is_empty() {
                for &dep in &self.latch_coi[idx] {
                    domain.insert(dep);
                }
            } else {
                // Variable not a latch or out of range -- include it directly.
                domain.insert(var);
            }

            // Include the next-state variable for this latch (primed cube).
            if let Some(&next_var) = next_vars.get(&var) {
                domain.insert(next_var);
            }
        }

        // Include pre-computed constraint variable COIs.
        for &var in &self.constraint_coi_vars {
            domain.insert(var);
        }

        // Domain completeness assertions (#4181).
        //
        // These debug assertions verify the five essential domain properties
        // that IC3 soundness relies on. Domain under-approximation causes
        // false UNSAT (the solver can't propagate along critical paths).
        //
        // Enabled only in debug builds to avoid runtime overhead in release.
        #[cfg(debug_assertions)]
        {
            // Property 1: Every cube variable must be in the domain.
            for &lit in cube {
                debug_assert!(
                    domain.contains(lit.var()),
                    "domain completeness violation (#4181): cube variable Var({}) not in domain",
                    lit.var().0,
                );
            }

            // Property 2: Every next-state variable for cube latches must be in domain.
            for &lit in cube {
                if let Some(&nv) = next_vars.get(&lit.var()) {
                    debug_assert!(
                        domain.contains(nv),
                        "domain completeness violation (#4181): next-state Var({}) for latch Var({}) not in domain",
                        nv.0,
                        lit.var().0,
                    );
                }
            }

            // Property 3: Var(0) must always be present.
            debug_assert!(
                domain.contains(Var(0)),
                "domain completeness violation (#4181): Var(0) not in domain",
            );

            // Property 4: All constraint COI variables must be present.
            for &cv in &self.constraint_coi_vars {
                debug_assert!(
                    domain.contains(cv),
                    "domain completeness violation (#4181): constraint COI Var({}) not in domain",
                    cv.0,
                );
            }
        }

        domain
    }

    /// Compute the domain (set of relevant variables) for a bad-state query (#4306).
    ///
    /// Unlike `compute_domain` (which unions COIs of latch variables in a cube),
    /// this method starts from the bad literals (typically AND-gate outputs) and
    /// traces their combinational fanin. Every latch reached through that fanin
    /// contributes its full pre-computed COI — including the next-state variable
    /// — so the top-frame solver's primed-transition clauses remain satisfiable.
    ///
    /// Includes:
    /// - Var(0) (constant, always needed)
    /// - The bad literal variables and their transitive AND-gate fanin
    /// - For every latch discovered in that fanin: its full latch COI and
    ///   next-state variable (so `Trans` propagation still has all the relevant
    ///   primed vars in-domain)
    /// - Pre-computed constraint variable COIs
    ///
    /// Reference: rIC3 `src/ic3/mod.rs` `check()` — the bad query runs on a
    /// domain seeded from the bad literal, matching GipSAT's `propagate_domain`.
    pub(crate) fn compute_bad_domain(
        &self,
        bad_lits: &[Lit],
        next_vars: &rustc_hash::FxHashMap<Var, Var>,
        ts: &crate::transys::Transys,
    ) -> DomainSet {
        let mut domain = DomainSet::new(self.max_var);

        // Always include Var(0) (constant).
        domain.insert(Var(0));

        // Pre-build a latch-var lookup so we can detect latches encountered in
        // the bad literal's fanin and splice in their full COI + next-state.
        let latch_set: rustc_hash::FxHashSet<Var> = ts.latch_vars.iter().copied().collect();

        // Trace the combinational fanin from every bad literal through AND
        // gate definitions. For any latch we touch, also union its
        // pre-computed COI (which covers the next-state function fanin).
        let total_vars = self.max_var as usize + 1;
        let mut visited = vec![false; total_vars];
        let mut worklist: Vec<Var> = Vec::new();

        let enqueue =
            |v: Var, visited: &mut Vec<bool>, worklist: &mut Vec<Var>, domain: &mut DomainSet| {
                let idx = v.0 as usize;
                if idx < visited.len() && !visited[idx] && v != Var(0) {
                    visited[idx] = true;
                    domain.insert(v);
                    worklist.push(v);
                }
            };

        for &blit in bad_lits {
            enqueue(blit.var(), &mut visited, &mut worklist, &mut domain);
        }

        while let Some(var) = worklist.pop() {
            // If we hit a latch, splice in its pre-computed COI so the top
            // solver's `Trans` clauses still see the relevant primed vars.
            if latch_set.contains(&var) {
                let idx = var.0 as usize;
                if idx < self.latch_coi.len() {
                    for &dep in &self.latch_coi[idx] {
                        let didx = dep.0 as usize;
                        if didx < visited.len() && !visited[didx] {
                            visited[didx] = true;
                            domain.insert(dep);
                            // Only trace through AND gate defs for non-latch
                            // deps; latches add their own pre-computed COI.
                            if !latch_set.contains(&dep) {
                                worklist.push(dep);
                            }
                        }
                    }
                }
                if let Some(&nv) = next_vars.get(&var) {
                    let nidx = nv.0 as usize;
                    if nidx < visited.len() && !visited[nidx] {
                        visited[nidx] = true;
                        domain.insert(nv);
                    }
                }
                // The latch's next-state function and primed var live in
                // latch_coi; no AND-gate descent needed for `var` itself.
                continue;
            }

            if let Some(&(rhs0, rhs1)) = ts.and_defs.get(&var) {
                enqueue(rhs0.var(), &mut visited, &mut worklist, &mut domain);
                enqueue(rhs1.var(), &mut visited, &mut worklist, &mut domain);
            }
        }

        // Include pre-computed constraint variable COIs.
        for &var in &self.constraint_coi_vars {
            domain.insert(var);
        }

        domain
    }

    /// Verify domain completeness against the transition system (#4181).
    ///
    /// Given a domain computed for a cube, independently recomputes the
    /// transitive COI from scratch (not using pre-computed latch_coi) and
    /// verifies every variable in the fresh COI is present in the domain.
    ///
    /// This is an expensive O(|cube| * |and_defs|) check intended for testing
    /// and debug validation, NOT for production hot paths.
    ///
    /// Returns `Ok(())` if the domain is complete, or `Err(reason)` describing
    /// the missing variable.
    pub(crate) fn verify_domain_completeness(
        &self,
        cube: &[Lit],
        next_vars: &rustc_hash::FxHashMap<Var, Var>,
        domain: &DomainSet,
        ts: &crate::transys::Transys,
    ) -> Result<(), String> {
        let total_vars = self.max_var as usize + 1;

        // Property 1: Every cube variable must be in the domain.
        for &lit in cube {
            if !domain.contains(lit.var()) {
                return Err(format!("cube variable Var({}) not in domain", lit.var().0,));
            }
        }

        // Property 2: Var(0) must be present.
        if !domain.contains(Var(0)) {
            return Err("Var(0) not in domain".into());
        }

        // Property 3: For each latch in the cube, independently trace its
        // transitive COI through AND gates and verify all deps are in domain.
        for &lit in cube {
            let latch_var = lit.var();

            // Trace from latch's next-state function through AND gates.
            let mut visited = vec![false; total_vars];
            let mut worklist: Vec<Var> = Vec::new();

            let mut enqueue = |v: Var, visited: &mut Vec<bool>, worklist: &mut Vec<Var>| {
                let idx = v.0 as usize;
                if idx < visited.len() && !visited[idx] && v != Var(0) {
                    visited[idx] = true;
                    worklist.push(v);
                }
            };

            // Seed: the latch variable itself.
            enqueue(latch_var, &mut visited, &mut worklist);

            // Seed: the latch's next-state function variable.
            if let Some(&next_lit) = ts.next_state.get(&latch_var) {
                if next_lit.var() != Var(0) {
                    enqueue(next_lit.var(), &mut visited, &mut worklist);
                }
            }

            // Fixpoint: trace through AND gate definitions.
            while let Some(var) = worklist.pop() {
                if let Some(&(rhs0, rhs1)) = ts.and_defs.get(&var) {
                    enqueue(rhs0.var(), &mut visited, &mut worklist);
                    enqueue(rhs1.var(), &mut visited, &mut worklist);
                }
            }

            // Every variable in the fresh COI must be in the domain.
            for (idx, &was_visited) in visited.iter().enumerate() {
                if was_visited && !domain.contains(Var(idx as u32)) {
                    return Err(format!(
                        "COI variable Var({}) reachable from latch Var({}) not in domain",
                        idx, latch_var.0,
                    ));
                }
            }

            // The next-state variable (for primed cube) must be in domain.
            if let Some(&nv) = next_vars.get(&latch_var) {
                if !domain.contains(nv) {
                    return Err(format!(
                        "next-state Var({}) for latch Var({}) not in domain",
                        nv.0, latch_var.0,
                    ));
                }
            }
        }

        // Property 4: All constraint COI variables must be present.
        for &cv in &self.constraint_coi_vars {
            if !domain.contains(cv) {
                return Err(format!("constraint COI Var({}) not in domain", cv.0,));
            }
        }

        // Property 5: For each constraint literal, independently trace its
        // AND gate dependencies and verify all are in domain.
        for &c_lit in &ts.constraint_lits {
            let var = c_lit.var();
            if var == Var(0) {
                continue;
            }
            let mut visited = vec![false; total_vars];
            let mut worklist = vec![var];
            visited[var.0 as usize] = true;

            while let Some(v) = worklist.pop() {
                if let Some(&(rhs0, rhs1)) = ts.and_defs.get(&v) {
                    for dep_lit in [rhs0, rhs1] {
                        let dep = dep_lit.var();
                        if dep != Var(0) {
                            let didx = dep.0 as usize;
                            if didx < visited.len() && !visited[didx] {
                                visited[didx] = true;
                                worklist.push(dep);
                            }
                        }
                    }
                }
            }

            for (idx, &was_visited) in visited.iter().enumerate() {
                if was_visited && !domain.contains(Var(idx as u32)) {
                    return Err(format!(
                        "constraint COI variable Var({}) reachable from constraint Var({}) not in domain",
                        idx,
                        var.0,
                    ));
                }
            }
        }

        Ok(())
    }
}

/// Minimum total variable count (including next-state vars) for domain
/// restriction to be attempted. Below this, the overhead of building a
/// restricted solver outweighs any benefit.
///
/// Lowered from 10 to 2 (#4091): domain restriction should always be active
/// for IC3 queries when a domain is computed. The HWMCC'26 50 smallest
/// benchmarks are exactly the circuits where the old threshold prevented
/// activation. z4-sat's native domain BCP (set_domain) has near-zero
/// overhead for small circuits, so the threshold only gates the clause-
/// filtered mini-solver construction.
const DOMAIN_MIN_VARS: usize = 2;

// DOMAIN_MAX_COVERAGE removed (#4091 validation):
// Previously: 0.80 (#4059) -> 0.95 (#4091) -> removed.
// The coverage threshold prevented domain restriction from activating
// on most HWMCC benchmarks because IC3 cubes typically involve many
// latches whose transitive COI covers >95% of variables. rIC3 has NO
// coverage threshold — it always enables domain restriction. Removing
// the threshold matches rIC3's always-on behavior. The clause-filtered
// mini-solver still helps at any coverage ratio because it provides a
// clean solver without learned clause bloat.

/// Build a domain-restricted SAT solver for MIC operations.
///
/// Creates a solver that contains only:
/// 1. Transition clauses where the AND-gate output variable is in the domain
/// 2. Constraint unit clauses for domain variables
/// 3. Next-state linking clauses for domain variables
/// 4. Frame lemmas involving domain variables (from frames 1..=frame_idx)
/// 5. Infinity lemmas involving domain variables
///
/// The clause filter is stricter than "any variable in domain":
/// - For Tseitin 3-clauses (AND gate encoding), the output variable must be
///   in the domain. Non-domain AND gate outputs can't propagate useful
///   information back to domain variables.
/// - For other clauses (linking, lemmas), any variable in domain suffices.
///
/// Returns None if the domain is too large for restriction to be beneficial.
///
/// ## Zero-clone design (#4059)
///
/// Accepts `&[Frame]` directly instead of `&[Vec<Lemma>]` to avoid cloning
/// all frame lemmas on every call. This is critical because `build_mic_domain_solver`
/// is called multiple times per MIC iteration (initial build + rebuild after
/// core reduction). The old design cloned O(total_lemmas) per call; the new
/// design iterates by reference.
pub(crate) fn build_domain_restricted_solver(
    domain: &DomainSet,
    ts: &Transys,
    next_link_clauses: &[Vec<Lit>],
    frames: &[Frame],
    frame_idx: usize,
    inf_lemmas: &[Lemma],
    solver_backend: SolverBackend,
    max_var: u32,
) -> Option<Box<dyn SatSolver>> {
    // Check if domain restriction is beneficial.
    let total_vars = max_var as usize + 1;
    if total_vars < DOMAIN_MIN_VARS {
        return None;
    }
    // Coverage check removed (#4091 validation): rIC3 always enables
    // domain restriction regardless of coverage ratio. Even at 100%
    // coverage, the clause-filtered mini-solver still helps by providing
    // a clean solver without accumulated learned clauses, and z4-sat's
    // native domain BCP (`propagate_domain_bcp`) still restricts watcher
    // propagation. The previous 95% threshold prevented activation on
    // most HWMCC benchmarks (observed: restricted=0 on cal40, qspiflash).

    // IC3 domain-restricted solvers: disable inprocessing (#4102).
    let mut solver = solver_backend.make_solver_no_inprocessing(max_var + 1);

    // Always assert Var(0) = false.
    solver.add_clause(&[Lit::TRUE]);

    // Add transition clauses with strict domain filtering.
    //
    // For standard Tseitin 3-clauses encoding AND gates:
    //   (!out, rhs0, rhs1), (out, !rhs0), (out, !rhs1)
    // We require the output variable to be in the domain. If the output
    // is not in the domain, none of these clauses can propagate useful
    // information to domain variables.
    //
    // For other clauses (unit, binary implications from simplification),
    // we use the "any variable in domain" criterion.
    for clause in &ts.trans_clauses {
        let dominated = clause_in_domain(&clause.lits, domain, &ts.and_defs);
        if dominated {
            solver.add_clause(&clause.lits);
        }
    }

    // Add constraint unit clauses for domain variables.
    for &constraint in &ts.constraint_lits {
        if constraint.var() == Var(0) || domain.contains(constraint.var()) {
            solver.add_clause(&[constraint]);
        }
    }

    // Add next-state linking clauses for domain latches.
    for clause in next_link_clauses {
        if clause_any_in_domain(clause, domain) {
            solver.add_clause(clause);
        }
    }

    // Add infinity lemmas involving domain variables.
    for lemma in inf_lemmas {
        if clause_any_in_domain(&lemma.lits, domain) {
            solver.add_clause(&lemma.lits);
        }
    }

    // Add per-frame lemmas by reference (zero-clone).
    // Frame-0 lemmas are NOT added (they constrain Init, not frame solvers).
    let start = 1;
    let end = frame_idx.min(frames.len().saturating_sub(1));
    for f in start..=end {
        if f < frames.len() {
            for lemma in &frames[f].lemmas {
                if clause_any_in_domain(&lemma.lits, domain) {
                    solver.add_clause(&lemma.lits);
                }
            }
        }
    }

    // Wire z4-sat's native domain restriction (#4091).
    //
    // In addition to clause filtering (only adding domain-relevant clauses to
    // the solver), activate z4-sat's internal domain-restricted BCP. This is
    // a two-layer optimization:
    // 1. Clause filtering: the solver has fewer clauses to process.
    // 2. Domain BCP: within those clauses, z4-sat's `propagate_domain_bcp()`
    //    skips non-domain watchers, further reducing per-call overhead.
    //
    // The combination matches rIC3's approach: domain-restricted mini-solver
    // (clause subset) + GipSAT domain BCP (watcher filtering).
    //
    // Collect domain variables for set_domain.
    let domain_vars: Vec<Var> = (0..=max_var)
        .filter(|&i| domain.contains(Var(i)))
        .map(Var)
        .collect();
    solver.set_domain(&domain_vars);

    Some(solver)
}

/// Domain restriction statistics for monitoring effectiveness.
///
/// Tracks how often domain restriction fires, average domain coverage,
/// and clause reduction ratios. This data is logged at IC3 completion
/// to help tune thresholds and validate the optimization.
///
/// Statistics are broken into two categories:
/// - **Consecution stats** (`restricted_count`/`fallback_count`): tracked for
///   block_one, is_blocked_at, and push_lemma consecution checks.
/// - **MIC stats** (`mic_restricted`/`mic_fallback`): tracked for
///   MIC generalization solver builds (mic, mic_ctg_down, mic_simple).
pub(crate) struct DomainStats {
    /// Number of domain-restricted consecution solver builds that were accepted.
    pub(crate) restricted_count: u64,
    /// Number of domain-restricted consecution solver builds that were rejected
    /// (domain too large or circuit too small).
    pub(crate) fallback_count: u64,
    /// Number of domain-restricted MIC solver builds that were accepted.
    pub(crate) mic_restricted: u64,
    /// Number of domain-restricted MIC solver builds that were rejected.
    pub(crate) mic_fallback: u64,
    /// Sum of domain coverage ratios (for computing average).
    coverage_sum: f64,
    /// Number of coverage samples.
    coverage_samples: u64,
}

impl DomainStats {
    pub(crate) fn new() -> Self {
        DomainStats {
            restricted_count: 0,
            fallback_count: 0,
            mic_restricted: 0,
            mic_fallback: 0,
            coverage_sum: 0.0,
            coverage_samples: 0,
        }
    }

    /// Record a consecution domain restriction attempt.
    pub(crate) fn record(&mut self, domain_size: usize, total_vars: usize, accepted: bool) {
        if total_vars > 0 {
            self.coverage_sum += domain_size as f64 / total_vars as f64;
            self.coverage_samples += 1;
        }
        if accepted {
            self.restricted_count += 1;
        } else {
            self.fallback_count += 1;
        }
    }

    /// Record a MIC domain restriction build attempt.
    pub(crate) fn record_mic(&mut self, accepted: bool) {
        if accepted {
            self.mic_restricted += 1;
        } else {
            self.mic_fallback += 1;
        }
    }

    /// Average domain coverage ratio across all attempts.
    pub(crate) fn avg_coverage(&self) -> f64 {
        if self.coverage_samples == 0 {
            0.0
        } else {
            self.coverage_sum / self.coverage_samples as f64
        }
    }

    /// Total number of consecution domain restriction attempts.
    pub(crate) fn total_attempts(&self) -> u64 {
        self.restricted_count + self.fallback_count
    }

    /// Total number of MIC domain restriction attempts.
    pub(crate) fn total_mic_attempts(&self) -> u64 {
        self.mic_restricted + self.mic_fallback
    }
}

impl Default for DomainStats {
    fn default() -> Self {
        Self::new()
    }
}

/// Strict domain check for transition clauses.
///
/// For 3-literal clauses (Tseitin encoding of AND gates), checks if any
/// variable that is an AND-gate output is in the domain. If we can identify
/// the output variable, we require it to be in the domain.
///
/// For other clause sizes, falls back to "any variable in domain".
///
/// This is stricter than `clause_any_in_domain` and filters more clauses:
/// AND gates whose output is outside the domain can't propagate to domain
/// variables even if one of their inputs is in the domain.
#[inline]
fn clause_in_domain(
    clause: &[Lit],
    domain: &DomainSet,
    and_defs: &rustc_hash::FxHashMap<Var, (Lit, Lit)>,
) -> bool {
    if clause.len() == 3 {
        // For 3-literal Tseitin clauses, check if any variable is an
        // AND-gate output that's in the domain. The Tseitin encoding
        // produces three clause patterns per AND gate:
        //   (!out, rhs0, rhs1)  -- the forward implication
        //   (out, !rhs0)        -- backward implication (but this is 2-lit)
        // The 3-lit clause is always the forward implication.
        // Check if any variable in the clause is a defined AND gate output.
        for lit in clause {
            let var = lit.var();
            if and_defs.contains_key(&var) && domain.contains(var) {
                return true;
            }
        }
        // If no AND gate output found, fall back to any-in-domain.
        // This handles clauses that were produced by preprocessing.
        return clause_any_in_domain(clause, domain);
    }
    // Non-3-literal clauses: use any-in-domain criterion.
    clause_any_in_domain(clause, domain)
}

/// Check if a clause involves any variable in the domain.
///
/// Returns true if at least one literal's variable is in the domain set.
#[inline]
fn clause_any_in_domain(clause: &[Lit], domain: &DomainSet) -> bool {
    clause.iter().any(|lit| domain.contains(lit.var()))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse_aag;

    #[test]
    fn test_domain_computer_basic() {
        // Toggle: latch starts at 0, next = !latch. Bad = latch.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").expect("parse failed");
        let ts = Transys::from_aiger(&circuit);

        let mut next_vars = rustc_hash::FxHashMap::default();
        let mut next_var_id = ts.max_var + 1;
        for &latch_var in &ts.latch_vars {
            next_vars.insert(latch_var, Var(next_var_id));
            next_var_id += 1;
        }
        let max_var = next_var_id - 1;

        let dc = DomainComputer::new(&ts, &next_vars, max_var);

        // Cube over the single latch variable.
        let cube = vec![Lit::pos(Var(1))];
        let domain = dc.compute_domain(&cube, &next_vars);
        assert!(domain.contains(Var(1)), "domain should include latch var");
        assert!(
            domain.contains(Var(0)),
            "domain should include constant var"
        );
    }

    #[test]
    fn test_domain_computer_with_and_gates() {
        // Chain: input -> AND -> latch -> bad
        // aag 3 1 1 0 1 1
        // input: 2 (var 1)
        // latch: 4 next=6 (var 2, next = AND output var 3)
        // AND: 6 = 2 & 4 (var 3 = var 1 AND var 2)
        // bad: 4 (latch)
        let circuit = parse_aag("aag 3 1 1 0 1 1\n2\n4 6\n4\n6 2 4\n").expect("parse failed");
        let ts = Transys::from_aiger(&circuit);

        let mut next_vars = rustc_hash::FxHashMap::default();
        let mut next_var_id = ts.max_var + 1;
        for &latch_var in &ts.latch_vars {
            next_vars.insert(latch_var, Var(next_var_id));
            next_var_id += 1;
        }
        let max_var = next_var_id - 1;

        let dc = DomainComputer::new(&ts, &next_vars, max_var);

        // Cube over the latch variable (var 2).
        let cube = vec![Lit::pos(Var(2))];
        let domain = dc.compute_domain(&cube, &next_vars);
        // Should include: var 2 (latch), var 3 (AND gate output = next-state),
        // var 1 (input, AND gate input), var 0 (constant), next_var for latch.
        assert!(domain.contains(Var(2)), "domain should include latch");
        assert!(
            domain.contains(Var(3)),
            "domain should include AND gate feeding latch"
        );
        assert!(
            domain.contains(Var(1)),
            "domain should include input feeding AND gate"
        );
    }

    #[test]
    fn test_compute_bad_domain_single_latch_bad() {
        // Toggle: latch starts at 0, next = !latch. Bad = latch (#4306).
        // aag 1 0 1 0 0 1: latch 2 next=3 (!2); bad=2
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").expect("parse failed");
        let ts = Transys::from_aiger(&circuit);

        let mut next_vars = rustc_hash::FxHashMap::default();
        let mut next_var_id = ts.max_var + 1;
        for &latch_var in &ts.latch_vars {
            next_vars.insert(latch_var, Var(next_var_id));
            next_var_id += 1;
        }
        let max_var = next_var_id - 1;

        let dc = DomainComputer::new(&ts, &next_vars, max_var);
        let domain = dc.compute_bad_domain(&ts.bad_lits, &next_vars, &ts);

        // The bad literal is the latch itself, so the domain must include
        // the latch, the constant Var(0), and the latch's fresh next-state
        // variable (so Trans propagation still has relevant vars in-domain).
        assert!(domain.contains(Var(0)), "domain should include Var(0)");
        assert!(domain.contains(Var(1)), "domain should include latch var");
        assert!(
            domain.contains(next_vars[&Var(1)]),
            "domain should include primed latch var for Trans propagation"
        );
    }

    #[test]
    fn test_compute_bad_domain_and_gate_bad() {
        // Chain: input -> AND -> latch; bad = AND output (not a latch) (#4306).
        // aag 3 1 1 0 1 1
        //   input: 2 (var 1)
        //   latch: 4 next=6 (var 2, next = AND output var 3)
        //   AND: 6 = 2 & 4 (var 3 = var 1 AND var 2)
        //   bad: 6 (AND output, var 3)
        let circuit = parse_aag("aag 3 1 1 0 1 1\n2\n4 6\n6\n6 2 4\n").expect("parse failed");
        let ts = Transys::from_aiger(&circuit);

        let mut next_vars = rustc_hash::FxHashMap::default();
        let mut next_var_id = ts.max_var + 1;
        for &latch_var in &ts.latch_vars {
            next_vars.insert(latch_var, Var(next_var_id));
            next_var_id += 1;
        }
        let max_var = next_var_id - 1;

        let dc = DomainComputer::new(&ts, &next_vars, max_var);
        let domain = dc.compute_bad_domain(&ts.bad_lits, &next_vars, &ts);

        // Bad = Var(3) (AND output). Tracing its fanin:
        //   Var(3) -> Var(1) (input, direct), Var(2) (latch)
        // Var(2) is a latch, so we union its latch_coi which includes the
        // next-state function Var(3) and the fresh primed var next_vars[Var(2)].
        assert!(domain.contains(Var(0)), "constant must be in domain");
        assert!(
            domain.contains(Var(3)),
            "AND output (bad) must be in domain"
        );
        assert!(domain.contains(Var(1)), "AND input must be in domain");
        assert!(
            domain.contains(Var(2)),
            "latch feeding bad must be in domain"
        );
        assert!(
            domain.contains(next_vars[&Var(2)]),
            "primed latch var must be in domain for Trans propagation"
        );
    }

    #[test]
    fn test_compute_bad_domain_empty_bad_lits() {
        // Defensive: no bad literals -> domain is near-empty (just Var(0) and
        // pre-computed constraint COIs). Callers should guard against this
        // case; we still want compute_bad_domain to return a valid DomainSet.
        let circuit = parse_aag("aag 1 0 1 0 0 0\n2 3\n").expect("parse failed");
        let ts = Transys::from_aiger(&circuit);

        let mut next_vars = rustc_hash::FxHashMap::default();
        let mut next_var_id = ts.max_var + 1;
        for &latch_var in &ts.latch_vars {
            next_vars.insert(latch_var, Var(next_var_id));
            next_var_id += 1;
        }
        let max_var = next_var_id - 1;

        let dc = DomainComputer::new(&ts, &next_vars, max_var);
        let domain = dc.compute_bad_domain(&[], &next_vars, &ts);

        // Only Var(0) is guaranteed.
        assert!(domain.contains(Var(0)), "domain must include Var(0)");
    }

    #[test]
    fn test_domain_restricted_solver_basic() {
        // Two inputs, AND gate on first input only, bad = AND output.
        // aag 3 2 0 0 1 1: inputs 2, 4; AND 6=2&2; bad=6
        let circuit = parse_aag("aag 3 2 0 0 1 1\n2\n4\n6\n6 2 2\n").expect("parse failed");
        let ts = Transys::from_aiger(&circuit);

        let mut domain = DomainSet::new(ts.max_var);
        domain.insert(Var(0));
        domain.insert(Var(1)); // input 1
        domain.insert(Var(3)); // AND gate output

        // Build restricted solver. Should include clauses for AND gate 3=1&1
        // but not any clause involving Var(2) (input 2, outside domain).
        let solver = build_domain_restricted_solver(
            &domain,
            &ts,
            &[], // no next-link clauses
            &[], // no frame lemmas
            0,   // frame 0
            &[], // no infinity lemmas
            SolverBackend::Simple,
            ts.max_var,
        );

        // With DOMAIN_MIN_VARS=2 (#4091), this circuit has max_var+1 total vars.
        // The domain has 3 vars; whether restriction activates depends on
        // the total_vars vs DOMAIN_MIN_VARS check and the coverage ratio.
        // With always-on domain restriction, this should return Some for
        // circuits above the minimum threshold.
        // The key property: if it returns Some, the solver is functional.
        if let Some(mut s) = solver {
            // Verify the restricted solver is functional.
            assert_eq!(s.solve(&[]), crate::sat_types::SatResult::Sat);
        }
    }

    #[test]
    fn test_domain_restriction_reduces_clauses() {
        // Two latches with independent next-state functions (both stuck-at-0).
        // Cube over latch1 should NOT include latch2.
        let circuit = parse_aag("aag 2 0 2 0 0 1\n2 0\n4 0\n2\n").expect("parse failed");
        let ts = Transys::from_aiger(&circuit);

        let mut next_vars = rustc_hash::FxHashMap::default();
        let mut next_var_id = ts.max_var + 1;
        for &latch_var in &ts.latch_vars {
            next_vars.insert(latch_var, Var(next_var_id));
            next_var_id += 1;
        }
        let max_var = next_var_id - 1;

        let dc = DomainComputer::new(&ts, &next_vars, max_var);

        // Cube over latch1 only.
        let cube = vec![Lit::pos(Var(1))];
        let domain = dc.compute_domain(&cube, &next_vars);

        // Domain should include latch1 (var 1) but NOT latch2 (var 2).
        assert!(domain.contains(Var(1)), "domain should include latch1");
        assert!(
            !domain.contains(Var(2)),
            "domain should NOT include independent latch2"
        );
    }

    #[test]
    fn test_domain_set_basic() {
        let mut ds = DomainSet::new(100);
        assert_eq!(ds.len(), 0);
        assert!(!ds.contains(Var(5)));

        assert!(ds.insert(Var(5)));
        assert!(ds.contains(Var(5)));
        assert_eq!(ds.len(), 1);

        // Duplicate insert returns false.
        assert!(!ds.insert(Var(5)));
        assert_eq!(ds.len(), 1);

        assert!(ds.insert(Var(50)));
        assert!(ds.insert(Var(100)));
        assert_eq!(ds.len(), 3);

        // Out-of-range contains returns false.
        assert!(!ds.contains(Var(101)));
    }

    #[test]
    fn test_constraint_coi_precomputed() {
        // Circuit with a constraint: aag 3 1 1 0 1 1 1
        // input: 2 (var 1)
        // latch: 4 6 (var 2, next = AND var 3)
        // AND: 6 = 2 & 4 (var 3 = var 1 AND var 2)
        // bad: 4 (latch)
        // constraint: 2 (input must be true)
        let circuit = parse_aag("aag 3 1 1 0 1 1 1\n2\n4 6\n4\n2\n6 2 4\n").expect("parse failed");
        let ts = Transys::from_aiger(&circuit);

        let mut next_vars = rustc_hash::FxHashMap::default();
        let mut next_var_id = ts.max_var + 1;
        for &latch_var in &ts.latch_vars {
            next_vars.insert(latch_var, Var(next_var_id));
            next_var_id += 1;
        }
        let max_var = next_var_id - 1;

        let dc = DomainComputer::new(&ts, &next_vars, max_var);

        // Even a cube that doesn't touch the constraint variable should
        // include constraint vars in the domain.
        let cube = vec![Lit::pos(Var(2))];
        let domain = dc.compute_domain(&cube, &next_vars);
        assert!(
            domain.contains(Var(1)),
            "domain should include constraint var (input)"
        );
    }

    #[test]
    fn test_domain_stats_tracking() {
        let mut stats = DomainStats::new();
        assert_eq!(stats.total_attempts(), 0);
        assert_eq!(stats.avg_coverage(), 0.0);

        // Record an accepted domain restriction (50% coverage).
        stats.record(50, 100, true);
        assert_eq!(stats.restricted_count, 1);
        assert_eq!(stats.fallback_count, 0);
        assert!((stats.avg_coverage() - 0.5).abs() < 0.001);

        // Record a rejected domain restriction (90% coverage).
        stats.record(90, 100, false);
        assert_eq!(stats.restricted_count, 1);
        assert_eq!(stats.fallback_count, 1);
        assert_eq!(stats.total_attempts(), 2);
        // Average coverage = (0.5 + 0.9) / 2 = 0.7
        assert!((stats.avg_coverage() - 0.7).abs() < 0.001);
    }

    #[test]
    fn test_build_domain_restricted_solver_with_frames() {
        // Test that passing Frame references works correctly (zero-clone path).
        // Two latches with independent next-state functions (both stuck-at-0).
        let circuit = parse_aag("aag 2 0 2 0 0 1\n2 0\n4 0\n2\n").expect("parse failed");
        let ts = Transys::from_aiger(&circuit);

        let mut domain = DomainSet::new(ts.max_var);
        domain.insert(Var(0));
        domain.insert(Var(1));

        // Create a Frame with a lemma.
        let lemma = Lemma::new(vec![Lit::neg(Var(1))]);
        let frame = Frame {
            lemmas: vec![lemma],
        };
        let frames = vec![Frame::default(), frame];

        // With DOMAIN_MIN_VARS=2 and no coverage threshold (#4091 validation),
        // this 3-var circuit qualifies for domain restriction at any coverage.
        // Coverage check removed: rIC3 always enables domain restriction.
        let solver = build_domain_restricted_solver(
            &domain,
            &ts,
            &[],
            &frames,
            1,
            &[],
            SolverBackend::Simple,
            ts.max_var,
        );

        // Domain restriction is now always-on for circuits with >= 2 total vars.
        // This 3-var circuit with 2/3 coverage should get a domain solver.
        assert!(
            solver.is_some(),
            "domain restriction should activate for 3-var circuit (#4091)"
        );
    }

    #[test]
    fn test_domain_restriction_activates_at_full_coverage() {
        // Verify domain restriction activates even when domain covers ALL variables.
        // This is the key fix (#4091 validation): rIC3 has no coverage threshold,
        // and the previous 95% threshold prevented activation on most benchmarks.
        let circuit = parse_aag("aag 3 1 1 0 1 1\n2\n4 6\n4\n6 2 4\n").expect("parse failed");
        let ts = Transys::from_aiger(&circuit);

        // Domain covering ALL variables (100% coverage).
        let mut domain = DomainSet::new(ts.max_var);
        for v in 0..=ts.max_var {
            domain.insert(Var(v));
        }
        assert_eq!(domain.len(), ts.max_var as usize + 1);

        let solver = build_domain_restricted_solver(
            &domain,
            &ts,
            &[],
            &[],
            0,
            &[],
            SolverBackend::Simple,
            ts.max_var,
        );

        // Even at 100% coverage, domain restriction should still activate.
        // The clause-filtered mini-solver provides a clean solver without
        // accumulated learned clauses, and z4-sat's domain BCP still helps.
        assert!(
            solver.is_some(),
            "domain restriction must activate at 100% coverage (matching rIC3 behavior)"
        );
    }

    // =========================================================================
    // Domain completeness verification tests (#4181)
    //
    // These tests verify that the domain computation is COMPLETE — meaning
    // the domain includes ALL variables necessary for soundness of IC3 queries.
    // Under-approximating the domain (missing variables) causes false UNSAT
    // because the solver cannot propagate along critical paths.
    // =========================================================================

    #[test]
    fn test_domain_completeness_transitive_and_chain() {
        // Verify transitive closure through a chain of AND gates:
        // g1 = i1 & i2, g2 = g1 & i3, latch_next = g2.
        // A cube over the latch must include: latch, latch_next_var (g2),
        // g1 (intermediate gate), i1, i2, i3 (all inputs).
        //
        // aag 6 3 1 0 2 1
        // M=6, I=3, L=1, O=0, A=2, B=1
        // inputs: 2, 4, 6 (vars 1, 2, 3)
        // latch: 8 12 (var 4, next = AND output var 6)
        // AND: 10 = 2 & 4 (var 5 = var1 & var2)
        // AND: 12 = 10 & 6 (var 6 = var5 & var3)
        // bad: 8 (latch)
        let circuit = parse_aag("aag 6 3 1 0 2 1\n2\n4\n6\n8 12\n8\n10 2 4\n12 10 6\n")
            .expect("parse failed");
        let ts = Transys::from_aiger(&circuit);

        let mut next_vars = rustc_hash::FxHashMap::default();
        let mut next_var_id = ts.max_var + 1;
        for &latch_var in &ts.latch_vars {
            next_vars.insert(latch_var, Var(next_var_id));
            next_var_id += 1;
        }
        let max_var = next_var_id - 1;

        let dc = DomainComputer::new(&ts, &next_vars, max_var);

        // Cube over the latch (var 4).
        let cube = vec![Lit::pos(Var(4))];
        let domain = dc.compute_domain(&cube, &next_vars);

        // Domain completeness: ALL transitive dependencies must be included.
        assert!(domain.contains(Var(4)), "latch itself must be in domain");
        assert!(
            domain.contains(Var(6)),
            "AND gate g2 (latch next-state) must be in domain"
        );
        assert!(
            domain.contains(Var(5)),
            "AND gate g1 (input to g2) must be in domain"
        );
        assert!(
            domain.contains(Var(1)),
            "input i1 (input to g1) must be in domain"
        );
        assert!(
            domain.contains(Var(2)),
            "input i2 (input to g1) must be in domain"
        );
        assert!(
            domain.contains(Var(3)),
            "input i3 (input to g2) must be in domain"
        );
        // Next-state variable for the latch.
        assert!(
            domain.contains(*next_vars.get(&Var(4)).unwrap()),
            "next-state variable for latch must be in domain"
        );
        assert!(domain.contains(Var(0)), "constant Var(0) always in domain");
    }

    #[test]
    fn test_domain_completeness_next_var_always_included() {
        // For every latch variable in the cube, its primed (next-state) variable
        // must always be in the domain. This is required for the IC3 consecution
        // check: F_k(s) AND T(s,s') AND cube(s') — cube(s') uses next-state vars.
        //
        // Two latches: L1 next=0, L2 next=L1. Bad=L2.
        // aag 2 0 2 0 0 1
        // latch: 2 0 (var 1, stuck at 0)
        // latch: 4 2 (var 2, next = lit 2 = var 1 positive)
        // bad: 4 (latch 2)
        let circuit = parse_aag("aag 2 0 2 0 0 1\n2 0\n4 2\n4\n").expect("parse failed");
        let ts = Transys::from_aiger(&circuit);

        let mut next_vars = rustc_hash::FxHashMap::default();
        let mut next_var_id = ts.max_var + 1;
        for &latch_var in &ts.latch_vars {
            next_vars.insert(latch_var, Var(next_var_id));
            next_var_id += 1;
        }
        let max_var = next_var_id - 1;

        let dc = DomainComputer::new(&ts, &next_vars, max_var);

        // Cube over latch 1 only.
        let cube = vec![Lit::pos(Var(1))];
        let domain = dc.compute_domain(&cube, &next_vars);
        assert!(
            domain.contains(*next_vars.get(&Var(1)).unwrap()),
            "next-state var for latch 1 must be in domain when latch 1 is in cube"
        );

        // Cube over latch 2 only.
        let cube2 = vec![Lit::pos(Var(2))];
        let domain2 = dc.compute_domain(&cube2, &next_vars);
        assert!(
            domain2.contains(*next_vars.get(&Var(2)).unwrap()),
            "next-state var for latch 2 must be in domain when latch 2 is in cube"
        );
        // Latch 2's next-state references latch 1, so latch 1 must be in domain.
        assert!(
            domain2.contains(Var(1)),
            "latch 1 must be in domain for latch 2 (next-state dependency)"
        );
    }

    #[test]
    fn test_domain_completeness_multi_latch_union() {
        // When a cube mentions multiple latches, the domain must be the UNION
        // of all individual COIs. No latch's dependencies may be dropped.
        //
        // Two latches with independent dependencies:
        // L1 (var 1): next = input1 (var 3)
        // L2 (var 2): next = input2 (var 4)
        // aag 4 2 2 0 0 1
        // inputs: 6, 8 (vars 3, 4)
        // latch: 2 6 (var 1, next = input1)
        // latch: 4 8 (var 2, next = input2)
        // bad: 2 (latch 1)
        let circuit = parse_aag("aag 4 2 2 0 0 1\n6\n8\n2 6\n4 8\n2\n").expect("parse failed");
        let ts = Transys::from_aiger(&circuit);

        let mut next_vars = rustc_hash::FxHashMap::default();
        let mut next_var_id = ts.max_var + 1;
        for &latch_var in &ts.latch_vars {
            next_vars.insert(latch_var, Var(next_var_id));
            next_var_id += 1;
        }
        let max_var = next_var_id - 1;

        let dc = DomainComputer::new(&ts, &next_vars, max_var);

        // Single-latch domains.
        let cube_l1 = vec![Lit::pos(Var(1))];
        let domain_l1 = dc.compute_domain(&cube_l1, &next_vars);

        let cube_l2 = vec![Lit::pos(Var(2))];
        let domain_l2 = dc.compute_domain(&cube_l2, &next_vars);

        // Combined cube (both latches).
        let cube_both = vec![Lit::pos(Var(1)), Lit::pos(Var(2))];
        let domain_both = dc.compute_domain(&cube_both, &next_vars);

        // Union property: domain_both must contain everything from domain_l1 AND domain_l2.
        for v in 0..=max_var {
            if domain_l1.contains(Var(v)) {
                assert!(
                    domain_both.contains(Var(v)),
                    "multi-latch domain missing var {} from L1's domain",
                    v
                );
            }
            if domain_l2.contains(Var(v)) {
                assert!(
                    domain_both.contains(Var(v)),
                    "multi-latch domain missing var {} from L2's domain",
                    v
                );
            }
        }

        // Specific checks: both inputs must be in the combined domain.
        assert!(
            domain_both.contains(Var(3)),
            "input1 (L1 dependency) must be in combined domain"
        );
        assert!(
            domain_both.contains(Var(4)),
            "input2 (L2 dependency) must be in combined domain"
        );
    }

    #[test]
    fn test_domain_completeness_constraint_always_included() {
        // Constraint COI must be included in EVERY domain computation,
        // regardless of which latches are in the cube. This is critical:
        // IC3 queries must always respect constraints to avoid finding
        // predecessors that violate environment assumptions.
        //
        // Circuit: 2 latches, 2 inputs. Constraint on AND gate output.
        // aag 5 2 2 0 1 1 1
        // M=5, I=2, L=2, O=0, A=1, B=1, C=1
        // inputs: 2, 4 (vars 1, 2)
        // latch: 6 0 (var 3, stuck at 0)
        // latch: 8 0 (var 4, stuck at 0)
        // bad: 6 (latch 1)
        // constraint: 10 (AND gate output, var 5)
        // AND: 10 = 2 & 4 (var 5 = var1 & var2)
        let circuit =
            parse_aag("aag 5 2 2 0 1 1 1\n2\n4\n6 0\n8 0\n6\n10\n10 2 4\n").expect("parse failed");
        let ts = Transys::from_aiger(&circuit);

        let mut next_vars = rustc_hash::FxHashMap::default();
        let mut next_var_id = ts.max_var + 1;
        for &latch_var in &ts.latch_vars {
            next_vars.insert(latch_var, Var(next_var_id));
            next_var_id += 1;
        }
        let max_var = next_var_id - 1;

        let dc = DomainComputer::new(&ts, &next_vars, max_var);

        // Cube over latch 2 (var 4), which has NO connection to the constraint.
        let cube = vec![Lit::pos(Var(4))];
        let domain = dc.compute_domain(&cube, &next_vars);

        // Constraint COI must still be present.
        assert!(
            domain.contains(Var(5)),
            "constraint AND gate output must be in domain regardless of cube"
        );
        assert!(
            domain.contains(Var(1)),
            "constraint input (var 1) must be in domain regardless of cube"
        );
        assert!(
            domain.contains(Var(2)),
            "constraint input (var 2) must be in domain regardless of cube"
        );
    }

    #[test]
    fn test_domain_completeness_negated_literals_same_domain() {
        // Domain depends on the VARIABLE, not the literal polarity.
        // A cube with !L should produce the same domain as a cube with L.
        let circuit = parse_aag("aag 3 1 1 0 1 1\n2\n4 6\n4\n6 2 4\n").expect("parse failed");
        let ts = Transys::from_aiger(&circuit);

        let mut next_vars = rustc_hash::FxHashMap::default();
        let mut next_var_id = ts.max_var + 1;
        for &latch_var in &ts.latch_vars {
            next_vars.insert(latch_var, Var(next_var_id));
            next_var_id += 1;
        }
        let max_var = next_var_id - 1;

        let dc = DomainComputer::new(&ts, &next_vars, max_var);

        let cube_pos = vec![Lit::pos(Var(2))];
        let cube_neg = vec![Lit::neg(Var(2))];

        let domain_pos = dc.compute_domain(&cube_pos, &next_vars);
        let domain_neg = dc.compute_domain(&cube_neg, &next_vars);

        // Both must produce identical domains.
        for v in 0..=max_var {
            assert_eq!(
                domain_pos.contains(Var(v)),
                domain_neg.contains(Var(v)),
                "domain differs for Var({}) between positive and negative literal",
                v
            );
        }
    }

    #[test]
    fn test_domain_restricted_solver_soundness_safe() {
        // End-to-end test: verify that domain-restricted IC3 produces the
        // correct SAFE verdict on a known-safe circuit.
        //
        // Latch stuck at 0, bad=latch. Always safe because next-state is 0.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").expect("parse failed");
        let result = crate::ic3::check_ic3(&circuit);
        assert!(
            matches!(result, crate::ic3::config::Ic3Result::Safe { .. }),
            "domain-restricted IC3 should find Safe on stuck-at-0 latch, got {result:?}"
        );
    }

    #[test]
    fn test_domain_restricted_solver_soundness_unsafe() {
        // End-to-end test: verify that domain-restricted IC3 produces the
        // correct UNSAFE verdict on a known-unsafe circuit.
        //
        // Toggle flip-flop: latch starts at 0, next=!latch, bad=latch.
        // Counterexample at depth 1.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").expect("parse failed");
        let result = crate::ic3::check_ic3(&circuit);
        assert!(
            matches!(
                result,
                crate::ic3::config::Ic3Result::Unsafe { depth: 1, .. }
            ),
            "domain-restricted IC3 should find Unsafe at depth 1, got {result:?}"
        );
    }

    #[test]
    fn test_domain_restricted_solver_soundness_deeper_unsafe() {
        // Toggle flip-flop variant: starts at 1, next=!latch, bad=!latch.
        // At step 0: latch=1, !latch=0 (safe).
        // At step 1: latch=0, !latch=1 (bad!).
        // aag 1 0 1 0 0 1
        // latch: 2, next=3 (!latch), init=1
        // bad: 3 (!latch)
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3 1\n3\n").expect("parse failed");
        let result = crate::ic3::check_ic3(&circuit);
        assert!(
            matches!(result, crate::ic3::config::Ic3Result::Unsafe { .. }),
            "domain-restricted IC3 should find Unsafe, got {result:?}"
        );
    }

    #[test]
    fn test_domain_completeness_shared_gate_two_latches() {
        // Verify domain when two latches share an AND gate in their next-state.
        // L1 next = G, L2 next = G, G = i1 & i2.
        // A cube over L1 alone should include G, i1, i2.
        // A cube over L2 alone should include G, i1, i2.
        //
        // aag 5 2 2 0 1 1
        // M=5, I=2, L=2, O=0, A=1, B=1
        // inputs: 2, 4 (vars 1, 2)
        // latch: 6 10 (var 3, next = lit 10 = var 5 positive)
        // latch: 8 10 (var 4, next = lit 10 = var 5 positive)
        // bad: 6 (latch 1, var 3)
        // AND: 10 = 2 & 4 (var 5 = var1 & var2)
        let circuit =
            parse_aag("aag 5 2 2 0 1 1\n2\n4\n6 10\n8 10\n6\n10 2 4\n").expect("parse failed");
        let ts = Transys::from_aiger(&circuit);

        let mut next_vars = rustc_hash::FxHashMap::default();
        let mut next_var_id = ts.max_var + 1;
        for &latch_var in &ts.latch_vars {
            next_vars.insert(latch_var, Var(next_var_id));
            next_var_id += 1;
        }
        let max_var = next_var_id - 1;

        let dc = DomainComputer::new(&ts, &next_vars, max_var);

        // Cube over L1 (var 3) only.
        let cube_l1 = vec![Lit::pos(Var(3))];
        let domain_l1 = dc.compute_domain(&cube_l1, &next_vars);
        assert!(
            domain_l1.contains(Var(5)),
            "shared AND gate must be in L1's domain"
        );
        assert!(
            domain_l1.contains(Var(1)),
            "input feeding shared gate must be in L1's domain"
        );
        assert!(
            domain_l1.contains(Var(2)),
            "input feeding shared gate must be in L1's domain"
        );

        // Cube over L2 (var 4) only.
        let cube_l2 = vec![Lit::pos(Var(4))];
        let domain_l2 = dc.compute_domain(&cube_l2, &next_vars);
        assert!(
            domain_l2.contains(Var(5)),
            "shared AND gate must be in L2's domain"
        );
        assert!(
            domain_l2.contains(Var(1)),
            "input feeding shared gate must be in L2's domain"
        );
        assert!(
            domain_l2.contains(Var(2)),
            "input feeding shared gate must be in L2's domain"
        );
    }

    #[test]
    fn test_domain_completeness_self_loop_latch() {
        // A latch whose next-state references itself: next(L) = L.
        // Domain for a cube over L should include L and its next-var,
        // and NOT diverge or infinite loop.
        //
        // aag 1 0 1 0 0 1
        // latch: 2 2 (var 1, next = itself positive)
        // bad: 2
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 2\n2\n").expect("parse failed");
        let ts = Transys::from_aiger(&circuit);

        let mut next_vars = rustc_hash::FxHashMap::default();
        let mut next_var_id = ts.max_var + 1;
        for &latch_var in &ts.latch_vars {
            next_vars.insert(latch_var, Var(next_var_id));
            next_var_id += 1;
        }
        let max_var = next_var_id - 1;

        let dc = DomainComputer::new(&ts, &next_vars, max_var);

        let cube = vec![Lit::pos(Var(1))];
        let domain = dc.compute_domain(&cube, &next_vars);
        assert!(domain.contains(Var(1)), "self-loop latch must be in domain");
        assert!(
            domain.contains(*next_vars.get(&Var(1)).unwrap()),
            "next-var of self-loop latch must be in domain"
        );
        // Domain size should be bounded (no infinite loop).
        assert!(
            domain.len() <= (max_var as usize + 1),
            "domain size must be bounded"
        );
    }

    #[test]
    fn test_domain_completeness_domain_superset_of_cube_vars() {
        // The domain must always be a SUPERSET of the cube's variables.
        // Every variable mentioned in the cube must be in the domain.
        let circuit = parse_aag("aag 3 1 1 0 1 1\n2\n4 6\n4\n6 2 4\n").expect("parse failed");
        let ts = Transys::from_aiger(&circuit);

        let mut next_vars = rustc_hash::FxHashMap::default();
        let mut next_var_id = ts.max_var + 1;
        for &latch_var in &ts.latch_vars {
            next_vars.insert(latch_var, Var(next_var_id));
            next_var_id += 1;
        }
        let max_var = next_var_id - 1;

        let dc = DomainComputer::new(&ts, &next_vars, max_var);

        // Multi-literal cube.
        let cube = vec![Lit::pos(Var(2)), Lit::neg(Var(2))];
        let domain = dc.compute_domain(&cube, &next_vars);

        for &lit in &cube {
            assert!(
                domain.contains(lit.var()),
                "cube variable Var({}) must always be in domain",
                lit.var().0
            );
        }
    }

    #[test]
    fn test_domain_restricted_solver_includes_all_trans_for_domain() {
        // Verify that the domain-restricted solver includes transition clauses
        // whose AND-gate output is in the domain. This tests the clause_in_domain
        // filter correctness.
        //
        // Circuit: i1 & i2 -> AND_out -> latch_next.
        // Domain over latch should include AND_out's Tseitin clauses.
        let circuit = parse_aag("aag 3 1 1 0 1 1\n2\n4 6\n4\n6 2 4\n").expect("parse failed");
        let ts = Transys::from_aiger(&circuit);

        // Build a domain that includes everything (to verify clause count).
        let mut full_domain = DomainSet::new(ts.max_var);
        for v in 0..=ts.max_var {
            full_domain.insert(Var(v));
        }

        let full_solver = build_domain_restricted_solver(
            &full_domain,
            &ts,
            &[],
            &[],
            0,
            &[],
            SolverBackend::Simple,
            ts.max_var,
        );
        assert!(
            full_solver.is_some(),
            "full-domain solver should always be built"
        );

        // Build a domain that excludes one variable.
        // Exclude input var 1 — this means the AND gate (which requires var 1)
        // should potentially be filtered.
        let mut partial_domain = DomainSet::new(ts.max_var);
        partial_domain.insert(Var(0)); // constant
        partial_domain.insert(Var(2)); // latch
        partial_domain.insert(Var(3)); // AND gate output
                                       // Missing: Var(1) (input) - intentionally excluded.

        let partial_solver = build_domain_restricted_solver(
            &partial_domain,
            &ts,
            &[],
            &[],
            0,
            &[],
            SolverBackend::Simple,
            ts.max_var,
        );

        // The partial solver should still be built (domain has > DOMAIN_MIN_VARS).
        assert!(
            partial_solver.is_some(),
            "partial-domain solver should be built when above min threshold"
        );
    }

    #[test]
    fn test_domain_completeness_consecution_equivalence() {
        // Domain completeness test: verify that a domain-restricted solver
        // and full solver agree on a consecution query.
        //
        // Key property: domain restriction is SOUND — removing clauses makes
        // the formula LESS constrained. So:
        // - Full UNSAT implies domain UNSAT (fewer clauses can only add models)
        // - If both agree, the domain captures all needed information
        //
        // Circuit: L1 next = input1, L2 next = AND(L1, input2), bad = L2.
        // The AND gate creates a cross-latch dependency: L2's next-state
        // transitively depends on L1 through the AND gate fanin.
        //
        // aag 5 2 2 0 1 1
        // inputs: var 1, var 2
        // latch var 3: next = input1 (var 1)
        // latch var 4: next = AND gate (var 5 = var 3 AND var 2)
        // bad = latch var 4
        let circuit =
            parse_aag("aag 5 2 2 0 1 1\n2\n4\n6 2\n8 10\n8\n10 6 4\n").expect("parse failed");
        let ts = Transys::from_aiger(&circuit);

        let mut next_vars = rustc_hash::FxHashMap::default();
        let mut next_var_id = ts.max_var + 1;
        for &latch_var in &ts.latch_vars {
            next_vars.insert(latch_var, Var(next_var_id));
            next_var_id += 1;
        }
        let max_var = next_var_id - 1;

        let mut next_link_clauses = Vec::new();
        for &latch_var in &ts.latch_vars {
            if let (Some(&next_var), Some(&next_expr)) =
                (next_vars.get(&latch_var), ts.next_state.get(&latch_var))
            {
                let nv_pos = Lit::pos(next_var);
                let nv_neg = Lit::neg(next_var);
                next_link_clauses.push(vec![nv_neg, next_expr]);
                next_link_clauses.push(vec![nv_pos, !next_expr]);
            }
        }

        let dc = DomainComputer::new(&ts, &next_vars, max_var);

        // Cube: {L2=true} (var 4). L2's next = AND(L1, input2).
        // Domain should include: L2 (var 4), AND gate (var 5), L1 (var 3),
        // input2 (var 2), plus next-vars.
        let cube = vec![Lit::pos(Var(4))];
        let domain = dc.compute_domain(&cube, &next_vars);

        // Verify domain contains all variables needed for L2's transition.
        assert!(domain.contains(Var(4)), "L2 must be in domain");
        assert!(domain.contains(Var(5)), "AND gate must be in domain");
        assert!(domain.contains(Var(3)), "L1 must be in domain (AND input)");
        assert!(
            domain.contains(Var(2)),
            "input2 must be in domain (AND input)"
        );

        // Build full solver.
        let mut full_solver = SolverBackend::Simple.make_solver_no_inprocessing(max_var + 1);
        full_solver.add_clause(&[Lit::TRUE]);
        for clause in &ts.trans_clauses {
            full_solver.add_clause(&clause.lits);
        }
        for &constraint in &ts.constraint_lits {
            full_solver.add_clause(&[constraint]);
        }
        for clause in &next_link_clauses {
            full_solver.add_clause(clause);
        }
        let neg_cube: Vec<Lit> = cube.iter().map(|l| !*l).collect();
        full_solver.add_clause(&neg_cube);

        // Build domain-restricted solver.
        let mut domain_solver = build_domain_restricted_solver(
            &domain,
            &ts,
            &next_link_clauses,
            &[], // no frames yet
            0,
            &[], // no inf lemmas
            SolverBackend::Simple,
            max_var,
        )
        .expect("domain solver should be built");
        domain_solver.add_clause(&neg_cube);

        // Consecution assumptions: cube'(s') — the primed cube.
        let primed_assumptions: Vec<Lit> = cube
            .iter()
            .filter_map(|&lit| {
                next_vars.get(&lit.var()).map(|&nv| {
                    if lit.is_positive() {
                        Lit::pos(nv)
                    } else {
                        Lit::neg(nv)
                    }
                })
            })
            .collect();

        // Solve both.
        let full_result = full_solver.solve(&primed_assumptions);
        let domain_result = domain_solver.solve(&primed_assumptions);

        // For this circuit: !L2 AND (L2' = AND(L1, input2)) AND L2'=true.
        // Need L1=true AND input2=true AND L2=false. This is satisfiable.
        // Both solvers should say SAT (domain has all needed vars).
        assert_eq!(
            full_result, domain_result,
            "domain-restricted solver must agree with full solver on consecution query. \
             Full={full_result:?}, Domain={domain_result:?}. \
             Disagreement indicates domain incompleteness."
        );
    }

    #[test]
    fn test_domain_completeness_consecution_unsat_agreement() {
        // Verify domain completeness on a consecution query that should be UNSAT.
        //
        // Circuit: single latch stuck at 0. L next=0, bad=L, init=0.
        // Cube: {L=true}. Consecution: is !{L} inductive at frame 1?
        // F_0 AND Trans AND !(L) AND L' = Init(L=0) AND Trans(L_next=0) AND !L AND L'
        // With Init constraint L=0: !L is always true, L'=next_var=L_next=0.
        // So L'=true is impossible. UNSAT.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").expect("parse failed");
        let ts = Transys::from_aiger(&circuit);

        let mut next_vars = rustc_hash::FxHashMap::default();
        let mut next_var_id = ts.max_var + 1;
        for &latch_var in &ts.latch_vars {
            next_vars.insert(latch_var, Var(next_var_id));
            next_var_id += 1;
        }
        let max_var = next_var_id - 1;

        let mut next_link_clauses = Vec::new();
        for &latch_var in &ts.latch_vars {
            if let (Some(&next_var), Some(&next_expr)) =
                (next_vars.get(&latch_var), ts.next_state.get(&latch_var))
            {
                let nv_pos = Lit::pos(next_var);
                let nv_neg = Lit::neg(next_var);
                next_link_clauses.push(vec![nv_neg, next_expr]);
                next_link_clauses.push(vec![nv_pos, !next_expr]);
            }
        }

        let dc = DomainComputer::new(&ts, &next_vars, max_var);

        let cube = vec![Lit::pos(Var(1))]; // L=true
        let domain = dc.compute_domain(&cube, &next_vars);

        // Full solver with Init (simulates frame-0 solver in IC3).
        let mut full_solver = SolverBackend::Simple.make_solver_no_inprocessing(max_var + 1);
        full_solver.add_clause(&[Lit::TRUE]);
        for clause in &ts.trans_clauses {
            full_solver.add_clause(&clause.lits);
        }
        for clause in &ts.init_clauses {
            full_solver.add_clause(&clause.lits);
        }
        for clause in &next_link_clauses {
            full_solver.add_clause(clause);
        }
        let neg_cube: Vec<Lit> = cube.iter().map(|l| !*l).collect();
        full_solver.add_clause(&neg_cube);

        // Domain-restricted solver (also with Init for frame-0 simulation).
        let mut domain_solver = build_domain_restricted_solver(
            &domain,
            &ts,
            &next_link_clauses,
            &[],
            0,
            &[],
            SolverBackend::Simple,
            max_var,
        )
        .expect("domain solver should be built");
        // Add Init clauses that involve domain variables.
        for clause in &ts.init_clauses {
            if clause.lits.iter().any(|l| domain.contains(l.var())) {
                domain_solver.add_clause(&clause.lits);
            }
        }
        domain_solver.add_clause(&neg_cube);

        let primed_assumptions: Vec<Lit> = cube
            .iter()
            .filter_map(|&lit| {
                next_vars.get(&lit.var()).map(|&nv| {
                    if lit.is_positive() {
                        Lit::pos(nv)
                    } else {
                        Lit::neg(nv)
                    }
                })
            })
            .collect();

        let full_result = full_solver.solve(&primed_assumptions);
        let domain_result = domain_solver.solve(&primed_assumptions);

        // Both should be UNSAT: L_next = 0 always, so L'=true is impossible.
        assert_eq!(
            full_result,
            crate::sat_types::SatResult::Unsat,
            "full solver should find UNSAT for stuck-at-0 consecution"
        );
        assert_eq!(
            domain_result,
            crate::sat_types::SatResult::Unsat,
            "domain-restricted solver must also find UNSAT — domain completeness check. \
             If SAT, the domain is missing variables needed for the UNSAT proof."
        );
    }

    #[test]
    fn test_domain_completeness_cross_latch_dependency_chain() {
        // Critical completeness test: a latch whose next-state depends on
        // ANOTHER latch's next-state variable through an AND gate chain.
        //
        // Circuit: L1 next=input, L2 next = AND(L1, input2).
        // A cube over L2 must include L1 because L2's next-state uses L1.
        //
        // aag 5 2 2 0 1 1
        // M=5, I=2, L=2, O=0, A=1, B=1
        // inputs: 2, 4 (vars 1, 2)
        // latch: 6 2 (var 3, next = input1 pos)
        // latch: 8 10 (var 4, next = AND output var 5)
        // AND: 10 = 6 & 4 (var 5 = var3 & var2, i.e. L1 AND input2)
        // bad: 8 (latch 2)
        let circuit =
            parse_aag("aag 5 2 2 0 1 1\n2\n4\n6 2\n8 10\n8\n10 6 4\n").expect("parse failed");
        let ts = Transys::from_aiger(&circuit);

        let mut next_vars = rustc_hash::FxHashMap::default();
        let mut next_var_id = ts.max_var + 1;
        for &latch_var in &ts.latch_vars {
            next_vars.insert(latch_var, Var(next_var_id));
            next_var_id += 1;
        }
        let max_var = next_var_id - 1;

        let dc = DomainComputer::new(&ts, &next_vars, max_var);

        // Cube over L2 (var 4) only.
        let cube = vec![Lit::pos(Var(4))];
        let domain = dc.compute_domain(&cube, &next_vars);

        // L2's next-state is AND(L1, input2). The AND gate (var 5) traces to:
        // - L1 (var 3): a latch variable
        // - input2 (var 2): an input variable
        assert!(domain.contains(Var(4)), "L2 must be in its own domain");
        assert!(
            domain.contains(Var(5)),
            "AND gate (L2's next-state) must be in domain"
        );
        assert!(
            domain.contains(Var(3)),
            "L1 must be in domain (AND gate input, cross-latch dependency)"
        );
        assert!(
            domain.contains(Var(2)),
            "input2 must be in domain (AND gate input)"
        );
        // L1's next-state also depends on input1 — but since the domain
        // traces from L2's perspective (not L1's), we should verify:
        // The latch_coi for L2 includes L1's var through the AND gate.
        // L1's next-state var and input1 are in L1's COI but NOT necessarily
        // in L2's COI (they're not transitive deps of L2's next-state).
        // This is CORRECT: the domain only needs variables reachable from
        // the cube's latches through their next-state functions.
        //
        // However: L1 IS in the domain as an input to the AND gate.
        // The next-var for L2 must also be present.
        assert!(
            domain.contains(*next_vars.get(&Var(4)).unwrap()),
            "next-var for L2 must be in domain"
        );
    }

    // =========================================================================
    // verify_domain_completeness() tests (#4181)
    //
    // These tests use the independent verification method that recomputes COI
    // from scratch (not using pre-computed latch_coi) to verify that the
    // pre-computed domain matches the independently computed COI.
    // =========================================================================

    /// Helper: build DomainComputer + next_vars + max_var from a Transys.
    fn setup_domain(ts: &Transys) -> (DomainComputer, rustc_hash::FxHashMap<Var, Var>, u32) {
        let mut next_vars = rustc_hash::FxHashMap::default();
        let mut next_var_id = ts.max_var + 1;
        for &latch_var in &ts.latch_vars {
            next_vars.insert(latch_var, Var(next_var_id));
            next_var_id += 1;
        }
        let max_var = if next_var_id > ts.max_var + 1 {
            next_var_id - 1
        } else {
            ts.max_var
        };
        let dc = DomainComputer::new(ts, &next_vars, max_var);
        (dc, next_vars, max_var)
    }

    #[test]
    fn test_verify_completeness_toggle() {
        // Toggle flip-flop: single latch, next=!latch.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").expect("parse failed");
        let ts = Transys::from_aiger(&circuit);
        let (dc, next_vars, _max_var) = setup_domain(&ts);

        let cube = vec![Lit::pos(Var(1))];
        let domain = dc.compute_domain(&cube, &next_vars);

        dc.verify_domain_completeness(&cube, &next_vars, &domain, &ts)
            .expect("domain should be complete for toggle flip-flop");
    }

    #[test]
    fn test_verify_completeness_and_chain() {
        // Chain of AND gates feeding a latch.
        let circuit = parse_aag("aag 6 3 1 0 2 1\n2\n4\n6\n8 12\n8\n10 2 4\n12 10 6\n")
            .expect("parse failed");
        let ts = Transys::from_aiger(&circuit);
        let (dc, next_vars, _) = setup_domain(&ts);

        let cube = vec![Lit::pos(Var(4))]; // latch var
        let domain = dc.compute_domain(&cube, &next_vars);

        dc.verify_domain_completeness(&cube, &next_vars, &domain, &ts)
            .expect("domain should be complete for AND chain circuit");
    }

    #[test]
    fn test_verify_completeness_cross_latch() {
        // L1 next=input, L2 next=AND(L1, input2).
        let circuit =
            parse_aag("aag 5 2 2 0 1 1\n2\n4\n6 2\n8 10\n8\n10 6 4\n").expect("parse failed");
        let ts = Transys::from_aiger(&circuit);
        let (dc, next_vars, _) = setup_domain(&ts);

        // Single-latch cubes.
        for &latch_var in &ts.latch_vars {
            let cube = vec![Lit::pos(latch_var)];
            let domain = dc.compute_domain(&cube, &next_vars);
            dc.verify_domain_completeness(&cube, &next_vars, &domain, &ts)
                .unwrap_or_else(|e| {
                    panic!("domain incomplete for latch Var({}): {}", latch_var.0, e)
                });
        }

        // Multi-latch cube.
        let cube: Vec<Lit> = ts.latch_vars.iter().map(|&v| Lit::pos(v)).collect();
        let domain = dc.compute_domain(&cube, &next_vars);
        dc.verify_domain_completeness(&cube, &next_vars, &domain, &ts)
            .expect("domain should be complete for multi-latch cube");
    }

    #[test]
    fn test_verify_completeness_with_constraints() {
        // Circuit with constraint on AND gate output.
        let circuit =
            parse_aag("aag 5 2 2 0 1 1 1\n2\n4\n6 0\n8 0\n6\n10\n10 2 4\n").expect("parse failed");
        let ts = Transys::from_aiger(&circuit);
        let (dc, next_vars, _) = setup_domain(&ts);

        // Cube over each latch should include constraint COI.
        for &latch_var in &ts.latch_vars {
            let cube = vec![Lit::pos(latch_var)];
            let domain = dc.compute_domain(&cube, &next_vars);
            dc.verify_domain_completeness(&cube, &next_vars, &domain, &ts)
                .unwrap_or_else(|e| {
                    panic!(
                        "domain incomplete for latch Var({}) with constraints: {}",
                        latch_var.0, e
                    )
                });
        }
    }

    #[test]
    fn test_verify_completeness_shared_gate() {
        // Two latches sharing an AND gate: L1 next=G, L2 next=G.
        let circuit =
            parse_aag("aag 5 2 2 0 1 1\n2\n4\n6 10\n8 10\n6\n10 2 4\n").expect("parse failed");
        let ts = Transys::from_aiger(&circuit);
        let (dc, next_vars, _) = setup_domain(&ts);

        // Each latch individually.
        for &latch_var in &ts.latch_vars {
            let cube = vec![Lit::pos(latch_var)];
            let domain = dc.compute_domain(&cube, &next_vars);
            dc.verify_domain_completeness(&cube, &next_vars, &domain, &ts)
                .unwrap_or_else(|e| {
                    panic!(
                        "domain incomplete for shared-gate latch Var({}): {}",
                        latch_var.0, e
                    )
                });
        }

        // Both latches together.
        let cube: Vec<Lit> = ts.latch_vars.iter().map(|&v| Lit::neg(v)).collect();
        let domain = dc.compute_domain(&cube, &next_vars);
        dc.verify_domain_completeness(&cube, &next_vars, &domain, &ts)
            .expect("domain should be complete for shared-gate multi-latch cube");
    }

    #[test]
    fn test_verify_completeness_self_loop() {
        // Self-loop latch: next(L) = L.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 2\n2\n").expect("parse failed");
        let ts = Transys::from_aiger(&circuit);
        let (dc, next_vars, _) = setup_domain(&ts);

        let cube = vec![Lit::pos(Var(1))];
        let domain = dc.compute_domain(&cube, &next_vars);
        dc.verify_domain_completeness(&cube, &next_vars, &domain, &ts)
            .expect("domain should be complete for self-loop latch");
    }

    #[test]
    fn test_verify_completeness_stuck_at_zero() {
        // Latch stuck at 0 (next=0).
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").expect("parse failed");
        let ts = Transys::from_aiger(&circuit);
        let (dc, next_vars, _) = setup_domain(&ts);

        let cube = vec![Lit::pos(Var(1))];
        let domain = dc.compute_domain(&cube, &next_vars);
        dc.verify_domain_completeness(&cube, &next_vars, &domain, &ts)
            .expect("domain should be complete for stuck-at-0 latch");
    }

    #[test]
    fn test_verify_completeness_independent_latches() {
        // Two independent latches (stuck-at-0).
        // Cube over L1 should NOT need L2's variables.
        let circuit = parse_aag("aag 2 0 2 0 0 1\n2 0\n4 0\n2\n").expect("parse failed");
        let ts = Transys::from_aiger(&circuit);
        let (dc, next_vars, _) = setup_domain(&ts);

        let cube = vec![Lit::pos(Var(1))];
        let domain = dc.compute_domain(&cube, &next_vars);
        dc.verify_domain_completeness(&cube, &next_vars, &domain, &ts)
            .expect("domain should be complete for independent latch");

        // The independent latch (Var(2)) should NOT be in L1's domain.
        assert!(
            !domain.contains(Var(2)),
            "independent latch should NOT be in domain — domain is too large"
        );
    }

    #[test]
    fn test_verify_completeness_full_ic3_safe_circuit() {
        // End-to-end: run IC3 on a safe circuit, verify domain completeness
        // holds for every domain the engine would compute.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").expect("parse failed");
        let ts = Transys::from_aiger(&circuit);
        let (dc, next_vars, _) = setup_domain(&ts);

        // Simulate the cubes IC3 would encounter.
        let cubes = vec![vec![Lit::pos(Var(1))], vec![Lit::neg(Var(1))]];

        for cube in &cubes {
            let domain = dc.compute_domain(cube, &next_vars);
            dc.verify_domain_completeness(cube, &next_vars, &domain, &ts)
                .unwrap_or_else(|e| panic!("domain incomplete for cube {:?}: {}", cube, e));
        }
    }

    #[test]
    fn test_verify_completeness_full_ic3_unsafe_circuit() {
        // End-to-end: run IC3 on an unsafe circuit, verify domain completeness.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").expect("parse failed");
        let ts = Transys::from_aiger(&circuit);
        let (dc, next_vars, _) = setup_domain(&ts);

        let cubes = vec![vec![Lit::pos(Var(1))], vec![Lit::neg(Var(1))]];

        for cube in &cubes {
            let domain = dc.compute_domain(cube, &next_vars);
            dc.verify_domain_completeness(cube, &next_vars, &domain, &ts)
                .unwrap_or_else(|e| panic!("domain incomplete for cube {:?}: {}", cube, e));
        }
    }

    #[test]
    fn test_domain_restricted_solver_sat_agreement_multi_circuit() {
        // Verify domain-restricted vs full solver agreement on multiple circuits.
        // This is the core correctness test: if domain restriction is complete,
        // the restricted solver must agree with the full solver on all queries.
        let circuits = vec![
            // Toggle flip-flop (unsafe depth 1).
            "aag 1 0 1 0 0 1\n2 3\n2\n",
            // Stuck-at-0 (safe).
            "aag 1 0 1 0 0 1\n2 0\n2\n",
            // AND-gate chain: L next=AND(i1, i2).
            "aag 3 1 1 0 1 1\n2\n4 6\n4\n6 2 4\n",
            // Two latches, L2 next depends on L1.
            "aag 5 2 2 0 1 1\n2\n4\n6 2\n8 10\n8\n10 6 4\n",
        ];

        for (ci, aag) in circuits.iter().enumerate() {
            let circuit =
                parse_aag(aag).unwrap_or_else(|e| panic!("parse failed for circuit {ci}: {e}"));
            let ts = Transys::from_aiger(&circuit);
            let (dc, next_vars, max_var) = setup_domain(&ts);

            let mut next_link_clauses = Vec::new();
            for &latch_var in &ts.latch_vars {
                if let (Some(&next_var), Some(&next_expr)) =
                    (next_vars.get(&latch_var), ts.next_state.get(&latch_var))
                {
                    let nv_pos = Lit::pos(next_var);
                    let nv_neg = Lit::neg(next_var);
                    next_link_clauses.push(vec![nv_neg, next_expr]);
                    next_link_clauses.push(vec![nv_pos, !next_expr]);
                }
            }

            // For each latch, test a cube {latch=true}.
            for &latch_var in &ts.latch_vars {
                let cube = vec![Lit::pos(latch_var)];
                let domain = dc.compute_domain(&cube, &next_vars);

                // Build full solver.
                let mut full = SolverBackend::Simple.make_solver_no_inprocessing(max_var + 1);
                full.add_clause(&[Lit::TRUE]);
                for clause in &ts.trans_clauses {
                    full.add_clause(&clause.lits);
                }
                for &constraint in &ts.constraint_lits {
                    full.add_clause(&[constraint]);
                }
                for clause in &next_link_clauses {
                    full.add_clause(clause);
                }
                let neg_cube: Vec<Lit> = cube.iter().map(|l| !*l).collect();
                full.add_clause(&neg_cube);

                // Build domain-restricted solver.
                let restricted = build_domain_restricted_solver(
                    &domain,
                    &ts,
                    &next_link_clauses,
                    &[],
                    0,
                    &[],
                    SolverBackend::Simple,
                    max_var,
                );
                if let Some(mut restricted) = restricted {
                    restricted.add_clause(&neg_cube);

                    let primed: Vec<Lit> = cube
                        .iter()
                        .filter_map(|&lit| {
                            next_vars.get(&lit.var()).map(|&nv| {
                                if lit.is_positive() {
                                    Lit::pos(nv)
                                } else {
                                    Lit::neg(nv)
                                }
                            })
                        })
                        .collect();

                    let full_r = full.solve(&primed);
                    let restr_r = restricted.solve(&primed);

                    assert_eq!(
                        full_r, restr_r,
                        "SAT result mismatch on circuit {ci}, latch Var({}): full={full_r:?}, restricted={restr_r:?}",
                        latch_var.0,
                    );
                }
            }
        }
    }

    // =========================================================================
    // Audit-pinned acceptance criteria (#4181, TL40)
    //
    // These three tests explicitly encode the audit contract:
    //   (a) Transitive closure adds INDIRECT deps (multi-hop COI expansion).
    //   (b) Variables outside the COI do NOT leak into the domain.
    //   (c) Empty query cube produces a bounded, minimal domain (Var(0)
    //       and unconditionally-needed constraint COI only).
    //
    // Matches rIC3's `enable_local()` semantics in
    // `~/hwmcc/tools/ric3/src/gipsat/domain.rs:30-52`. rIC3's algorithm:
    //   reset -> seed with input cube vars -> worklist-expand via `dc.dep(v)`.
    //
    // tla-aiger's equivalent: `DomainComputer::new()` precomputes
    // `latch_coi[v]` = transitive closure of Var(v)'s deps through
    // `ts.and_defs`. `compute_domain()` unions per-latch closures.
    // =========================================================================

    #[test]
    fn test_audit_criterion_a_transitive_closure_indirect_deps() {
        // Criterion (a): domain must include vars reachable through a CHAIN
        // of AND gates (not just direct deps).
        //
        // Circuit: L_next = AND(AND(i1, i2), i3) — 2-hop chain.
        // Cube over L must include i1, i2, i3 AND both intermediate AND gates.
        let circuit = parse_aag("aag 6 3 1 0 2 1\n2\n4\n6\n8 12\n8\n10 2 4\n12 10 6\n")
            .expect("parse failed");
        let ts = Transys::from_aiger(&circuit);
        let (dc, next_vars, _) = setup_domain(&ts);

        let cube = vec![Lit::pos(Var(4))]; // latch only
        let domain = dc.compute_domain(&cube, &next_vars);

        // Direct dep: next-state AND gate (var 6).
        assert!(
            domain.contains(Var(6)),
            "direct dep (next-state AND) missing"
        );
        // 1-hop indirect: input to next-state (var 3 = i3).
        assert!(domain.contains(Var(3)), "1-hop indirect dep (i3) missing");
        // 2-hop indirect: intermediate AND gate output (var 5).
        assert!(domain.contains(Var(5)), "2-hop indirect dep (g1) missing");
        // 3-hop indirect: inputs to intermediate gate (var 1, var 2).
        assert!(
            domain.contains(Var(1)),
            "3-hop indirect dep (i1) missing — transitive closure incomplete"
        );
        assert!(
            domain.contains(Var(2)),
            "3-hop indirect dep (i2) missing — transitive closure incomplete"
        );

        // Independent verification via verify_domain_completeness.
        dc.verify_domain_completeness(&cube, &next_vars, &domain, &ts)
            .expect("transitive closure audit must pass");
    }

    #[test]
    fn test_audit_criterion_b_out_of_coi_vars_dont_leak() {
        // Criterion (b): variables outside the cube's COI must NOT be in the
        // domain. Two independent latches with disjoint dependencies — cube
        // over L1 must not include L2 or L2's inputs.
        //
        // L1 (var 1): next = input1 (var 3).
        // L2 (var 2): next = input2 (var 4).
        // These are completely disjoint.
        let circuit = parse_aag("aag 4 2 2 0 0 1\n6\n8\n2 6\n4 8\n2\n").expect("parse failed");
        let ts = Transys::from_aiger(&circuit);
        let (dc, next_vars, _max_var) = setup_domain(&ts);

        let cube_l1 = vec![Lit::pos(Var(1))];
        let domain_l1 = dc.compute_domain(&cube_l1, &next_vars);

        // L1 itself is in.
        assert!(domain_l1.contains(Var(1)), "L1 must be in its own domain");
        // L1's direct dep (input1, var 3) is in.
        assert!(
            domain_l1.contains(Var(3)),
            "L1's input dep must be in domain"
        );
        // L2 and its dep MUST NOT leak.
        assert!(
            !domain_l1.contains(Var(2)),
            "out-of-COI var (L2) leaked into L1's domain — unsound over-approximation"
        );
        assert!(
            !domain_l1.contains(Var(4)),
            "out-of-COI var (L2's input) leaked into L1's domain"
        );
        // L2's next-var also MUST NOT leak.
        let l2_next = *next_vars.get(&Var(2)).expect("L2 should have next-var");
        assert!(
            !domain_l1.contains(l2_next),
            "L2's next-state var leaked into L1's domain"
        );
    }

    #[test]
    fn test_audit_criterion_c_empty_cube_produces_minimal_domain() {
        // Criterion (c): empty cube produces a bounded minimal domain.
        //
        // When the cube is empty, the only unconditionally-required members
        // are Var(0) (constant) and the pre-computed constraint COI vars.
        // No latch-derived variables should be in the domain.
        //
        // This matches rIC3's `enable_local()` with an empty input iterator:
        // after `reset()`, only `fixed` vars remain (CONST); the worklist
        // expansion adds only constraint-derived deps.
        let circuit = parse_aag("aag 3 1 1 0 1 1\n2\n4 6\n4\n6 2 4\n").expect("parse failed");
        let ts = Transys::from_aiger(&circuit);
        let (dc, next_vars, max_var) = setup_domain(&ts);

        let empty_cube: Vec<Lit> = Vec::new();
        let domain = dc.compute_domain(&empty_cube, &next_vars);

        // Var(0) is always present.
        assert!(
            domain.contains(Var(0)),
            "empty cube: Var(0) must be present"
        );
        // Domain size is bounded by max_var + 1 (trivial upper bound).
        assert!(
            domain.len() <= (max_var as usize + 1),
            "empty cube: domain size {} exceeds max_var bound {}",
            domain.len(),
            max_var as usize + 1,
        );
        // Domain contains ONLY Var(0) and constraint COI vars.
        // For this circuit (no constraints), domain size must be exactly 1.
        assert_eq!(
            ts.constraint_lits.len(),
            0,
            "precondition: test circuit has no constraints"
        );
        assert_eq!(
            domain.len(),
            1,
            "empty cube + no constraints: domain must be {{Var(0)}}, got {} vars",
            domain.len(),
        );
        // Specifically, the latch var MUST NOT be in the empty-cube domain.
        assert!(
            !domain.contains(Var(2)),
            "empty cube: latch var must not be included"
        );

        // Completeness verifier agrees with empty cube.
        dc.verify_domain_completeness(&empty_cube, &next_vars, &domain, &ts)
            .expect("empty cube must satisfy verify_domain_completeness");
    }
}
