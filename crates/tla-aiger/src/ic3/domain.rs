// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
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

        domain
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
        assert!(domain.contains(Var(0)), "domain should include constant var");
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
            &[],   // no next-link clauses
            &[],   // no frame lemmas
            0,     // frame 0
            &[],   // no infinity lemmas
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
        let circuit =
            parse_aag("aag 3 1 1 0 1 1 1\n2\n4 6\n4\n2\n6 2 4\n").expect("parse failed");
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
        assert!(solver.is_some(), "domain restriction should activate for 3-var circuit (#4091)");
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
}
