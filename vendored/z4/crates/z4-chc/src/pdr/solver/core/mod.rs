// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Core PDR utilities and initialization.
//!
//! Classification functions are in `classify`, cache operations in `cache_ops`.

mod cache_ops;
mod classify;
mod formula_analysis;
mod lemma_mgmt;
mod scc;

// Re-export public free functions so callers can use `core::filter_to_canonical_vars`
// and `core::ensure_prop_solver_split` without path changes.
pub(in crate::pdr::solver) use classify::{ensure_prop_solver_split, filter_to_canonical_vars};

use classify::{clause_has_ite, clause_is_integer_arithmetic, clause_is_pure_lia};

use super::{
    build_canonical_predicate_vars, build_predicate_users, build_push_cache_deps, caches,
    compute_reachable_predicates, fs, tarjan_scc, Arc, ChcExpr, ChcOp, ChcParser, ChcProblem,
    ChcResult, ChcSort, ChcVar, ConvergenceMonitor, ConvexClosure, Frame, FxHashMap, FxHashSet,
    Lemma, ObligationQueue, Path, PdrConfig, PdrResult, PdrSolver, PdrTelemetry, PredicateId,
    PriorityPob, ProofObligation, ReachFact, ReachFactId, ReachabilityState, RestartState,
    SmtResult, TracingState, VerificationCounters,
};

impl PdrSolver {
    /// Get cumulative frame constraint for a predicate at level k.
    /// This includes all lemmas from frames 1..=k (PDR frames are monotonic).
    ///
    /// Results are cached per (level, pred) and invalidated when any frame's
    /// lemma revision for this predicate changes (#2763).
    pub(in crate::pdr::solver) fn cumulative_frame_constraint(
        &self,
        level: usize,
        pred: PredicateId,
    ) -> Option<ChcExpr> {
        let num_frames = level.min(self.frames.len() - 1);

        // Compute revision fingerprint: sum of per-frame revisions for this predicate.
        // If any frame adds a lemma for pred, the sum changes → cache miss.
        let revision_sum: u64 = (1..=num_frames)
            .map(|lvl| self.frames[lvl].predicate_lemma_revision(pred))
            .sum();

        // Check cache
        let key = (level, pred);
        if let Some((cached_rev, cached_formula)) =
            self.caches.cumulative_constraint_cache.borrow().get(&key)
        {
            if *cached_rev == revision_sum {
                return Some(cached_formula.clone());
            }
        }

        // Cache miss: recompute
        let mut all_lemmas: Vec<&Lemma> = Vec::with_capacity(num_frames * 4);
        for lvl in 1..=num_frames {
            all_lemmas.extend(
                self.frames[lvl]
                    .lemmas
                    .iter()
                    .filter(|l| l.predicate == pred)
                    // Skip Bool(false) lemmas: they poison and_all via short-circuit,
                    // producing a trivially-false invariant that fails entry-clause
                    // verification (#3121).
                    .filter(|l| !matches!(l.formula, ChcExpr::Bool(false))),
            );
        }

        if all_lemmas.is_empty() {
            None
        } else {
            // Deduplicate by formula hash to avoid repeated `to_string()` allocation (#1037).
            // Collision safety: bucket by hash then confirm structural equality.
            let mut seen: FxHashMap<u64, Vec<&ChcExpr>> = FxHashMap::default();
            let unique: Vec<_> = all_lemmas
                .into_iter()
                .filter(|lemma| {
                    let bucket = seen.entry(lemma.formula_hash).or_default();
                    if bucket.contains(&&lemma.formula) {
                        false
                    } else {
                        bucket.push(&lemma.formula);
                        true
                    }
                })
                .collect();

            if unique.is_empty() {
                None
            } else {
                // Build flat conjunction (#2508: avoid deep right-skewed And trees)
                let formula = ChcExpr::and_all(unique.into_iter().map(|l| l.formula.clone()));
                self.insert_cumulative_constraint_cache_entry(key, (revision_sum, formula.clone()));
                Some(formula)
            }
        }
    }
    /// Check if the solver should stop (cancelled by portfolio, solve_timeout exceeded,
    /// reach-fact store saturation, or global TermStore memory exceeded #2769).
    #[inline]
    pub(in crate::pdr) fn is_cancelled(&self) -> bool {
        self.config
            .cancellation_token
            .as_ref()
            .is_some_and(crate::cancellation::CancellationToken::is_cancelled)
            || self
                .solve_deadline
                .is_some_and(|d| std::time::Instant::now() >= d)
            || self.reachability.reach_facts_saturated
            || z4_core::TermStore::global_memory_exceeded()
    }

    /// Parse a CHC input string and run PDR.
    ///
    /// `pub(crate)` — external callers should use [`AdaptivePortfolio::solve()`]
    /// which returns [`VerifiedChcResult`]. Part of #5747: structural verification invariant.
    pub(crate) fn solve_from_str(input: &str, config: PdrConfig) -> ChcResult<PdrResult> {
        let problem = ChcParser::parse(input)?;

        // Try case-split for unconstrained constant arguments.
        // This handles benchmarks like dillig12_m where an argument is constant
        // throughout execution but unconstrained at init, and used as a mode flag
        // in ITE guards (compared against some constant).
        if config.tla_trace_path.is_none() {
            if let Some(case_split_result) = Self::try_case_split_solve(&problem, config.clone()) {
                return Ok(case_split_result);
            }
        }

        let trace_path = config.tla_trace_path.clone();
        let mut solver = Self::new(problem, config);
        if let Some(path) = trace_path.as_deref() {
            solver.enable_tla_trace_from_path(path);
        }
        Ok(solver.solve())
    }

    /// Solve a pre-parsed problem with case-split optimization.
    ///
    /// This is the main entry point for solving CHC problems where the
    /// problem has already been parsed. It includes case-split for
    /// unconstrained constant arguments.
    pub(crate) fn solve_problem(problem: &ChcProblem, config: PdrConfig) -> PdrResult {
        // Try case-split for unconstrained constant arguments.
        // Skip when running under a cancellation token (portfolio engine) since
        // the Adaptive strategy already runs case-split as Stage 0 (#5399).
        // Redundant case-splits consume the portfolio timeout before the main
        // solver reaches kernel discovery. Also skip under trace mode so the
        // top-level PDR run owns a single coherent JSONL file instead of
        // per-branch solvers recreating it.
        if config.cancellation_token.is_none() && config.tla_trace_path.is_none() {
            if let Some(case_split_result) = Self::try_case_split_solve(problem, config.clone()) {
                return case_split_result;
            }
        }

        let trace_path = config.tla_trace_path.clone();
        let mut solver = Self::new(problem.clone(), config);
        if let Some(path) = trace_path.as_deref() {
            solver.enable_tla_trace_from_path(path);
        }
        solver.solve()
    }

    /// Parse a CHC file and run PDR.
    ///
    /// `pub(crate)` — external callers should use [`AdaptivePortfolio::solve()`]
    /// which returns [`VerifiedChcResult`]. Part of #5747: structural verification invariant.
    pub(crate) fn solve_from_file(
        path: impl AsRef<Path>,
        config: PdrConfig,
    ) -> ChcResult<PdrResult> {
        let input = fs::read_to_string(path)?;
        Self::solve_from_str(&input, config)
    }

    /// Create a new PDR solver
    pub(crate) fn new(mut problem: ChcProblem, config: PdrConfig) -> Self {
        // Expand nullary fail predicates first (CHC-COMP pattern)
        // This transforms `fail => false` queries into direct queries
        problem.expand_nullary_fail_queries(config.verbose);

        // #6047: Try full scalarization (including BV-indexed arrays) first.
        // If the result has reasonable arity (≤64 params per predicate), keep it.
        // Otherwise fall back to Int-only scalarization to avoid arity explosion
        // (zani harnesses: 68 → 191 params with full BV scalarization, #6163).
        // Gated on pre-scalarization array sort check (#6366).
        let has_array_sorts_before = problem.predicates().iter().any(|p| {
            p.arg_sorts
                .iter()
                .any(|s| matches!(s, ChcSort::Array(_, _)))
        });
        if has_array_sorts_before {
            let max_arity = problem
                .predicates()
                .iter()
                .map(|p| p.arg_sorts.len())
                .max()
                .unwrap_or(0);
            let mut scalarized = problem.clone();
            scalarized.try_scalarize_const_array_selects();
            let new_max_arity = scalarized
                .predicates()
                .iter()
                .map(|p| p.arg_sorts.len())
                .max()
                .unwrap_or(0);
            if new_max_arity <= 64 || new_max_arity <= max_arity * 3 {
                problem = scalarized;
            } else {
                // Full scalarization causes arity explosion; try property-directed
                // scalarization instead. This only scalarizes at constant indices
                // found in query clauses (typically 1-5 indices for zani harnesses),
                // adding minimal parameters while enabling PDR to check array
                // properties without bit-blasting overhead. Part of #6047.
                problem.try_scalarize_property_directed();
                // Also apply Int-only scalarization for any remaining Int-indexed arrays.
                problem.try_scalarize_int_indexed_const_array_selects();
            }
        }

        // #6366: Detect whether the POST-scalarization problem still has array sorts.
        // Must be checked after scalarization because successful scalarization removes
        // array sorts from predicate signatures (e.g., Array Int Bool → scalar Int params).
        // This flag gates all array-specific overhead in the hot blocking loop.
        let uses_arrays = problem.predicates().iter().any(|p| {
            p.arg_sorts
                .iter()
                .any(|s| matches!(s, ChcSort::Array(_, _)))
        });

        // OR splitting is enabled by default to eliminate disjunctive constraints that
        // can force expensive SMT case-splitting during verification (e.g. three_dots_moving_2).
        problem.try_split_ors_in_clauses(8, config.verbose);
        let problem_has_ite = problem.clauses().iter().any(clause_has_ite);
        let problem_is_integer_arithmetic_before_ite_split =
            problem.clauses().iter().all(clause_is_integer_arithmetic);
        // ITE splitting: generous limit for single-predicate problems; conservative
        // re-enable for multi-predicate integer-arithmetic problems where ITEs keep
        // the clause surface off the pure-LIA fast path (e.g. s_multipl_24, #1362).
        // Non-integer problems still skip splitting to avoid clause churn on BV/array paths.
        let num_predicates = problem.predicates().len();
        if num_predicates <= 1 {
            problem.try_split_ites_in_clauses(32, config.verbose);
        } else if problem_has_ite && problem_is_integer_arithmetic_before_ite_split {
            problem.try_split_ites_in_clauses(8, config.verbose);
        } else if config.verbose {
            safe_eprintln!(
                "CHC: skipping ite-splitting for multi-predicate problem ({} predicates)",
                num_predicates
            );
        }
        // #1362: Snapshot error clause constraints BEFORE mod/div elimination.
        let original_error_constraints: FxHashMap<usize, ChcExpr> = problem
            .clauses()
            .iter()
            .enumerate()
            .filter(|(_, c)| matches!(c.head, crate::ClauseHead::False))
            .filter_map(|(i, c)| c.body.constraint.as_ref().map(|cst| (i, cst.clone())))
            .collect();
        if config.verbose && !original_error_constraints.is_empty() {
            safe_eprintln!(
                "PDR: Snapshot {} original error clause constraints before mod/div elimination (#1362)",
                original_error_constraints.len()
            );
        }
        // #7410 D2: eliminate_mod_in_constraints DISABLED.
        // A/B test at commit 494cf19ac showed +9 SAT benchmarks (33→42/55) with
        // 0 regressions when disabled. The auxiliary quotient/remainder variables
        // from Euclidean decomposition make PDR lemma discovery harder. The SMT
        // solver's LIA theory handles (mod x k) natively for constant k, and
        // expr_is_integer_arithmetic() already classifies mod/div as pure LIA.

        // #6480/#6358: Detect whether the normalized clause surface is pure LIA
        // (no ITE/mod/div) before trusting incremental SAT results. Parser
        // normalization can move arithmetic ITEs out of the residual body
        // constraint and into predicate arguments, so scanning only
        // `clause.body.constraint` is insufficient for benchmarks like
        // `half_true_modif_m`.
        let problem_is_pure_lia_raw = problem.clauses().iter().all(clause_is_pure_lia);
        let problem_is_integer_arithmetic =
            problem.clauses().iter().all(clause_is_integer_arithmetic);
        // #7048: Integer arithmetic problems (ITE + mod/div over ints) are
        // effectively pure LIA: the SMT solver handles mod/div natively.
        // Promote to pure LIA to enable full incremental SAT trust and
        // standard generalization (no BV-specific overhead).
        let problem_is_pure_lia = problem_is_pure_lia_raw || problem_is_integer_arithmetic;
        if config.verbose {
            safe_eprintln!(
                "PDR: problem_is_pure_lia = {} (raw={}, int_arith={}, gates incremental SAT trust, #6480/#7048)",
                problem_is_pure_lia, problem_is_pure_lia_raw, problem_is_integer_arithmetic
            );
        }

        let predicate_vars = build_canonical_predicate_vars(&problem);
        let push_cache_deps = build_push_cache_deps(&problem);
        let predicate_users = build_predicate_users(&problem);
        // Build cache of predicates that have fact clauses (computed once)
        let predicates_with_facts: FxHashSet<PredicateId> = problem
            .facts()
            .filter_map(|f| f.head.predicate_id())
            .collect();
        // Compute predicates reachable from init via transitions (#1419)
        let reachable_predicates = compute_reachable_predicates(&problem, &predicates_with_facts);
        // Compute SCC info for cyclic predicate handling
        let scc_info = tarjan_scc(&problem);
        if config.verbose {
            for scc in &scc_info.sccs {
                if scc.is_cyclic && scc.predicates.len() > 1 {
                    safe_eprintln!(
                        "PDR: Detected cyclic SCC with {} predicates: {:?}",
                        scc.predicates.len(),
                        scc.predicates.iter().map(|p| p.index()).collect::<Vec<_>>()
                    );
                }
            }
        }
        // Extract restart threshold before moving config
        let restart_threshold_init = config.restart_initial_threshold;
        let smt = problem.make_smt_context();
        let problem_size_hint = super::convergence_monitor::ProblemSizeHint::from_problem(&problem);
        Self {
            problem,
            config,
            caches: caches::PdrCacheStore::new(
                predicate_vars,
                push_cache_deps,
                predicate_users,
                predicates_with_facts,
                reachable_predicates,
            ),
            // Start with F_0 (init) and F_1 (true).
            frames: vec![Frame::new(), Frame::new()],
            obligations: ObligationQueue::default(),
            iterations: 0,
            smt,
            array_clause_sessions: FxHashMap::default(),
            mbp: crate::mbp::Mbp::new(),
            reachability: ReachabilityState::new(),
            verification: VerificationCounters::default(),
            convex_closure_engine: ConvexClosure::new(),
            scc_info,
            // Restart state (#1270)
            restart: RestartState::new(restart_threshold_init),
            // TLA2 trace state (#3301)
            tracing: TracingState::default(),
            // Solve deadline (set at start of solve() from config.solve_timeout)
            solve_deadline: None,
            // Telemetry counters (#2450, #3301)
            telemetry: PdrTelemetry::default(),
            // Convergence monitor for stagnation detection
            convergence: ConvergenceMonitor::new(),
            generalization_escalation_level: 0,
            generalization_strategy: super::GeneralizationStrategy::Default,
            terminated_by_stagnation: false,
            lemma_quality: super::convergence_monitor::LemmaQualityMetrics::new(),
            problem_size_hint,
            // Per-predicate persistent solvers (#6358).
            // Initialized empty; contexts created lazily on first query.
            prop_solvers: FxHashMap::default(),
            // Problem feature flag (#6366): gates array-specific overhead.
            uses_arrays,
            // Problem feature flag (#6480): gates incremental SAT trust.
            problem_is_pure_lia,
            // Problem feature flag (#5970): relaxed gate for ITE/mod/div.
            problem_is_integer_arithmetic,
            // Cross-check budget (#5970): 5s total for executor cross-checks.
            cross_check_budget: std::time::Duration::from_secs(5),
            // Startup convergence flag (#5970).
            startup_converged: false,
            // Deferred entry-inductive retry queue (#5970).
            deferred_entry_invariants: Vec::new(),
            // Deferred self-inductive retry queue (menlo_park_term_simpl_2).
            deferred_self_inductive_invariants: Vec::new(),
            // Rejected-invariant cache (#7006): skip re-checking known failures.
            rejected_invariants: FxHashSet::default(),
            original_error_constraints,
        }
    }

    /// Get or create a per-predicate prop_solver with full lemma backfill (#6358).
    ///
    /// When a `PredicatePropSolver` is lazily created, it must contain ALL existing
    /// frame lemmas for that predicate. Without backfill, queries against a freshly
    /// created prop_solver would miss lemmas and return incorrect SAT results.
    ///
    /// This method:
    /// 1. Checks if a prop_solver already exists for `pred` (fast path)
    /// 2. If not, creates one and asserts every existing frame lemma for `pred`
    /// 3. Returns a mutable reference to the prop_solver
    ///
    /// All prop_solver access should go through this method to ensure correctness.
    ///
    /// NOTE: In contexts where `self.problem.clauses()` is borrowed (clause loop
    /// iterations), use `ensure_prop_solver_split` with explicit field borrows to
    /// avoid borrow conflicts.
    pub(in crate::pdr) fn ensure_prop_solver(
        &mut self,
        pred: PredicateId,
    ) -> &mut super::prop_solver::PredicatePropSolver {
        ensure_prop_solver_split(&mut self.prop_solvers, &self.frames, pred)
    }

    /// Get clause-guarded propagated lemmas as a conjunction, applied to clause head args.
    ///
    /// Returns `Bool(true)` if there are no clause-guarded lemmas for this (pred, clause)
    /// at the requested level.
    ///
    /// # Design (#2459 Phase 3, #2536 level-awareness)
    ///
    /// Z3 Spacer asserts `(rule_tag => renamed_lemma)` into the parent's solver,
    /// level-parameterized: a child lemma at level L is asserted at parent levels
    /// 1..next_level(L). Z4 iterates per-clause, so the tag guard is implicit.
    /// Level filtering ensures we only include lemmas valid at the requested level.
    ///
    /// A lemma with `max_level >= check_level` is included; others are skipped.
    /// Reference: z3/src/muz/spacer/spacer_context.cpp:1949-1954
    pub(in crate::pdr) fn clause_guarded_constraint(
        &self,
        pred: PredicateId,
        clause_index: usize,
        head_args: &[ChcExpr],
        check_level: usize,
    ) -> ChcExpr {
        let Some(guarded) = self.caches.clause_guarded_lemmas.get(&(pred, clause_index)) else {
            return ChcExpr::Bool(true);
        };
        if guarded.is_empty() {
            return ChcExpr::Bool(true);
        }
        let mut conjuncts = Vec::with_capacity(guarded.len());
        for (lemma, max_level) in guarded {
            // #2536: Only include lemmas valid at this level.
            // Matches Z3's level-parameterized assertion in updt_solver_with_lemmas.
            if *max_level < check_level {
                continue;
            }
            if let Some(applied) = self.apply_to_args(pred, lemma, head_args) {
                conjuncts.push(applied);
            }
        }
        if conjuncts.is_empty() {
            ChcExpr::Bool(true)
        } else {
            ChcExpr::and_all(conjuncts)
        }
    }

    /// Current number of queued obligations (heap + deque).
    fn obligation_queue_size(&self) -> usize {
        self.obligations.heap.len() + self.obligations.deque.len()
    }

    /// Maximum queue size: 2x max_obligations.
    /// Prevents unbounded memory growth from POB explosion (#2956 Finding 5).
    fn obligation_queue_cap(&self) -> usize {
        self.config.max_obligations.saturating_mul(2)
    }

    /// Push a proof obligation to the queue.
    /// Assigns a monotonic queue_id for deterministic tie-breaking.
    /// Drops the POB if the queue is at capacity and marks this strengthen
    /// attempt as incomplete (must degrade to Unknown).
    pub(in crate::pdr::solver) fn push_obligation(&mut self, mut pob: ProofObligation) {
        let cap = self.obligation_queue_cap();
        if self.obligation_queue_size() >= cap {
            if self.config.verbose && !self.obligations.overflowed {
                safe_eprintln!(
                    "PDR: obligation queue overflow at cap {}; degrading result to Unknown",
                    cap
                );
            }
            self.obligations.overflowed = true;
            return;
        }
        pob.queue_id = self.obligations.next_id;
        self.obligations.next_id += 1;
        if self.config.use_level_priority {
            self.obligations.heap.push(PriorityPob(pob));
        } else {
            self.obligations.deque.push_back(pob);
        }
    }

    /// Push a proof obligation with high priority (for DFS: to front).
    /// Assigns a monotonic queue_id for deterministic tie-breaking.
    /// Drops the POB if the queue is at capacity and marks this strengthen
    /// attempt as incomplete (must degrade to Unknown).
    pub(in crate::pdr::solver) fn push_obligation_front(&mut self, mut pob: ProofObligation) {
        let cap = self.obligation_queue_cap();
        if self.obligation_queue_size() >= cap {
            if self.config.verbose && !self.obligations.overflowed {
                safe_eprintln!(
                    "PDR: obligation queue overflow at cap {}; degrading result to Unknown",
                    cap
                );
            }
            self.obligations.overflowed = true;
            return;
        }
        pob.queue_id = self.obligations.next_id;
        self.obligations.next_id += 1;
        if self.config.use_level_priority {
            // In level-priority mode, all POBs go to the heap (level determines order)
            self.obligations.heap.push(PriorityPob(pob));
        } else {
            self.obligations.deque.push_front(pob);
        }
    }

    /// Pop the next proof obligation
    pub(in crate::pdr::solver) fn pop_obligation(&mut self) -> Option<ProofObligation> {
        if self.config.use_level_priority {
            self.obligations.heap.pop().map(|p| p.0)
        } else {
            self.obligations.deque.pop_front()
        }
    }

    pub(in crate::pdr) fn canonical_vars(&self, pred: PredicateId) -> Option<&[ChcVar]> {
        self.caches.predicate_vars.get(&pred).map(Vec::as_slice)
    }

    // ========================================================================
    // SCC-based cyclic predicate strengthening
    // ========================================================================

    /// Translate a lemma from one predicate's canonical vars to another's.
    /// Returns None if predicates have different arities.
    ///
    /// z4 uses canonical variables named `__p{pred_idx}_a{arg_idx}`. Translation
    /// builds a substitution from source vars to target vars.
    pub(in crate::pdr::solver) fn translate_lemma(
        &self,
        lemma: &ChcExpr,
        from_pred: PredicateId,
        to_pred: PredicateId,
    ) -> Option<ChcExpr> {
        let from_vars = self.canonical_vars(from_pred)?;
        let to_vars = self.canonical_vars(to_pred)?;

        if from_vars.len() != to_vars.len() {
            return None; // Different arity - can't translate
        }

        // Build substitution: __p{from}_a{i} -> __p{to}_a{i}
        let subst: Vec<(ChcVar, ChcExpr)> = from_vars
            .iter()
            .zip(to_vars.iter())
            .map(|(f, t)| (f.clone(), ChcExpr::var(t.clone())))
            .collect();

        Some(lemma.substitute(&subst))
    }
}

#[allow(clippy::unwrap_used)]
#[cfg(test)]
#[path = "../core_tests/mod.rs"]
mod tests;
