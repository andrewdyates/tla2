// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! IC3 engine struct definition, constructor, and solver management.

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

use rustc_hash::FxHashMap;

use super::config::{Ic3Config, MAX_SOLVER_REBUILDS_PER_FRAME, PANIC_FALLBACK_THRESHOLD, SOLVER_REBUILD_BASE, UNKNOWN_FALLBACK_THRESHOLD};
use super::domain::{DomainComputer, DomainStats};
use super::frame::{Frames, Lemma};
use super::lift::LiftSolver;
use super::obligation::ObligationQueue;
use super::predprop;
use super::vsids;
use crate::sat_types::{Lit, SatResult, SatSolver, SimpleSolver, SolverBackend, Var};
use crate::ternary::TernarySim;
use crate::transys::Transys;

/// The IC3/PDR model checking engine.
///
/// Uses separate current-state and next-state variables. Each frame solver
/// contains the transition relation with fresh next-state variables, so that
/// the inductiveness check `F_k(s) AND T(s,s') AND cube(s')` can properly
/// constrain the successor state independently of the current state.
pub struct Ic3Engine {
    /// The transition system being checked.
    pub(super) ts: Transys,
    /// Per-frame SAT solvers. `solvers[i]` encodes F_i AND Trans AND next-linking.
    pub(super) solvers: Vec<Box<dyn SatSolver>>,
    /// Frame sequence.
    pub(super) frames: Frames,
    /// Priority queue of proof obligations.
    pub(super) obligations: ObligationQueue,
    /// Fresh next-state variable for each latch: latch_var -> next_var.
    pub(super) next_vars: FxHashMap<Var, Var>,
    /// Maximum variable index (including allocated next-state vars).
    pub(super) max_var: u32,
    /// CNF clauses that link next-state vars to next-state expressions.
    /// `next_var <=> next_state_expr` encoded as Tseitin clauses.
    pub(super) next_link_clauses: Vec<Vec<Lit>>,
    /// SAT solver backend selection. See [`SolverBackend`] for options.
    pub(super) solver_backend: SolverBackend,
    /// Cancellation flag shared with portfolio.
    pub(super) cancelled: Arc<AtomicBool>,
    /// Pre-computed init state: var -> required_polarity (true=positive, false=negative).
    /// Built from unit init clauses for O(1) cube-init consistency checks.
    pub(super) init_map: FxHashMap<Var, bool>,
    /// Reverse map: next_var -> latch_var, for ternary lift prefilter and UNSAT core mapping.
    pub(super) reverse_next: FxHashMap<Var, Var>,
    /// Ternary simulator for predecessor cube minimization.
    pub(super) ternary_sim: TernarySim,
    /// SAT-based predecessor lifting solver (minimizes predecessor cubes via UNSAT cores).
    pub(super) lift: LiftSolver,
    /// Bucket-queue VSIDS for MIC literal ordering.
    /// Provides O(1) amortized variable selection via activity bucketing,
    /// with adaptive fallback to binary heap after restarts.
    /// Reference: rIC3 `gipsat/vsids.rs:248-311` (`Bucket` struct).
    pub(super) vsids: vsids::BucketQueueVsids,
    /// Infinity frame: lemmas that are self-inductive relative to the top frame.
    /// These never need re-propagation — they hold at all reachable depths.
    pub(super) inf_lemmas: Vec<Lemma>,
    /// Solver for infinity frame inductiveness checks.
    /// Contains Trans + all infinity lemmas. A lemma pushed here is globally inductive.
    pub(super) inf_solver: Box<dyn SatSolver>,
    /// Configuration for portfolio diversity.
    pub(super) config: Ic3Config,
    /// Counter for solve_with_temporary_clause calls across all frame solvers.
    /// Used to trigger periodic solver rebuilds to clear accumulated internal
    /// state (learned clause bloat, dead variable metadata).
    pub(super) solve_count: usize,
    /// Pre-computed variable dependency graph for domain restriction.
    ///
    /// Used by MIC to build domain-restricted mini-solvers that contain only
    /// clauses involving variables in the cube's cone of influence. This is
    /// the tla-aiger equivalent of rIC3's `propagate_domain()` optimization:
    /// since z4-sat doesn't support internal domain restriction, we achieve
    /// the same effect by building restricted solvers at the application level.
    pub(super) domain_computer: DomainComputer,
    /// Domain restriction effectiveness statistics (#4059).
    ///
    /// Tracks how often domain restriction fires vs falls back to full solver,
    /// average domain coverage, and total attempts. Logged at IC3 completion
    /// to help tune thresholds and validate the optimization is effective.
    pub(super) domain_stats: DomainStats,
    /// Count of consecutive SatResult::Unknown from non-poisoned solvers (#4074).
    ///
    /// When z4-sat produces FINALIZE_SAT_FAIL (InvalidSatModel), the solver
    /// returns Unknown without becoming poisoned. IC3 cannot make progress
    /// because consecution checks never get definitive SAT/UNSAT answers. After
    /// `UNKNOWN_FALLBACK_THRESHOLD` consecutive Unknown results, the engine
    /// automatically switches to `Z4NoPreprocess` and rebuilds all solvers.
    ///
    /// NOTE: In the IC3 path, `solve_incremental_ic3()` never calls
    /// `preprocess()`, so BVE does not actually run. FINALIZE_SAT_FAIL
    /// in this context comes from model reconstruction issues in the
    /// incremental CDCL loop, not from BVE variable elimination.
    pub(super) unknown_count: usize,
    /// Whether the engine has already fallen back to Z4NoPreprocess due to
    /// persistent FINALIZE_SAT_FAIL errors. Prevents repeated fallback attempts.
    pub(super) fell_back_to_no_preprocess: bool,
    /// Earliest frame that changed since the last propagation round.
    ///
    /// When a lemma is added to frame k (via block_one or propagation), we
    /// update this to `min(earliest_changed_frame, k)`. On each propagation
    /// round, propagation starts from `max(earliest_changed_frame, 1)` and
    /// after completion resets to `depth` (the current top frame).
    ///
    /// This mirrors rIC3's `frame.early` optimization, which avoids redundant
    /// re-propagation of frames that haven't changed since the last round.
    /// Reference: rIC3 `frame.rs:75` — `pub early: usize`.
    pub(super) earliest_changed_frame: usize,
    /// Optional predicate propagation solver for backward bad-state analysis.
    /// When `config.predprop` is true, this solver is initialized and used
    /// as an alternative path in `get_bad()` to find predecessors of bad states
    /// via backward transition analysis.
    /// Reference: rIC3 `ic3/predprop.rs` — `PredProp` struct.
    pub(super) predprop_solver: Option<predprop::PredPropSolver>,
    /// Per-frame cross-check failure count. Tracks how many times
    /// `verify_consecution_independent` has disagreed with z4-sat at each frame.
    /// When a frame exceeds `MAX_CROSSCHECK_FAILURES`, the cross-check is
    /// disabled for that frame to break the infinite rebuild loop where z4-sat
    /// consistently returns false UNSAT for certain clause structures.
    pub(super) crosscheck_failures: Vec<usize>,
    /// Total cross-check failures across ALL frames (#4121).
    ///
    /// Complements per-frame `crosscheck_failures` to detect distributed failure
    /// patterns where z4-sat produces false UNSAT across many different frames,
    /// each under the per-frame threshold. When this exceeds
    /// `MAX_TOTAL_CROSSCHECK_FAILURES`, trigger immediate SimpleSolver fallback
    /// without waiting for any single frame to hit `MAX_CROSSCHECK_FAILURES`.
    ///
    /// Root cause: microban_1 regression where crosscheck failures were spread
    /// across many frames (each new depth creates a fresh frame with 0 failures),
    /// causing repeated expensive rebuilds before SimpleSolver fallback triggered.
    pub(super) total_crosscheck_failures: usize,
    /// When true, all consecution cross-checking is permanently disabled (#4105, #4121).
    ///
    /// Set either:
    /// 1. At engine construction time for high-constraint circuits (constraint_lits /
    ///    latches > 5), where SimpleSolver's basic DPLL is known to produce false SAT
    ///    on constraint-dense formulas. Waiting for the failure budget wastes time.
    /// 2. At runtime when the global cross-check budget is exhausted on a clause-heavy
    ///    circuit. On such circuits, falling back to SimpleSolver makes things worse.
    ///
    /// In both cases, the post-convergence `validate_invariant_budgeted()` provides
    /// the ultimate soundness safety net.
    pub(super) crosscheck_disabled: bool,
    /// Counter for consecution verification sampling (#4092 optimization).
    ///
    /// Instead of cross-checking every consecution result with SimpleSolver,
    /// we verify every `consecution_verify_interval()`-th check. The mandatory
    /// `validate_invariant()` on convergence provides the ultimate safety net,
    /// so per-lemma sampling trades some early detection for much less overhead.
    pub(super) consecution_verify_counter: usize,
    /// Count of proof obligations dropped due to high activity (GAP-2, #4151).
    ///
    /// Tracked for observability: helps tune `drop_po_threshold` across benchmarks.
    /// A high drop count suggests the threshold may be too low (too aggressive),
    /// while zero drops with timeouts suggests the threshold may be too high.
    pub(super) po_drop_count: usize,
    /// Counter for spurious init-consistent predecessors (#4105).
    ///
    /// Tracks how many times an init-consistent predecessor's verify_trace check
    /// has failed at block_one's SAT branch. When this counter exceeds
    /// `MAX_SPURIOUS_INIT_PREDS`, the engine skips the expensive verify_trace
    /// call entirely for init-consistent predecessors and just re-queues the
    /// original PO. This prevents the infinite loop where:
    ///   get_bad() -> SAT predecessor -> init-consistent -> verify_trace fails ->
    ///   re-queue -> get_bad() finds same cube -> repeat.
    pub(super) spurious_init_pred_count: usize,
    /// Count of z4-sat panics caught during this IC3 run (#4092).
    ///
    /// z4-sat has known bugs in conflict analysis / backtrack that cause panics
    /// on certain clause structures. The panic itself is caught and the solver
    /// is rebuilt, but the solver state may have been corrupted *before* the
    /// panic manifested — earlier queries may have returned incorrect UNSAT
    /// results that produced unsound lemmas. After a panic, the frame lemmas
    /// are potentially tainted.
    ///
    /// When this counter reaches `PANIC_FALLBACK_THRESHOLD`:
    /// 1. Fall back to SimpleSolver (which doesn't have these bugs)
    /// 2. Purge ALL frame lemmas (they may be unsound from pre-crash corruption)
    /// 3. Rebuild all solvers from scratch
    ///
    /// This is more aggressive than the Unknown fallback (which just switches
    /// backends) because panics indicate solver corruption that may have produced
    /// silently wrong results before the panic was detected.
    pub(super) panic_count: usize,
    /// Per-frame solver rebuild counter (#4105).
    ///
    /// Tracks how many times the solver at each frame index has been rebuilt
    /// (due to poisoning, Unknown results, etc.). When `rebuild_counts[i]`
    /// exceeds `MAX_SOLVER_REBUILDS_PER_FRAME`, further rebuilds at that frame
    /// are skipped and Unknown/poisoned results are treated conservatively
    /// (as Sat — no false UNSAT). This breaks the infinite rebuild loop on
    /// constraint-dense circuits like microban_1 where z4-sat repeatedly
    /// corrupts or produces Unknown at the same frame.
    pub(super) rebuild_counts: Vec<usize>,
}

impl Ic3Engine {
    /// Create a new IC3 engine from a transition system.
    ///
    /// Allocates fresh next-state variables for each latch so that IC3's
    /// inductiveness check can properly distinguish current and next states.
    pub fn new(ts: Transys) -> Self {
        Self::with_config(ts, Ic3Config::default())
    }

    /// Create a new IC3 engine with a specific configuration.
    pub fn with_config(ts: Transys, config: Ic3Config) -> Self {
        // Circuit-size-based CTG adaptation (#4065).
        // Adjust CTG parameters based on circuit size when circuit_adapt is enabled.
        let mut config = config;
        if config.circuit_adapt {
            let num_latches = ts.num_latches;
            if num_latches < 100 {
                // Small circuits: aggressive CTG (deep recursion is cheap).
                config.ctg_max = config.ctg_max.max(5);
                config.ctg_limit = config.ctg_limit.max(15);
            } else if num_latches > 500 {
                // Large circuits: conservative CTG (early cutoff to avoid blowup).
                config.ctg_max = config.ctg_max.min(2);
                config.ctg_limit = config.ctg_limit.min(1);
            }
            // Medium circuits (100..=500): use configured values as-is.
        }

        // Allocate fresh next-state variables beyond max_var.
        let mut next_var_id = ts.max_var + 1;
        let mut next_vars = FxHashMap::default();
        for &latch_var in &ts.latch_vars {
            next_vars.insert(latch_var, Var(next_var_id));
            next_var_id += 1;
        }

        // Internal signals (#4148): allocate next-state variables for AND-gate
        // outputs selected as internal signals. Enables prime_cube() to map
        // internal signal literals to their primed versions.
        if config.internal_signals {
            for &isig_var in &ts.internal_signals {
                next_vars.insert(isig_var, Var(next_var_id));
                next_var_id += 1;
            }
        }

        let max_var = if next_var_id > ts.max_var + 1 {
            next_var_id - 1
        } else {
            ts.max_var
        };

        // Build linking clauses: next_var <=> next_state_expr
        // For each latch: next_var_i <=> f_i(current_state, inputs)
        // Encoded as: (!next_var OR f_i) AND (next_var OR !f_i)
        let mut next_link_clauses = Vec::new();
        for &latch_var in &ts.latch_vars {
            if let (Some(&next_var), Some(&next_expr)) =
                (next_vars.get(&latch_var), ts.next_state.get(&latch_var))
            {
                let nv_pos = Lit::pos(next_var);
                let nv_neg = Lit::neg(next_var);
                // next_var <=> next_expr
                // (!next_var OR next_expr) AND (next_var OR !next_expr)
                next_link_clauses.push(vec![nv_neg, next_expr]);
                next_link_clauses.push(vec![nv_pos, !next_expr]);
            }
        }

        // Internal signals (#4148): Tseitin linking clauses for primed internal
        // signals. For g = AND(a, b), create: g' <=> AND(resolve(a), resolve(b))
        if config.internal_signals {
            for &isig_var in &ts.internal_signals {
                if let Some(&next_var) = next_vars.get(&isig_var) {
                    if let Some(&(rhs0, rhs1)) = ts.and_defs.get(&isig_var) {
                        let rhs0_primed = Self::resolve_lit_to_primed(rhs0, &next_vars);
                        let rhs1_primed = Self::resolve_lit_to_primed(rhs1, &next_vars);
                        let nv_pos = Lit::pos(next_var);
                        let nv_neg = Lit::neg(next_var);
                        next_link_clauses.push(vec![nv_neg, rhs0_primed]);
                        next_link_clauses.push(vec![nv_neg, rhs1_primed]);
                        next_link_clauses.push(vec![nv_pos, !rhs0_primed, !rhs1_primed]);
                    }
                }
            }
        }

        // Pre-compute init map from unit init clauses.
        let mut init_map = FxHashMap::default();
        for clause in &ts.init_clauses {
            if clause.lits.len() == 1 {
                let lit = clause.lits[0];
                init_map.insert(lit.var(), lit.is_positive());
            }
        }

        // Pre-compute reverse next-state map.
        let reverse_next: FxHashMap<Var, Var> = next_vars
            .iter()
            .map(|(&latch_var, &next_var)| (next_var, latch_var))
            .collect();

        let ternary_sim = TernarySim::new(&ts);
        let lift = LiftSolver::new(&ts, &next_vars, max_var);

        // Pre-compute variable dependency graph for domain restriction.
        // This enables building domain-restricted mini-solvers for MIC,
        // the key optimization from rIC3 (domain-restricted SAT).
        let domain_computer = DomainComputer::new(&ts, &next_vars, max_var);

        // Initialize bucket-queue VSIDS with seed-based perturbation for portfolio
        // diversity. Different seeds produce different MIC literal orderings,
        // leading to complementary generalization paths. This mirrors rIC3's --rseed.
        // Reference: rIC3 `gipsat/vsids.rs` — dual bucket/heap VSIDS.
        let vsids_config = vsids::VsidsConfig {
            random_seed: config.random_seed,
            decay: config.vsids_decay,
            switch_to_heap_after_restarts: config.bucket_queue_restarts,
            ..vsids::VsidsConfig::default()
        };
        let vsids = vsids::BucketQueueVsids::with_config(max_var, vsids_config);

        // Build predprop solver if enabled.
        let predprop_solver = if config.predprop {
            Some(predprop::PredPropSolver::new(
                &ts,
                &next_vars,
                max_var,
                &next_link_clauses,
                config.solver_backend,
            ))
        } else {
            None
        };

        // Auto-disable crosscheck for high-constraint circuits (#4121).
        // On circuits like microban (100-300+ constraint_lits on 20-60 latches),
        // SimpleSolver's basic DPLL produces false SAT on constraint-dense formulas.
        // Waiting for the cross-check failure budget to be exhausted wastes time
        // and can cause infinite rebuild loops (microban_1). Disable preemptively.
        let crosscheck_disabled = super::config::is_high_constraint_circuit(
            ts.trans_clauses.len(),
            ts.constraint_lits.len(),
            ts.latch_vars.len(),
        );
        if crosscheck_disabled {
            eprintln!(
                "IC3: auto-disabling crosscheck for high-constraint circuit \
                 (constraints={}, trans_clauses={}, latches={}, \
                 constraint_ratio={:.1}x, trans_ratio={:.1}x) (#4121)",
                ts.constraint_lits.len(),
                ts.trans_clauses.len(),
                ts.latch_vars.len(),
                if ts.latch_vars.is_empty() { 0.0 } else {
                    ts.constraint_lits.len() as f64 / ts.latch_vars.len() as f64
                },
                if ts.latch_vars.is_empty() { 0.0 } else {
                    ts.trans_clauses.len() as f64 / ts.latch_vars.len() as f64
                },
            );
        }

        let mut engine = Ic3Engine {
            ts,
            solvers: Vec::new(),
            frames: Frames::new(),
            obligations: ObligationQueue::new(),
            next_vars,
            max_var,
            next_link_clauses,
            solver_backend: config.solver_backend,
            cancelled: Arc::new(AtomicBool::new(false)),
            vsids,
            init_map,
            reverse_next,
            ternary_sim,
            lift,
            inf_lemmas: Vec::new(),
            inf_solver: Box::new(SimpleSolver::new()), // placeholder
            config,
            solve_count: 0,
            domain_computer,
            domain_stats: DomainStats::new(),
            unknown_count: 0,
            fell_back_to_no_preprocess: false,
            earliest_changed_frame: 1,
            predprop_solver,
            crosscheck_failures: Vec::new(),
            total_crosscheck_failures: 0,
            crosscheck_disabled,
            consecution_verify_counter: 0,
            po_drop_count: 0,
            spurious_init_pred_count: 0,
            panic_count: 0,
            rebuild_counts: Vec::new(),
        };
        engine.inf_solver = engine.build_inf_solver();
        engine
    }

    /// Resolve a literal to its primed version using the next_vars map (#4148).
    fn resolve_lit_to_primed(lit: Lit, next_vars: &FxHashMap<Var, Var>) -> Lit {
        if let Some(&next_var) = next_vars.get(&lit.var()) {
            if lit.is_positive() {
                Lit::pos(next_var)
            } else {
                Lit::neg(next_var)
            }
        } else {
            lit // Input or constant — no primed version
        }
    }

    /// Build an infinity frame solver pre-loaded with Trans + constraints + next-linking.
    pub(super) fn build_inf_solver(&self) -> Box<dyn SatSolver> {
        let mut s = self.make_solver();
        s.add_clause(&[Lit::TRUE]);
        for clause in &self.ts.trans_clauses {
            s.add_clause(&clause.lits);
        }
        for &constraint in &self.ts.constraint_lits {
            s.add_clause(&[constraint]);
        }
        for clause in &self.next_link_clauses {
            s.add_clause(clause);
        }
        // Re-add any existing infinity lemmas (needed after solver rebuild).
        for lemma in &self.inf_lemmas {
            s.add_clause(&lemma.lits);
        }
        s
    }

    /// Set the cancellation flag (shared with portfolio).
    ///
    /// Propagates the flag to all existing SAT solvers (frame solvers, inf solver,
    /// lift solver) so z4-sat's CDCL loop can exit promptly when cancelled (#4057).
    /// New solvers created by `make_solver` also receive the flag automatically.
    pub fn set_cancelled(&mut self, cancelled: Arc<AtomicBool>) {
        // Wire cancellation into all existing frame solvers.
        for solver in &mut self.solvers {
            solver.set_cancelled(cancelled.clone());
        }
        // Wire into the infinity frame solver.
        self.inf_solver.set_cancelled(cancelled.clone());
        // Wire into the lift solver.
        self.lift.set_cancelled(cancelled.clone());
        // Wire into the predprop solver if present (#4065).
        if let Some(ref mut pp) = self.predprop_solver {
            pp.set_cancelled(cancelled.clone());
        }
        self.cancelled = cancelled;
    }

    pub(super) fn is_cancelled(&self) -> bool {
        self.cancelled.load(Ordering::Relaxed)
    }

    /// Use SimpleSolver instead of the configured backend (for unit tests with tiny circuits).
    #[cfg(test)]
    pub fn with_simple_solver(mut self) -> Self {
        self.solver_backend = SolverBackend::Simple;
        self.inf_solver = self.build_inf_solver();
        self
    }

    /// Create a new SAT solver with the configured backend, inprocessing
    /// disabled, and cancellation flag wired in (#4057, #4102).
    ///
    /// IC3 makes thousands of short incremental SAT calls. Periodic
    /// inprocessing (BVE, vivification, subsumption, etc.) between these
    /// calls is harmful: it adds overhead with no benefit for short queries,
    /// and BVE/BCE can corrupt incremental state. rIC3's GipSAT never
    /// runs inprocessing — `make_solver_no_inprocessing()` achieves parity.
    pub(super) fn make_solver(&self) -> Box<dyn SatSolver> {
        let mut solver = self.solver_backend.make_solver_no_inprocessing(self.max_var + 1);
        // Wire cancellation flag into z4-sat's interrupt mechanism (#4057).
        // When the portfolio sets cancelled=true, z4-sat's internal CDCL loop
        // detects it via is_interrupted() and returns Unknown promptly.
        solver.set_cancelled(self.cancelled.clone());
        solver
    }

    /// Create a SimpleSolver for invariant validation (#4092).
    ///
    /// Validation uses SimpleSolver (basic DPLL) as an independent cross-check
    /// against z4-sat. The original false UNSAT issue was caused by MIC
    /// over-generalization producing init-inconsistent cubes at the IC3
    /// algorithm level, not by z4-sat's SAT solving. SimpleSolver serves
    /// as defense-in-depth to catch any future solver discrepancies.
    pub(super) fn make_validation_solver(&self) -> Box<dyn SatSolver> {
        let mut solver = SimpleSolver::new();
        solver.ensure_vars(self.max_var + 1);
        Box::new(solver)
    }

    /// Create a solver for non-consecution validation checks (#4121).
    ///
    /// For Check 1 (Init => Inv) and Check 3 (Inv => !Bad), SimpleSolver is safe
    /// but slow on medium-large circuits (>60 latches) where the number of
    /// trans_clauses overwhelms basic DPLL. The BVE soundness risk that motivates
    /// SimpleSolver for Check 2 (Inv AND T => Inv') does not apply to Check 1/3
    /// because these checks don't involve primed variables or inductive reasoning.
    ///
    /// For small circuits (<=60 latches), SimpleSolver is fast enough and provides
    /// maximum independence from the configured backend. For medium+ circuits,
    /// use Z4NoPreprocess (disables BVE/subsumption) which is significantly faster
    /// than SimpleSolver while still avoiding preprocessing-related soundness bugs.
    pub(super) fn make_fast_validation_solver(&self) -> Box<dyn SatSolver> {
        if self.ts.latch_vars.len() <= 60 {
            self.make_validation_solver()
        } else {
            SolverBackend::Z4NoPreprocess.make_solver_no_inprocessing(self.max_var + 1)
        }
    }

    /// Clone the infinity solver as a base for a new frame solver, or build
    /// from scratch if cloning fails. Always wires in the cancellation flag.
    ///
    /// This is the core of #4062: rIC3 clones `self.inf_solver` when extending
    /// to a new frame (`ic3/mod.rs:179`), carrying forward the transition
    /// relation, constraints, next-linking, and infinity lemmas. By cloning
    /// instead of rebuilding, we avoid replaying hundreds of clauses.
    ///
    /// For Z4SatCdclSolver, cloning replays the clause_log into a fresh solver
    /// (since z4-sat doesn't derive Clone). For SimpleSolver, it does a direct
    /// struct clone. If cloning fails (e.g., poisoned solver), we fall back to
    /// building from scratch with `make_solver()`.
    ///
    /// **Critical:** cloned solvers do NOT inherit the cancellation flag from
    /// the source solver. We must wire it in explicitly after every clone to
    /// ensure portfolio cancellation works (#4057).
    pub(super) fn clone_or_build_base_solver(&self) -> Box<dyn SatSolver> {
        // Prefer native incremental clone which preserves learned clauses
        // and VSIDS scores (#4091). Falls back to clause-log replay clone,
        // then to building from scratch.
        if let Some(mut cloned) = self.inf_solver.clone_for_incremental() {
            // Wire cancellation into the cloned solver (#4057).
            // clone_for_incremental() creates a fresh solver that doesn't
            // inherit the source's cancellation flag.
            cloned.set_cancelled(self.cancelled.clone());
            cloned
        } else if let Some(mut cloned) = self.inf_solver.clone_solver() {
            // Fallback: clause-log replay clone.
            cloned.set_cancelled(self.cancelled.clone());
            cloned
        } else {
            // Fallback: build from scratch (make_solver wires cancellation).
            let mut s = self.make_solver();
            s.add_clause(&[Lit::TRUE]);
            for clause in &self.ts.trans_clauses {
                s.add_clause(&clause.lits);
            }
            for &constraint in &self.ts.constraint_lits {
                s.add_clause(&[constraint]);
            }
            for clause in &self.next_link_clauses {
                s.add_clause(clause);
            }
            for lemma in &self.inf_lemmas {
                s.add_clause(&lemma.lits);
            }
            s
        }
    }

    /// Clone a frame solver to use as the base for the next frame's solver.
    ///
    /// Tries native incremental clone first (preserves learned clauses + VSIDS
    /// scores), then clause-log replay clone. Returns `None` if the source
    /// solver is poisoned or cloning fails, in which case the caller should
    /// fall back to `clone_or_build_base_solver()`.
    ///
    /// This enables **cascading frame solver cloning** (#4100): instead of
    /// cloning inf_solver for each frame and replaying all cumulative lemmas,
    /// we clone solver[i-1] (which already contains lemmas from frames 1..=i-1)
    /// and add only frame[i]'s lemmas. This reduces rebuild cost from
    /// O(frames * total_lemmas) to O(frames * avg_lemmas_per_frame).
    ///
    /// **Critical:** cloned solvers do NOT inherit the cancellation flag.
    /// The caller must wire it in explicitly after cloning (#4057).
    pub(super) fn clone_frame_solver(&self, solver: &dyn SatSolver) -> Option<Box<dyn SatSolver>> {
        if solver.is_poisoned() {
            return None;
        }
        // Prefer native incremental clone (preserves learned clauses + VSIDS).
        if let Some(mut cloned) = solver.clone_for_incremental() {
            cloned.set_cancelled(self.cancelled.clone());
            return Some(cloned);
        }
        // Fallback: clause-log replay clone.
        if let Some(mut cloned) = solver.clone_solver() {
            cloned.set_cancelled(self.cancelled.clone());
            return Some(cloned);
        }
        None
    }

    /// Rebuild all frame solvers from scratch to clear accumulated state.
    ///
    /// Even with push/pop (#4016), z4-sat's internal data structures may
    /// accumulate overhead over thousands of calls: learned clause databases
    /// grow, variable activity scores become skewed, and internal bookkeeping
    /// for scope management adds up.
    ///
    /// This method rebuilds each frame solver with only its current lemmas,
    /// the transition relation, constraints, and next-state linking. All
    /// accumulated internal state is discarded.
    ///
    /// ## Cascading frame solver cloning (#4100)
    ///
    /// Instead of cloning inf_solver for every frame and replaying all cumulative
    /// lemmas (O(frames * total_lemmas)), we use cascading clones: build solver[0]
    /// from inf_solver, then clone solver[0] to build solver[1] (adding only
    /// frame[1]'s lemmas), clone solver[1] to build solver[2], etc. This reduces
    /// rebuild cost to O(frames * avg_lemmas_per_frame) since each clone already
    /// contains the previous frame's lemmas.
    ///
    /// When native incremental cloning is available (z4-sat `clone_for_incremental`),
    /// the cloned solver inherits learned clauses and VSIDS scores from the previous
    /// frame, giving the new solver a warm start instead of cold-starting from scratch.
    ///
    /// Falls back to cloning from inf_solver if any frame solver clone fails
    /// (e.g., poisoned solver in the chain).
    ///
    /// Reference: rIC3's `clean_learnt(full)` prunes learned clauses
    /// periodically. Our approach is more aggressive (full rebuild) because
    /// z4-sat doesn't expose a learned-clause pruning API.
    pub(super) fn rebuild_solvers(&mut self) {
        // Rebuild the infinity solver first so we can clone it for frame solvers (#4062).
        self.inf_solver = self.build_inf_solver();

        let depth = self.frames.depth();
        let num_solvers = self.solvers.len().min(depth);
        let mut cloned_from_prev = 0usize;

        for i in 0..num_solvers {
            if i == 0 {
                // Frame 0: clone inf_solver as the base, add Init + frame-0 lemmas.
                // solver[0] must contain Init so that consecution at frame 0
                // correctly tests Init(x) AND Trans(x,x') AND c'(x') (#4074).
                let mut solver = self.clone_or_build_base_solver();
                for clause in &self.ts.init_clauses {
                    solver.add_clause(&clause.lits);
                }
                for lemma in &self.frames.frames[0].lemmas {
                    solver.add_clause(&lemma.lits);
                }
                self.solvers[i] = solver;
            } else {
                // Frame i >= 1: try cascading clone from solver[i-1] (#4100).
                // solver[i-1] already contains Trans + constraints + next-linking +
                // inf_lemmas + lemmas from frames 1..=i-1. We only need to add
                // frame[i]'s own lemmas.
                let upper = i.min(depth.saturating_sub(1));
                if let Some(mut solver) = self.clone_frame_solver(self.solvers[i - 1].as_ref()) {
                    // Cascading clone succeeded — add only this frame's lemmas.
                    for lemma in &self.frames.frames[upper].lemmas {
                        solver.add_clause(&lemma.lits);
                    }
                    self.solvers[i] = solver;
                    cloned_from_prev += 1;
                } else {
                    // Cascading clone failed (previous solver poisoned or clone
                    // unsupported). Fall back to inf_solver clone + full replay.
                    let mut solver = self.clone_or_build_base_solver();
                    for f in 1..=upper {
                        for lemma in &self.frames.frames[f].lemmas {
                            solver.add_clause(&lemma.lits);
                        }
                    }
                    self.solvers[i] = solver;
                }
            }
        }
        // Rebuild predprop solver with all infinity lemmas (#4101).
        if let Some(ref mut pp) = self.predprop_solver {
            let inf_lemma_clauses: Vec<Vec<Lit>> =
                self.inf_lemmas.iter().map(|l| l.lits.clone()).collect();
            pp.rebuild(&inf_lemma_clauses);
        }

        self.solve_count = 0;
        // Reset per-frame rebuild counters after a full rebuild (#4105).
        for count in &mut self.rebuild_counts {
            *count = 0;
        }
        eprintln!(
            "IC3: rebuilt {} frame solvers + inf solver ({} cascading clones){}",
            num_solvers,
            cloned_from_prev,
            if self.predprop_solver.is_some() {
                format!(
                    " + predprop ({} lemmas)",
                    self.predprop_solver.as_ref().map_or(0, |pp| pp.lemma_count()),
                )
            } else {
                String::new()
            },
        );
    }

    /// Rebuild a single frame solver from scratch.
    ///
    /// Used to recover from solver poisoning: when a z4-sat panic is caught
    /// by `catch_unwind`, the solver is marked poisoned and all subsequent
    /// calls return `Unknown`. Rather than losing the entire IC3 engine,
    /// we rebuild just the affected solver with the correct frame lemmas
    /// and retry the operation.
    ///
    /// This is the key recovery mechanism for #4040: z4-sat panics during
    /// conflict analysis or clause shrinking no longer kill the IC3 engine.
    /// The poisoned solver is replaced with a fresh one, and IC3 continues
    /// from where it left off.
    /// Check whether the solver at `idx` has exceeded its rebuild budget (#4105).
    ///
    /// Returns `true` if the solver has been rebuilt too many times and further
    /// rebuilds should be skipped. Callers should treat the query result
    /// conservatively (as Sat) when this returns `true`.
    pub(super) fn solver_rebuild_budget_exceeded(&self, idx: usize) -> bool {
        if idx < self.rebuild_counts.len() {
            self.rebuild_counts[idx] >= MAX_SOLVER_REBUILDS_PER_FRAME
        } else {
            false
        }
    }

    pub(super) fn rebuild_solver_at(&mut self, idx: usize) {
        // Increment per-frame rebuild counter (#4105).
        while self.rebuild_counts.len() <= idx {
            self.rebuild_counts.push(0);
        }
        self.rebuild_counts[idx] += 1;
        if self.rebuild_counts[idx] > MAX_SOLVER_REBUILDS_PER_FRAME {
            eprintln!(
                "IC3: rebuild budget exceeded at frame {} ({} rebuilds, max {}) — \
                 skipping rebuild (#4105)",
                idx,
                self.rebuild_counts[idx],
                MAX_SOLVER_REBUILDS_PER_FRAME,
            );
            return;
        }

        // Track whether this rebuild is due to a z4-sat panic (#4092).
        // The solver was poisoned by catch_unwind after a panic — this means
        // the solver's state was corrupted, and prior results may be unsound.
        let was_poisoned = self.solvers[idx].is_poisoned();

        let depth = self.frames.depth();
        let upper = idx.min(depth.saturating_sub(1));

        // Cascading clone optimization (#4100): for frames >= 1, try cloning
        // from the previous frame's solver instead of rebuilding from inf_solver.
        // The previous solver already has all cumulative lemmas 1..=idx-1, so
        // we only need to add frame[idx]'s lemmas.
        //
        // CRITICAL: do NOT clone from a poisoned previous solver — that's the
        // whole reason we're rebuilding. Only cascade if the previous solver
        // is healthy.
        if idx >= 1 {
            if let Some(mut solver) = self.clone_frame_solver(self.solvers[idx - 1].as_ref()) {
                for lemma in &self.frames.frames[upper].lemmas {
                    solver.add_clause(&lemma.lits);
                }
                self.solvers[idx] = solver;
                eprintln!("IC3: rebuilt solver at frame {idx} (cascading clone from frame {})", idx - 1);
                if was_poisoned {
                    self.handle_solver_panic();
                }
                return;
            }
        }

        // Fallback: clone inf_solver as a base (#4062), then replay all
        // per-frame lemmas. This path is used for frame 0, or when the
        // previous frame solver is poisoned/uncloneable.
        let mut solver = self.clone_or_build_base_solver();
        // solver[0] gets only frame-0 lemmas.
        // solver[k>=1] gets lemmas from frames 1..=k (NOT frame 0).
        // Adding frame-0 lemmas to solver[k>=1] over-constrains it (#4039).
        if idx == 0 {
            // Add Init clauses for frame 0 (#4074).
            for clause in &self.ts.init_clauses {
                solver.add_clause(&clause.lits);
            }
            for lemma in &self.frames.frames[0].lemmas {
                solver.add_clause(&lemma.lits);
            }
        } else {
            for f in 1..=upper {
                for lemma in &self.frames.frames[f].lemmas {
                    solver.add_clause(&lemma.lits);
                }
            }
        }
        self.solvers[idx] = solver;
        eprintln!("IC3: rebuilt solver at frame {idx} (from inf_solver)");
        if was_poisoned {
            self.handle_solver_panic();
        }
    }

    /// Handle a z4-sat panic by tracking it and triggering fallback (#4092).
    ///
    /// Called after `rebuild_solver_at` when the rebuild was due to a poisoned
    /// solver (z4-sat panic). Increments the panic counter and, when the
    /// threshold is reached:
    /// 1. Falls back to SimpleSolver (no known panic bugs)
    /// 2. Purges ALL frame lemmas — they may be unsound from pre-crash corruption
    /// 3. Rebuilds all solvers from scratch with the new backend
    ///
    /// Returns `true` if a full reset was triggered (caller should restart
    /// the IC3 loop from the current depth instead of continuing).
    pub(super) fn handle_solver_panic(&mut self) -> bool {
        self.panic_count += 1;
        if self.panic_count >= PANIC_FALLBACK_THRESHOLD
            && self.solver_backend != SolverBackend::Simple
        {
            let num_latches = self.ts.latch_vars.len();
            eprintln!(
                "IC3: z4-sat panic #{} — falling back to SimpleSolver and purging \
                 all frame lemmas ({} latches). Prior lemmas may be unsound from \
                 pre-crash solver corruption (#4092).",
                self.panic_count, num_latches,
            );

            // Switch to SimpleSolver.
            self.solver_backend = SolverBackend::Simple;
            self.fell_back_to_no_preprocess = true; // skip intermediate stage

            // Purge ALL frame lemmas — they were produced by a buggy solver.
            // The IC3 algorithm will re-derive sound lemmas from scratch using
            // SimpleSolver. This is aggressive but necessary: the z4-sat
            // corruption may have produced incorrect UNSAT results that created
            // unsound lemmas before the panic manifested.
            let depth = self.frames.depth();
            let mut purged = 0usize;
            for f in 0..depth {
                purged += self.frames.frames[f].lemmas.len();
                self.frames.frames[f].lemmas.clear();
            }
            self.inf_lemmas.clear();
            eprintln!(
                "IC3: purged {} frame lemmas + {} inf lemmas across {} frames",
                purged, 0, depth,
            );

            // Rebuild the lift solver with SimpleSolver backend.
            self.lift = LiftSolver::new_no_preprocess(&self.ts, &self.next_vars, self.max_var);
            self.lift.set_cancelled(self.cancelled.clone());

            // Rebuild domain computer.
            self.domain_computer = DomainComputer::new(&self.ts, &self.next_vars, self.max_var);

            // Update predprop solver backend before rebuild.
            if let Some(ref mut pp) = self.predprop_solver {
                pp.set_solver_backend(self.solver_backend);
            }

            // Rebuild all solvers from scratch with SimpleSolver.
            self.rebuild_solvers();
            self.unknown_count = 0;

            return true;
        }
        false
    }

    /// Fall back to a simpler solver backend when z4-sat produces persistent
    /// FINALIZE_SAT_FAIL (InvalidSatModel) errors (#4074).
    ///
    /// z4-sat's CDCL solver has a known model reconstruction bug that causes
    /// `finalize_sat_model()` to return Unknown on certain clause structures
    /// (e.g., cal14, cal42, bakery). The solver returns Unknown without
    /// panicking, so `is_poisoned()` is false. But IC3 cannot make progress
    /// because SAT results (needed for predecessor extraction in consecution
    /// checks) never arrive.
    ///
    /// Two-stage fallback:
    /// 1. First attempt: Z4NoPreprocess (disables BVE/subsumption). This
    ///    avoids BVE-specific model reconstruction bugs.
    /// 2. Second attempt: SimpleSolver (basic DPLL). This avoids ALL z4-sat
    ///    bugs at the cost of performance. Viable for small circuits (<50
    ///    latches) which is exactly the class of benchmarks affected.
    ///
    /// This is a one-shot escalation per stage (NoPreprocess -> Simple).
    pub(super) fn fallback_solver_backend(&mut self) {
        if !self.fell_back_to_no_preprocess {
            // Stage 1: try disabling preprocessing first.
            eprintln!(
                "IC3: falling back to Z4NoPreprocess due to {} consecutive Unknown results \
                 (FINALIZE_SAT_FAIL from z4-sat)",
                self.unknown_count,
            );
            self.solver_backend = SolverBackend::Z4NoPreprocess;
            self.fell_back_to_no_preprocess = true;
        } else {
            // Stage 2: Z4NoPreprocess also failed. Fall back to SimpleSolver.
            // SimpleSolver is a basic DPLL without UNSAT cores or incremental
            // features. MIC generalization will be weaker (no core-based reduction)
            // but correct. Viable for small circuits (<50 latches).
            eprintln!(
                "IC3: falling back to SimpleSolver due to {} consecutive Unknown results \
                 (FINALIZE_SAT_FAIL persists even without preprocessing)",
                self.unknown_count,
            );
            self.solver_backend = SolverBackend::Simple;
        }
        self.unknown_count = 0;
        // Rebuild the lift solver. Use no-preprocessing variant since the lift
        // solver primarily uses UNSAT cores (less affected by model bugs).
        self.lift = LiftSolver::new_no_preprocess(&self.ts, &self.next_vars, self.max_var);
        self.lift.set_cancelled(self.cancelled.clone());
        // Rebuild domain computer.
        self.domain_computer = DomainComputer::new(&self.ts, &self.next_vars, self.max_var);
        // Update predprop solver backend before rebuild (#4101).
        if let Some(ref mut pp) = self.predprop_solver {
            pp.set_solver_backend(self.solver_backend);
        }
        // Rebuild all frame solvers + infinity solver + predprop with the new backend.
        self.rebuild_solvers();
    }

    /// Compute the adaptive solver rebuild threshold based on circuit size.
    ///
    /// Small circuits (< 20 latches) use the base threshold. Larger circuits
    /// scale proportionally, since they have more frame solvers and rebuilding
    /// is more expensive.
    pub(super) fn rebuild_threshold(&self) -> usize {
        let scale = (self.ts.latch_vars.len() / 20).max(1);
        SOLVER_REBUILD_BASE.saturating_mul(scale)
    }
}
