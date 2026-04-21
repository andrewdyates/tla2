// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded Model Checking (BMC) engine for CHC
//!
//! BMC unrolls the transition relation k times and checks if a bad state is reachable.
//! Unlike PDR which proves safety by finding inductive invariants, BMC is good for
//! finding bugs (SAT cases) by exhaustively searching bounded execution paths.
//!
//! # Algorithm (Level-Based Encoding)
//!
//! Based on Z3's `dl_bmc_engine.cpp` linear BMC class. For each level k:
//!
//! 1. Create level predicates `P#k` = "predicate P is reachable at level k"
//! 2. Create level arguments `P#k_i` = "argument i of P at level k"
//! 3. Create rule indicators `rule:P#k_i` = "rule i derives P at level k"
//!
//! Encoding:
//! - `P#k => rule:P#k_0 ∨ rule:P#k_1 ∨ ...` (at least one rule applies)
//! - `rule:P#k_i => body_constraints ∧ head_equalities ∧ body_predicates#(k-1)`
//! - At level 0, rules with body predicates are disabled
//!
//! # Complementarity with PDR
//!
//! - PDR: Good for proving safety (UNSAT/Safe cases)
//! - BMC: Good for finding bugs (SAT/Unsafe cases)
//!
//! A portfolio approach runs both in parallel, returning whichever finishes first.

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use crate::cancellation::CancellationToken;
use crate::engine_config::ChcEngineConfig;
use crate::engine_result::ChcEngineResult;
use crate::pdr::counterexample::{Counterexample, CounterexampleStep};
use crate::pdr::model::InvariantModel;
use crate::smt::executor_adapter::{parse_model_into, quote_symbol, sort_to_smtlib};
use crate::smt::{IncrementalSatContext, SmtContext, SmtValue};
use crate::{ChcExpr, ChcProblem, ChcSort, ChcVar, ClauseHead, HornClause, PredicateId};
use rustc_hash::{FxHashMap, FxHashSet};
use std::panic::AssertUnwindSafe;

/// BMC solver configuration
#[derive(Debug, Clone)]
pub struct BmcConfig {
    /// Common engine settings (verbose, cancellation).
    pub(crate) base: ChcEngineConfig,
    /// Maximum unrolling depth (number of transitions)
    pub(crate) max_depth: usize,
    /// When true, BMC returns Safe (not Unknown) if max_depth is exhausted
    /// without finding a counterexample. Sound ONLY for acyclic CHC problems
    /// where no execution path can exceed `max_depth` transitions.
    pub(crate) acyclic_safe: bool,
    /// Per-depth SMT query timeout. When `Some`, each depth's `check_sat` call
    /// is bounded. This prevents BV bitblasting at deep unrolling depths from
    /// consuming the entire portfolio budget on a single query (#5877).
    /// When `None` (default), individual depth queries run unbounded.
    pub(crate) per_depth_timeout: Option<std::time::Duration>,
}

impl Default for BmcConfig {
    fn default() -> Self {
        Self {
            base: ChcEngineConfig::default(),
            max_depth: 50,
            acyclic_safe: false,
            per_depth_timeout: None,
        }
    }
}

impl BmcConfig {
    /// Create config with verbose and cancellation token (convenience for callers).
    pub fn with_engine_config(
        max_depth: usize,
        verbose: bool,
        cancellation_token: Option<CancellationToken>,
    ) -> Self {
        Self {
            base: ChcEngineConfig {
                verbose,
                cancellation_token,
            },
            max_depth,
            acyclic_safe: false,
            per_depth_timeout: None,
        }
    }
}

/// A counterexample trace from BMC (internal representation before conversion
/// to the unified Counterexample type).
#[derive(Debug, Clone)]
pub(crate) struct BmcCounterexample {
    pub states: Vec<FxHashMap<String, SmtValue>>,
}

impl BmcCounterexample {
    fn into_counterexample(self) -> Counterexample {
        let steps = self
            .states
            .iter()
            .map(|state| {
                let assignments: FxHashMap<String, i64> = state
                    .iter()
                    .filter_map(|(k, v)| match v {
                        SmtValue::Int(n) => Some((k.clone(), *n)),
                        SmtValue::Bool(b) => Some((k.clone(), if *b { 1 } else { 0 })),
                        SmtValue::BitVec(val, _w) => Some((k.clone(), *val as i64)),
                        _ => None,
                    })
                    .collect();
                CounterexampleStep {
                    predicate: PredicateId(0),
                    assignments,
                }
            })
            .collect();
        Counterexample {
            steps,
            witness: None,
        }
    }
}

/// BMC solver for CHC problems
pub struct BmcSolver {
    problem: ChcProblem,
    config: BmcConfig,
}

impl Drop for BmcSolver {
    fn drop(&mut self) {
        std::mem::take(&mut self.problem).iterative_drop();
    }
}

impl BmcSolver {
    /// Create a new BMC solver
    pub(crate) fn new(problem: ChcProblem, config: BmcConfig) -> Self {
        Self { problem, config }
    }

    /// Solve using bounded model checking.
    ///
    /// Returns `Unsafe` if a counterexample is found within `max_depth` steps,
    /// `Safe` if `acyclic_safe` is set and all depths are exhausted without
    /// counterexample (sound for acyclic problems where paths are bounded),
    /// or `Unknown` otherwise.
    ///
    /// Tries the per-depth fresh Executor path first (#7982/#7983), which uses
    /// z4-dpll's full DPLL(T) executor with cached SMT prefix. Falls back to
    /// the legacy IncrementalSatContext path if the executor fails.
    pub fn solve(&self) -> ChcEngineResult {
        tracing::debug!(
            "BMC: Starting with max_depth={}, acyclic_safe={}",
            self.config.max_depth,
            self.config.acyclic_safe
        );

        if self.problem.predicates().is_empty() {
            return ChcEngineResult::Unknown;
        }
        let queries: Vec<_> = self.problem.queries().collect();
        if queries.is_empty() {
            return ChcEngineResult::Unknown;
        }

        // Per-depth fresh Executor (#7982/#7983): for each depth k, build
        // the complete BMC formula and run one check-sat. Avoids the legacy
        // path's O(n) fresh LiaSolver creation per DPLL(T) iteration.
        match self.solve_via_executor(&queries) {
            Some(result) => return result,
            None => {
                tracing::debug!("BMC: Executor path failed, falling back to legacy");
            }
        }

        self.solve_legacy(&queries)
    }

    /// Legacy BMC solve using IncrementalSatContext (non-incremental theory solver).
    ///
    /// Kept as fallback when the executor path fails.
    fn solve_legacy(&self, queries: &[&HornClause]) -> ChcEngineResult {
        let mut smt = self.problem.make_smt_context();
        let mut inc = IncrementalSatContext::new();

        // Assert level 0 constraints as background (fact clauses only).
        let mut level0_conjuncts = Vec::new();
        self.compile_level(0, &mut level0_conjuncts);
        let level0_formula = ChcExpr::and_all(level0_conjuncts.iter().cloned());
        inc.assert_background(&level0_formula, &mut smt);
        inc.finalize_background(&smt);

        for k in 0..=self.config.max_depth {
            if self.config.base.is_cancelled() {
                tracing::debug!("BMC: Cancelled by portfolio at depth {}", k);
                return ChcEngineResult::Unknown;
            }
            if let Some(result) = self.check_depth(k, queries, &mut smt, &mut inc) {
                return result;
            }
        }

        if self.config.acyclic_safe {
            tracing::debug!(
                "BMC: Acyclic exhaustion at depth {} — returning Safe",
                self.config.max_depth
            );
            return ChcEngineResult::Safe(crate::pdr::model::InvariantModel::default());
        }

        tracing::debug!(
            "BMC: No counterexample found within {} steps",
            self.config.max_depth
        );
        ChcEngineResult::Unknown
    }

    /// Check a single BMC depth. Returns `Some(result)` if a counterexample is
    /// found or an early-exit condition is met, `None` to continue to next depth.
    fn check_depth(
        &self,
        k: usize,
        queries: &[&HornClause],
        smt: &mut SmtContext,
        inc: &mut IncrementalSatContext,
    ) -> Option<ChcEngineResult> {
        tracing::debug!("BMC: Checking depth k={}", k);
        // For k > 0, add level k constraints permanently.
        if k > 0 {
            let mut level_conjuncts = Vec::new();
            self.compile_level(k, &mut level_conjuncts);
            let level_formula = ChcExpr::and_all(level_conjuncts.iter().cloned());
            inc.assert_permanent(&level_formula, smt);
            inc.refresh_var_map(smt);
        }

        // Build query at level k (temporary — different for each depth).
        let mut query_conjuncts = Vec::new();
        for query in queries {
            self.compile_query(query, k, &mut query_conjuncts);
        }
        let query_formula = ChcExpr::and_all(query_conjuncts.iter().cloned());

        let timeout = self.config.per_depth_timeout;
        // #5877: Set per-depth timeout on the SmtContext so BV bitblasting
        // and Tseitin encoding can check it (not just the DPLL(T) solve loop).
        let _timeout_guard = timeout.map(|t| smt.scoped_check_timeout(Some(t)));
        let result =
            match inc.check_sat_incremental(std::slice::from_ref(&query_formula), smt, timeout) {
                crate::smt::IncrementalCheckResult::RetryFresh(_) => {
                    inc.check_sat_fresh_query(std::slice::from_ref(&query_formula), timeout)
                }
                other => other,
            };

        match result {
            crate::smt::IncrementalCheckResult::Sat(model) => {
                tracing::debug!("BMC: Found counterexample at depth {}", k);
                let trace = self.extract_trace_from_incremental(&model, k);
                let cex = BmcCounterexample { states: trace };
                Some(ChcEngineResult::Unsafe(cex.into_counterexample()))
            }
            crate::smt::IncrementalCheckResult::Unsat => {
                tracing::debug!("BMC: No counterexample at depth {}", k);
                None
            }
            crate::smt::IncrementalCheckResult::Unknown
            | crate::smt::IncrementalCheckResult::RetryFresh(_) => {
                tracing::debug!("BMC: SMT unknown at depth {}, continuing", k);
                None
            }
        }
    }

    // ============ Per-Depth Fresh Executor (#7982/#7983) ============

    /// Solve BMC via per-depth fresh Executor with cached SMT prefix.
    ///
    /// For each depth k, builds the complete BMC formula (levels 0..k + query
    /// at k) and runs ONE check-sat on a fresh Executor. The SMT prefix
    /// (declarations + level assertions) is cached and extended incrementally
    /// to avoid O(k^2) re-serialization.
    ///
    /// Returns `Some(result)` on success, `None` if the executor path fails
    /// (caller falls back to legacy path).
    fn solve_via_executor(&self, queries: &[&HornClause]) -> Option<ChcEngineResult> {
        // Try single-executor with activation literals first (#7983).
        // Transitions accumulate as permanent assertions; only the per-depth
        // query uses an activation literal via check-sat-assuming. Learned
        // clauses from depth k persist and help solve depth k+1.
        if let Some(result) = self.solve_single_executor(queries, self.config.max_depth) {
            return Some(result);
        }
        // Fallback: per-depth fresh executor (always works, but discards
        // learned clauses between depths).
        self.solve_per_depth_fresh(queries, self.config.max_depth)
    }

    /// Single persistent Executor with activation literals for per-depth queries.
    ///
    /// Transition constraints accumulate as permanent assertions (monotonic).
    /// The query at each depth is guarded by an activation literal:
    ///   `(assert (=> _bmc_qact_k query_k))`
    /// and solved via `(check-sat-assuming (_bmc_qact_k))`.
    ///
    /// Learned clauses persist across depths, helping deeper queries.
    /// Returns `None` if check-sat-assuming returns unknown (fallback needed).
    fn solve_single_executor(
        &self,
        queries: &[&HornClause],
        max_depth: usize,
    ) -> Option<ChcEngineResult> {
        let logic = self.detect_bmc_logic();
        let mut smt_cmds = format!(
            "(set-logic {logic})\n(set-option :produce-models true)\n"
        );
        let mut declared_vars: FxHashSet<String> = FxHashSet::default();

        // Build level 0 constraints + declarations
        let mut level0_conjuncts = Vec::new();
        self.compile_level_flat(0, &mut level0_conjuncts);
        for conjunct in &level0_conjuncts {
            for var in &conjunct.vars() {
                if declared_vars.insert(var.name.clone()) {
                    let sort_str = sort_to_smtlib(&var.sort);
                    let name = quote_symbol(&var.name);
                    smt_cmds.push_str(&format!("(declare-const {name} {sort_str})\n"));
                }
            }
            let s = InvariantModel::expr_to_smtlib(conjunct);
            smt_cmds.push_str(&format!("(assert {s})\n"));
        }

        // Parse and create executor with level 0 assertions
        let commands = z4_frontend::parse(&smt_cmds).ok()?;
        let mut exec = z4_dpll::Executor::new();
        Self::exec_commands(&mut exec, &commands)?;

        for k in 0..=max_depth {
            if self.config.base.is_cancelled() {
                return Some(ChcEngineResult::Unknown);
            }

            // For k > 0, add level k transition constraints (permanent)
            if k > 0 {
                let mut level_smt = String::new();
                let mut level_conjuncts = Vec::new();
                self.compile_level_flat(k, &mut level_conjuncts);
                for conjunct in &level_conjuncts {
                    for var in &conjunct.vars() {
                        if declared_vars.insert(var.name.clone()) {
                            let sort_str = sort_to_smtlib(&var.sort);
                            let name = quote_symbol(&var.name);
                            level_smt.push_str(&format!("(declare-const {name} {sort_str})\n"));
                        }
                    }
                    let s = InvariantModel::expr_to_smtlib(conjunct);
                    level_smt.push_str(&format!("(assert {s})\n"));
                }
                if !level_smt.is_empty() {
                    let cmds = z4_frontend::parse(&level_smt).ok()?;
                    Self::exec_commands(&mut exec, &cmds)?;
                }
            }

            // Build query at depth k
            let mut query_conjuncts = Vec::new();
            for query in queries {
                self.compile_query(query, k, &mut query_conjuncts);
            }
            if query_conjuncts.is_empty() {
                continue;
            }

            // Declare query variables + activation literal
            let act_name = format!("_bmc_qact_{k}");
            let mut query_smt = format!("(declare-const {act_name} Bool)\n");
            let mut query_declared: FxHashSet<String> = FxHashSet::default();
            let mut query_parts = Vec::new();
            for conjunct in &query_conjuncts {
                for var in &conjunct.vars() {
                    if !declared_vars.contains(&var.name)
                        && query_declared.insert(var.name.clone())
                    {
                        let sort_str = sort_to_smtlib(&var.sort);
                        let name = quote_symbol(&var.name);
                        query_smt.push_str(&format!("(declare-const {name} {sort_str})\n"));
                    }
                }
                query_parts.push(InvariantModel::expr_to_smtlib(conjunct));
            }

            // Assert (=> act_k (and query_parts...)) as permanent assertion
            let query_body = if query_parts.len() == 1 {
                query_parts[0].clone()
            } else {
                format!("(and {})", query_parts.join(" "))
            };
            query_smt.push_str(&format!("(assert (=> {act_name} {query_body}))\n"));

            // check-sat-assuming with only the bare activation literal
            query_smt.push_str(&format!("(check-sat-assuming ({act_name}))\n"));
            query_smt.push_str("(get-model)\n");

            let cmds = z4_frontend::parse(&query_smt).ok()?;
            let outputs = Self::exec_commands(&mut exec, &cmds)?;

            // Find the check-sat result
            let result_str = outputs
                .iter()
                .find(|s| {
                    let t = s.trim();
                    t == "sat" || t == "unsat" || t == "unknown"
                })
                .map(String::as_str)
                .unwrap_or("unknown");

            tracing::debug!("BMC-single: depth={} result: {}", k, result_str);

            match result_str.trim() {
                "sat" => {
                    let model_str = outputs.last().map(String::as_str).unwrap_or("");
                    let mut model = FxHashMap::default();
                    let dt_ctor_names = FxHashSet::default();
                    parse_model_into(&mut model, model_str, &dt_ctor_names);
                    let trace = self.extract_trace(&model, k);
                    let cex = BmcCounterexample { states: trace };
                    return Some(ChcEngineResult::Unsafe(cex.into_counterexample()));
                }
                "unsat" => {
                    // Learned clauses persist. Continue to next depth.
                    continue;
                }
                _ => {
                    // Unknown — fall back to per-depth fresh.
                    tracing::debug!(
                        "BMC-single: unknown at depth {}, falling back",
                        k
                    );
                    return None;
                }
            }
        }

        if self.config.acyclic_safe {
            Some(ChcEngineResult::Safe(
                crate::pdr::model::InvariantModel::default(),
            ))
        } else {
            Some(ChcEngineResult::Unknown)
        }
    }

    /// Per-depth fresh-executor: one check-sat per depth with cached prefix.
    fn solve_per_depth_fresh(
        &self,
        queries: &[&HornClause],
        max_depth: usize,
    ) -> Option<ChcEngineResult> {
        let logic = self.detect_bmc_logic();
        let mut smt_prefix = format!(
            "(set-logic {logic})\n(set-option :produce-models true)\n"
        );
        let mut declared_vars: FxHashSet<String> = FxHashSet::default();

        for k in 0..=max_depth {
            if self.config.base.is_cancelled() {
                return Some(ChcEngineResult::Unknown);
            }

            // Append level k constraints to cached prefix.
            let mut level_conjuncts = Vec::new();
            self.compile_level_flat(k, &mut level_conjuncts);
            for conjunct in &level_conjuncts {
                for var in &conjunct.vars() {
                    if declared_vars.insert(var.name.clone()) {
                        let sort_str = sort_to_smtlib(&var.sort);
                        let name = quote_symbol(&var.name);
                        smt_prefix.push_str(&format!("(declare-const {name} {sort_str})\n"));
                    }
                }
                let s = InvariantModel::expr_to_smtlib(conjunct);
                smt_prefix.push_str(&format!("(assert {s})\n"));
            }

            // Build query at depth k.
            let mut query_conjuncts = Vec::new();
            for query in queries {
                self.compile_query(query, k, &mut query_conjuncts);
            }
            if query_conjuncts.is_empty() {
                continue;
            }

            let mut smt = smt_prefix.clone();
            // #8782: Track query-local variable declarations to prevent
            // duplicate declare-const for the same variable name. Without
            // this, a variable like `x` appearing in both a deferred equality
            // (P#0_0 = x+1) and a constraint (x >= 5) would be declared twice,
            // creating two independent variables that the SMT solver treats as
            // distinct — causing spurious counterexamples.
            let mut query_declared: FxHashSet<String> = FxHashSet::default();
            for conjunct in &query_conjuncts {
                for var in &conjunct.vars() {
                    if !declared_vars.contains(&var.name)
                        && query_declared.insert(var.name.clone())
                    {
                        let sort_str = sort_to_smtlib(&var.sort);
                        let name = quote_symbol(&var.name);
                        smt.push_str(&format!("(declare-const {name} {sort_str})\n"));
                    }
                }
                let s = InvariantModel::expr_to_smtlib(conjunct);
                smt.push_str(&format!("(assert {s})\n"));
            }
            smt.push_str("(check-sat)\n(get-model)\n");

            let commands = z4_frontend::parse(&smt).ok()?;
            let mut exec = z4_dpll::Executor::new();
            let outputs = Self::exec_commands(&mut exec, &commands)?;

            let result_str = outputs.first().map(String::as_str).unwrap_or("unknown");
            tracing::debug!("BMC-exec: depth={} result: {}", k, result_str);

            if result_str == "sat" {
                let model_str = outputs.get(1).map(String::as_str).unwrap_or("");
                let mut model = FxHashMap::default();
                let dt_ctor_names = FxHashSet::default();
                parse_model_into(&mut model, model_str, &dt_ctor_names);
                let trace = self.extract_trace(&model, k);
                let cex = BmcCounterexample { states: trace };
                return Some(ChcEngineResult::Unsafe(cex.into_counterexample()));
            }
        }

        if self.config.acyclic_safe {
            Some(ChcEngineResult::Safe(
                crate::pdr::model::InvariantModel::default(),
            ))
        } else {
            Some(ChcEngineResult::Unknown)
        }
    }

    /// Detect the SMT-LIB logic for this BMC problem based on sorts used.
    fn detect_bmc_logic(&self) -> &'static str {
        let mut has_bv = false;
        let mut has_real = false;
        let mut has_array = false;
        for pred in self.problem.predicates() {
            for sort in &pred.arg_sorts {
                match sort {
                    ChcSort::BitVec(_) => has_bv = true,
                    ChcSort::Real => has_real = true,
                    ChcSort::Array(_, _) => has_array = true,
                    _ => {}
                }
            }
        }
        if has_array {
            if has_bv {
                "QF_ABV"
            } else {
                "QF_AUFLIA"
            }
        } else if has_bv {
            "QF_BV"
        } else if has_real {
            "QF_LIRA"
        } else {
            "QF_LIA"
        }
    }

    /// Execute commands via the executor with panic safety.
    /// Returns `Some(outputs)` on success, `None` on failure.
    fn exec_commands(
        exec: &mut z4_dpll::Executor,
        commands: &[z4_frontend::Command],
    ) -> Option<Vec<String>> {
        z4_core::catch_z4_panics(
            AssertUnwindSafe(|| match exec.execute_all(commands) {
                Ok(out) => Ok(out),
                Err(e) => {
                    tracing::debug!("BMC-exec: executor error: {e}");
                    Err(())
                }
            }),
            |reason| {
                tracing::debug!("BMC-exec: z4 panic: {reason}");
                Err(())
            },
        )
        .ok()
    }

    // ============ Level-Based Encoding Helpers ============
    // Based on Z3's dl_bmc_engine.cpp linear BMC class

    /// Create level predicate: `P#level` (boolean)
    ///
    /// This represents "predicate P is reachable at level"
    fn level_predicate(&self, pred: PredicateId, level: usize) -> ChcExpr {
        let pred_info = self
            .problem
            .get_predicate(pred)
            .expect("BmcSolver: predicate ID from problem should be valid");
        let name = format!("{}#{}", pred_info.name, level);
        ChcExpr::Var(ChcVar::new(name, ChcSort::Bool))
    }

    /// Create level argument: `P#level_idx` (appropriate sort)
    ///
    /// This represents "argument idx of predicate P at level"
    fn level_arg(&self, pred: PredicateId, idx: usize, level: usize) -> ChcExpr {
        let pred_info = self
            .problem
            .get_predicate(pred)
            .expect("BmcSolver: predicate ID from problem should be valid");
        let name = format!("{}#{}_{}", pred_info.name, level, idx);
        let sort = pred_info
            .arg_sorts
            .get(idx)
            .expect("BmcSolver: argument index should be within predicate arity")
            .clone();
        ChcExpr::Var(ChcVar::new(name, sort))
    }

    /// Create rule indicator: `rule:P#level_rule_idx` (boolean)
    ///
    /// This represents "rule rule_idx was used to derive P at level"
    fn rule_indicator(&self, pred: PredicateId, rule_idx: usize, level: usize) -> ChcExpr {
        let pred_info = self
            .problem
            .get_predicate(pred)
            .expect("BmcSolver: predicate ID from problem should be valid");
        let name = format!("rule:{}#{}_{}", pred_info.name, level, rule_idx);
        ChcExpr::Var(ChcVar::new(name, ChcSort::Bool))
    }

    /// Create level variable: `P#level_rule_idx_var_idx` (appropriate sort)
    ///
    /// This represents internal variables used in a rule at a specific level
    fn level_var(
        &self,
        pred: PredicateId,
        rule_idx: usize,
        var_idx: usize,
        level: usize,
        sort: ChcSort,
    ) -> ChcExpr {
        let pred_info = self
            .problem
            .get_predicate(pred)
            .expect("BmcSolver: predicate ID from problem should be valid");
        let name = format!("{}#{}_{}_{}", pred_info.name, level, rule_idx, var_idx);
        ChcExpr::Var(ChcVar::new(name, sort))
    }

    /// Build variable substitution for a rule at a level
    ///
    /// Following Z3's mk_rule_vars approach:
    /// 1. Head arguments map to level arguments
    /// 2. Body predicate arguments map to level-1 arguments
    /// 3. Remaining variables get unique level-specific names
    fn mk_rule_vars(
        &self,
        clause: &HornClause,
        head_pred: PredicateId,
        rule_idx: usize,
        level: usize,
    ) -> FxHashMap<String, ChcExpr> {
        let mut subst: FxHashMap<String, ChcExpr> = FxHashMap::default();

        // 1. Map head argument variables to level arguments.
        // #2660: Expression head args (e.g., x+1) are handled correctly — their constituent
        // vars are clause-local and get mapped by step 3 (level-specific vars). The head arg
        // equality at the usage site (level_arg = expr[subst]) captures the relationship.
        if let ClauseHead::Predicate(_, head_args) = &clause.head {
            for (k, arg) in head_args.iter().enumerate() {
                if let ChcExpr::Var(v) = arg {
                    if !subst.contains_key(&v.name) {
                        subst.insert(v.name.clone(), self.level_arg(head_pred, k, level));
                    }
                }
            }
        }

        // 2. Map body predicate argument variables to (level-1) arguments.
        // #2660: Same as above — expression body args' constituent vars handled by step 3.
        if level > 0 {
            for (body_pred, body_args) in &clause.body.predicates {
                for (k, arg) in body_args.iter().enumerate() {
                    if let ChcExpr::Var(v) = arg {
                        if !subst.contains_key(&v.name) {
                            subst.insert(v.name.clone(), self.level_arg(*body_pred, k, level - 1));
                        }
                    }
                }
            }
        }

        // 3. Map remaining variables to level-specific variables
        let mut var_idx = 0;
        let body_vars = clause.body.vars();
        for v in body_vars {
            if !subst.contains_key(&v.name) {
                subst.insert(
                    v.name.clone(),
                    self.level_var(head_pred, rule_idx, var_idx, level, v.sort.clone()),
                );
                var_idx += 1;
            }
        }

        subst
    }

    /// Compile level constraints for a single level
    ///
    /// Following Z3's compile() method:
    /// - For each predicate P, assert: P#level => ∨ rule:P#level_i
    /// - For each rule i, assert: rule:P#level_i => body ∧ head_equalities ∧ body_preds#(level-1)
    fn compile_level(&self, level: usize, conjuncts: &mut Vec<ChcExpr>) {
        for pred in self.problem.predicates() {
            let rules: Vec<_> = self.problem.clauses_defining_with_index(pred.id).collect();
            if rules.is_empty() {
                continue;
            }

            // Collect rule indicators for this predicate at this level
            let mut rule_indicators = Vec::new();

            for (rule_idx, clause) in &rules {
                let rule_ind = self.rule_indicator(pred.id, *rule_idx, level);
                rule_indicators.push(rule_ind.clone());

                // At level 0, rules with body predicates are disabled
                if level == 0 && !clause.body.predicates.is_empty() {
                    // Assert ¬rule_ind (disable this rule at level 0)
                    conjuncts.push(ChcExpr::not(rule_ind));
                    continue;
                }

                // Build rule body constraint
                let mut rule_conjuncts = Vec::new();

                // 1. Build variable substitution
                let subst = self.mk_rule_vars(clause, pred.id, *rule_idx, level);

                // 2. Head argument equalities: P#level_k = head_arg_k[subst]
                if let ClauseHead::Predicate(_, head_args) = &clause.head {
                    for (arg_idx, head_arg) in head_args.iter().enumerate() {
                        let level_arg = self.level_arg(pred.id, arg_idx, level);
                        let substituted_arg = head_arg.substitute_name_map(&subst);
                        rule_conjuncts.push(ChcExpr::eq(level_arg, substituted_arg));
                    }
                }

                // 3. Body predicate constraints: body_pred#(level-1) and arg equalities
                for (body_pred, body_args) in &clause.body.predicates {
                    debug_assert!(level > 0, "Body predicate at level 0 should be disabled");

                    // Assert body predicate is reachable at level-1
                    rule_conjuncts.push(self.level_predicate(*body_pred, level - 1));

                    // Body arg equalities: body_pred#(level-1)_k = body_arg_k[subst]
                    for (arg_idx, body_arg) in body_args.iter().enumerate() {
                        let level_arg = self.level_arg(*body_pred, arg_idx, level - 1);
                        let substituted_arg = body_arg.substitute_name_map(&subst);
                        rule_conjuncts.push(ChcExpr::eq(level_arg, substituted_arg));
                    }
                }

                // 4. Body constraint: φ[subst]
                if let Some(constraint) = &clause.body.constraint {
                    let substituted = constraint.substitute_name_map(&subst);
                    rule_conjuncts.push(substituted);
                }

                // Assert: rule_ind => (body conjuncts)
                if !rule_conjuncts.is_empty() {
                    let body = ChcExpr::and_all(rule_conjuncts.iter().cloned());
                    conjuncts.push(ChcExpr::implies(rule_ind, body));
                }
            }

            // Assert: P#level => ∨ rule_indicators
            if !rule_indicators.is_empty() {
                let level_pred = self.level_predicate(pred.id, level);
                let or_rules = ChcExpr::or_all(rule_indicators);
                conjuncts.push(ChcExpr::implies(level_pred, or_rules));
            }
        }
    }

    /// Compile a query clause at a specific level
    ///
    /// For query `P(x) ∧ φ(x) => false`:
    /// - Assert P#level (query predicate is reachable)
    /// - Assert φ(P#level_args) (constraint is satisfied)
    fn compile_query(&self, query: &HornClause, level: usize, conjuncts: &mut Vec<ChcExpr>) {
        // Build a substitution from query variables to level arguments
        let mut subst: FxHashMap<String, ChcExpr> = FxHashMap::default();

        // Two-pass argument mapping: first collect all variable->level_arg mappings,
        // then apply substitution to non-variable arguments so all variables resolve.
        // Deferred non-variable equalities (level_var, raw_expr) wait for full subst.
        let mut deferred_equalities: Vec<(ChcExpr, ChcExpr)> = Vec::new();

        // Pass 1: map variables to level arguments, defer non-variable args
        for (body_pred, body_args) in &query.body.predicates {
            conjuncts.push(self.level_predicate(*body_pred, level));

            for (arg_idx, body_arg) in body_args.iter().enumerate() {
                let level_var = self.level_arg(*body_pred, arg_idx, level);
                if let ChcExpr::Var(v) = body_arg {
                    if !subst.contains_key(&v.name) {
                        subst.insert(v.name.clone(), level_var);
                    } else {
                        // Variable already mapped — add equality constraint
                        conjuncts.push(ChcExpr::eq(level_var, subst[&v.name].clone()));
                    }
                } else {
                    // Defer non-variable args until all variable mappings are built
                    deferred_equalities.push((level_var, body_arg.clone()));
                }
            }
        }

        // Pass 2: apply complete substitution to deferred non-variable arguments
        for (level_var, raw_expr) in deferred_equalities {
            let substituted_arg = raw_expr.substitute_name_map(&subst);
            conjuncts.push(ChcExpr::eq(level_var, substituted_arg));
        }

        // Apply substitution to constraint and assert it
        if let Some(constraint) = &query.body.constraint {
            let substituted = constraint.substitute_name_map(&subst);
            conjuncts.push(substituted);
        }
    }

    /// Extract execution trace from incremental SMT model (same format as non-incremental).
    fn extract_trace_from_incremental(
        &self,
        model: &FxHashMap<String, SmtValue>,
        k: usize,
    ) -> Vec<FxHashMap<String, SmtValue>> {
        self.extract_trace(model, k)
    }

    /// Extract execution trace from SMT model
    fn extract_trace(
        &self,
        model: &FxHashMap<String, SmtValue>,
        k: usize,
    ) -> Vec<FxHashMap<String, SmtValue>> {
        let mut trace = Vec::new();

        for step in 0..=k {
            let mut state = FxHashMap::default();
            for (var_name, value) in model {
                // Check if this variable belongs to this step (format: P#step_arg)
                // Parse level-based variable names
                if let Some(level_part) = var_name.find('#') {
                    let after_hash = &var_name[level_part + 1..];
                    if let Some(underscore) = after_hash.find('_') {
                        if let Ok(level) = after_hash[..underscore].parse::<usize>() {
                            if level == step {
                                state.insert(var_name.clone(), value.clone());
                            }
                        }
                    }
                }
            }
            trace.push(state);
        }

        trace
    }

    // ============ Direct Flat Encoding (#7983) ============

    /// Compile level constraints using a direct flat encoding (no rule indicators).
    ///
    /// Instead of:  P#k => rule:P#k_0 | rule:P#k_1, rule:P#k_i => body_i
    /// Produces:    P#k => (or (and body_0_conjuncts) (and body_1_conjuncts))
    fn compile_level_flat(&self, level: usize, conjuncts: &mut Vec<ChcExpr>) {
        for pred in self.problem.predicates() {
            let rules: Vec<_> = self.problem.clauses_defining_with_index(pred.id).collect();
            if rules.is_empty() {
                continue;
            }

            let mut rule_disjuncts = Vec::new();

            for (rule_idx, clause) in &rules {
                if level == 0 && !clause.body.predicates.is_empty() {
                    continue;
                }

                let mut rule_conjuncts = Vec::new();
                let subst = self.mk_rule_vars(clause, pred.id, *rule_idx, level);

                if let ClauseHead::Predicate(_, head_args) = &clause.head {
                    for (arg_idx, head_arg) in head_args.iter().enumerate() {
                        let level_arg = self.level_arg(pred.id, arg_idx, level);
                        let substituted_arg = head_arg.substitute_name_map(&subst);
                        rule_conjuncts.push(ChcExpr::eq(level_arg, substituted_arg));
                    }
                }

                for (body_pred, body_args) in &clause.body.predicates {
                    debug_assert!(level > 0);
                    rule_conjuncts.push(self.level_predicate(*body_pred, level - 1));
                    for (arg_idx, body_arg) in body_args.iter().enumerate() {
                        let level_arg = self.level_arg(*body_pred, arg_idx, level - 1);
                        let substituted_arg = body_arg.substitute_name_map(&subst);
                        rule_conjuncts.push(ChcExpr::eq(level_arg, substituted_arg));
                    }
                }

                if let Some(constraint) = &clause.body.constraint {
                    rule_conjuncts.push(constraint.substitute_name_map(&subst));
                }

                if !rule_conjuncts.is_empty() {
                    rule_disjuncts.push(ChcExpr::and_all(rule_conjuncts.iter().cloned()));
                }
            }

            let level_pred = self.level_predicate(pred.id, level);
            if !rule_disjuncts.is_empty() {
                let body = if rule_disjuncts.len() == 1 {
                    rule_disjuncts.remove(0)
                } else {
                    ChcExpr::or_all(rule_disjuncts)
                };
                conjuncts.push(ChcExpr::implies(level_pred, body));
            } else {
                // No applicable rules at this level (e.g., all rules have body
                // predicates and we're at level 0). The predicate cannot be true
                // here — assert NOT(P#level) to prevent spurious counterexamples.
                conjuncts.push(ChcExpr::not(level_pred));
            }
        }
    }

}

#[cfg(test)]
mod tests;
