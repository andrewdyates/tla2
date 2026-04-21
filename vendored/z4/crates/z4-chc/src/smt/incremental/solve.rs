// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! DPLL(T) solving loop for incremental SAT contexts.
//!
//! Contains the main `check_sat_incremental` method that runs the DPLL(T) loop
//! over the persistent SAT solver, plus helpers for theory conflict clauses and
//! branch-and-bound split registration.

use super::{IncrementalCheckResult, IncrementalPlan, IncrementalSatContext};
use crate::smt::context::SmtContext;
use crate::smt::model_verify::is_theory_atom;
use crate::{ChcExpr, ChcSort, ChcVar};
use num_bigint::BigInt;
use rustc_hash::FxHashMap;
use z4_core::term::{Symbol, TermData};
use z4_core::{Sort, TermId, TermStore};

impl IncrementalSatContext {
    /// Check satisfiability of the current background plus query assumptions.
    ///
    /// The `assumptions` are encoded as Tseitin roots and provided to SAT as
    /// per-call assumptions (temporary for this solve only).
    ///
    /// Theory lemmas discovered during DPLL(T) are added to SAT as learned constraints.
    pub(crate) fn check_sat_incremental(
        &mut self,
        assumptions: &[ChcExpr],
        smt: &mut SmtContext,
        timeout: Option<std::time::Duration>,
    ) -> IncrementalCheckResult {
        use z4_core::{TheoryResult, TheorySolver};
        use z4_lia::LiaSolver;

        // #6692: FreshOnly plan → always use fresh solving from background_exprs.
        if matches!(self.plan, IncrementalPlan::FreshOnly(_)) {
            return self.check_sat_fresh_query(assumptions, timeout);
        }

        // Reset per-check conversion budget (#2771).
        smt.reset_conversion_budget();

        if self.background_conversion_budget_exceeded {
            return IncrementalCheckResult::Unknown;
        }

        let start = std::time::Instant::now();

        // Collect propagated equalities with transitive var=var closure (#2445).
        let mut propagated_equalities: FxHashMap<String, i64> = FxHashMap::default();
        // #5877: Collect BV var=const equalities for BV-native PDR mode.
        let mut propagated_bv_equalities: FxHashMap<String, (u128, u32)> = FxHashMap::default();
        let assumption_refs: Vec<&ChcExpr> = assumptions.iter().collect();
        let contradiction = SmtContext::collect_int_equalities_with_closure(
            &assumption_refs,
            &mut propagated_equalities,
        );
        if contradiction {
            return IncrementalCheckResult::Unsat;
        }

        // Build substitution from equalities.
        // SOUNDNESS: Only apply substitution when there is NO background (#2739).
        // When a background is present (self.finalized), substituting equalities
        // from assumptions can drop constraints that conflict with the background
        // (e.g., background has x=0, assumption x=1 → substituted to true → dropped).
        // Without background, all constraints are in assumptions, so substitution
        // only simplifies without losing information.
        let subst: Vec<(ChcVar, ChcExpr)> = if self.finalized {
            Vec::new() // Skip substitution when background is present
        } else {
            propagated_equalities
                .iter()
                .map(|(name, val)| (ChcVar::new(name, ChcSort::Int), ChcExpr::int(*val)))
                .collect()
        };

        // Phase 1: Preprocess and convert all assumptions to TermIds (requires &mut smt)
        let mut assumption_terms: Vec<TermId> = Vec::with_capacity(assumptions.len());
        let mut saw_false = false;
        for (idx, a) in assumptions.iter().enumerate() {
            let namespace = format!("q{idx}");
            let substituted = if subst.is_empty() {
                a.clone()
            } else {
                a.substitute(&subst)
            };
            // Always use preprocess_incremental_assumption (#2913): per-expression
            // propagate_constants() can eliminate var=var equalities (e.g., E=C → true)
            // that other assumption expressions still reference, causing the theory
            // solver to treat the eliminated variable as unconstrained.
            let normalized =
                SmtContext::preprocess_incremental_assumption(&substituted, &namespace);
            SmtContext::collect_int_var_const_equalities(&normalized, &mut propagated_equalities);
            SmtContext::collect_bv_var_const_equalities(&normalized, &mut propagated_bv_equalities);

            match normalized {
                ChcExpr::Bool(true) => continue,
                ChcExpr::Bool(false) => {
                    saw_false = true;
                    break;
                }
                _ => {
                    assumption_terms.push(smt.convert_expr(&normalized));
                }
            }
        }

        if saw_false {
            return IncrementalCheckResult::Unsat;
        }

        // Bail out if conversion budget was exceeded (#2771).
        if smt.conversion_budget_exceeded() {
            return IncrementalCheckResult::Unknown;
        }

        // #6047/#7016: When any background or assumption expression contains
        // array operations or datatype sorts, dispatch to z4-dpll's Executor
        // which has proper array and DT theory support.
        let has_array_ops = self
            .background_exprs
            .iter()
            .chain(assumptions.iter())
            .any(ChcExpr::contains_array_ops);
        let has_dt = self
            .background_exprs
            .iter()
            .chain(assumptions.iter())
            .any(ChcExpr::contains_dt_ops);
        if has_array_ops || has_dt {
            let remaining_timeout = timeout
                .map(|t| {
                    t.checked_sub(start.elapsed())
                        .unwrap_or(std::time::Duration::from_millis(100))
                })
                .unwrap_or(std::time::Duration::from_secs(10));
            let all_exprs: Vec<ChcExpr> = self
                .background_exprs
                .iter()
                .chain(assumptions.iter())
                .cloned()
                .collect();
            let executor_result = crate::smt::executor_adapter::check_sat_conjunction_via_executor(
                &all_exprs,
                &propagated_equalities,
                remaining_timeout,
            );
            if !matches!(executor_result, IncrementalCheckResult::Unknown) {
                return executor_result;
            }
            // Fall through to internal DPLL(T) if executor also returns Unknown.
        }

        // #5877: Check timeout before expensive encoding phase. BV bitblasting
        // produces O(k * W * branches) clauses where k=depth, W=bitwidth,
        // branches=transition disjuncts. If the timeout has already expired,
        // skip encoding entirely.
        if let Some(t) = timeout {
            if start.elapsed() >= t {
                return IncrementalCheckResult::Unknown;
            }
        }

        // Phase 2: Encode all TermIds via Tseitin (borrows &smt.terms immutably)
        let state = self
            .tseitin_state
            .take()
            .expect("must finalize_background before check");
        let mut tseitin = z4_core::Tseitin::from_state(&smt.terms, state);

        let mut sat_assumptions: Vec<z4_sat::Literal> = Vec::with_capacity(assumption_terms.len());
        for &term in &assumption_terms {
            let encoded = tseitin.encode_assertion(term);

            // Grow SAT solver for any new variables
            self.sat.ensure_num_vars(tseitin.num_vars() as usize);

            // Definitional clauses go global (they are tautologies)
            for clause in &encoded.def_clauses {
                let lits: Vec<z4_sat::Literal> = clause
                    .0
                    .iter()
                    .map(|&lit| z4_sat::Literal::from_dimacs(lit))
                    .collect();
                self.sat.add_clause_global(lits);
            }

            // Assert query roots as SAT assumptions (temporary for this solve call).
            // This avoids scoped-unit-clause leakage across push/pop (#2739).
            sat_assumptions.push(z4_sat::Literal::from_dimacs(encoded.root_lit));
        }

        // Update mappings for model extraction
        self.term_to_var = tseitin
            .term_to_var()
            .iter()
            .map(|(&k, &v)| (k, v))
            .collect();
        self.var_to_term = tseitin
            .var_to_term()
            .iter()
            .map(|(&k, &v)| (k, v))
            .collect();
        self.num_vars = tseitin.num_vars();

        // Save Tseitin state for future queries
        self.tseitin_state = Some(tseitin.into_state());

        // #5877: Check timeout before BV bitblasting (can be expensive for
        // deep BMC unrollings with BV32 operations).
        if let Some(t) = timeout {
            if start.elapsed() >= t {
                return IncrementalCheckResult::Unknown;
            }
        }

        // Bit-blast any new BV predicates in query assumptions (#5122).
        self.bitblast_new_bv_predicates(&smt.terms, false);

        // Update shared var_map with any new variables introduced by preprocessing
        self.var_map = smt.var_map().clone();
        self.var_original_names = smt.var_original_names.clone();

        // DPLL(T) loop
        let mut split_count: usize = 0;
        const MAX_SPLITS: usize = 1_000_000; // #2472: match non-incremental cap

        loop {
            if let Some(t) = timeout {
                if start.elapsed() >= t {
                    return IncrementalCheckResult::Unknown;
                }
            }
            if TermStore::global_memory_exceeded() {
                return IncrementalCheckResult::Unknown;
            }

            let should_stop = || timeout.is_some_and(|t| start.elapsed() >= t);
            let sat_result = self
                .sat
                .solve_with_assumptions_interruptible(&sat_assumptions, should_stop);

            match sat_result.result() {
                z4_sat::AssumeResult::Sat(model) => {
                    let mut lia = LiaSolver::new(&smt.terms);
                    if let Some(t) = timeout {
                        lia.set_timeout_callback(move || start.elapsed() >= t);
                    }

                    // Sync theory solver with atomic constraints
                    for (&var_idx, &term_id) in &self.var_to_term {
                        if !is_theory_atom(&smt.terms, term_id) {
                            continue;
                        }
                        // Skip BV atoms — they are already encoded in SAT via
                        // bit-blasting and must not be sent to the LIA solver (#5122).
                        if SmtContext::is_bv_theory_atom(&smt.terms, term_id) {
                            continue;
                        }
                        // Skip array atoms — no array theory in CHC DPLL(T) (#6047).
                        if SmtContext::is_array_theory_atom(&smt.terms, term_id) {
                            continue;
                        }
                        let sat_var = z4_sat::Variable::new(var_idx - 1);
                        if let Some(value) = model.get(sat_var.index()) {
                            lia.assert_literal(term_id, *value);
                        }
                    }

                    // #6810: LRA emits NeedModelEquality / NeedModelEqualities
                    // when multiple variables are pinned to the same value. These
                    // are Nelson-Oppen suggestions for multi-theory combination.
                    // The incremental solver uses LIA alone — the model is already
                    // valid. Remap to Sat so the existing model extraction handles it.
                    let lia_result = match lia.check() {
                        TheoryResult::NeedModelEquality(_)
                        | TheoryResult::NeedModelEqualities(_) => TheoryResult::Sat,
                        other => other,
                    };
                    match lia_result {
                        TheoryResult::Sat => {
                            let lia_model = lia.extract_model();
                            return self.build_incremental_model(
                                model,
                                &lia_model,
                                &lia,
                                smt,
                                &propagated_equalities,
                                &propagated_bv_equalities,
                                assumptions,
                            );
                        }
                        TheoryResult::Unsat(conflict) => {
                            if let Some(result) = self.add_theory_conflict_clause(
                                &conflict,
                                model,
                                "incremental unsat",
                            ) {
                                return result;
                            }
                        }
                        TheoryResult::NeedStringLemma(_) => {
                            // String theory not supported in CHC; return Unknown to avoid
                            // spinning the DPLL(T) loop requesting the same lemma (#6091).
                            return IncrementalCheckResult::Unknown;
                        }
                        TheoryResult::UnsatWithFarkas(conflict) => {
                            if let Some(result) = self.add_theory_conflict_clause(
                                &conflict.literals,
                                model,
                                "incremental farkas",
                            ) {
                                return result;
                            }
                        }
                        TheoryResult::Unknown => {
                            return IncrementalCheckResult::Unknown;
                        }
                        TheoryResult::NeedSplit(split) => {
                            // Split value must be non-integral (branch-and-bound invariant)
                            debug_assert!(
                                !split.value.is_integer(),
                                "BUG: CHC-INC NeedSplit value {} is integral (floor={}, ceil={})",
                                split.value,
                                split.floor,
                                split.ceil
                            );
                            debug_assert!(
                                split.floor < split.ceil,
                                "BUG: CHC-INC NeedSplit floor {} >= ceil {}",
                                split.floor,
                                split.ceil
                            );

                            // Guard: mk_le/mk_ge require Int or Real sort (#2941)
                            let var_sort = smt.terms.sort(split.variable);
                            if !matches!(var_sort, Sort::Int | Sort::Real) {
                                return IncrementalCheckResult::Unknown;
                            }

                            let floor_term = smt.terms.mk_int(split.floor.clone());
                            let ceil_term = smt.terms.mk_int(split.ceil.clone());
                            let le_atom = smt.terms.mk_le(split.variable, floor_term);
                            let ge_atom = smt.terms.mk_ge(split.variable, ceil_term);

                            if let Some(result) = self.register_split_atoms(
                                le_atom,
                                ge_atom,
                                &mut split_count,
                                MAX_SPLITS,
                            ) {
                                return result;
                            }
                        }
                        TheoryResult::NeedDisequalitySplit(split) => {
                            let var_sort = smt.terms.sort(split.variable).clone();
                            let (left_atom, right_atom) =
                                if var_sort == Sort::Int && split.excluded_value.is_integer() {
                                    let excluded = split.excluded_value.numer().clone();
                                    let le_bound = smt.terms.mk_int(&excluded - BigInt::from(1));
                                    let ge_bound = smt.terms.mk_int(&excluded + BigInt::from(1));
                                    (
                                        smt.terms.mk_le(split.variable, le_bound),
                                        smt.terms.mk_ge(split.variable, ge_bound),
                                    )
                                } else if var_sort == Sort::Int {
                                    let floor_val = split.excluded_value.floor().to_integer();
                                    let ceil_val = split.excluded_value.ceil().to_integer();
                                    let le_bound = smt.terms.mk_int(floor_val);
                                    let ge_bound = smt.terms.mk_int(ceil_val);
                                    (
                                        smt.terms.mk_le(split.variable, le_bound),
                                        smt.terms.mk_ge(split.variable, ge_bound),
                                    )
                                } else {
                                    let excluded_term =
                                        smt.terms.mk_rational(split.excluded_value.clone());
                                    (
                                        smt.terms.mk_lt(split.variable, excluded_term),
                                        smt.terms.mk_gt(split.variable, excluded_term),
                                    )
                                };

                            if let Some(result) = self.register_split_atoms(
                                left_atom,
                                right_atom,
                                &mut split_count,
                                MAX_SPLITS,
                            ) {
                                return result;
                            }
                        }
                        TheoryResult::NeedExpressionSplit(split) => {
                            // Multi-variable disequality split: E != F
                            // Create atoms (E < F) OR (E > F) — same as non-incremental solver

                            // Extract LHS and RHS from the disequality term.
                            let (lhs, rhs) = match smt.terms.get(split.disequality_term) {
                                TermData::App(Symbol::Named(name), args)
                                    if args.len() == 2 && (name == "=" || name == "distinct") =>
                                {
                                    (args[0], args[1])
                                }
                                TermData::Not(inner) => match smt.terms.get(*inner) {
                                    TermData::App(Symbol::Named(name), args)
                                        if args.len() == 2
                                            && (name == "=" || name == "distinct") =>
                                    {
                                        (args[0], args[1])
                                    }
                                    _ => return IncrementalCheckResult::Unknown,
                                },
                                _ => return IncrementalCheckResult::Unknown,
                            };

                            if !matches!(smt.terms.sort(lhs), Sort::Int | Sort::Real)
                                || smt.terms.sort(lhs) != smt.terms.sort(rhs)
                            {
                                return IncrementalCheckResult::Unknown;
                            }

                            let lt_atom = smt.terms.mk_lt(lhs, rhs);
                            let gt_atom = smt.terms.mk_gt(lhs, rhs);

                            if let Some(result) = self.register_split_atoms(
                                lt_atom,
                                gt_atom,
                                &mut split_count,
                                MAX_SPLITS,
                            ) {
                                return result;
                            }
                        }
                        _ => {
                            // Unknown TheoryResult variant; return Unknown (#6091).
                            return IncrementalCheckResult::Unknown;
                        }
                    }
                }
                z4_sat::AssumeResult::Unsat(_) => {
                    return IncrementalCheckResult::Unsat;
                }
                z4_sat::AssumeResult::Unknown => {
                    return IncrementalCheckResult::Unknown;
                }
                // Future AssumeResult variants: treat as Unknown (sound) (#6091).
                #[allow(unreachable_patterns)]
                _ => {
                    return IncrementalCheckResult::Unknown;
                }
            }
        }
    }

    /// Convert a theory conflict (slice of `TheoryLit`) into a SAT blocking clause
    /// and add it globally to the SAT solver. Returns `Some(IncrementalCheckResult::Unsat)`
    /// if the conflict is empty or produces an empty clause (degenerate UNSAT),
    /// otherwise `None` (clause was added, continue DPLL(T) loop).
    ///
    /// Used by both `TheoryResult::Unsat` and `TheoryResult::UnsatWithFarkas` handlers
    /// in `check_sat_incremental`.
    fn add_theory_conflict_clause(
        &mut self,
        conflict: &[z4_core::TheoryLit],
        model: &[bool],
        debug_label: &str,
    ) -> Option<IncrementalCheckResult> {
        if conflict.is_empty() {
            return Some(IncrementalCheckResult::Unsat);
        }
        debug_assert!(
            conflict.iter().all(|lit| {
                self.term_to_var.get(&lit.term).is_none_or(|&cnf_var| {
                    let sat_var = z4_sat::Variable::new(cnf_var - 1);
                    model.get(sat_var.index()).is_none_or(|&v| v == lit.value)
                })
            }),
            "BUG: theory conflict literal contradicts SAT assignment ({debug_label})"
        );
        let clause: Vec<z4_sat::Literal> = conflict
            .iter()
            .filter_map(|lit| {
                self.term_to_var.get(&lit.term).map(|&cnf_var| {
                    let sat_var = z4_sat::Variable::new(cnf_var - 1);
                    if lit.value {
                        z4_sat::Literal::negative(sat_var)
                    } else {
                        z4_sat::Literal::positive(sat_var)
                    }
                })
            })
            .collect();
        if clause.is_empty() {
            return Some(IncrementalCheckResult::Unsat);
        }
        self.sat.add_clause_global(clause);
        None
    }

    /// Register a pair of split atoms as a global disjunction in the SAT solver.
    ///
    /// Returns `Some(IncrementalCheckResult::Unknown)` if `split_count` exceeds
    /// `MAX_SPLITS`, otherwise `None` (clause was added, continue DPLL(T) loop).
    ///
    /// Used by `NeedSplit`, `NeedDisequalitySplit`, and `NeedExpressionSplit` handlers.
    fn register_split_atoms(
        &mut self,
        left_atom: TermId,
        right_atom: TermId,
        split_count: &mut usize,
        max_splits: usize,
    ) -> Option<IncrementalCheckResult> {
        *split_count += 1;
        if *split_count > max_splits {
            return Some(IncrementalCheckResult::Unknown);
        }

        let left_var = *self.term_to_var.entry(left_atom).or_insert_with(|| {
            self.num_vars += 1;
            self.var_to_term.insert(self.num_vars, left_atom);
            self.num_vars
        });
        let right_var = *self.term_to_var.entry(right_atom).or_insert_with(|| {
            self.num_vars += 1;
            self.var_to_term.insert(self.num_vars, right_atom);
            self.num_vars
        });

        self.sat.ensure_num_vars(self.num_vars as usize);

        let left_sat_var = z4_sat::Variable::new(left_var - 1);
        let right_sat_var = z4_sat::Variable::new(right_var - 1);
        self.sat.add_clause_global(vec![
            z4_sat::Literal::positive(left_sat_var),
            z4_sat::Literal::positive(right_sat_var),
        ]);
        None
    }
}
