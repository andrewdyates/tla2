// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! DPLL(T) theory loop for check_sat queries.
//!
//! Runs the SAT solver in a loop, synchronizing Boolean models with
//! theory solvers (LIA, EUF, arrays) and handling theory conflicts,
//! model assembly, and term-growth splits.

use z4_core::{Sort, TermStore};

use super::super::context::SmtContext;
use super::super::model_verify::is_theory_atom;
use super::super::types::{FarkasConflict, SmtResult, UnsatCore};
use super::support::{build_theory_solvers, LiaReusableState};
use super::term_growth;
use super::{CnfState, PreparedQuery, TermGrowthAction};
use crate::ChcExpr;

#[cfg(test)]
use super::record_sat_model_iteration_for_tests;

impl SmtContext {
    /// Run the DPLL(T) theory loop for a check_sat query.
    ///
    /// Takes ownership of the prepared query and CNF state, running
    /// the SAT solver in a loop with theory synchronization until a
    /// terminal result is reached.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn run_check_sat_theory_loop(
        &mut self,
        expr: &ChcExpr,
        prepared: PreparedQuery,
        cnf_state: CnfState,
        split_state: &mut term_growth::SplitState,
        start: std::time::Instant,
        timeout: Option<std::time::Duration>,
    ) -> SmtResult {
        use z4_core::term::TermData;
        use z4_core::{TheoryResult, TheorySolver};

        let PreparedQuery {
            features,
            propagated_model,
            needs_euf,
            _needs_executor: _,
            ..
        } = prepared;
        let has_array_ops = features.has_array_ops;

        // Destructure CnfState into locals for the theory loop.
        let CnfState {
            mut term_to_var,
            mut var_to_term,
            mut num_vars,
            mut sat,
            assumptions,
            assumption_map,
            bv_var_offset,
            bv_term_to_bits,
        } = cnf_state;

        let debug = crate::debug_chc_smt_enabled();

        // Detect Real-sorted theory atoms. DPLL(T) without theory propagation
        // is incomplete for LRA: it may return false-UNSAT when no Boolean
        // assignment is theory-consistent, even though a satisfying assignment
        // exists. Guard UNSAT results when Real variables are present. (#5925)
        let has_real_theory_atoms = var_to_term.values().any(|&term_id| {
            use z4_core::term::TermData;
            if !is_theory_atom(&self.terms, term_id) {
                return false;
            }
            match self.terms.get(term_id) {
                TermData::App(_, args) => args
                    .iter()
                    .any(|&a| matches!(self.terms.sort(a), Sort::Real)),
                _ => false,
            }
        });

        // Solve (DPLL(T) loop). QF_LIA is decidable, so avoid hard iteration
        // cutoffs that can return spurious Unknown on hard-but-finite queries.
        let mut dt_iterations: usize = 0;
        let mut lia_reusable_state = LiaReusableState::default();
        if debug {
            safe_eprintln!(
                "[CHC-SMT] === INITIAL var_to_term MAPPING ({} vars) ===",
                var_to_term.len()
            );
            let mut sorted_vars: Vec<_> = var_to_term.iter().collect();
            sorted_vars.sort_by_key(|(&k, _)| k);
            for (&var_idx, &term_id) in &sorted_vars {
                safe_eprintln!(
                    "[CHC-SMT]   v{} -> {:?} = {:?}",
                    var_idx,
                    term_id,
                    self.terms.get(term_id)
                );
            }
            if let Some(ref assumptions) = assumptions {
                safe_eprintln!("[CHC-SMT] === ASSUMPTIONS ({}) ===", assumptions.len());
                for a in assumptions {
                    safe_eprintln!("[CHC-SMT]   assumption DIMACS {}", a.to_dimacs());
                }
            }
        }
        loop {
            let (mut lia, mut array_solver, mut euf_solver, mut lia_needs_cut_replay) =
                build_theory_solvers(
                    &self.terms,
                    has_array_ops,
                    needs_euf,
                    start,
                    timeout,
                    &mut lia_reusable_state,
                );

            let term_growth_action = loop {
                if let Some(timeout) = timeout {
                    if start.elapsed() >= timeout {
                        if debug {
                            safe_eprintln!("[CHC-SMT] Timeout exceeded");
                        }
                        return SmtResult::Unknown;
                    }
                }
                if TermStore::global_memory_exceeded() {
                    if debug {
                        safe_eprintln!("[CHC-SMT] Global term memory budget exceeded");
                    }
                    return SmtResult::Unknown;
                }
                // #5925: DPLL(T) iteration cap for Real-sorted formulas.
                // Without theory propagation, DPLL(T) is incomplete for LRA —
                // it may spin indefinitely adding blocking clauses without finding
                // a theory-consistent model. Cap iterations to prevent PDR from
                // using false-UNSAT results that would appear if we ran longer.
                if has_real_theory_atoms && dt_iterations > 1000 {
                    if debug {
                        safe_eprintln!(
                        "[CHC-SMT] LRA iteration cap reached ({} iterations), returning Unknown",
                        dt_iterations
                    );
                    }
                    return SmtResult::Unknown;
                }
                dt_iterations += 1;
                if debug && dt_iterations.is_multiple_of(10_000) {
                    safe_eprintln!("[CHC-SMT] DPLL(T) iteration {}", dt_iterations);
                }
                // Create interruptible callback for timeout enforcement.
                // This is checked every ~100 conflicts inside the SAT solver.
                let should_stop = || timeout.is_some_and(|t| start.elapsed() >= t);
                let sat_result = if let Some(assumptions) = &assumptions {
                    sat.solve_with_assumptions_interruptible(assumptions, should_stop)
                        .into_inner()
                } else {
                    match sat.solve_interruptible(should_stop).into_inner() {
                        z4_sat::SatResult::Sat(model) => z4_sat::AssumeResult::Sat(model),
                        z4_sat::SatResult::Unsat => z4_sat::AssumeResult::Unsat(Vec::new()),
                        z4_sat::SatResult::Unknown => z4_sat::AssumeResult::Unknown,
                        #[allow(unreachable_patterns)]
                        _ => z4_sat::AssumeResult::Unknown,
                    }
                };

                match sat_result {
                    z4_sat::AssumeResult::Sat(model) => {
                        #[cfg(test)]
                        record_sat_model_iteration_for_tests();

                        lia.soft_reset();
                        if let Some(arr) = array_solver.as_mut() {
                            arr.soft_reset();
                        }
                        if let Some(euf) = euf_solver.as_mut() {
                            euf.soft_reset();
                        }

                        // Sync theory solver with atomic constraints only (not Boolean combinations).
                        // Skip BV atoms — they are handled by eager bit-blasting (#5122).
                        for (&var_idx, &term_id) in &var_to_term {
                            // Skip Boolean combinations - theory solver only handles atomic predicates
                            if !is_theory_atom(&self.terms, term_id) {
                                if debug {
                                    safe_eprintln!(
                                        "[CHC-SMT]   SKIPPED non-theory-atom {:?} = {:?}",
                                        term_id,
                                        self.terms.get(term_id)
                                    );
                                }
                                continue;
                            }
                            // Skip BV theory atoms — already encoded in SAT via bit-blasting.
                            if features.has_bv && Self::is_bv_theory_atom(&self.terms, term_id) {
                                continue;
                            }
                            // CNF vars are 1-indexed, SAT model is 0-indexed
                            let sat_var = z4_sat::Variable::new(var_idx - 1);
                            if let Some(value) = model.get(sat_var.index()) {
                                let is_array_atom =
                                    Self::is_array_theory_atom(&self.terms, term_id);
                                // #6047: Assert array atoms to array + EUF solvers.
                                if is_array_atom {
                                    if let Some(ref mut arr) = array_solver {
                                        arr.assert_literal(term_id, *value);
                                    }
                                    if let Some(ref mut euf) = euf_solver {
                                        euf.assert_literal(term_id, *value);
                                    }
                                } else {
                                    // Arithmetic atoms go to LIA
                                    lia.assert_literal(term_id, *value);
                                }
                                // EUF gets all atoms for congruence closure
                                if !is_array_atom {
                                    if let Some(ref mut euf) = euf_solver {
                                        euf.assert_literal(term_id, *value);
                                    }
                                }
                            }
                        }

                        let lia_result = {
                            if lia_needs_cut_replay {
                                lia.replay_learned_cuts();
                                lia_needs_cut_replay = false;
                            }

                            if debug {
                                safe_eprintln!(
                                    "[CHC-SMT] iter {}: SAT model, asserting {} terms to LIA{}",
                                    dt_iterations,
                                    var_to_term.len(),
                                    if needs_euf { " + EUF" } else { "" }
                                );
                                for (&var_idx, &term_id) in &var_to_term {
                                    let sat_var = z4_sat::Variable::new(var_idx - 1);
                                    if let Some(value) = model.get(sat_var.index()) {
                                        safe_eprintln!(
                                            "[CHC-SMT]   term {:?} = {}",
                                            term_id,
                                            value
                                        );
                                    }
                                }
                            }
                            let lia_result = lia.check();

                            // #6047: If LIA is Sat and we have EUF/array solvers, run
                            // simplified Nelson-Oppen: propagate LIA equalities to EUF,
                            // check EUF congruence, then (if arrays present) check array
                            // axioms. This handles both array axiom checking and UF
                            // congruence from BvToInt abstraction.
                            if matches!(lia_result, TheoryResult::Sat) && needs_euf {
                                if let Some(ref mut euf) = euf_solver {
                                    // Propagate equalities from LIA to EUF
                                    let lia_eqs = lia.propagate_equalities();
                                    for eq in &lia_eqs.equalities {
                                        euf.assert_shared_equality(eq.lhs, eq.rhs, &eq.reason);
                                    }

                                    // Check EUF for congruence conflicts
                                    let euf_result = euf.check();
                                    if let TheoryResult::Unsat(conflict) = euf_result {
                                        TheoryResult::Unsat(conflict)
                                    } else if let Some(ref mut arr) = array_solver {
                                        // Propagate EUF equalities to arrays
                                        let euf_eqs = euf.propagate_equalities();
                                        for eq in &euf_eqs.equalities {
                                            arr.assert_shared_equality(eq.lhs, eq.rhs, &eq.reason);
                                        }

                                        // Check array axioms (ROW1, ROW2, extensionality)
                                        let arr_result = arr.check();
                                        match arr_result {
                                            TheoryResult::Unsat(conflict) => {
                                                TheoryResult::Unsat(conflict)
                                            }
                                            TheoryResult::Sat => TheoryResult::Sat,
                                            // Array solver may return Unknown for complex cases
                                            _ => TheoryResult::Sat,
                                        }
                                    } else {
                                        TheoryResult::Sat
                                    }
                                } else {
                                    TheoryResult::Sat
                                }
                            } else {
                                lia_result
                            }
                        };
                        // Check timeout after LIA solver call (can take a long time)
                        if let Some(timeout) = timeout {
                            if start.elapsed() >= timeout {
                                if debug {
                                    safe_eprintln!("[CHC-SMT] Timeout exceeded after LIA check");
                                }
                                return SmtResult::Unknown;
                            }
                        }
                        if debug {
                            safe_eprintln!(
                                "[CHC-SMT] iter {}: LIA result: {:?}",
                                dt_iterations,
                                lia_result
                            );
                        }
                        match lia_result {
                            TheoryResult::Sat => {
                                use super::theory_model::{
                                    extract_theory_sat_values, ExtractResult,
                                };
                                let extract = extract_theory_sat_values(
                                    &self.terms,
                                    &self.var_map,
                                    &self.var_original_names,
                                    &model,
                                    &term_to_var,
                                    &mut lia,
                                    &bv_term_to_bits,
                                    bv_var_offset,
                                    has_array_ops,
                                    &mut array_solver,
                                );
                                let mut values = match extract {
                                    ExtractResult::Values(v) => v,
                                    ExtractResult::Overflow => return SmtResult::Unknown,
                                };

                                // Check equality/disequality/comparison constraints
                                // that LIA might have missed.
                                let lia_model = lia.extract_model();
                                let mut violated_constraint = None;
                                for (&var_idx, &term_id) in &var_to_term {
                                    let sat_var = z4_sat::Variable::new(var_idx - 1);
                                    let Some(&sat_value) = model.get(sat_var.index()) else {
                                        continue;
                                    };

                                    if let TermData::App(sym, args) = self.terms.get(term_id) {
                                        let sym_name = sym.name();
                                        if args.len() == 2 {
                                            let lhs_val =
                                                self.get_term_value(args[0], &values, &lia_model);
                                            let rhs_val =
                                                self.get_term_value(args[1], &values, &lia_model);
                                            if let (Some(l), Some(r)) = (lhs_val, rhs_val) {
                                                let actual_value = match sym_name {
                                                    "=" => l == r,
                                                    "distinct" => l != r,
                                                    "<" => l < r,
                                                    "<=" => l <= r,
                                                    ">" => l > r,
                                                    ">=" => l >= r,
                                                    _ => continue,
                                                };
                                                if sat_value != actual_value {
                                                    violated_constraint =
                                                        Some((var_idx, sat_value));
                                                    break;
                                                }
                                            }
                                        }
                                    }
                                }

                                if let Some((violated_var, violated_val)) = violated_constraint {
                                    if debug {
                                        let term_id = var_to_term.get(&violated_var);
                                        safe_eprintln!(
                                        "[CHC-SMT] iter {}: violated_constraint v{}={}, term={:?} = {:?}",
                                        dt_iterations, violated_var, violated_val,
                                        term_id, term_id.map(|t| self.terms.get(*t))
                                    );
                                    }
                                    let sat_var = z4_sat::Variable::new(violated_var - 1);
                                    let blocking_lit = if violated_val {
                                        z4_sat::Literal::negative(sat_var)
                                    } else {
                                        z4_sat::Literal::positive(sat_var)
                                    };
                                    if debug {
                                        safe_eprintln!(
                                        "[CHC-SMT] iter {}: violated_constraint blocking (DIMACS): [{}]",
                                        dt_iterations, blocking_lit.to_dimacs()
                                    );
                                    }
                                    sat.add_clause(vec![blocking_lit]);
                                    continue;
                                }

                                for (name, value) in &propagated_model {
                                    values.entry(name.clone()).or_insert_with(|| value.clone());
                                }
                                return Self::sat_or_unknown(expr, values, "DPLL(T) loop");
                            }
                            TheoryResult::Unsat(conflict) => {
                                // Add blocking clause
                                if debug {
                                    safe_eprintln!(
                                        "[CHC-SMT] iter {}: TheoryResult::Unsat, {} conflict lits:",
                                        dt_iterations,
                                        conflict.len()
                                    );
                                    for lit in &conflict {
                                        let cnf_var = term_to_var.get(&lit.term).copied();
                                        safe_eprintln!(
                                            "[CHC-SMT]   {:?} (value={}) = {:?}, cnf_var={:?}",
                                            lit.term,
                                            lit.value,
                                            self.terms.get(lit.term),
                                            cnf_var
                                        );
                                    }
                                }
                                if conflict.is_empty() {
                                    // #5925: guard for LRA incompleteness
                                    return if has_real_theory_atoms {
                                        SmtResult::Unknown
                                    } else {
                                        SmtResult::Unsat
                                    };
                                }
                                // Verify conflict literals match current SAT assignment
                                assert!(
                                    conflict.iter().all(|lit| {
                                        term_to_var.get(&lit.term).is_none_or(|&cnf_var| {
                                            let sat_var = z4_sat::Variable::new(cnf_var - 1);
                                            model
                                                .get(sat_var.index())
                                                .is_none_or(|&v| v == lit.value)
                                        })
                                    }),
                                    "BUG: theory conflict literal contradicts SAT assignment"
                                );
                                // Build blocking clause. If any conflict literal
                                // has no CNF variable, the clause would be weaker
                                // than the real conflict — risking false UNSAT (#5384).
                                let mut clause: Vec<z4_sat::Literal> =
                                    Vec::with_capacity(conflict.len());
                                let mut dropped_count = 0usize;
                                for lit in &conflict {
                                    match term_to_var.get(&lit.term) {
                                        Some(&cnf_var) => {
                                            let sat_var = z4_sat::Variable::new(cnf_var - 1);
                                            clause.push(if lit.value {
                                                z4_sat::Literal::negative(sat_var)
                                            } else {
                                                z4_sat::Literal::positive(sat_var)
                                            });
                                        }
                                        None => {
                                            dropped_count += 1;
                                            if debug {
                                                safe_eprintln!(
                                                "[CHC-SMT]   DROPPED: {:?} (value={}) = {:?} - no CNF var",
                                                lit.term,
                                                lit.value,
                                                self.terms.get(lit.term)
                                            );
                                            }
                                        }
                                    }
                                }
                                if debug {
                                    safe_eprintln!(
                                        "[CHC-SMT] iter {}: blocking clause (DIMACS): {:?}",
                                        dt_iterations,
                                        clause.iter().map(|l| l.to_dimacs()).collect::<Vec<_>>()
                                    );
                                }
                                if dropped_count > 0 {
                                    // Unmapped conflict literals: blocking clause
                                    // would be incomplete → return Unknown (#5384).
                                    if debug {
                                        safe_eprintln!(
                                        "[CHC-SMT] iter {}: {} conflict lits dropped, returning Unknown",
                                        dt_iterations, dropped_count
                                    );
                                    }
                                    return SmtResult::Unknown;
                                }
                                if clause.is_empty() {
                                    // #5925: guard for LRA incompleteness
                                    return if has_real_theory_atoms {
                                        SmtResult::Unknown
                                    } else {
                                        SmtResult::Unsat
                                    };
                                }
                                sat.add_clause(clause);
                            }
                            TheoryResult::Unknown => {
                                return SmtResult::Unknown;
                            }
                            TheoryResult::NeedSplit(split) => {
                                // LIA needs branch-and-bound: the LRA relaxation found x = frac,
                                // so we must explore (x <= floor) OR (x >= ceil)

                                // Split value must be non-integral (branch-and-bound invariant)
                                debug_assert!(
                                !split.value.is_integer(),
                                "BUG: CHC-SMT NeedSplit value {} is integral (floor={}, ceil={})",
                                split.value,
                                split.floor,
                                split.ceil
                            );
                                debug_assert!(
                                    split.floor < split.ceil,
                                    "BUG: CHC-SMT NeedSplit floor {} >= ceil {}",
                                    split.floor,
                                    split.ceil
                                );

                                split_state.split_count += 1;
                                if split_state.split_count > split_state.max_splits {
                                    if debug {
                                        safe_eprintln!(
                                            "[CHC-SMT] Exceeded max splits ({})",
                                            split_state.max_splits
                                        );
                                    }
                                    return SmtResult::Unknown;
                                }

                                if debug {
                                    safe_eprintln!("[CHC-SMT] iter {}: NeedSplit on var {:?}, value={}, floor={}, ceil={}",
                                    dt_iterations, split.variable, split.value, split.floor, split.ceil);
                                }

                                // Guard: mk_le/mk_ge require Int or Real sort (#2941)
                                let var_sort = self.terms.sort(split.variable);
                                if !matches!(var_sort, Sort::Int | Sort::Real) {
                                    return SmtResult::Unknown;
                                }

                                lia_reusable_state.capture(&mut lia);
                                break TermGrowthAction::Split { split };
                            }
                            TheoryResult::NeedDisequalitySplit(split) => {
                                // Disequality split: var != excluded_value
                                // Create atoms (var < excluded_value) OR (var > excluded_value)

                                split_state.split_count += 1;
                                if split_state.split_count > split_state.max_splits {
                                    if debug {
                                        safe_eprintln!(
                                            "[CHC-SMT] Exceeded max splits ({})",
                                            split_state.max_splits
                                        );
                                    }
                                    return SmtResult::Unknown;
                                }

                                lia_reusable_state.capture(&mut lia);
                                break TermGrowthAction::DisequalitySplit { model, split };
                            }
                            TheoryResult::NeedExpressionSplit(split) => {
                                // Multi-variable disequality split: E != F
                                // Create atoms (E < F) OR (E > F) - avoids infinite value enumeration

                                split_state.split_count += 1;
                                if split_state.split_count > split_state.max_splits {
                                    if debug {
                                        safe_eprintln!(
                                            "[CHC-SMT] Exceeded max splits ({})",
                                            split_state.max_splits
                                        );
                                    }
                                    return SmtResult::Unknown;
                                }

                                lia_reusable_state.capture(&mut lia);
                                break TermGrowthAction::ExpressionSplit { split };
                            }
                            TheoryResult::NeedStringLemma(_) => {
                                // String theory not supported in CHC; return Unknown to avoid
                                // spinning the DPLL(T) loop requesting the same lemma (#6091).
                                return SmtResult::Unknown;
                            }
                            TheoryResult::UnsatWithFarkas(conflict) => {
                                // If we have Farkas coefficients, preserve them for interpolation
                                if let Some(ref farkas) = conflict.farkas {
                                    // Empty conflict = direct theory UNSAT
                                    if conflict.literals.is_empty() {
                                        return SmtResult::UnsatWithFarkas(FarkasConflict {
                                            conflict_terms: Vec::new(),
                                            polarities: Vec::new(),
                                            farkas: farkas.clone(),
                                            origins: Vec::new(),
                                        });
                                    }
                                    // Non-empty conflict: build blocking clause.
                                    // Dropped literals → return Unknown (#5384).
                                    let mut clause: Vec<z4_sat::Literal> =
                                        Vec::with_capacity(conflict.literals.len());
                                    let mut dropped_count = 0usize;
                                    for lit in &conflict.literals {
                                        match term_to_var.get(&lit.term) {
                                            Some(&cnf_var) => {
                                                let sat_var = z4_sat::Variable::new(cnf_var - 1);
                                                clause.push(if lit.value {
                                                    z4_sat::Literal::negative(sat_var)
                                                } else {
                                                    z4_sat::Literal::positive(sat_var)
                                                });
                                            }
                                            None => {
                                                dropped_count += 1;
                                                if debug {
                                                    safe_eprintln!(
                                                    "[CHC-SMT]   Farkas DROPPED: {:?} (value={}) = {:?} - no CNF var",
                                                    lit.term, lit.value, self.terms.get(lit.term)
                                                );
                                                }
                                            }
                                        }
                                    }
                                    if debug {
                                        safe_eprintln!(
                                        "[CHC-SMT] iter {}: Farkas blocking clause (DIMACS): {:?}",
                                        dt_iterations,
                                        clause.iter().map(|l| l.to_dimacs()).collect::<Vec<_>>()
                                    );
                                    }
                                    if dropped_count > 0 {
                                        if debug {
                                            safe_eprintln!(
                                            "[CHC-SMT] iter {}: {} Farkas lits dropped, returning Unknown",
                                            dt_iterations, dropped_count
                                        );
                                        }
                                        return SmtResult::Unknown;
                                    }
                                    if clause.is_empty() {
                                        // All conflict literals unmapped = direct theory UNSAT
                                        return SmtResult::UnsatWithFarkas(FarkasConflict {
                                            conflict_terms: conflict
                                                .literals
                                                .iter()
                                                .map(|l| l.term)
                                                .collect(),
                                            polarities: conflict
                                                .literals
                                                .iter()
                                                .map(|l| l.value)
                                                .collect(),
                                            farkas: farkas.clone(),
                                            origins: Vec::new(),
                                        });
                                    }
                                    sat.add_clause(clause);
                                } else {
                                    // No Farkas coefficients - treat as plain Unsat
                                    if conflict.literals.is_empty() {
                                        // #5925: guard for LRA incompleteness
                                        return if has_real_theory_atoms {
                                            SmtResult::Unknown
                                        } else {
                                            SmtResult::Unsat
                                        };
                                    }
                                    let mut clause: Vec<z4_sat::Literal> =
                                        Vec::with_capacity(conflict.literals.len());
                                    let mut dropped_count = 0usize;
                                    for lit in &conflict.literals {
                                        match term_to_var.get(&lit.term) {
                                            Some(&cnf_var) => {
                                                let sat_var = z4_sat::Variable::new(cnf_var - 1);
                                                clause.push(if lit.value {
                                                    z4_sat::Literal::negative(sat_var)
                                                } else {
                                                    z4_sat::Literal::positive(sat_var)
                                                });
                                            }
                                            None => {
                                                dropped_count += 1;
                                            }
                                        }
                                    }
                                    if dropped_count > 0 {
                                        return SmtResult::Unknown;
                                    }
                                    if clause.is_empty() {
                                        // #5925: guard for LRA incompleteness
                                        return if has_real_theory_atoms {
                                            SmtResult::Unknown
                                        } else {
                                            SmtResult::Unsat
                                        };
                                    }
                                    sat.add_clause(clause);
                                }
                            }
                            _ => {
                                // Unknown TheoryResult variant; return Unknown (#6091).
                                return SmtResult::Unknown;
                            }
                        }
                    }
                    z4_sat::AssumeResult::Unsat(core) => {
                        if debug {
                            safe_eprintln!(
                                "[CHC-SMT] SAT returned UNSAT after {} iterations, core len={}",
                                dt_iterations,
                                core.len()
                            );
                            safe_eprintln!(
                                "[CHC-SMT]   UNSAT core (DIMACS): {:?}",
                                core.iter().map(|l| l.to_dimacs()).collect::<Vec<_>>()
                            );
                        }

                        // #5384 defense: verify UNSAT by replaying original clauses in a
                        // fresh solver (no learned clauses). If the fresh solver returns
                        // SAT, the main solver's UNSAT was caused by an incorrect learned
                        // clause. We recover by replacing the main solver with the fresh
                        // one and re-running the SAT check on the next iteration.
                        if let Some(trace) = sat.clause_trace() {
                            if trace.learned_clauses().next().is_some() {
                                let orig_clauses: Vec<Vec<z4_sat::Literal>> =
                                    trace.original_clauses().map(|e| e.clause.clone()).collect();
                                let mut fresh = z4_sat::Solver::new(num_vars as usize);
                                fresh.enable_clause_trace();
                                // #7410: Vivify is pure overhead for one-shot CHC SAT queries.
                                fresh.set_vivify_enabled(false);
                                if features.has_bv {
                                    fresh.disable_all_inprocessing();
                                }
                                for cl in &orig_clauses {
                                    fresh.add_clause(cl.clone());
                                }
                                let fresh_is_sat = if let Some(ref assumptions) = assumptions {
                                    fresh.solve_with_assumptions(assumptions).is_sat()
                                } else {
                                    fresh.solve().is_sat()
                                };
                                if fresh_is_sat {
                                    if debug {
                                        safe_eprintln!(
                                        "[CHC-SMT] UNSAT recovery: fresh solver SAT on {} orig clauses, \
                                         discarding bad learned clauses",
                                        orig_clauses.len(),
                                    );
                                    }
                                    sat = fresh;
                                    continue;
                                }
                            }
                        }

                        // #5925 soundness guard: DPLL(T) without theory propagation
                        // is incomplete for LRA. When the SAT solver exhausts all
                        // Boolean assignments and Real-sorted theory atoms were
                        // present, the UNSAT may be false — return Unknown instead
                        // of Unsat to prevent PDR from producing wrong "sat" results.
                        if has_real_theory_atoms {
                            if debug {
                                safe_eprintln!(
                                    "[CHC-SMT] LRA incompleteness guard: returning Unknown \
                                 (Real-sorted theory atoms detected, DPLL(T) may be incomplete)"
                                );
                            }
                            return SmtResult::Unknown;
                        }

                        if let Some(map) = &assumption_map {
                            let mut conjuncts = Vec::new();
                            for lit in core {
                                if let Some(expr) = map.get(&lit) {
                                    conjuncts.push(expr.clone());
                                }
                            }
                            if !conjuncts.is_empty() {
                                return SmtResult::UnsatWithCore(UnsatCore {
                                    conjuncts,
                                    ..Default::default()
                                });
                            }
                        }
                        return SmtResult::Unsat;
                    }
                    z4_sat::AssumeResult::Unknown => return SmtResult::Unknown,
                    #[allow(unreachable_patterns)]
                    _ => return SmtResult::Unknown,
                }
            };

            if let Err(result) = self.apply_term_growth_action(
                term_growth_action,
                &mut term_to_var,
                &mut var_to_term,
                &mut num_vars,
                &mut sat,
                split_state,
                debug,
                dt_iterations,
            ) {
                return result;
            }
        }
    }
}
