// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! QF_SLIA solving pipeline: combined Strings + EUF + LIA theory.
//!
//! Split from `strings.rs` for code health (#7006, #5970).
//! The pure QF_S solver remains in `strings.rs`; shared helpers
//! (decomposition, bounded-var detection, alphabet, candidates)
//! are in `strings_analysis.rs`.

use z4_core::term::{Constant, Symbol, TermData};
use z4_core::{Sort, StringLemma, TermId};

use crate::combined_solvers::StringsLiaSolver;
use crate::executor_types::{Result, SolveResult};

use super::super::mod_div_elim::eliminate_int_mod_div_by_constant;
use super::super::Executor;
use super::skolem_cache::ExecutorSkolemCache;
use super::strings_analysis::{MAX_CONSECUTIVE_DUPLICATE_LEMMAS, MAX_PIVOT_CANDIDATES};
use super::{debug_auflia_enabled, MAX_SPLITS_LIA, MAX_STRING_LEMMA_ITERATIONS};

impl Executor {
    fn explicit_string_assignments(
        &self,
        assertions: &[TermId],
    ) -> hashbrown::HashMap<TermId, String> {
        let mut assignments = hashbrown::HashMap::new();

        for &assertion in assertions {
            let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(assertion) else {
                continue;
            };
            if name != "=" || args.len() != 2 {
                continue;
            }

            let lhs = args[0];
            let rhs = args[1];
            match (self.ctx.terms.get(lhs), self.ctx.terms.get(rhs)) {
                (TermData::Var(_, _), TermData::Const(Constant::String(value)))
                    if *self.ctx.terms.sort(lhs) == Sort::String =>
                {
                    assignments.insert(lhs, value.clone());
                }
                (TermData::Const(Constant::String(value)), TermData::Var(_, _))
                    if *self.ctx.terms.sort(rhs) == Sort::String =>
                {
                    assignments.insert(rhs, value.clone());
                }
                _ => {}
            }
        }

        assignments
    }

    fn model_respects_detected_string_bounds(
        &self,
        bounds: &[super::strings_analysis::LengthBound],
        assumptions: &[TermId],
    ) -> bool {
        if bounds.is_empty() {
            return true;
        }

        let mut observed_values = self
            .last_model
            .as_ref()
            .and_then(|model| model.string_model.as_ref())
            .map(|string_model| string_model.values.clone())
            .unwrap_or_default();
        observed_values.extend(self.explicit_string_assignments(assumptions));

        bounds.iter().all(|bound| {
            observed_values.get(&bound.var).is_none_or(|value| {
                let len = value.chars().count();
                len >= bound.lower && len <= bound.upper
            })
        })
    }

    fn merge_explicit_string_assignments_into_model(&mut self, assertions: &[TermId]) {
        let assignments = self.explicit_string_assignments(assertions);
        if assignments.is_empty() {
            return;
        }

        if let Some(model) = self.last_model.as_mut() {
            let string_model = model
                .string_model
                .get_or_insert_with(z4_strings::StringModel::default);
            string_model.values.extend(assignments);
        }
    }

    /// Solve QF_SLIA using combined Strings + EUF + LIA theory.
    ///
    /// Injects str.len axioms (non-negativity, zero-length ↔ empty string,
    /// concat length decomposition) as additional assertions, then runs
    /// the `StringsLiaSolver` combined theory with branch-and-bound for
    /// integer arithmetic.
    pub(in crate::executor) fn solve_strings_lia(&mut self) -> Result<SolveResult> {
        if debug_auflia_enabled() {
            safe_eprintln!(
                "[SLIA] === solve_strings_lia ENTER depth={} ===",
                self.pivot_enum_depth
            );
        }
        // Constant-fold ground string operations (#4057 design). When all
        // arguments to a string op are constants (e.g., str.substr("hello",1,3)),
        // evaluate eagerly and replace with the result. This eliminates ground
        // computation from the formula before routing to QF_S or SLIA pipeline.
        {
            let folded = self.fold_ground_string_ops(&self.ctx.assertions.clone());
            // Early UNSAT: if any assertion folds to false
            if folded.iter().any(|&t| {
                matches!(
                    self.ctx.terms.get(t),
                    TermData::Const(Constant::Bool(false))
                )
            }) {
                return Ok(SolveResult::Unsat);
            }
            // Remove trivially-true assertions
            let non_trivial: Vec<TermId> = folded
                .into_iter()
                .filter(|&t| {
                    !matches!(self.ctx.terms.get(t), TermData::Const(Constant::Bool(true)))
                })
                .collect();
            // Early SAT: all assertions folded to true
            if non_trivial.is_empty() {
                self.skip_model_eval = true;
                self.last_model = Some(super::super::model::Model {
                    sat_model: Vec::new(),
                    term_to_var: hashbrown::HashMap::new(),
                    euf_model: None,
                    array_model: None,
                    lra_model: None,
                    lia_model: None,
                    bv_model: None,
                    fp_model: None,
                    string_model: None,
                    seq_model: None,
                });
                return Ok(SolveResult::Sat);
            }
            self.ctx.assertions = non_trivial;
        }

        if self.has_exact_string_length_contradiction(&self.ctx.assertions) {
            return Ok(SolveResult::Unsat);
        }

        // Soundness guard (#3598): if the user assertions contain no arithmetic
        // constraints and no string-int bridge operators, solve via the pure
        // string path even under QF_SLIA.
        //
        // Many benchmarks declare QF_SLIA but are purely string equations.
        // Routing those to the SLIA pipeline can introduce false UNSAT from
        // arithmetic-side interactions that are irrelevant to the formula.
        let needs_slia = self.ctx.assertions.iter().any(|&a| {
            crate::term_helpers::contains_arithmetic_ops(&self.ctx.terms, a)
                || crate::term_helpers::contains_string_ops(&self.ctx.terms, a)
        });
        if !needs_slia {
            return self.solve_strings();
        }

        // Pivot-bounded word equation pre-pass (#3826).
        //
        // For benchmarks with a short bounded string variable (e.g., len(A) <= 2),
        // enumerate candidate values for that variable and try each as an extra
        // assertion. This converts an expensive CEGAR loop with many NeedStringLemma
        // rounds into a small bounded search over concrete variable assignments.
        //
        // The re-entry guard prevents infinite recursion when the inner call
        // to solve_strings_lia triggers pivot detection again.
        if self.pivot_enum_depth == 0 {
            let pivot_bounds = self.detect_bounded_string_vars();
            // Multi-variable bounded formulas are allowed here as long as the
            // inner assumption solve returns a concrete string model whose
            // observed assignments respect every detected length bound.
            if !pivot_bounds.is_empty() {
                if let Some(pivot) = pivot_bounds
                    .iter()
                    .min_by_key(|b| b.upper.saturating_sub(b.lower))
                {
                    let alphabet = self.collect_alphabet();
                    if !alphabet.is_empty() {
                        let candidates =
                            Self::generate_candidates(&alphabet, pivot.lower, pivot.upper);
                        if !candidates.is_empty() && candidates.len() <= MAX_PIVOT_CANDIDATES {
                            let pivot_var = pivot.var;
                            if debug_auflia_enabled() {
                                safe_eprintln!(
                                    "[SLIA] Pivot enum: var={:?}, len=[{}..={}], {} candidates",
                                    pivot_var,
                                    pivot.lower,
                                    pivot.upper,
                                    candidates.len()
                                );
                            }
                            // Pre-create equality terms for all candidates (before DpllT borrow).
                            let candidate_eqs: Vec<TermId> = candidates
                                .iter()
                                .map(|s| {
                                    let str_term = self.ctx.terms.mk_string(s.clone());
                                    self.ctx.terms.mk_eq(pivot_var, str_term)
                                })
                                .collect();

                            self.pivot_enum_depth += 1;
                            // Budget: 2 seconds per candidate, but respect any
                            // existing deadline from the API layer.
                            let saved_deadline = self.solve_deadline;
                            let assertions_snapshot = self.ctx.assertions.clone();
                            let mut all_unsat = true;
                            for (i, &eq_term) in candidate_eqs.iter().enumerate() {
                                if self.should_abort_theory_loop() {
                                    self.pivot_enum_depth -= 1;
                                    self.solve_deadline = saved_deadline;
                                    return Ok(SolveResult::Unknown);
                                }
                                // Set per-candidate deadline: min(2s from now, existing deadline).
                                let candidate_deadline =
                                    std::time::Instant::now() + std::time::Duration::from_secs(2);
                                self.solve_deadline = Some(match saved_deadline {
                                    Some(dl) => dl.min(candidate_deadline),
                                    None => candidate_deadline,
                                });
                                let result = match self.solve_strings_lia_with_assumptions(
                                    &assertions_snapshot,
                                    &[eq_term],
                                ) {
                                    Ok(SolveResult::Sat) => {
                                        self.last_result = Some(SolveResult::Sat);
                                        match self.finalize_sat_model_validation()? {
                                            SolveResult::Sat => {
                                                self.finalize_sat_assumption_validation(&[eq_term])
                                            }
                                            other => Ok(other),
                                        }
                                    }
                                    other => other,
                                };
                                match result {
                                    Ok(SolveResult::Sat) => {
                                        // Defense-in-depth: the assumption
                                        // solve already downgraded any SAT
                                        // whose concrete strings violate the
                                        // scoped length bounds. Re-check here
                                        // against the pre-pass bounds because
                                        // this SAT result will be trusted
                                        // immediately by the outer solver.
                                        let model_ok = self.model_respects_detected_string_bounds(
                                            &pivot_bounds,
                                            &[eq_term],
                                        );
                                        if model_ok {
                                            // The inner solver may omit
                                            // assumption-driven assignments
                                            // from the extracted string model.
                                            self.merge_explicit_string_assignments_into_model(&[
                                                eq_term,
                                            ]);
                                            if debug_auflia_enabled() {
                                                safe_eprintln!(
                                                "[SLIA] Pivot enum: candidate {} '{}' → SAT (model verified)",
                                                i,
                                                candidates[i]
                                            );
                                            }
                                            self.pivot_enum_depth -= 1;
                                            self.solve_deadline = saved_deadline;
                                            return Ok(SolveResult::Sat);
                                        }
                                        // Model violates a length bound —
                                        // inner solver was unsound. Treat as
                                        // Unknown and try next candidate.
                                        if debug_auflia_enabled() {
                                            safe_eprintln!(
                                            "[SLIA] Pivot enum: candidate {} '{}' → SAT but model violates length bounds",
                                            i,
                                            candidates[i]
                                        );
                                        }
                                        all_unsat = false;
                                    }
                                    Ok(SolveResult::Unsat) => {
                                        if debug_auflia_enabled() {
                                            safe_eprintln!(
                                                "[SLIA] Pivot enum: candidate {} '{}' → UNSAT",
                                                i,
                                                candidates[i]
                                            );
                                        }
                                    }
                                    Ok(SolveResult::Unknown) | Err(_) => {
                                        all_unsat = false;
                                        if debug_auflia_enabled() {
                                            safe_eprintln!(
                                            "[SLIA] Pivot enum: candidate {} '{}' → Unknown/Error",
                                            i,
                                            candidates[i]
                                        );
                                        }
                                    }
                                }
                            }
                            self.pivot_enum_depth -= 1;
                            self.solve_deadline = saved_deadline;
                            // If ALL candidates returned UNSAT, the formula is
                            // UNSAT (sound: every concrete value was ruled out).
                            if all_unsat {
                                return Ok(SolveResult::Unsat);
                            }
                            // Not all candidates UNSAT — fall through to the
                            // normal CEGAR loop for final determination.
                        }
                    }
                }
            }
        }

        // Step 1: Collect str.len terms and inject length axioms.
        let str_len_axioms = self.collect_str_len_axioms();

        // Step 2: Preprocess (same as solve_auf_lia).
        let mod_elim = eliminate_int_mod_div_by_constant(&mut self.ctx.terms, &self.ctx.assertions);
        let mut preprocessed = mod_elim.constraints;
        preprocessed.extend(mod_elim.rewritten);
        preprocessed.extend(str_len_axioms);

        // Exact overlap reduction (#4055): when positive prefix/suffix-style
        // constraints and a concrete length uniquely determine a string, assert
        // the resolved equality eagerly (e.g., "ab" prefix + "bc" suffix + len=3
        // implies x = "abc").
        let overlap_equalities = self.preregister_overlap_constant_equalities(&preprocessed);
        preprocessed.extend(overlap_equalities);

        // Pre-register eager str.contains decompositions (Phase 2, #3402).
        let mut skolem_cache = ExecutorSkolemCache::new();
        let mut decomposed_vars = hashbrown::HashSet::new();
        let mut contains_decomposed_vars = hashbrown::HashSet::new();
        let contains_decomps = self.preregister_contains_decompositions(
            &preprocessed,
            &mut skolem_cache,
            &mut decomposed_vars,
            &mut contains_decomposed_vars,
        );
        let contains_reduced_term_ids = self.collect_decomposition_concat_terms(&contains_decomps);
        // Collect length axioms from decomposition terms (#3850): decompositions
        // introduce new str.len and str.++ terms that weren't in the original
        // formula. Without their length axioms, LIA can't derive the arithmetic
        // contradictions needed for soundness (e.g., len(x) = len(sk) + 2*len(x) + len(sk2)).
        let decomp_len_axioms = self.collect_str_len_axioms_from_roots(&contains_decomps);
        preprocessed.extend(contains_decomps);
        preprocessed.extend(decomp_len_axioms);

        // #4057: solve in two effort passes. First expose only light
        // substr/str.at reductions plus contains decompositions. If that
        // still returns unknown, add replace reductions in a second pass.
        let (effort1_reductions, effort1_reduced_term_ids) = self.preregister_extf_reductions(
            &preprocessed,
            &mut skolem_cache,
            &mut decomposed_vars,
            true,
            false,
        );
        let effort1_len_axioms = self.collect_str_len_axioms_from_roots(&effort1_reductions);
        let contains_from_effort1 = self.preregister_contains_decompositions(
            &effort1_reductions,
            &mut skolem_cache,
            &mut decomposed_vars,
            &mut contains_decomposed_vars,
        );
        let contains_from_effort1_reduced_term_ids =
            self.collect_decomposition_concat_terms(&contains_from_effort1);
        let decomp_len_axioms_2 = self.collect_str_len_axioms_from_roots(&contains_from_effort1);

        let mut preprocessed_pass0 = preprocessed.clone();
        preprocessed_pass0.extend(effort1_reductions);
        preprocessed_pass0.extend(effort1_len_axioms);
        preprocessed_pass0.extend(contains_from_effort1);
        preprocessed_pass0.extend(decomp_len_axioms_2);

        let mut preregistered_reduced_term_ids_pass0 = effort1_reduced_term_ids;
        preregistered_reduced_term_ids_pass0.extend(contains_reduced_term_ids.iter().copied());
        preregistered_reduced_term_ids_pass0
            .extend(contains_from_effort1_reduced_term_ids.iter().copied());
        preregistered_reduced_term_ids_pass0.sort_unstable();
        preregistered_reduced_term_ids_pass0.dedup();

        let pass0_result = self.solve_strings_lia_preprocessed(
            &preprocessed_pass0,
            &preregistered_reduced_term_ids_pass0,
            &mut skolem_cache,
        );

        let result = match pass0_result {
            Ok(SolveResult::Unknown) => {
                // Only build replace reductions after the light pass stalls.
                // Precomputing effort-2 terms up front reintroduces the heavy
                // path into pass 0 and defeats the #4057 split-pipeline intent.
                let (effort2_reductions, effort2_reduced_term_ids) = self
                    .preregister_extf_reductions(
                        &preprocessed_pass0,
                        &mut skolem_cache,
                        &mut decomposed_vars,
                        false,
                        true,
                    );
                if effort2_reductions.is_empty() {
                    Ok(SolveResult::Unknown)
                } else {
                    if debug_auflia_enabled() {
                        safe_eprintln!(
                            "[SLIA] pass 0 returned Unknown; escalating with replace preregistration"
                        );
                    }

                    let effort2_len_axioms =
                        self.collect_str_len_axioms_from_roots(&effort2_reductions);
                    let contains_from_effort2 = self.preregister_contains_decompositions(
                        &effort2_reductions,
                        &mut skolem_cache,
                        &mut decomposed_vars,
                        &mut contains_decomposed_vars,
                    );
                    let contains_from_effort2_reduced_term_ids =
                        self.collect_decomposition_concat_terms(&contains_from_effort2);
                    let decomp_len_axioms_3 =
                        self.collect_str_len_axioms_from_roots(&contains_from_effort2);

                    let mut preprocessed_pass1 = preprocessed_pass0;
                    preprocessed_pass1.extend(effort2_reductions);
                    preprocessed_pass1.extend(effort2_len_axioms);
                    preprocessed_pass1.extend(contains_from_effort2);
                    preprocessed_pass1.extend(decomp_len_axioms_3);

                    let mut preregistered_reduced_term_ids_pass1 =
                        preregistered_reduced_term_ids_pass0;
                    preregistered_reduced_term_ids_pass1.extend(effort2_reduced_term_ids);
                    preregistered_reduced_term_ids_pass1
                        .extend(contains_from_effort2_reduced_term_ids);
                    preregistered_reduced_term_ids_pass1.sort_unstable();
                    preregistered_reduced_term_ids_pass1.dedup();

                    self.solve_strings_lia_preprocessed(
                        &preprocessed_pass1,
                        &preregistered_reduced_term_ids_pass1,
                        &mut skolem_cache,
                    )
                }
            }
            other => other,
        };
        if debug_auflia_enabled() {
            safe_eprintln!(
                "[SLIA] === solve_strings_lia EXIT depth={}: {:?} ===",
                self.pivot_enum_depth,
                result
            );
        }
        result
    }

    /// Solve QF_SLIA under assumptions (#7656).
    ///
    /// This reuses [`Self::solve_strings_lia`] by temporarily appending
    /// assumptions to the active assertion set, ensuring str.len/string
    /// axioms are generated from both assertions and assumptions.
    ///
    /// Uses `with_isolated_incremental_state` to prevent assumption-scoped
    /// clauses from leaking into the persistent SAT solver (#7656).
    pub(in crate::executor) fn solve_strings_lia_with_assumptions(
        &mut self,
        assertions: &[TermId],
        assumptions: &[TermId],
    ) -> Result<SolveResult> {
        let mut scoped_assertions = Vec::with_capacity(assertions.len() + assumptions.len());
        scoped_assertions.extend(assertions.iter().copied());
        scoped_assertions.extend(assumptions.iter().copied());
        let scoped_bounds = self.detect_bounded_string_vars_in(&scoped_assertions);

        let result = self.with_isolated_incremental_state(Some(scoped_assertions), |exec| {
            exec.solve_strings_lia()
        });

        match result {
            Ok(SolveResult::Unsat) => {
                // Keep assumption-core behavior consistent even without minimal core extraction.
                self.last_assumption_core = Some(assumptions.to_vec());
                Ok(SolveResult::Unsat)
            }
            Ok(SolveResult::Sat) => {
                if !self.model_respects_detected_string_bounds(&scoped_bounds, assumptions) {
                    if debug_auflia_enabled() {
                        safe_eprintln!(
                            "[SLIA] assumption solve produced SAT with concrete string violating detected length bounds; downgrading to Unknown"
                        );
                    }
                    self.last_model = None;
                    self.last_assumption_core = None;
                    return Ok(SolveResult::Unknown);
                }
                self.merge_explicit_string_assignments_into_model(assumptions);
                self.last_assumption_core = None;
                Ok(SolveResult::Sat)
            }
            Ok(SolveResult::Unknown) => {
                self.last_assumption_core = None;
                Ok(SolveResult::Unknown)
            }
            Err(err) => {
                self.last_assumption_core = None;
                Err(err)
            }
        }
    }

    fn solve_strings_lia_preprocessed(
        &mut self,
        assertions: &[TermId],
        preregistered_reduced_term_ids: &[TermId],
        skolem_cache: &mut ExecutorSkolemCache,
    ) -> Result<SolveResult> {
        // Pre-create integer constants for values 0..max_string_len so the
        // N-O bridge's int_const_terms map has entries for LIA-derived values
        // like str.len(y) = 3 that do not appear literally in the formula.
        let mut max_len = 0usize;
        let mut stack: Vec<TermId> = assertions.to_vec();
        let mut visited = hashbrown::HashSet::new();
        while let Some(tid) = stack.pop() {
            if !visited.insert(tid) {
                continue;
            }
            match self.ctx.terms.get(tid) {
                TermData::Const(Constant::String(s)) => {
                    max_len = max_len.max(s.len());
                }
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, t, e) => {
                    stack.push(*c);
                    stack.push(*t);
                    stack.push(*e);
                }
                TermData::Let(bindings, body) => {
                    for (_, value) in bindings.iter() {
                        stack.push(*value);
                    }
                    stack.push(*body);
                }
                _ => {}
            }
        }
        for i in 0..=max_len {
            let _pre_intern = self.ctx.terms.mk_int(num_bigint::BigInt::from(i));
        }

        let mut emitted_dynamic_len_axioms: hashbrown::HashSet<TermId> =
            assertions.iter().copied().collect();
        let mut last_lemma: Option<StringLemma> = None;
        let mut duplicate_streak = 0usize;
        let mut dynamic_reduced_term_ids: Vec<TermId> = Vec::new();
        let saved_assertions = std::mem::replace(&mut self.ctx.assertions, assertions.to_vec());
        let saved_assertion_len = saved_assertions.len();

        // Clear the persistent SAT solver before each SLIA solve (#6688).
        // SLIA uses preprocessed temporary assertions (mod/div elimination,
        // str.len axioms, pivot candidates) that change between calls —
        // especially during pivot enumeration. Reusing a persistent solver
        // across calls with different assertion sets causes false UNSAT from
        // accumulated learned clauses. The legacy macro always created a
        // fresh SAT solver per call; this preserves that semantic.
        if let Some(ref mut state) = self.incr_theory_state {
            state.lia_persistent_sat = None;
            state.encoded_assertions.clear();
        }

        let result = solve_incremental_split_loop_pipeline!(self,
            tag: "SLIA",
            persistent_sat_field: lia_persistent_sat,
            create_theory: {
                let empty_id = self.ctx.terms.mk_string(String::new());
                let mut theory = StringsLiaSolver::new(&self.ctx.terms);
                theory.set_empty_string_id(empty_id);
                for &tid in preregistered_reduced_term_ids {
                    theory.mark_reduced(tid);
                }
                for &tid in &dynamic_reduced_term_ids {
                    theory.mark_reduced(tid);
                }
                theory
            },
            extract_models: |theory| {
                use crate::executor::theories::solve_harness::TheoryModels;
                let (euf, lia, string_model) = theory.extract_all_models();
                TheoryModels {
                    euf: Some(euf),
                    lia,
                    string: Some(string_model),
                    ..TheoryModels::default()
                }
            },
            max_splits: MAX_SPLITS_LIA,
            pre_theory_import: |theory, lc, hc, ds| {
                theory.import_learned_state(std::mem::take(lc), std::mem::take(hc));
                theory.import_dioph_state(std::mem::take(ds));
            },
            post_theory_export: |theory| {
                let (lc, hc) = theory.take_learned_state();
                let ds = theory.take_dioph_state();
                (lc, hc, ds)
            },
            eager_extension: true,
            disable_preprocess: true,
            pre_iter_check: |_s| self.should_abort_theory_loop(),
            max_string_lemma_requests: MAX_STRING_LEMMA_ITERATIONS,
            handle_string_lemma: |lemma, negations| {
                if last_lemma.as_ref() == Some(&lemma) {
                    duplicate_streak += 1;
                } else {
                    duplicate_streak = 0;
                }
                let stall = duplicate_streak >= MAX_CONSECUTIVE_DUPLICATE_LEMMAS;
                if stall && debug_auflia_enabled() {
                    safe_eprintln!(
                        "[SLIA] duplicate-streak {} for {:?} lemma (x={:?}, y={:?}, off={}) — stalled",
                        duplicate_streak + 1,
                        lemma.kind,
                        lemma.x,
                        lemma.y,
                        lemma.char_offset,
                    );
                }
                last_lemma = Some(lemma.clone());

                if stall {
                    (Vec::new(), true)
                } else {
                    let mut clauses = self.create_string_lemma_clauses(&lemma, skolem_cache);

                    for tid in self.string_lemma_reduced_terms(&lemma, skolem_cache) {
                        if !dynamic_reduced_term_ids.contains(&tid) {
                            dynamic_reduced_term_ids.push(tid);
                        }
                    }

                    let new_roots: Vec<TermId> = clauses
                        .iter()
                        .flat_map(|clause| clause.iter().copied())
                        .collect();
                    let dynamic_len_axioms =
                        self.collect_str_len_axioms_from_roots(&new_roots);
                    for axiom in dynamic_len_axioms {
                        if emitted_dynamic_len_axioms.insert(axiom) {
                            clauses.extend(self.lower_dynamic_axiom_to_clauses(axiom));
                        }
                    }

                    if self.produce_proofs_enabled() {
                        for clause in &clauses {
                            for &atom in clause {
                                negations.note_fresh_term(atom);
                            }
                        }
                    }

                    if debug_auflia_enabled() {
                        safe_eprintln!(
                            "[SLIA] string {:?} lemma (x={:?}, y={:?}, off={}, {} clauses)",
                            lemma.kind,
                            lemma.x,
                            lemma.y,
                            lemma.char_offset,
                            clauses.len()
                        );
                    }

                    (clauses, false)
                }
            }
        );

        self.ctx.assertions = saved_assertions;
        debug_assert!(
            self.ctx.assertions.len() == saved_assertion_len,
            "BUG: solve_strings_lia_preprocessed: assertion count {} != saved {saved_assertion_len} after restore",
            self.ctx.assertions.len()
        );
        result
    }
}
