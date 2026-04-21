// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Array+EUF solve entry points and axiom fixpoint loops.

use super::super::super::Executor;
use super::{reachable_term_set, ArrayAxiomMode};
use crate::combined_solvers::combiner::TheoryCombiner;
use crate::executor::theories::solve_harness::TheoryModels;
use crate::executor_types::{Result, SolveResult};
use crate::preprocess::PreprocessingPass;
#[cfg(not(kani))]
use hashbrown::HashSet;
#[cfg(kani)]
use z4_core::kani_compat::DetHashSet as HashSet;
use z4_core::TermId;

#[derive(Clone, Copy)]
struct ArrayAxiomPlan {
    eager_row: bool,
    eager_row2b: bool,
    assertion_budget: Option<usize>,
}

impl ArrayAxiomPlan {
    fn from_mode(mode: ArrayAxiomMode) -> Self {
        match mode {
            ArrayAxiomMode::EagerAll => Self {
                eager_row: true,
                eager_row2b: true,
                assertion_budget: None,
            },
            ArrayAxiomMode::LazyRow2FinalCheck => Self {
                eager_row: true,
                eager_row2b: false,
                assertion_budget: Some(800),
            },
        }
    }
}

impl Executor {
    /// Solve using combined EUF + Arrays theory.
    ///
    /// Uses `solve_incremental_split_loop_pipeline!` with `eager_extension: true`
    /// so array ROW2 axioms discovered during `check()` are injected inline via
    /// `ExtCheckResult::AddClauses` instead of requiring O(N) full SAT re-solve
    /// round-trips through the outer loop (#6546 Packet 6).
    pub(crate) fn solve_array_euf(&mut self) -> Result<SolveResult> {
        // Push/pop incremental mode: use the persistent no-split incremental
        // pipeline that only processes scoped assertions, avoiding phantom
        // axioms from dead terms in the append-only TermStore (#6726).
        if self.incremental_mode {
            return self.solve_array_euf_incremental();
        }

        // Normalize assertion grouping up front so array axiom generation sees
        // the same surface for `(assert (and ...))` and multiple `(assert ...)`
        // forms (#6885).
        let mut flatten_pass = crate::preprocess::FlattenAnd::new();
        flatten_pass.apply(&mut self.ctx.terms, &mut self.ctx.assertions);

        // #6820: Inline store-flat array equalities before axiom generation.
        // Store-flat benchmarks (storecomm_*_sf_*, storeinv_*_sf_*, swap_*_sf_*)
        // assert chains of (= a_N (store a_{N-1} idx val)). Substituting each
        // a_N with its store expression converts select(a_N, k) into
        // select(store(...), k), which directly triggers ROW axioms.
        let pre_subst_len = self.ctx.assertions.len();
        super::super::solve_harness::substitute_store_flat_equalities(
            &mut self.ctx.terms,
            &mut self.ctx.assertions,
        );
        // When store-flat substitution removed defining equalities, scope the
        // axiom fixpoint to terms reachable from the surviving assertions.
        // Without this, dead array variables (still in the TermStore) generate
        // thousands of spurious axioms.
        let scoped = self.ctx.assertions.len() < pre_subst_len;
        if scoped {
            let start_len = self.ctx.terms.len();
            let reachable = reachable_term_set(&self.ctx.terms, &self.ctx.assertions);
            self.array_axiom_scope = Some((reachable, start_len));
        }

        // Use the full array axiom fixpoint (extensionality + ROW2b + store
        // decomposition) for QF_AX. The lighter fixpoint_5 with ROW2b budget=0
        // misses upward select propagation needed for storeinv cross-swap _nf_
        // patterns where let-expanded nested stores have no intermediate variable
        // equalities (#4304, #6282).
        //
        // #6546 Packet 4: eager ROW1+ROW2, lazy ROW2b. The fully lazy
        // mode (LazyRowFinalCheck) was tested in W4:3050 and regressed all
        // storeinv sizes. EagerAll was tested in W4:3055 and still timed out
        // on size7 — the bottleneck is the DPLL(T) refinement loop overhead,
        // not the eager clause surface.
        self.run_array_axiom_fixpoint_at(0, ArrayAxiomMode::LazyRow2FinalCheck);

        // Clear the temporary scope so the DPLL(T) lazy axiom path isn't
        // restricted.
        if scoped {
            self.array_axiom_scope = None;
        }

        let solve_interrupt = self.solve_interrupt.clone();
        let solve_deadline = self.solve_deadline;
        self.with_isolated_incremental_state(None, |this| {
            solve_incremental_split_loop_pipeline!(this,
                tag: "ArrayEUF",
                persistent_sat_field: persistent_sat,
                create_theory: TheoryCombiner::array_euf(&this.ctx.terms),
                extract_models: |theory| {
                    theory.scope_euf_model_to_roots(&this.ctx.assertions);
                    let (euf, arr) = theory.extract_euf_array_models();
                    theory.clear_euf_model_scope();
                    TheoryModels {
                        euf: Some(euf),
                        array: Some(arr),
                        ..TheoryModels::default()
                    }
                },
                max_splits: 1,
                pre_theory_import: |_theory, _lc, _hc, _ds| {},
                post_theory_export: |_theory| {
                    (vec![], Default::default(), Default::default())
                },
                eager_extension: true,
                pre_iter_check: |_s| {
                    solve_interrupt
                        .as_ref()
                        .is_some_and(|flag| flag.load(std::sync::atomic::Ordering::Relaxed))
                        || solve_deadline.is_some_and(|dl| std::time::Instant::now() >= dl)
                }
            )
        })
    }

    /// Solve QF_AX incrementally using SAT scope selectors (#6726).
    ///
    /// Maintains a persistent SAT solver and TseitinState that retain
    /// learned clauses and term-to-var mappings across check-sat calls.
    /// Uses SAT scope selectors (push/pop) for correct scoping, so only
    /// active assertions produce axioms — dead terms from popped scopes
    /// are never visible to the theory combiner.
    fn solve_array_euf_incremental(&mut self) -> Result<SolveResult> {
        let model_roots = self.ctx.assertions.clone();
        solve_incremental_theory_pipeline!(self,
            tag: "ArrayEUF",
            create_theory: TheoryCombiner::array_euf(&self.ctx.terms),
            extract_models: |theory| {
                theory.scope_euf_model_to_roots(&model_roots);
                let (euf, arr) = theory.extract_euf_array_models();
                theory.clear_euf_model_scope();
                TheoryModels {
                    euf: Some(euf),
                    array: Some(arr),
                    ..TheoryModels::default()
                }
            },
            track_theory_stats: true,
            set_unknown_on_error: false
        )
    }

    /// Run the array axiom fixpoint with extensionality + store decomposition (#6282).
    ///
    /// `dedup_protect` is the number of assertions at the front of
    /// `self.ctx.assertions` that must not be removed by deduplication.
    /// Callers that later `drain(dedup_protect..)` to extract newly-added axioms
    /// pass their snapshot length here so that `retain` cannot shrink the
    /// assertion list below that index (#6340).
    ///
    /// `mode` controls whether ROW/ROW2b axioms are generated eagerly or
    /// deferred to the runtime `ArraySolver` (#6546).
    pub(in crate::executor) fn run_array_axiom_fixpoint_at(
        &mut self,
        dedup_protect: usize,
        mode: ArrayAxiomMode,
    ) {
        self.run_array_axiom_fixpoint_at_plan(dedup_protect, ArrayAxiomPlan::from_mode(mode), &[]);
    }

    #[cfg(test)]
    pub(in crate::executor) fn run_array_axiom_fixpoint_lazy_row_final_check_for_tests(
        &mut self,
        dedup_protect: usize,
    ) {
        self.run_array_axiom_fixpoint_at_plan(
            dedup_protect,
            ArrayAxiomPlan {
                eager_row: false,
                eager_row2b: false,
                assertion_budget: None,
            },
            &[],
        );
    }

    /// Run the array axiom fixpoint with extra root terms included in the
    /// reachable set for scope filtering (#6736). Used by check-sat-assuming
    /// paths where assumption terms contain array operations that need axioms
    /// but are not in `self.ctx.assertions`.
    fn run_array_axiom_fixpoint_at_plan(
        &mut self,
        dedup_protect: usize,
        plan: ArrayAxiomPlan,
        assumption_roots: &[TermId],
    ) {
        // In incremental mode, scope axiom generation to terms reachable from
        // current assertions (and assumption roots, if any). This prevents
        // phantom axioms from dead terms in popped scopes (#6726). Terms
        // created during the fixpoint (idx >= start_len) always pass the
        // scope check.
        if self.incremental_mode {
            let start_len = self.ctx.terms.len();
            let reachable = if assumption_roots.is_empty() {
                reachable_term_set(&self.ctx.terms, &self.ctx.assertions)
            } else {
                // Include assumption terms in the reachable set so
                // assumption-only array operations get axioms (#6736).
                let mut roots =
                    Vec::with_capacity(self.ctx.assertions.len() + assumption_roots.len());
                roots.extend_from_slice(&self.ctx.assertions);
                roots.extend_from_slice(assumption_roots);
                reachable_term_set(&self.ctx.terms, &roots)
            };
            self.array_axiom_scope = Some((reachable, start_len));
        }

        // #6820: Reset store-eq cache for this fixpoint invocation.
        // Store equalities are stable across inner rounds (they come from
        // the original formula), so we collect them once on the first scan.
        self.reset_array_congruence_caches();

        let eager_row = plan.eager_row;
        let eager_row2b = plan.eager_row2b;
        // #6820: Budget controls to prevent exponential growth in the eager
        // axiom fixpoint. Storecomm-family benchmarks (N stores, same base)
        // cause O(N²) congruence axioms × ROW feedback loops. The DPLL(T)
        // ArraySolver handles any remaining axioms lazily via event-driven
        // queues.
        let fixpoint_start_terms = self.ctx.terms.len();
        let fixpoint_term_budget: usize = 10_000;
        // #6820: For LazyRow2FinalCheck (QF_AUFLIA combined solver), cap
        // the clause (assertion) count. Excessive eager clauses slow SAT
        // solving on satisfiable instances. Profiling shows storeinv SAT
        // benchmarks go from 8.72s (1139 assertions) to 0.76s (988 capped)
        // at size 7, and from TIMEOUT to 1.84s at size 10.
        let assertion_budget = plan.assertion_budget;

        for _outer in 0..20_usize {
            let n = self.ctx.terms.len();
            self.add_array_extensionality_axioms();
            {
                let mut row2b_used = 0_usize;
                for _round in 0..20_usize {
                    let inner_n = self.ctx.terms.len();
                    self.add_store_value_congruence_axioms();
                    self.add_store_other_side_congruence_axioms();
                    self.add_store_disjunctive_index_axioms();
                    let _seeded_row_terms = self.seed_array_row_terms();
                    // (#6282 Phase A) Keep ROW2b budget at 1000.
                    // Reducing below 1000 causes regressions on SAT
                    // instances (test_store_permutation_distinct_indices_sat_5086).
                    if row2b_used < 1000 {
                        let remaining = 1000 - row2b_used;
                        let _seeded_row2b_terms = self.seed_array_row2b_terms(remaining);
                        if eager_row2b {
                            row2b_used += self.add_array_row2b_clauses(remaining);
                        }
                    }
                    if eager_row {
                        // ROW1 clauses (i = k → select(store(a,i,v),k) = v) are always
                        // generated eagerly on mixed-theory paths, but the pure
                        // ArrayEUF route can defer them to the runtime ArraySolver.
                        // ROW2b (upward) is only eager in EagerAll mode.
                        self.add_array_row_clauses();
                    }
                    if self.ctx.terms.len() == inner_n {
                        break;
                    }
                    // #6820: Bail out of the inner fixpoint if we've exceeded
                    // the term budget. The remaining axioms will be generated
                    // lazily by the DPLL(T) ArraySolver.
                    if self.ctx.terms.len() - fixpoint_start_terms > fixpoint_term_budget {
                        break;
                    }
                }
                // Dedup only axioms added after dedup_protect (#6340).
                // Seed `seen` with the protected prefix so new duplicates of
                // existing assertions are still removed, but the prefix itself
                // is never touched — callers rely on stable indices 0..dedup_protect.
                let mut seen: HashSet<TermId> = self.ctx.assertions[..dedup_protect]
                    .iter()
                    .copied()
                    .collect();
                let mut tail = self.ctx.assertions.split_off(dedup_protect);
                tail.retain(|a| seen.insert(*a));
                self.ctx.assertions.extend(tail);
            }
            self.add_store_store_base_decomposition_axioms();
            if self.ctx.terms.len() == n {
                break;
            }
            // #6820: Also bail outer loop on term budget.
            if self.ctx.terms.len() - fixpoint_start_terms > fixpoint_term_budget {
                break;
            }
            // #6820: Bail on assertion (clause) budget after dedup.
            // For LazyRow2FinalCheck, excessive clauses slow SAT solving;
            // the runtime ArraySolver handles remaining axioms lazily.
            if let Some(budget) = assertion_budget {
                if self.ctx.assertions.len() > budget {
                    break;
                }
            }
        }

        self.array_axiom_scope = None;
    }

    /// Run the full eager array axiom fixpoint at a given dedup_protect offset.
    pub(in crate::executor) fn run_array_axiom_full_fixpoint_at(&mut self, dedup_protect: usize) {
        self.run_array_axiom_fixpoint_at(dedup_protect, ArrayAxiomMode::EagerAll);
    }

    /// Run the full eager array axiom fixpoint with extra root terms for
    /// assumption-aware scope filtering (#6736).
    ///
    /// In incremental mode, assumption terms are not in `self.ctx.assertions`
    /// and would be excluded from the reachable set that scopes axiom
    /// generation. This variant includes `assumption_roots` in the reachable
    /// set so array operations appearing only in assumptions get proper axioms.
    pub(in crate::executor) fn run_array_axiom_full_fixpoint_at_with_roots(
        &mut self,
        dedup_protect: usize,
        assumption_roots: &[TermId],
    ) {
        self.run_array_axiom_fixpoint_at_plan(
            dedup_protect,
            ArrayAxiomPlan::from_mode(ArrayAxiomMode::EagerAll),
            assumption_roots,
        );
    }

    /// Run the full eager array axiom fixpoint, deduplicating all assertions.
    pub(in crate::executor) fn run_array_axiom_full_fixpoint(&mut self) {
        self.run_array_axiom_fixpoint_at(0, ArrayAxiomMode::EagerAll);
    }

    /// Run the Array+EUF fixpoint (store congruence + array congruence + ROW).
    ///
    /// Includes `add_array_congruence_axioms` which creates `select(B,k)` from
    /// `select(A,k)` when `A = B`. Used by the pure array and BV paths, which do
    /// not need the store-store base decomposition used by the combined solvers.
    pub(in crate::executor) fn run_array_axiom_fixpoint_5(&mut self) {
        self.run_array_axiom_fixpoint_inner(true, &[]);
    }

    /// Run the Array+EUF fixpoint with extra root terms for assumption-aware
    /// scope filtering (#6736). Used by QF_AX check-sat-assuming paths where
    /// assumption terms contain array operations that need congruence axioms
    /// but are not in `self.ctx.assertions`.
    pub(in crate::executor) fn run_array_axiom_fixpoint_5_with_roots(
        &mut self,
        assumption_roots: &[TermId],
    ) {
        self.run_array_axiom_fixpoint_inner(true, assumption_roots);
    }

    fn run_array_axiom_fixpoint_inner(
        &mut self,
        include_congruence: bool,
        assumption_roots: &[TermId],
    ) {
        // Scope filtering for incremental mode (#6726).
        if self.incremental_mode {
            let start_len = self.ctx.terms.len();
            let reachable = if assumption_roots.is_empty() {
                reachable_term_set(&self.ctx.terms, &self.ctx.assertions)
            } else {
                let mut roots =
                    Vec::with_capacity(self.ctx.assertions.len() + assumption_roots.len());
                roots.extend_from_slice(&self.ctx.assertions);
                roots.extend_from_slice(assumption_roots);
                reachable_term_set(&self.ctx.terms, &roots)
            };
            self.array_axiom_scope = Some((reachable, start_len));
        }

        self.reset_array_congruence_caches();

        // Unified fixpoint: all axiom generators including ROW2b run together.
        // ROW2b (upward select propagation) creates new select terms that feed
        // into congruence and ROW1/ROW2 generators in subsequent rounds.
        // Deep store chains (storeinv with 7-level nesting, #6282) require
        // multiple rounds to chain through all levels.
        //
        // Budget limits ROW2b axiom count per fixpoint invocation to prevent
        // O(selects × stores) blowup on large formulas.
        let row2b_budget = 0_usize;
        let mut row2b_used = 0_usize;
        for _round in 0..20_usize {
            let n = self.ctx.terms.len();
            self.add_store_value_congruence_axioms();
            self.add_store_other_side_congruence_axioms();
            self.add_store_disjunctive_index_axioms();
            if include_congruence {
                self.add_array_congruence_axioms();
            }
            self.add_array_row_lemmas();
            // ROW2b upward propagation (#6282): for select(A, j) where A is
            // the base of store(A, i, v) = B, create select(B, j) and assert
            // (= i j) ∨ (= select(A,j) select(B,j)).
            if row2b_used < row2b_budget {
                let remaining = row2b_budget - row2b_used;
                row2b_used += self.add_array_row2b_upward_lemmas(remaining);
            }
            if self.ctx.terms.len() == n {
                break;
            }
        }
        // Deduplicate assertions.
        let mut seen: HashSet<TermId> = HashSet::with_capacity(self.ctx.assertions.len());
        self.ctx.assertions.retain(|a| seen.insert(*a));

        self.array_axiom_scope = None;
    }
}
