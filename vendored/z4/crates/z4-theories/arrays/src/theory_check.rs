// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Array theory check implementation.
//!
//! Dispatches to sub-check methods (ROW1, ROW2, self-store, etc.) and batches
//! their results. Extracted from `theory_impl.rs` to keep each file under 500 lines.

use super::*;

impl ArraySolver<'_> {
    /// Core check logic: dispatches to sub-check methods and batches results.
    ///
    /// Each sub-check returns `Option<TheoryResult>`:
    /// - `Unsat` conflicts are returned immediately
    /// - `NeedLemmas` are batched and returned together
    /// - `NeedModelEquality` requests are batched at lower priority
    pub(crate) fn check_impl(&mut self) -> TheoryResult {
        self.check_count += 1;

        // Invariant: scope markers are within trail bounds
        debug_assert!(
            self.scopes.iter().all(|&mark| mark <= self.trail.len()),
            "arrays: scope marker exceeds trail length"
        );

        // Invariant: eq_pair_index keys are canonically ordered (min, max)
        debug_assert!(
            self.eq_pair_index.keys().all(|(a, b)| a <= b),
            "arrays: eq_pair_index has non-canonical key ordering"
        );

        // Invariant: diseq_set keys are canonically ordered
        debug_assert!(
            self.diseq_set.iter().all(|(a, b)| a <= b),
            "arrays: diseq_set has non-canonical key ordering"
        );

        // Invariant: external_diseqs are canonically ordered
        debug_assert!(
            self.external_diseqs.iter().all(|(a, b)| a <= b),
            "arrays: external_diseqs has non-canonical key ordering"
        );

        // Invariant: select_cache entries are valid select terms
        debug_assert!(
            self.select_cache.iter().all(|(term_id, _)| {
                matches!(self.terms.get(*term_id), TermData::App(sym, args) if sym.name() == "select" && args.len() == 2)
            }),
            "arrays: select_cache contains non-select terms"
        );

        self.populate_caches();

        // Build equivalence class cache once for this check() call.
        self.build_equiv_class_cache();

        // #6694: Restore early-return for direct Unsat conflicts, but keep
        // batching for stable clause-producing results and model-equality
        // requests.
        let mut batched_lemmas: Vec<TheoryLemma> = Vec::new();
        let mut model_eq_requests: Vec<ModelEqualityRequest> = Vec::new();

        // Check ROW1: select(store(a, i, v), i) = v
        if let Some(result) = self.check_row1() {
            match result {
                TheoryResult::Unsat(ref _reasons) => {
                    tracing::debug!("arrays check: ROW1 conflict");
                    #[cfg(debug_assertions)]
                    self.validate_conflict_explanation(_reasons);
                    self.conflict_count += 1;
                    return result;
                }
                TheoryResult::NeedLemmas(lemmas) => {
                    tracing::debug!(count = lemmas.len(), "arrays check: ROW1 batch lemmas");
                    batched_lemmas.extend(lemmas);
                }
                _ => {
                    tracing::debug!("arrays check: ROW1 non-sat result");
                }
            }
        }

        // Check self-store: store(a, i, v) = a implies select(a, i) = v (Fix for #920)
        if let Some(result) = self.check_self_store() {
            match result {
                TheoryResult::Unsat(ref _reasons) => {
                    tracing::debug!("arrays check: self-store conflict");
                    #[cfg(debug_assertions)]
                    self.validate_conflict_explanation(_reasons);
                    self.conflict_count += 1;
                    return result;
                }
                TheoryResult::NeedLemmas(lemmas) => {
                    tracing::debug!(
                        count = lemmas.len(),
                        "arrays check: self-store batch lemmas"
                    );
                    batched_lemmas.extend(lemmas);
                }
                _ => {
                    tracing::debug!("arrays check: self-store non-sat result");
                }
            }
        }

        // Check ROW2 downward: queued `(store, select)` pairs
        if let Some(result) = self.check_row2() {
            match result {
                TheoryResult::Unsat(ref _reasons) => {
                    tracing::debug!("arrays check: ROW2 conflict");
                    #[cfg(debug_assertions)]
                    self.validate_conflict_explanation(_reasons);
                    self.conflict_count += 1;
                    return result;
                }
                TheoryResult::NeedLemmas(lemmas) => {
                    tracing::debug!(count = lemmas.len(), "arrays check: ROW2 batch lemmas");
                    batched_lemmas.extend(lemmas);
                }
                TheoryResult::NeedModelEquality(req) => {
                    tracing::debug!("arrays check: ROW2 NeedModelEquality");
                    model_eq_requests.push(req);
                }
                TheoryResult::NeedModelEqualities(reqs) => {
                    tracing::debug!(count = reqs.len(), "arrays check: ROW2 NeedModelEqualities");
                    model_eq_requests.extend(reqs);
                }
                _ => {
                    tracing::debug!("arrays check: ROW2 non-sat result");
                }
            }
        }

        // Expensive O(n²) checks: deferred to final_check() when the combined
        // solver will call it at fixpoint. In standalone mode (unit tests, or when
        // defer_expensive_checks is false), run them here for correctness (#6282).
        if !self.defer_expensive_checks {
            if let Some(conflict) =
                self.check_expensive_axioms(&mut batched_lemmas, &mut model_eq_requests)
            {
                return conflict;
            }
        }

        // Check const-array reads (event-driven via pending_const_reads queue)
        if let Some(result) = self.check_const_array_read() {
            match result {
                TheoryResult::Unsat(ref _reasons) => {
                    tracing::debug!("arrays check: const-array-read conflict");
                    #[cfg(debug_assertions)]
                    self.validate_conflict_explanation(_reasons);
                    self.conflict_count += 1;
                    return result;
                }
                TheoryResult::NeedLemmas(lemmas) => {
                    tracing::debug!(
                        count = lemmas.len(),
                        "arrays check: const-array-read batch lemmas"
                    );
                    batched_lemmas.extend(lemmas);
                }
                _ => {
                    tracing::debug!("arrays check: const-array-read non-sat result");
                }
            }
        }

        // Deduplicate batched ROW2 lemmas: multiple ROW2 pairs may produce
        // overlapping lemmas. Canonicalize clause literal order then deduplicate.
        for lemma in &mut batched_lemmas {
            lemma.clause.sort_by_key(|lit| (lit.term.0, lit.value));
        }
        let pre_dedup = batched_lemmas.len();
        {
            let mut seen = HashSet::new();
            batched_lemmas.retain(|lemma| seen.insert(lemma.clause.clone()));
        }

        // Also filter out lemmas already emitted in a prior check() call.
        batched_lemmas.retain(|lemma| !self.applied_theory_lemmas.contains(&lemma.clause));

        if pre_dedup != batched_lemmas.len() {
            tracing::debug!(
                pre_dedup,
                post_dedup = batched_lemmas.len(),
                "arrays check: deduplicated batched lemmas"
            );
        }

        // Return batched ROW2 lemmas (highest priority — they constrain search).
        if !batched_lemmas.is_empty() {
            tracing::debug!(
                count = batched_lemmas.len(),
                "arrays check: returning batched ROW2 lemmas"
            );
            return TheoryResult::NeedLemmas(batched_lemmas);
        }

        if !model_eq_requests.is_empty() {
            return match model_eq_requests.len() {
                1 => TheoryResult::NeedModelEquality(
                    model_eq_requests
                        .pop()
                        .expect("invariant: len checked above"),
                ),
                _ => TheoryResult::NeedModelEqualities(model_eq_requests),
            };
        }

        tracing::debug!("arrays check: sat");
        TheoryResult::Sat
    }

    /// Run expensive O(n²) axiom checks that are deferred to final_check() in
    /// combined solver mode. Returns `Some(conflict)` on Unsat for early exit.
    fn check_expensive_axioms(
        &mut self,
        batched_lemmas: &mut Vec<TheoryLemma>,
        model_eq_requests: &mut Vec<ModelEqualityRequest>,
    ) -> Option<TheoryResult> {
        // ROW2 upward (axiom 2b)
        if let Some(result) = self.check_row2_upward_with_guidance() {
            match result {
                TheoryResult::Unsat(ref _reasons) => {
                    tracing::debug!("arrays check: ROW2-upward conflict");
                    #[cfg(debug_assertions)]
                    self.validate_conflict_explanation(_reasons);
                    self.conflict_count += 1;
                    return Some(result);
                }
                TheoryResult::NeedLemmas(lemmas) => {
                    tracing::debug!(
                        count = lemmas.len(),
                        "arrays check: ROW2-upward batch lemmas"
                    );
                    batched_lemmas.extend(lemmas);
                }
                TheoryResult::NeedModelEquality(req) => {
                    tracing::debug!("arrays check: ROW2-upward NeedModelEquality");
                    model_eq_requests.push(req);
                }
                TheoryResult::NeedModelEqualities(reqs) => {
                    tracing::debug!(
                        count = reqs.len(),
                        "arrays check: ROW2-upward NeedModelEqualities"
                    );
                    model_eq_requests.extend(reqs);
                }
                _ => {}
            }
        }

        // ROW2 extended via store chain following
        if let Some(result) = self.check_row2_extended() {
            match result {
                TheoryResult::Unsat(ref _reasons) => {
                    tracing::debug!("arrays check: ROW2-extended conflict");
                    #[cfg(debug_assertions)]
                    self.validate_conflict_explanation(_reasons);
                    self.conflict_count += 1;
                    return Some(result);
                }
                TheoryResult::NeedLemmas(lemmas) => {
                    tracing::debug!(
                        count = lemmas.len(),
                        "arrays check: ROW2-extended batch lemmas"
                    );
                    batched_lemmas.extend(lemmas);
                }
                _ => {
                    tracing::debug!("arrays check: ROW2-extended non-sat result");
                }
            }
        }

        // Nested select conflicts
        if let Some(result) = self.check_nested_select_conflicts() {
            match result {
                TheoryResult::Unsat(ref _reasons) => {
                    tracing::debug!("arrays check: nested-select conflict");
                    #[cfg(debug_assertions)]
                    self.validate_conflict_explanation(_reasons);
                    self.conflict_count += 1;
                    return Some(result);
                }
                TheoryResult::NeedLemmas(lemmas) => {
                    tracing::debug!(
                        count = lemmas.len(),
                        "arrays check: nested-select batch lemmas"
                    );
                    batched_lemmas.extend(lemmas);
                }
                _ => {
                    tracing::debug!("arrays check: nested-select non-sat result");
                }
            }
        }

        // Check store chain resolution
        if let Some(result) = self.check_store_chain_resolution() {
            match result {
                TheoryResult::Unsat(ref _reasons) => {
                    tracing::debug!("arrays check: store-chain conflict");
                    #[cfg(debug_assertions)]
                    self.validate_conflict_explanation(_reasons);
                    self.conflict_count += 1;
                    return Some(result);
                }
                TheoryResult::NeedLemmas(lemmas) => {
                    tracing::debug!(
                        count = lemmas.len(),
                        "arrays check: store-chain batch lemmas"
                    );
                    batched_lemmas.extend(lemmas);
                }
                _ => {
                    tracing::debug!("arrays check: store-chain non-sat result");
                }
            }
        }

        // Check conflicting store equalities
        if let Some(result) = self.check_conflicting_store_equalities() {
            match result {
                TheoryResult::Unsat(ref _reasons) => {
                    tracing::debug!("arrays check: conflicting-store-eq conflict");
                    #[cfg(debug_assertions)]
                    self.validate_conflict_explanation(_reasons);
                    self.conflict_count += 1;
                    return Some(result);
                }
                TheoryResult::NeedLemmas(lemmas) => {
                    tracing::debug!(
                        count = lemmas.len(),
                        "arrays check: conflicting-store-eq batch lemmas"
                    );
                    batched_lemmas.extend(lemmas);
                }
                _ => {
                    tracing::debug!("arrays check: conflicting-store-eq non-sat result");
                }
            }
        }

        // Check array equality implications
        if let Some(result) = self.check_array_equality() {
            match result {
                TheoryResult::Unsat(ref _reasons) => {
                    tracing::debug!("arrays check: array-equality conflict");
                    #[cfg(debug_assertions)]
                    self.validate_conflict_explanation(_reasons);
                    self.conflict_count += 1;
                    return Some(result);
                }
                TheoryResult::NeedLemmas(lemmas) => {
                    tracing::debug!(
                        count = lemmas.len(),
                        "arrays check: array-equality batch lemmas"
                    );
                    batched_lemmas.extend(lemmas);
                }
                _ => {
                    tracing::debug!("arrays check: array-equality non-sat result");
                }
            }
        }

        None
    }
}
