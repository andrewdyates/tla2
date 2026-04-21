// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Deferred `final_check()` driver for `ArraySolver`.
//!
//! Extracted from `lib.rs` to reduce crate root size.
//! Contains the `final_check()` method that runs expensive O(n²) array
//! axiom checks deferred from `check()` (#6282 Packet 2).

use super::*;

impl ArraySolver<'_> {
    /// Deferred consistency checks that are too expensive for every `check()` call.
    ///
    /// Called by the combined theory solver when all theories report SAT and the
    /// Nelson-Oppen fixpoint has converged. Runs the O(n²) array axiom checks
    /// that were removed from `check()` for performance (#6282 Packet 2):
    ///
    /// - **ROW2 upward (axiom 2b):** `select(A, j) = select(store(A,i,v), j)` when `i ≠ j`.
    ///   Propagates selects from base arrays "up" to store results.
    /// - **ROW2 extended:** Store chain following for select pairs that normalize to
    ///   the same (base, index).
    /// - **Nested select conflicts:** Recursive simplification for 3D arrays.
    ///
    /// Reference: Z3's `theory_array::final_check_eh()` defers axiom 2b until
    /// the solver is otherwise stuck. This mirrors that pattern.
    pub fn final_check(&mut self) -> TheoryResult {
        self.populate_caches();

        self.final_check_call_count += 1;

        // #6546: Short-circuit when the equality/disequality graph and caches
        // haven't changed since the last final_check that returned Sat. The
        // O(selects^2) checks in check_row2_extended and check_nested_select_conflicts
        // dominate runtime on storeinv SAT benchmarks (e.g., 580ms/call for 152
        // selects). If no new equalities, disequalities, or terms appeared, the
        // sub-checks will return None again.
        let fc_snapshot = (
            self.eq_adj_version,
            self.diseq_set.len(),
            self.select_cache.len(),
            self.store_cache.len(),
            self.requested_model_eqs.len(),
        );
        if self.final_check_snapshot == Some(fc_snapshot) {
            return TheoryResult::Sat;
        }
        if self.select_cache.is_empty() && self.store_cache.is_empty() {
            self.final_check_snapshot = Some(fc_snapshot);
            return TheoryResult::Sat;
        }

        self.build_equiv_class_cache();

        tracing::debug!(
            call = self.final_check_call_count,
            selects = self.select_cache.len(),
            stores = self.store_cache.len(),
            diseqs = self.diseq_set.len(),
            eq_adj_ver = self.eq_adj_version,
            "array final_check"
        );

        // #6820: Accumulate model equality requests across ALL sub-checks so
        // they are returned as a single batch. Previously each sub-check returned
        // early on NeedModelEquality, causing O(rounds) re-solves where each round
        // only discovered a few new pairs. Batching reduces swap size-10 from
        // 45+ rounds to ~1-3 rounds by collecting requests from both
        // check_row2_upward_with_guidance and check_disjunctive_store_target_equalities
        // in one pass. Conflicts and lemmas still return immediately.
        let mut model_eq_requests: Vec<ModelEqualityRequest> = Vec::new();

        // (#6282 Phase A) ROW2 upward with guidance: check for conflicts AND
        // request NeedModelEquality for undecided index pairs. The dedup set
        // (requested_model_eqs) prevents infinite N-O fixpoint restarts by
        // ensuring each undecided pair is requested at most once per problem.
        if let Some(result) = self.check_row2_upward_with_guidance() {
            match result {
                TheoryResult::Unsat(_) => {
                    tracing::debug!("arrays final_check: ROW2-upward conflict");
                    self.conflict_count += 1;
                    return result;
                }
                TheoryResult::NeedLemmas(lemmas) => {
                    tracing::debug!(
                        count = lemmas.len(),
                        "arrays final_check: ROW2-upward lemma batch"
                    );
                    return TheoryResult::NeedLemmas(lemmas);
                }
                TheoryResult::NeedModelEquality(req) => {
                    tracing::debug!("arrays final_check: ROW2-upward NeedModelEquality (batching)");
                    model_eq_requests.push(req);
                }
                TheoryResult::NeedModelEqualities(reqs) => {
                    tracing::debug!(
                        count = reqs.len(),
                        "arrays final_check: ROW2-upward NeedModelEqualities (batching)"
                    );
                    model_eq_requests.extend(reqs);
                }
                _ => {}
            }
        }

        // ROW2 extended via store chain following.
        if let Some(result) = self.check_row2_extended() {
            match result {
                TheoryResult::Unsat(_) => {
                    tracing::debug!("arrays final_check: ROW2-extended conflict");
                    self.conflict_count += 1;
                    return result;
                }
                TheoryResult::NeedLemmas(lemmas) => {
                    tracing::debug!(
                        count = lemmas.len(),
                        "arrays final_check: ROW2-extended lemma batch"
                    );
                    return TheoryResult::NeedLemmas(lemmas);
                }
                _ => {
                    tracing::debug!("arrays final_check: ROW2-extended non-sat result");
                }
            }
        }

        // Nested select conflicts (3D arrays via recursive simplification).
        if let Some(result) = self.check_nested_select_conflicts() {
            match result {
                TheoryResult::Unsat(_) => {
                    tracing::debug!("arrays final_check: nested-select conflict");
                    self.conflict_count += 1;
                    return result;
                }
                TheoryResult::NeedLemmas(lemmas) => {
                    tracing::debug!(
                        count = lemmas.len(),
                        "arrays final_check: nested-select lemma batch"
                    );
                    return TheoryResult::NeedLemmas(lemmas);
                }
                _ => {
                    tracing::debug!("arrays final_check: nested-select non-sat result");
                }
            }
        }

        // #6546: Store chain resolution, conflicting store equalities, and
        // array equality checks are deferred from check() to here in combined
        // solver mode. These do full cache scans (O(N*C) to O(N^2)) and are
        // too expensive to run on every check() call.
        if let Some(result) = self.check_store_chain_resolution() {
            match result {
                TheoryResult::Unsat(_) => {
                    tracing::debug!("arrays final_check: store-chain conflict");
                    self.conflict_count += 1;
                    return result;
                }
                TheoryResult::NeedLemmas(lemmas) => {
                    tracing::debug!(
                        count = lemmas.len(),
                        "arrays final_check: store-chain lemma batch"
                    );
                    return TheoryResult::NeedLemmas(lemmas);
                }
                _ => {
                    tracing::debug!("arrays final_check: store-chain non-sat result");
                }
            }
        }

        if let Some(result) = self.check_conflicting_store_equalities() {
            match result {
                TheoryResult::Unsat(_) => {
                    tracing::debug!("arrays final_check: conflicting-store-eq conflict");
                    self.conflict_count += 1;
                    return result;
                }
                TheoryResult::NeedLemmas(lemmas) => {
                    tracing::debug!(
                        count = lemmas.len(),
                        "arrays final_check: conflicting-store-eq lemma batch"
                    );
                    return TheoryResult::NeedLemmas(lemmas);
                }
                _ => {
                    tracing::debug!("arrays final_check: conflicting-store-eq non-sat result");
                }
            }
        }

        if let Some(result) = self.check_disjunctive_store_target_equalities() {
            match result {
                TheoryResult::Unsat(_) => {
                    tracing::debug!("arrays final_check: disjunctive-store-target conflict");
                    self.conflict_count += 1;
                    return result;
                }
                TheoryResult::NeedLemmas(lemmas) => {
                    tracing::debug!(
                        count = lemmas.len(),
                        "arrays final_check: disjunctive-store-target lemma batch"
                    );
                    return TheoryResult::NeedLemmas(lemmas);
                }
                TheoryResult::NeedModelEquality(req) => {
                    tracing::debug!(
                        "arrays final_check: disjunctive-store-target NeedModelEquality (batching)"
                    );
                    model_eq_requests.push(req);
                }
                TheoryResult::NeedModelEqualities(reqs) => {
                    tracing::debug!(
                        count = reqs.len(),
                        "arrays final_check: disjunctive-store-target NeedModelEqualities (batching)"
                    );
                    model_eq_requests.extend(reqs);
                }
                _ => {
                    tracing::debug!("arrays final_check: disjunctive-store-target non-sat result");
                }
            }
        }

        if let Some(result) = self.check_array_equality() {
            match result {
                TheoryResult::Unsat(_) => {
                    tracing::debug!("arrays final_check: array-equality conflict");
                    self.conflict_count += 1;
                    return result;
                }
                TheoryResult::NeedLemmas(lemmas) => {
                    tracing::debug!(
                        count = lemmas.len(),
                        "arrays final_check: array-equality lemma batch"
                    );
                    return TheoryResult::NeedLemmas(lemmas);
                }
                _ => {
                    tracing::debug!("arrays final_check: array-equality non-sat result");
                }
            }
        }

        // #6820: Return accumulated model equality requests as one batch.
        // This reduces the number of SAT re-solve rounds for problems with
        // many undecided index pairs (swap size-10: 45 pairs).
        if !model_eq_requests.is_empty() {
            tracing::debug!(
                count = model_eq_requests.len(),
                "arrays final_check: returning batched model equality requests"
            );
            return match model_eq_requests.len() {
                1 => TheoryResult::NeedModelEquality(
                    model_eq_requests
                        .pop()
                        .expect("invariant: len checked above"),
                ),
                _ => TheoryResult::NeedModelEqualities(model_eq_requests),
            };
        }

        // All sub-checks passed — save snapshot for short-circuit (#6546).
        self.final_check_snapshot = Some(fc_snapshot);
        TheoryResult::Sat
    }
}
