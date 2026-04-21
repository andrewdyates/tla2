// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Forward subsumption using equivalence-aware representatives.

use crate::clause_arena::ClauseArena;
use crate::literal::Literal;

use super::union_find::UnionFind;
use super::{debug_congruence_enabled, CongruenceClosure};

impl CongruenceClosure {
    /// Forward subsumption using equivalence-aware representatives.
    ///
    /// After congruence closure, clauses may become subsumed when equivalent
    /// literals are treated as identical. Example: (a, c) subsumes (b, c, d)
    /// when a ≡ b.
    ///
    /// Called from the solver wrapper AFTER proof emission is complete, because
    /// RUP checks need gate-defining clauses alive during decide/propagate.
    ///
    /// Reference: CaDiCaL congruence.cpp:4955-5073 forward_subsume_matching_clauses()
    #[allow(unreachable_code)] // Subsumption disabled (#7432) but implementation preserved
    pub(crate) fn forward_subsume_with_equivalences(
        &mut self,
        clauses: &mut ClauseArena,
        equivalence_edges: &[(Literal, Literal)],
    ) -> u64 {
        if equivalence_edges.is_empty() {
            return 0;
        }

        // Soundness gate (#7432): representative-based clause deletion has no
        // reconstruction plumbing. When it removes an irredundant original
        // clause, SAT finalization can fail closed with InvalidSatModel
        // because the original formula ledger no longer matches clause_db.
        // LRAT mode already disables this path for the same reason (#6270).
        // Until congruence subsumption records reconstructible deletions, keep
        // the pass off in all modes and let decompose consume the binary
        // equivalences without deleting clauses here.
        if debug_congruence_enabled() {
            eprintln!(
                "[congruence] forward subsumption skipped: no reconstruction support for representative-based deletions"
            );
        }
        let _ = clauses;
        return 0;

        // Build UF from equivalence edges.
        let num_lits = self.num_vars * 2;
        let mut uf = UnionFind::new(num_lits);
        for &(lhs, rhs) in equivalence_edges {
            let li = lhs.index();
            let ri = rhs.index();
            if li < num_lits && ri < num_lits {
                let _ = uf.union_lits(li, ri);
            }
        }
        let vals: Option<&[i8]> = None; // No level-0 vals in solver context
        let mut subsumed_count: u64 = 0;

        // Phase 1: Identify matchable variables (vars with non-trivial representative).
        let mut matchable = vec![false; self.num_vars];
        for var in 0..self.num_vars {
            let lit_idx = var * 2;
            if lit_idx >= num_lits {
                continue;
            }
            let repr = uf.find(lit_idx);
            if repr != lit_idx {
                matchable[var] = true;
                let repr_var = repr / 2;
                if repr_var < self.num_vars {
                    matchable[repr_var] = true;
                }
            }
        }

        // Phase 2: Build candidate list (non-binary irredundant with matchable vars).
        // Collect all clause indices first to avoid borrow conflict
        // (indices() borrows arena immutably, mark_garbage borrows mutably).
        let all_indices: Vec<usize> = clauses.indices().collect();
        let mut candidates: Vec<(usize, usize)> = Vec::new();
        let mut repr_buf: Vec<usize> = Vec::new();
        let mut marked = vec![false; num_lits];

        for idx in all_indices {
            if clauses.is_garbage(idx) {
                continue;
            }
            let len = clauses.len_of(idx);
            if len <= 2 || clauses.is_learned(idx) {
                continue;
            }

            repr_buf.clear();
            let mut contains_matchable = false;
            let mut is_tautology = false;

            for i in 0..len {
                let lit = clauses.literal(idx, i);
                let li = lit.index();
                // Skip false literals (level-0 assignments).
                if let Some(v) = vals {
                    if li < v.len() {
                        if v[li] < 0 {
                            continue;
                        }
                        if v[li] > 0 {
                            is_tautology = true;
                            break;
                        }
                    }
                }

                if li >= num_lits {
                    continue;
                }
                let repr = uf.find(li);
                if repr >= num_lits {
                    continue;
                }
                if marked[repr] {
                    continue; // duplicate representative
                }
                let neg_repr = repr ^ 1;
                if neg_repr < num_lits && marked[neg_repr] {
                    is_tautology = true;
                    break;
                }

                marked[repr] = true;
                repr_buf.push(repr);

                let var_idx = li / 2;
                if var_idx < self.num_vars && matchable[var_idx] {
                    contains_matchable = true;
                }
            }

            // Unmark.
            for &r in &repr_buf {
                marked[r] = false;
            }

            if is_tautology {
                clauses.mark_garbage_keep_data(idx);
                subsumed_count += 1;
                continue;
            }
            if !contains_matchable || repr_buf.is_empty() {
                continue;
            }

            candidates.push((idx, repr_buf.len()));
        }

        if candidates.is_empty() {
            return subsumed_count;
        }

        // Phase 3: Sort by representative count (smallest first = potential subsumers).
        candidates.sort_by_key(|&(_, count)| count);

        // Build occurrence lists indexed by representative literal.
        // CaDiCaL adds each non-subsumed clause to ONE occurrence list
        // (the least-occurring representative) to keep lists small.
        let mut occs: Vec<Vec<usize>> = vec![Vec::new(); num_lits];

        for &(clause_idx, _) in &candidates {
            if clauses.is_garbage(clause_idx) {
                continue;
            }

            // Mark all representative literals of this clause (index-based
            // access avoids borrowing the arena as a slice, allowing mutable
            // mark_garbage_keep_data below).
            repr_buf.clear();
            let clen = clauses.len_of(clause_idx);
            for i in 0..clen {
                let lit = clauses.literal(clause_idx, i);
                let li = lit.index();
                if let Some(v) = vals {
                    if li < v.len() && v[li] < 0 {
                        continue;
                    }
                }
                if li >= num_lits {
                    continue;
                }
                let repr = uf.find(li);
                if repr < num_lits && !marked[repr] {
                    marked[repr] = true;
                    repr_buf.push(repr);
                }
            }

            // Check occurrence lists for a subsuming clause.
            let mut found_subsuming = false;
            let mut least_occurring_repr = 0usize;
            let mut least_count = usize::MAX;

            'check: for &repr in &repr_buf {
                let occ_len = occs[repr].len();
                if occ_len < least_count {
                    least_count = occ_len;
                    least_occurring_repr = repr;
                }
                for &other_idx in &occs[repr] {
                    if clauses.is_garbage(other_idx) {
                        continue;
                    }
                    // Check if other_idx subsumes clause_idx:
                    // all representative literals of other_idx must be marked.
                    let olen = clauses.len_of(other_idx);
                    let mut all_marked = true;
                    for j in 0..olen {
                        let olit = clauses.literal(other_idx, j);
                        let oli = olit.index();
                        if let Some(v) = vals {
                            if oli < v.len() && v[oli] < 0 {
                                continue;
                            }
                        }
                        if oli >= num_lits {
                            all_marked = false;
                            break;
                        }
                        let orepr = uf.find(oli);
                        if orepr >= num_lits || !marked[orepr] {
                            all_marked = false;
                            break;
                        }
                    }
                    if all_marked {
                        clauses.mark_garbage_keep_data(clause_idx);
                        subsumed_count += 1;
                        found_subsuming = true;
                        break 'check;
                    }
                }
            }

            // Unmark.
            for &r in &repr_buf {
                marked[r] = false;
            }

            // If not subsumed, add to occurrence list at the least-occurring repr.
            if !found_subsuming && !repr_buf.is_empty() {
                occs[least_occurring_repr].push(clause_idx);
            }
        }

        if debug_congruence_enabled() && subsumed_count > 0 {
            eprintln!("[congruence] forward subsumed {subsumed_count} clauses via equivalences");
        }

        subsumed_count
    }

    /// Build literal map from union-find
    pub(super) fn build_lit_map(&self, uf: &mut UnionFind) -> Vec<Literal> {
        let num_lits = self.num_vars * 2;
        let mut lit_map = Vec::with_capacity(num_lits);

        for lit_idx in 0..num_lits {
            let rep_idx = uf.find(lit_idx);
            lit_map.push(Literal::from_index(rep_idx));
        }

        // Postcondition: every representative in the output map is a fixpoint.
        debug_assert!(
            lit_map.iter().all(|&rep| {
                let ri = rep.index();
                ri < num_lits && uf.find(ri) == ri
            }),
            "BUG: build_lit_map produced non-fixpoint representative"
        );
        lit_map
    }
}
