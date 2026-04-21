// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Quotient chain construction for clause factorization.
//!
//! Builds a chain of quotient levels starting from a seed factor literal.
//! Each level identifies clauses that share an additional factor literal
//! while preserving their quotient structure.
//!
//! Reference: CaDiCaL `factor.cpp` — `first_factor`, `next_factor`, `flush`.

use crate::clause_arena::ClauseArena;
use crate::literal::Literal;
use crate::occ_list::OccList;

use super::{Factor, MARK_FACTOR, MARK_NOUNTED, MARK_QUOTIENT, MIN_FACTOR_MATCHES};

/// One level in the quotient chain.
pub(super) struct QuotientLevel {
    /// The factor literal at this level.
    pub factor: Literal,
    /// Clause indices in the clause_db that belong to this quotient level.
    pub clause_indices: Vec<usize>,
    /// For level k > 0: `matches[i]` is the index in level k-1's `clause_indices`
    /// that generated `clause_indices[i]`. Used by `flush_unmatched_clauses` to
    /// compact all levels to the same size. CaDiCaL: `Quotient::matches`.
    pub matches: Vec<usize>,
}

impl Factor {
    /// Build a chain of quotient levels for a starting factor literal.
    ///
    /// Level 0: clauses containing `first_factor`.
    /// Level k: clauses containing all factors[0..=k], filtered to same-size
    ///          groups where they differ only in the factor literal.
    ///
    /// Returns a chain of `QuotientLevel`s.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn build_quotient_chain(
        &mut self,
        clause_db: &ClauseArena,
        occ: &OccList,
        vals: &[i8],
        first_factor: Literal,
        eligible: &[usize],
        deleted: &[bool],
        ticks: &mut u64,
        effort_limit: u64,
    ) -> Vec<QuotientLevel> {
        let mut chain: Vec<QuotientLevel> = Vec::new();

        // Level 0: all eligible clauses (they all contain first_factor).
        chain.push(QuotientLevel {
            factor: first_factor,
            clause_indices: eligible.to_vec(),
            matches: Vec::new(), // level 0 has no predecessor
        });

        self.mark(first_factor, MARK_FACTOR);

        // Iteratively find next factors.
        loop {
            if *ticks > effort_limit {
                break;
            }

            let last_clauses = &chain
                .last()
                .expect("invariant: chain has initial level pushed before loop")
                .clause_indices;
            if last_clauses.len() < MIN_FACTOR_MATCHES {
                break;
            }

            let next = self.find_next_factor(clause_db, occ, vals, last_clauses, deleted, ticks);
            match next {
                Some((next_lit, matching_clauses, match_indices)) => {
                    self.mark(next_lit, MARK_FACTOR);
                    chain.push(QuotientLevel {
                        factor: next_lit,
                        clause_indices: matching_clauses,
                        matches: match_indices,
                    });
                }
                None => break,
            }
        }

        // Clear factor marks.
        for level in &chain {
            self.unmark(level.factor, MARK_FACTOR);
        }

        chain
    }

    /// Find the next factor literal for the quotient chain.
    ///
    /// Scans clauses in the last quotient level for literals that:
    /// - Are not already marked as factors
    /// - Appear in at least `MIN_FACTOR_MATCHES` clauses from the last level
    ///   with compatible quotient structure (same size, same quotient lits,
    ///   differing only in one non-factor literal).
    ///
    /// Returns the best next factor, clause indices that match it, and
    /// match indices (position in `last_clauses` that generated each match).
    fn find_next_factor(
        &mut self,
        clause_db: &ClauseArena,
        occ: &OccList,
        vals: &[i8],
        last_clauses: &[usize],
        deleted: &[bool],
        ticks: &mut u64,
    ) -> Option<(Literal, Vec<usize>, Vec<usize>)> {
        // For each clause in last_clauses, mark its quotient (non-factor) literals.
        // Find a "minimum" literal in the quotient to use as an occurrence list probe.
        // For each other clause sharing that min literal and same size, check if
        // it differs in exactly one non-factor literal (the candidate next factor).

        // Count occurrences of candidate next-factor literals.
        // Reuse self.counts (pre-allocated) instead of per-call allocation (#3366).
        // Take ownership temporarily to avoid borrow conflict with self.marks.
        let mut counts = std::mem::take(&mut self.counts);
        let mut counted: Vec<Literal> = Vec::new();
        let mut nounted: Vec<Literal> = Vec::new();

        for &ci in last_clauses {
            *ticks += 1;
            if deleted[ci] {
                continue;
            }
            if clause_db.is_empty_clause(ci) {
                continue;
            }
            if Self::clause_satisfied(clause_db.literals(ci), vals) {
                continue;
            }
            let lits = clause_db.literals(ci);

            // Find the non-factor literals (quotient) and the minimum-occ one.
            let mut min_lit: Option<Literal> = None;
            let mut min_occ = usize::MAX;
            let mut factor_count = 0u32;

            for &lit in lits {
                if self.is_marked(lit, MARK_FACTOR) {
                    factor_count += 1;
                    if factor_count > 1 {
                        break; // Clause has multiple factor lits — skip.
                    }
                } else {
                    self.mark(lit, MARK_QUOTIENT);
                    let occ_count = occ.count(lit);
                    if occ_count < min_occ {
                        min_occ = occ_count;
                        min_lit = Some(lit);
                    }
                }
            }

            if factor_count == 1 {
                if let Some(ml) = min_lit {
                    let clause_size = clause_db.len_of(ci);
                    // Scan occurrence list of min_lit for clauses matching the quotient.
                    for &di in occ.get(ml) {
                        *ticks += 1;
                        if di == ci || deleted[di] {
                            continue;
                        }
                        if clause_db.is_empty_clause(di)
                            || clause_db.is_learned(di)
                            || clause_db.len_of(di) != clause_size
                        {
                            continue;
                        }
                        if Self::clause_satisfied(clause_db.literals(di), vals) {
                            continue;
                        }
                        let d_lits = clause_db.literals(di);

                        // Check: d differs from ci in exactly one non-factor literal.
                        let mut next_candidate = None;
                        let mut valid = true;
                        for &lit in d_lits {
                            if self.is_marked(lit, MARK_QUOTIENT) {
                                continue;
                            }
                            if self.is_marked(lit, MARK_FACTOR) || self.is_marked(lit, MARK_NOUNTED)
                            {
                                valid = false;
                                break;
                            }
                            if next_candidate.is_some() {
                                valid = false;
                                break;
                            }
                            next_candidate = Some(lit);
                        }

                        if valid {
                            if let Some(nc) = next_candidate {
                                // nc is a candidate next factor.
                                let nc_idx = nc.index();
                                if nc_idx < counts.len() && counts[nc_idx] == 0 {
                                    counted.push(nc);
                                }
                                if nc_idx < counts.len() {
                                    counts[nc_idx] += 1;
                                }
                                self.mark(nc, MARK_NOUNTED);
                                nounted.push(nc);
                            }
                        }
                    }
                }
            }

            for &lit in &nounted {
                self.unmark(lit, MARK_NOUNTED);
            }
            nounted.clear();

            // Clear quotient marks.
            for &lit in lits {
                self.unmark(lit, MARK_QUOTIENT);
            }
        }

        // Find the best next factor: highest count, with tiebreak by occurrence list size.
        let mut best: Option<Literal> = None;
        let mut best_count = 0u32;
        let mut best_occ = 0usize;

        for &lit in &counted {
            let c = counts[lit.index()];
            if c < MIN_FACTOR_MATCHES as u32 {
                continue;
            }
            if c > best_count || (c == best_count && occ.count(lit) > best_occ) {
                best_count = c;
                best = Some(lit);
                best_occ = occ.count(lit);
            }
        }

        // Clear counts and restore buffer.
        for &lit in &counted {
            counts[lit.index()] = 0;
        }
        self.counts = counts;

        let next_lit = best?;

        // Collect clauses that match: for each clause in last_clauses, find its
        // partner clause containing next_lit instead of the original factor path.
        // This is CaDiCaL's `factorize_next()`.
        let mut matching: Vec<usize> = Vec::new();
        let mut match_indices: Vec<usize> = Vec::new();
        self.mark(next_lit, MARK_FACTOR); // Temporarily mark.

        for (last_idx, &ci) in last_clauses.iter().enumerate() {
            if deleted[ci] {
                continue;
            }
            if clause_db.is_empty_clause(ci) {
                continue;
            }
            if Self::clause_satisfied(clause_db.literals(ci), vals) {
                continue;
            }
            let lits = clause_db.literals(ci);
            let clause_size = clause_db.len_of(ci);

            let mut factor_count = 0u32;
            let mut min_lit: Option<Literal> = None;
            let mut min_occ = usize::MAX;

            for &lit in lits {
                if self.is_marked(lit, MARK_FACTOR) {
                    factor_count += 1;
                } else {
                    self.mark(lit, MARK_QUOTIENT);
                    let oc = occ.count(lit);
                    if oc < min_occ {
                        min_occ = oc;
                        min_lit = Some(lit);
                    }
                }
            }

            if factor_count == 1 {
                if let Some(ml) = min_lit {
                    for &di in occ.get(ml) {
                        if di == ci || deleted[di] {
                            continue;
                        }
                        if clause_db.is_empty_clause(di)
                            || clause_db.is_learned(di)
                            || clause_db.len_of(di) != clause_size
                        {
                            continue;
                        }
                        if Self::clause_satisfied(clause_db.literals(di), vals) {
                            continue;
                        }
                        let d_lits = clause_db.literals(di);
                        // Check: d has the same quotient but with next_lit instead of
                        // the factor from ci.
                        let mut ok = true;
                        for &lit in d_lits {
                            if self.is_marked(lit, MARK_QUOTIENT) || lit == next_lit {
                                continue;
                            }
                            // Any other non-quotient, non-next_lit literal disqualifies.
                            ok = false;
                            break;
                        }
                        if ok {
                            matching.push(di);
                            match_indices.push(last_idx);
                            break;
                        }
                    }
                }
            }

            for &lit in lits {
                self.unmark(lit, MARK_QUOTIENT);
            }
        }

        self.unmark(next_lit, MARK_FACTOR); // Clear temporary mark.

        if matching.len() >= MIN_FACTOR_MATCHES {
            Some((next_lit, matching, match_indices))
        } else {
            None
        }
    }
}

/// Compact previous quotient levels to only contain entries that matched
/// at level `current`. After flushing, all levels from 0 to `current` have
/// the same number of entries.
///
/// CaDiCaL reference: `factor.cpp:475-500` (`flush_unmatched_clauses`).
pub(super) fn flush_unmatched_clauses(chain: &mut [QuotientLevel], current: usize) {
    debug_assert!(current > 0, "cannot flush level 0");
    let prev = current - 1;
    let n = chain[current].clause_indices.len();
    debug_assert_eq!(n, chain[current].matches.len());

    for i in 0..n {
        let j = chain[current].matches[i];
        // Compact: move prev's entry [j] to position [i].
        chain[prev].clause_indices[i] = chain[prev].clause_indices[j];
        // Propagate match chain through previous levels.
        if prev > 0 {
            chain[prev].matches[i] = chain[prev].matches[j];
        }
        // Current level now maps to identity.
        chain[current].matches[i] = i;
    }
    // Truncate prev to matched size.
    chain[prev].clause_indices.truncate(n);
    if prev > 0 {
        chain[prev].matches.truncate(n);
    }
}

/// Find the best quotient depth for factoring.
///
/// At depth `d`, there are `d + 1` factors and `chain[d].clause_indices.len()` quotients.
/// Reduction = factors * quotients - factors - quotients.
/// Returns (best_depth, reduction).
pub(super) fn find_best_quotient(chain: &[QuotientLevel]) -> Option<(usize, i64)> {
    let mut best_idx = 0;
    let mut best_reduction: i64 = 0;

    for (i, level) in chain.iter().enumerate() {
        let factors = (i + 1) as i64;
        let quotients = level.clause_indices.len() as i64;
        let before = factors * quotients;
        let after = factors + quotients;
        let reduction = before - after;

        if reduction > best_reduction {
            best_reduction = reduction;
            best_idx = i;
        }
    }

    if best_reduction > 0 {
        Some((best_idx, best_reduction))
    } else {
        None
    }
}

/// Check if any two factors in the chain are complementary (f, ~f).
/// Returns (index_a, index_b) of the first complementary pair found.
pub(super) fn find_complementary_factors(factors: &[Literal]) -> Option<(usize, usize)> {
    for i in 0..factors.len() {
        for j in (i + 1)..factors.len() {
            if factors[i] == factors[j].negated() {
                return Some((i, j));
            }
        }
    }
    None
}
