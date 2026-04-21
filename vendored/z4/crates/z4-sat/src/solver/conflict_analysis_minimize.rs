// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Clause minimization for conflict analysis.
//!
//! CaDiCaL-style minimization with poison/removable marking to cache
//! results and avoid redundant work. Also includes LRAT chain computation
//! for literals removed by shrink/minimize.

use super::*;

impl Solver {
    /// Clear per-level seen tracking (CaDiCaL: `clear_analyzed_levels`).
    ///
    /// Resets `level_seen_count` and `level_seen_trail` for all levels that
    /// were touched during the most recent conflict analysis. Uses a dirty
    /// list (`level_seen_to_clear`) for O(touched) cleanup instead of O(max_level).
    pub(super) fn clear_level_seen(&mut self) {
        for &lvl in &self.min.level_seen_to_clear {
            let l = lvl as usize;
            if l < self.min.level_seen_count.len() {
                self.min.level_seen_count[l] = 0;
                self.min.level_seen_trail[l] = usize::MAX;
            }
        }
        self.min.level_seen_to_clear.clear();
    }

    /// Track a newly-seen literal's decision level for minimize early-aborts.
    ///
    /// CaDiCaL `analyze_literal` (analyze.cpp:303-309): increments `seen.count`
    /// and updates `seen.trail` (minimum trail position) for the literal's level.
    #[inline]
    pub(super) fn track_level_seen(&mut self, var_level: u32, var_idx: usize) {
        let lvl = var_level as usize;
        // Grow tracking arrays if needed (decision levels can exceed initial capacity).
        if lvl >= self.min.level_seen_count.len() {
            self.min.level_seen_count.resize(lvl + 1, 0);
            self.min.level_seen_trail.resize(lvl + 1, usize::MAX);
        }
        if self.min.level_seen_count[lvl] == 0 {
            self.min.level_seen_to_clear.push(var_level);
        }
        self.min.level_seen_count[lvl] += 1;
        let tpos = self.var_data[var_idx].trail_pos as usize;
        if tpos < self.min.level_seen_trail[lvl] {
            self.min.level_seen_trail[lvl] = tpos;
        }
    }

    /// Minimize the learned clause by removing redundant literals.
    ///
    /// Uses CaDiCaL-style minimization with poison/removable marking to cache
    /// results and avoid redundant work. A literal is redundant if it can be
    /// derived from other literals in the learned clause through resolution.
    pub(super) fn minimize_learned_clause(&mut self) {
        // Copy learned literals to clause_buf (reusable scratch buffer) to break
        // the borrow conflict between self.conflict and self.minimize_* arrays.
        // clause_buf's capacity persists across conflicts — no heap allocation.
        {
            let buf = self.conflict.clause_buf_mut();
            buf.clear();
        }
        let len = self.conflict.learned_count();
        for i in 0..len {
            let lit = self.conflict.learned_at(i);
            self.conflict.clause_buf_mut().push(lit);
        }

        // CaDiCaL minimize.cpp:205-209: sort by trail position (ascending)
        // before minimization. Earlier-assigned literals are checked first;
        // their antecedents are more likely to be already marked removable
        // or visited, establishing base cases sooner for later recursion.
        {
            let var_data = &self.var_data;
            self.conflict
                .clause_buf_mut()
                .sort_unstable_by_key(|lit| var_data[lit.variable().index()].trail_pos);
        }

        // Mark all learned literals as "visited" (in the clause) and populate
        // per-level seen counters + earliest trail position (CaDiCaL l.seen).
        let buf_len = self.conflict.clause_buf_mut().len();
        for i in 0..buf_len {
            let lit = self.conflict.clause_buf_mut()[i];
            let var_idx = lit.variable().index();
            self.min.minimize_flags[var_idx] |= MIN_VISITED;
            self.min.minimize_to_clear.push(var_idx);

            let lev = self.var_data[var_idx].level as usize;
            if self.min.minimize_level_count[lev] == 0 {
                self.min.minimize_levels_to_clear.push(lev as u32);
            }
            self.min.minimize_level_count[lev] += 1;
            let tp = self.var_data[var_idx].trail_pos as usize;
            if tp < self.min.minimize_level_trail[lev] {
                self.min.minimize_level_trail[lev] = tp;
            }
        }

        // clause_buf is already sorted by trail position (line 1030 above).
        // The marking loop above only reads clause_buf values — it does not
        // modify, remove, or reorder elements, so the sort order is preserved.

        // Run redundancy checks from the scratch buffer copy.
        // After this, minimize_removable[var] is true for literals that can be
        // removed; level-0 literals are also redundant but aren't in removable.
        // CaDiCaL minimize.cpp:134: progressively mark non-removable literals
        // as "keep" so later literals can use them as recursion base cases.
        for i in 0..buf_len {
            let lit = self.conflict.clause_buf_mut()[i];
            let redundant = self.is_redundant_cached(lit, 0);
            if !redundant {
                let v = lit.variable().index();
                self.min.minimize_flags[v] |= MIN_KEEP;
            }
        }

        // Compact learned in-place: retain only non-redundant literals.
        let var_data = &self.var_data;
        let flags = &self.min.minimize_flags;
        self.conflict.retain_learned(|lit| {
            let var_idx = lit.variable().index();
            var_data[var_idx].level != 0 && (flags[var_idx] & MIN_REMOVABLE == 0)
        });

        // Post-minimize: learned clause must be non-empty (UIP is separate,
        // but if all learned lits were removed, we still have a valid unit clause).
        // CaDiCaL: the learned clause can be empty (unit clause = just the UIP).

        // Clear all minimization state (CaDiCaL clear_minimized_literals)
        for &var_idx in &self.min.minimize_to_clear {
            self.min.minimize_flags[var_idx] = 0;
        }
        self.min.minimize_to_clear.clear();
        // Sparse reset of per-level tracking
        for &lev in &self.min.minimize_levels_to_clear {
            self.min.minimize_level_count[lev as usize] = 0;
            self.min.minimize_level_trail[lev as usize] = usize::MAX;
        }
        self.min.minimize_levels_to_clear.clear();
        // CaDiCaL analyze.cpp:448-450: all minimization flags cleared
        debug_assert!(
            self.min.minimize_to_clear.is_empty(),
            "BUG: minimize_to_clear not empty after clear"
        );
    }

    /// Check if a literal is redundant using cached poison/removable marks.
    ///
    /// Uses depth limiting and caches results for efficiency.
    /// Returns true if the literal can be removed from the learned clause.
    pub(super) fn is_redundant_cached(&mut self, lit: Literal, depth: u32) -> bool {
        let var_idx = lit.variable().index();

        // Variable being checked for redundancy must be assigned
        debug_assert!(
            self.var_is_assigned(var_idx),
            "BUG: is_redundant_cached for unassigned var {var_idx}"
        );

        // Level 0 literals are always redundant (they're always false)
        if self.var_data[var_idx].level == 0 {
            return true;
        }

        // Check cached results — order matches CaDiCaL minimize.cpp:22-24:
        // removable and keep are checked BEFORE poison. A variable can have
        // both poison and keep set (poison from failed recursive check, keep
        // from progressive marking in minimize_clause). Keep must win because
        // the literal IS in the clause and is a valid dependency termination.
        let mf = self.min.minimize_flags[var_idx];
        if mf & MIN_REMOVABLE != 0 {
            return true;
        }
        // CaDiCaL minimize.cpp:22: f.keep — literal confirmed kept in the
        // learned clause. Keep takes priority over poison.
        if mf & MIN_KEEP != 0 {
            return true;
        }
        if mf & MIN_POISON != 0 {
            return false;
        }

        // CaDiCaL minimize.cpp:24: current-level literals cannot be minimized
        // (the only path through current-level literals is the 1UIP itself).
        if self.var_data[var_idx].level == self.decision_level {
            return false;
        }

        // For recursive calls (depth > 0): if literal is already in learned clause,
        // we've reached a "kept" literal which is good - this path terminates.
        // For top-level calls (depth == 0): we're checking if THIS literal can be
        // removed, so don't return early just because it's in the clause.
        if depth > 0 && mf & MIN_VISITED != 0 {
            return true;
        }

        // Decision variables and binary literal reasons cannot be minimized.
        // Binary literal reasons (#8034) have no arena clause to recurse into.
        let reason_kind = self.var_reason_kind(var_idx);
        let reason = match reason_kind {
            ReasonKind::Decision => return false,
            ReasonKind::BinaryLiteral(reason_lit) => {
                // Binary literal reason: single antecedent literal.
                // Early-abort and depth checks still apply.

                // Early-abort checks (same as clause path below)
                {
                    let var_level = self.var_data[var_idx].level as usize;
                    let have_level_data = if !self.min.level_seen_to_clear.is_empty()
                        && var_level < self.min.level_seen_count.len()
                    {
                        Some((
                            self.min.level_seen_count[var_level],
                            self.min.level_seen_trail[var_level],
                        ))
                    } else if !self.min.minimize_levels_to_clear.is_empty()
                        && var_level < self.min.minimize_level_count.len()
                    {
                        Some((
                            self.min.minimize_level_count[var_level],
                            self.min.minimize_level_trail[var_level],
                        ))
                    } else {
                        None
                    };

                    if let Some((seen_count, seen_trail)) = have_level_data {
                        if depth == 0 && seen_count < 2 {
                            return false;
                        }
                        if (self.var_data[var_idx].trail_pos as usize) <= seen_trail {
                            return false;
                        }
                    }
                }

                if depth > self.min.minimize_depth_limit {
                    return false;
                }

                if self.min.minimize_flags[var_idx] & MIN_VISITED == 0 {
                    self.min.minimize_flags[var_idx] |= MIN_VISITED;
                    self.min.minimize_to_clear.push(var_idx);
                }

                self.search_ticks[usize::from(self.stable_mode)] += 1;

                // Single antecedent: check if the reason literal is redundant.
                if !self.is_redundant_cached(reason_lit, depth + 1) {
                    self.min.minimize_flags[var_idx] |= MIN_POISON;
                    return false;
                }

                self.min.minimize_flags[var_idx] |= MIN_REMOVABLE;
                return true;
            }
            ReasonKind::Clause(r) => r,
        };

        // Early-abort checks (CaDiCaL minimize.cpp:26-30).
        //
        // CaDiCaL reads `control[v.level].seen.count` and `.seen.trail` which
        // are populated for ALL variables seen during `analyze_literal` --
        // including current-level and resolved-away variables. Z4 mirrors this
        // via `level_seen_count` / `level_seen_trail` (set by `track_level_seen`
        // during conflict analysis). Using the analysis-phase data instead of
        // the minimize-phase data (which only covers learned-clause literals)
        // provides:
        //   1. Higher counts -- Knuth abort fires less often, enabling more
        //      minimization attempts on levels with resolved-away variables
        //   2. Lower trail positions -- trail-position abort fires less often,
        //      enabling minimization of variables assigned after resolved-away
        //      variables on the same level
        //
        // When analysis-phase data is available (normal pipeline:
        // analyze -> minimize -> clear_level_seen), prefer it. Fall back to
        // minimize-phase data for direct minimize_learned_clause() calls
        // (unit tests, isolated contexts).
        {
            let var_level = self.var_data[var_idx].level as usize;
            // Prefer analysis-phase data (CaDiCaL parity); fall back to
            // minimize-phase data if analysis-phase is not populated.
            let have_level_data = if !self.min.level_seen_to_clear.is_empty()
                && var_level < self.min.level_seen_count.len()
            {
                Some((
                    self.min.level_seen_count[var_level],
                    self.min.level_seen_trail[var_level],
                ))
            } else if !self.min.minimize_levels_to_clear.is_empty()
                && var_level < self.min.minimize_level_count.len()
            {
                Some((
                    self.min.minimize_level_count[var_level],
                    self.min.minimize_level_trail[var_level],
                ))
            } else {
                None
            };

            if let Some((seen_count, seen_trail)) = have_level_data {
                // Knuth's single-literal abort (CaDiCaL minimize.cpp:27-28):
                // if this is a top-level call and fewer than 2 literals from
                // this level were seen during analysis, minimization cannot
                // succeed (no other seen literal to serve as base case).
                if depth == 0 && seen_count < 2 {
                    return false;
                }
                // Trail-position abort (CaDiCaL minimize.cpp:29-30): if this
                // variable was assigned at or before the earliest seen literal
                // on its level, it cannot be resolved away.
                if (self.var_data[var_idx].trail_pos as usize) <= seen_trail {
                    return false;
                }
            }
        }

        // Depth limiting to prevent infinite recursion
        if depth > self.min.minimize_depth_limit {
            return false;
        }

        // Mark as visited for this minimization call (prevents infinite loops)
        if self.min.minimize_flags[var_idx] & MIN_VISITED == 0 {
            self.min.minimize_flags[var_idx] |= MIN_VISITED;
            self.min.minimize_to_clear.push(var_idx);
        }

        // Reason clause must have intact data. Clauses marked garbage via
        // mark_garbage_keep_data (eager subsumption) retain their literals.
        debug_assert!(
            !self.arena.is_empty_clause(reason.0 as usize),
            "BUG: reason clause {} for var {var_idx} is deleted during minimize",
            reason.0,
        );

        // CaDiCaL minimize.cpp:36: charge search tick per reason clause access.
        self.search_ticks[usize::from(self.stable_mode)] += 1;

        // Check all literals in the reason clause (iterate by index to avoid allocation)
        let clause_idx = reason.0 as usize;
        let clause_len = self.arena.len_of(clause_idx);

        for i in 0..clause_len {
            let reason_lit = self.arena.literal(clause_idx, i);
            let reason_var_idx = reason_lit.variable().index();

            // Skip the literal itself
            if reason_var_idx == var_idx {
                continue;
            }

            // Recursively check if this literal is redundant
            if !self.is_redundant_cached(reason_lit, depth + 1) {
                // Found a non-redundant literal - mark as poison
                self.min.minimize_flags[var_idx] |= MIN_POISON;
                return false;
            }
        }

        // All reason literals are redundant - mark as removable
        self.min.minimize_flags[var_idx] |= MIN_REMOVABLE;
        true
    }
}
