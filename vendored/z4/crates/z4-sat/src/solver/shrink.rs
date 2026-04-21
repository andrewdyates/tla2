// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Block-level clause shrinking (CaDiCaL shrink.cpp, Kissat shrink.c).
//!
//! After 1UIP conflict analysis, the learned clause may contain multiple
//! literals at the same decision level. Block-level shrinking attempts to
//! replace an entire "block" of same-level literals with a single "block UIP"
//! — a literal that implies all others at that level. This produces shorter
//! learned clauses than recursive minimization alone.
//!
//! Algorithm (`shrink=3` single-pass pipeline, matching Kissat/CaDiCaL):
//! 1. Sort learned clause by (decision level desc, trail position desc)
//!    — Kissat analyze.c:227-302
//! 2. Process blocks from the TAIL of the sorted clause (lowest levels first)
//!    so lower-level removability proofs warm the cache for higher blocks
//!    — Kissat shrink.c:371-377
//! 3. For each block of 2+ literals at the same level:
//!    a. Walk backward along the trail within that level, resolving reasons
//!    b. If block literals converge to a single literal, replace the block with it
//!    c. If resolution fails, fall back to per-literal minimization
//! 4. No flag reset. No second minimize pass. Removable/poison/keep caches
//!    persist across all blocks — Kissat minimize.c:175-178
//!
//! Reference: `reference/cadical/src/shrink.cpp` (507 lines)
//! Design: `designs/2026-03-23-clause-shrink-minimize-cadical-parity-gap.md`
//! Design: `designs/2026-03-23-issue-7862-shrink-removable-cache-promotion.md`

use super::*;

impl Solver {
    /// Shrink and minimize the learned clause in a single pass (`shrink=3`).
    ///
    /// Matches the Kissat/CaDiCaL `shrink=3` architecture:
    /// - Block-level shrinking with per-literal minimization fallback
    /// - Removable/poison/keep caches persist across all blocks
    /// - No flag reset between blocks, no second standalone minimize pass
    /// - Low-level blocks processed first to warm cache for higher blocks
    ///
    /// On block-UIP success, replaced literals are promoted to MIN_REMOVABLE
    /// (matching CaDiCaL `mark_shrinkable_as_removable`) while MIN_VISITED is
    /// cleared to maintain the soundness invariant that MIN_VISITED means
    /// "literal is currently in the learned clause."
    pub(super) fn shrink_and_minimize_learned_clause(&mut self) {
        if !self.shrink_enabled {
            self.minimize_learned_clause();
            return;
        }
        let learned_count = self.conflict.learned_count();
        if learned_count <= 1 {
            // Nothing to shrink for unit or binary clauses
            self.minimize_learned_clause();
            return;
        }

        // CaDiCaL shrink.cpp:427: at least one of minimize or shrink enabled
        debug_assert!(
            self.shrink_enabled,
            "BUG: shrink_and_minimize called but shrink_enabled is false",
        );

        // Set up MIN_VISITED for the learned clause literals.
        // This is needed so is_redundant_cached() can terminate recursion when
        // it reaches a literal that's in the clause. CaDiCaL does this at the
        // start of shrink_and_minimize_clause().
        for i in 0..learned_count {
            let lit = self.conflict.learned_at(i);
            let var_idx = lit.variable().index();
            if self.min.minimize_flags[var_idx] & MIN_VISITED == 0 {
                self.min.minimize_flags[var_idx] |= MIN_VISITED;
                self.min.minimize_to_clear.push(var_idx);
            }
        }
        // Also mark the asserting literal
        {
            let uip = self.conflict.asserting_literal();
            let var_idx = uip.variable().index();
            if self.min.minimize_flags[var_idx] & MIN_VISITED == 0 {
                self.min.minimize_flags[var_idx] |= MIN_VISITED;
                self.min.minimize_to_clear.push(var_idx);
            }
        }

        // Populate per-level minimize metadata BEFORE block processing.
        // This enables the Knuth single-literal abort and trail-position
        // abort during is_redundant_cached calls within the shrink phase,
        // eliminating the need for a post-shrink standalone minimize pass.
        // Reference: conflict_analysis_minimize.rs:91-100 (same logic).
        for i in 0..learned_count {
            let lit = self.conflict.learned_at(i);
            let var_idx = lit.variable().index();
            let lev = self.var_data[var_idx].level as usize;
            if lev >= self.min.minimize_level_count.len() {
                self.min.minimize_level_count.resize(lev + 1, 0);
                self.min.minimize_level_trail.resize(lev + 1, usize::MAX);
            }
            if self.min.minimize_level_count[lev] == 0 {
                self.min.minimize_levels_to_clear.push(lev as u32);
            }
            self.min.minimize_level_count[lev] += 1;
            let tp = self.var_data[var_idx].trail_pos as usize;
            if tp < self.min.minimize_level_trail[lev] {
                self.min.minimize_level_trail[lev] = tp;
            }
        }
        // Also include the asserting literal in per-level metadata.
        {
            let uip = self.conflict.asserting_literal();
            let var_idx = uip.variable().index();
            let lev = self.var_data[var_idx].level as usize;
            if lev >= self.min.minimize_level_count.len() {
                self.min.minimize_level_count.resize(lev + 1, 0);
                self.min.minimize_level_trail.resize(lev + 1, usize::MAX);
            }
            if self.min.minimize_level_count[lev] == 0 {
                self.min.minimize_levels_to_clear.push(lev as u32);
            }
            self.min.minimize_level_count[lev] += 1;
            let tp = self.var_data[var_idx].trail_pos as usize;
            if tp < self.min.minimize_level_trail[lev] {
                self.min.minimize_level_trail[lev] = tp;
            }
        }

        // Build a sortable representation: (level, trail_pos, literal_index)
        // We need to group by level and order by trail position within each level.
        let mut entries = std::mem::take(&mut self.ws_shrink_entries);
        entries.clear();
        for i in 0..learned_count {
            let lit = self.conflict.learned_at(i);
            let var_idx = lit.variable().index();
            // CaDiCaL shrink.cpp:68: each learned literal must be falsified
            debug_assert!(
                self.lit_val(lit) < 0,
                "BUG: learned literal {lit:?} at index {i} is not falsified (val={})",
                self.lit_val(lit),
            );
            let vd = self.var_data[var_idx];
            let lvl = vd.level;
            // CaDiCaL shrink.cpp:72: literal level must be > 0
            debug_assert!(
                lvl > 0,
                "BUG: learned literal {lit:?} at level 0 — should have been removed",
            );
            let tpos = vd.trail_pos as usize;
            // CaDiCaL shrink.cpp:113: trail position must be valid
            debug_assert!(
                tpos < self.trail.len(),
                "BUG: learned literal {lit:?} has trail_pos {tpos} >= trail.len() {}",
                self.trail.len(),
            );
            entries.push((lvl, tpos, i));
        }

        // Sort by level descending, then trail position descending within each
        // level. This gives us the Kissat clause layout (analyze.c:227-302).
        // We then process blocks from the TAIL (lowest levels first) so that
        // lower-level removability proofs warm the cache for higher-level
        // blocks (Kissat shrink.c:371-377, CaDiCaL shrink.cpp:450).
        entries.sort_unstable_by(|a, b| b.0.cmp(&a.0).then(b.1.cmp(&a.1)));

        // The asserting literal (UIP) is NOT in self.conflict.learned — it's in
        // self.conflict.asserting_lit. So we only process the non-UIP literals.

        // Process blocks. We collect the final learned literals into a new buffer.
        let mut result_lits = std::mem::take(&mut self.ws_shrink_result);
        result_lits.clear();
        let mut block_lits_ws = std::mem::take(&mut self.ws_shrink_block_lits);

        // Process from the END of the sorted entries (lowest level first).
        // The entries are sorted level-descending, so the tail has the lowest
        // levels. This matches Kissat's backward iteration over the clause.
        let mut block_end = entries.len();

        while block_end > 0 {
            let block_level = entries[block_end - 1].0;

            // Find start of this block (same level), scanning backward
            let mut block_start = block_end - 1;
            while block_start > 0 && entries[block_start - 1].0 == block_level {
                block_start -= 1;
            }

            let block_size = block_end - block_start;
            // CaDiCaL shrink.cpp:127-128: block must be non-empty and within bounds
            debug_assert!(block_size >= 1, "BUG: empty block in shrink");
            // CaDiCaL shrink.cpp:277: block level must not exceed current decision level
            debug_assert!(
                block_level <= self.decision_level,
                "BUG: block level {block_level} > decision level {}",
                self.decision_level,
            );

            if block_size >= 2 {
                self.stats.shrink_block_attempts += 1;
                // Try to find a block UIP (reuse workspace for block_lits)
                block_lits_ws.clear();
                for &(_, _, idx) in &entries[block_start..block_end] {
                    block_lits_ws.push(self.conflict.learned_at(idx));
                }

                if let Some(block_uip) = self.find_block_uip(&block_lits_ws, block_level) {
                    self.stats.shrink_block_successes += 1;
                    // Commit LRAT chain entries from block-UIP resolution (#4092).
                    for i in 0..self.ws_shrink_chain.len() {
                        self.conflict.add_to_chain(self.ws_shrink_chain[i]);
                    }
                    // CaDiCaL shrink.cpp:142: mark block UIP as kept
                    let uip_var = block_uip.variable().index();
                    self.min.minimize_flags[uip_var] |= MIN_KEEP;
                    if self.min.minimize_flags[uip_var] & MIN_VISITED == 0 {
                        self.min.minimize_flags[uip_var] |= MIN_VISITED;
                        self.min.minimize_to_clear.push(uip_var);
                    }
                    // Promote replaced block literals: clear MIN_VISITED (they
                    // are no longer in the clause) and set MIN_REMOVABLE (they
                    // were proven redundant by the block-UIP replacement).
                    // This matches CaDiCaL `mark_shrinkable_as_removable()`
                    // (shrink.cpp:22-62): block-local `shrinkable` state is
                    // promoted to persistent `removable` state. Later blocks
                    // and fallback minimize calls can reuse this cache.
                    //
                    // Soundness: the block-UIP B implies all replaced literals
                    // {X, Y, Z}. For any variable W whose removability proof
                    // went through X (via MIN_REMOVABLE, not MIN_VISITED), the
                    // proof is still valid: W's reason chain reaches X, and X
                    // is implied by B which IS in the clause.
                    for &lit in &block_lits_ws {
                        let v = lit.variable().index();
                        if v != uip_var {
                            // Clear MIN_VISITED: literal is no longer in the
                            // clause, must not serve as a recursive base case
                            // via `depth > 0 && MIN_VISITED` in
                            // is_redundant_cached.
                            self.min.minimize_flags[v] &= !MIN_VISITED;
                            // Set MIN_REMOVABLE: promote shrink success into
                            // the persistent removable cache, matching CaDiCaL
                            // mark_shrinkable_as_removable (shrink.cpp:46-61).
                            self.min.minimize_flags[v] |= MIN_REMOVABLE;
                            // Already on minimize_to_clear from the initial
                            // MIN_VISITED marking loop above.
                        }
                    }
                    result_lits.push(block_uip);
                } else {
                    // CaDiCaL shrunken_block_no_uip (shrink.cpp:157-179):
                    // Per-literal minimization on the failed block. Non-removable
                    // literals get minimize_keep = true; removable ones are dropped.
                    for &(_, _, idx) in &entries[block_start..block_end] {
                        let lit = self.conflict.learned_at(idx);
                        if self.is_redundant_cached(lit, 0) {
                            // Literal is removable — drop it from result.
                            // Clear MIN_VISITED since it's no longer in clause.
                            let v = lit.variable().index();
                            self.min.minimize_flags[v] &= !MIN_VISITED;
                        } else {
                            // CaDiCaL shrink.cpp:173: non-removable -> keep
                            let v = lit.variable().index();
                            self.min.minimize_flags[v] |= MIN_KEEP;
                            if self.min.minimize_flags[v] & MIN_VISITED == 0 {
                                self.min.minimize_flags[v] |= MIN_VISITED;
                                self.min.minimize_to_clear.push(v);
                            }
                            result_lits.push(lit);
                        }
                    }
                }
            } else {
                // CaDiCaL shrink.cpp:411: single literal block — keep it.
                // Matching CaDiCaL: singleton blocks are kept without running
                // minimize. The Knuth single-literal abort in is_redundant_cached
                // (minimize_level_count[level] < 2) would prevent removal anyway.
                let (_, _, idx) = entries[block_start];
                let lit = self.conflict.learned_at(idx);
                let v = lit.variable().index();
                self.min.minimize_flags[v] |= MIN_KEEP;
                if self.min.minimize_flags[v] & MIN_VISITED == 0 {
                    self.min.minimize_flags[v] |= MIN_VISITED;
                    self.min.minimize_to_clear.push(v);
                }
                result_lits.push(lit);
            }

            block_end = block_start;
        }

        // Block-level shrinking result: must not be larger than input
        debug_assert!(
            result_lits.len() <= learned_count,
            "BUG: shrink produced {} lits from {} — clause grew",
            result_lits.len(),
            learned_count,
        );

        // Replace the learned clause with the shrunken version
        self.conflict.replace_learned(&result_lits);

        // Return workspace Vecs
        self.ws_shrink_entries = entries;
        self.ws_shrink_result = result_lits;
        self.ws_shrink_block_lits = block_lits_ws;

        // Single-pass cleanup: clear all minimization state.
        // No second minimize pass needed — the block-by-block processing with
        // persistent removable/poison/keep caches already achieved the same
        // result. Kissat minimize.c:175-178 returns early when shrink > 2.
        for &var_idx in &self.min.minimize_to_clear {
            self.min.minimize_flags[var_idx] = 0;
        }
        self.min.minimize_to_clear.clear();
        for &lev in &self.min.minimize_levels_to_clear {
            self.min.minimize_level_count[lev as usize] = 0;
            self.min.minimize_level_trail[lev as usize] = usize::MAX;
        }
        self.min.minimize_levels_to_clear.clear();
    }

    /// Find a block UIP for a set of literals at the same decision level.
    ///
    /// Returns `Some(block_uip)` if found. LRAT chain IDs are accumulated in
    /// `self.ws_shrink_chain` (caller reads and commits them). Returns `None`
    /// if shrinking fails.
    ///
    /// Reference: CaDiCaL `shrink_block()` (shrink.cpp:270-336)
    fn find_block_uip(&mut self, block_lits: &[Literal], block_level: u32) -> Option<Literal> {
        // Block-level shrinking requires at least 2 literals at the same level.
        debug_assert!(
            block_lits.len() >= 2,
            "BUG: find_block_uip called with {} lits (expected >= 2)",
            block_lits.len(),
        );
        // All block literals must be at the specified level.
        debug_assert!(
            block_lits
                .iter()
                .all(|lit| self.var_data[lit.variable().index()].level == block_level),
            "BUG: find_block_uip: not all block literals are at level {block_level}",
        );
        // All block literals must be falsified under the current assignment
        // (they're part of the learned clause, which is a conflict clause).
        debug_assert!(
            block_lits.iter().all(|lit| self.lit_val(*lit) < 0),
            "BUG: find_block_uip: block literal not falsified",
        );

        if self.shrink_stamp_counter == u32::MAX {
            self.shrink_stamp.fill(0);
            self.shrink_stamp_counter = 0;
        }
        self.shrink_stamp_counter += 1;
        let stamp = self.shrink_stamp_counter;
        self.ws_shrink_chain.clear();
        let mut open = 0u32;
        let mut max_trail_pos = 0usize;

        // CaDiCaL shrink.cpp:276: shrinkable set must be empty at entry
        debug_assert_eq!(open, 0, "BUG: open counter non-zero at block-shrink entry");

        self.reap.clear();
        for &lit in block_lits {
            let var_idx = lit.variable().index();
            if var_idx >= self.shrink_stamp.len() {
                self.shrink_stamp.resize(var_idx + 1, 0);
            }
            self.shrink_stamp[var_idx] = stamp;
            open += 1;
            let tpos = self.var_data[var_idx].trail_pos as usize;
            if tpos > max_trail_pos {
                max_trail_pos = tpos;
            }
            // CaDiCaL shrink.cpp:112: push distance from max_trail into Reap.
            // (Distances are computed after max_trail_pos is finalized below.)
        }
        // Push distances into Reap now that max_trail_pos is known.
        for &lit in block_lits {
            let var_idx = lit.variable().index();
            let tpos = self.var_data[var_idx].trail_pos as usize;
            let dist = (max_trail_pos - tpos) as u32;
            self.reap.push(dist);
        }

        // CaDiCaL shrink.cpp:278: open must be < clause size (at least 1 open)
        debug_assert!(open > 0, "BUG: no open literals after stamping block");

        // CaDiCaL shrink.cpp:113: max trail position must be valid
        debug_assert!(
            max_trail_pos < self.trail.len(),
            "BUG: max_trail_pos {max_trail_pos} >= trail.len() {}",
            self.trail.len(),
        );
        loop {
            // Pop next stamped literal via Reap (amortized O(1), CaDiCaL shrink.cpp:288).
            // Distance = max_trail_pos - trail_pos, so trail_pos = max_trail_pos - dist.
            if self.reap.is_empty() {
                return None;
            }
            let dist = self.reap.pop();
            let pos = max_trail_pos - dist as usize;
            let uip_lit = self.trail[pos];
            open -= 1;

            if open == 0 {
                // Block UIP found. The UIP must be at the block level and
                // must be assigned true (it's on the trail). Its negation
                // will replace the block in the learned clause.
                debug_assert_eq!(
                    self.var_data[uip_lit.variable().index()].level,
                    block_level,
                    "BUG: block UIP at wrong level",
                );
                // CaDiCaL shrink.cpp:211: block UIP must be assigned true
                debug_assert!(
                    self.lit_val(uip_lit) > 0,
                    "BUG: block UIP {uip_lit:?} is not assigned true (val={})",
                    self.lit_val(uip_lit),
                );
                return Some(uip_lit.negated());
            }

            // CaDiCaL shrink.cpp:315: after resolving, at least 1 open remains
            debug_assert!(open >= 1, "BUG: open dropped to 0 without detecting UIP");

            // Resolve: get reason clause and mark same-level literals
            let var_idx = uip_lit.variable().index();
            // CaDiCaL shrink.cpp:242: resolved literal must be at block level
            debug_assert_eq!(
                self.var_data[var_idx].level, block_level,
                "BUG: resolving literal at level {} != block level {block_level}",
                self.var_data[var_idx].level,
            );
            let Some(reason_ref) = self.var_reason(var_idx) else {
                return None; // Decision variable — CaDiCaL shrink.cpp:243
            };

            // Record reason clause ID for LRAT (#4092, CaDiCaL shrink.cpp:443-503)
            if self.cold.lrat_enabled {
                let id = self.clause_id(reason_ref);
                if id != 0 {
                    self.ws_shrink_chain.push(id);
                }
            }

            // CaDiCaL shrink.cpp:246: charge search tick per reason clause access.
            self.search_ticks[usize::from(self.stable_mode)] += 1;

            let clause_idx = reason_ref.0 as usize;
            let clause_len = self.arena.len_of(clause_idx);
            for i in 0..clause_len {
                let reason_lit = self.arena.literal(clause_idx, i);
                let reason_var = reason_lit.variable().index();
                if reason_var == var_idx {
                    continue;
                }
                // CaDiCaL shrink.cpp:254: reason literals (other than pivot) must be falsified
                debug_assert!(
                    self.lit_val(reason_lit) < 0,
                    "BUG: reason literal {reason_lit:?} in clause {clause_idx} is not falsified (val={})",
                    self.lit_val(reason_lit),
                );
                let reason_level = self.var_data[reason_var].level;
                if reason_level == block_level {
                    if reason_var >= self.shrink_stamp.len() {
                        self.shrink_stamp.resize(reason_var + 1, 0);
                    }
                    if self.shrink_stamp[reason_var] != stamp {
                        self.shrink_stamp[reason_var] = stamp;
                        open += 1;
                        // Push distance into Reap for O(1) retrieval.
                        let reason_tpos = self.var_data[reason_var].trail_pos as usize;
                        let reason_dist = (max_trail_pos - reason_tpos) as u32;
                        self.reap.push(reason_dist);
                    }
                } else if reason_level != 0 && !self.is_literal_removable_for_shrink(reason_lit) {
                    return None;
                }
            }
        }
    }

    /// Check if a literal at a lower level is removable during block-UIP search.
    ///
    /// This is CaDiCaL's `shrink_literal()` for lower-level literals (shrink=3 mode).
    /// A lower-level literal is removable if:
    /// 1. It's at level 0 (trivially true)
    /// 2. It was already proven removable by minimization (`minimize_removable`)
    /// 3. It is in the "keep" cache (`minimize_keep`) from progressive marking
    /// 4. It was already proven non-removable (`minimize_poison`)
    /// 5. It can be proven removable via recursive minimization (`is_redundant_cached`)
    ///
    /// IMPORTANT: CaDiCaL checks `f.removable` (proven redundant), NOT "in the clause."
    /// A literal appearing in the learned clause at a lower level is a required
    /// dependency, not a removable one. The prior Z4 code incorrectly treated
    /// `minimize_visited` (in-clause) as removable, causing unsound block-UIP
    /// replacements that dropped necessary lower-level dependencies.
    /// Reference: CaDiCaL `shrink_literal()` (shrink.cpp:66-118, line 94).
    fn is_literal_removable_for_shrink(&mut self, lit: Literal) -> bool {
        let var_idx = lit.variable().index();
        // CaDiCaL shrink.cpp:68: literal must be falsified
        debug_assert!(
            self.lit_val(lit) < 0,
            "BUG: is_literal_removable_for_shrink called on non-falsified literal {lit:?}",
        );

        // Level 0 is always removable
        if self.var_data[var_idx].level == 0 {
            return true;
        }

        // Check existing minimize cache (CaDiCaL: f.removable)
        let mf = self.min.minimize_flags[var_idx];
        if mf & MIN_REMOVABLE != 0 {
            return true;
        }
        // CaDiCaL minimize.cpp:22 checks keep before poison. A literal can
        // carry both flags (poison from failed recursion, keep from progressive
        // marking); keep must win as a valid dependency base case.
        if mf & MIN_KEEP != 0 {
            return true;
        }
        if mf & MIN_POISON != 0 {
            return false;
        }

        // Note: Do NOT check minimize_visited here. CaDiCaL checks f.removable
        // (proven redundant via recursive minimization), not "in the clause."
        // A literal in the clause at a lower level is a required dependency.
        // The minimize_removable check above handles the CaDiCaL f.removable case.

        // Decision variables can't be removed
        if self.var_data[var_idx].reason == NO_REASON {
            return false;
        }

        // Try to prove removable via recursive minimization (shrink=3 mode)
        // This is CaDiCaL's "always_minimize_on_lower_blevel" behavior.
        self.is_redundant_cached(lit, 1)
    }
}

#[cfg(test)]
#[path = "shrink_tests.rs"]
mod tests;
