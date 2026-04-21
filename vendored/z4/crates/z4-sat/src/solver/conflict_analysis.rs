// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! 1UIP conflict analysis and clause learning.

use super::*;
#[cfg(test)]
use crate::kani_compat::det_hash_set_new;
use crate::solver_log::solver_log;

impl Solver {
    /// Analyze conflict and learn a clause using 1UIP scheme
    pub(super) fn analyze_conflict(&mut self, conflict_ref: ClauseRef) -> ConflictResult {
        solver_log!(self, "analyze conflict clause {}", conflict_ref.0);
        self.conflict.clear(&mut self.var_data);

        // Entry cleanliness: learned clause and resolution chain must be empty
        // after clear(). clause_buf is a reusable workspace — stale content is
        // overwritten before use, so it is not checked here.
        // CaDiCaL reference: analyze.cpp:944-948.
        debug_assert_eq!(
            self.conflict.learned_count(),
            0,
            "BUG: learned clause buffer not empty at analysis entry"
        );
        debug_assert!(
            self.decision_level > 0,
            "BUG: conflict analysis called at decision level 0"
        );

        let mut counter = 0; // Literals at current decision level
        let mut p: Option<Literal> = None;
        let mut index = self.trail.len();
        // Collect level-0 variables for the LRAT unit chain.
        let mut lrat_level0_vars: Vec<usize> = Vec::new();

        // OTFS accounting: resolved steps, current resolvent size, antecedent
        // size of the just-processed clause, and the last reason clause.
        let mut resolved: u32 = 0;
        let mut resolvent_size: u32 = 0;
        let mut antecedent_size: u32;
        let mut last_reason_ref: Option<ClauseRef> = None;

        // Bump conflict clause: set used, bump activity, recompute glue
        self.bump_clause(conflict_ref);

        // Forward LRAT chain: add the conflict clause ID to start the chain.
        // CaDiCaL analyze.cpp: the conflict clause is the seed of the resolution.
        if self.cold.lrat_enabled {
            let id = self.clause_id(conflict_ref);
            if id != 0 {
                self.conflict.add_to_chain(id);
            }
        }

        // CaDiCaL analyze.cpp:944: conflict clause must exist and be non-trivial
        debug_assert!(
            self.arena.len_of(conflict_ref.0 as usize) >= 2,
            "BUG: conflict clause {} has len {} (expected >= 2)",
            conflict_ref.0,
            self.arena.len_of(conflict_ref.0 as usize),
        );

        // Zero-copy clause iteration (#6989).
        let mut current_clause_offset = conflict_ref.0 as usize;
        let mut current_clause_len = self.arena.len_of(current_clause_offset);

        loop {
            let clause_len = current_clause_len;
            // OTFS accounting starts with the pivot/UIP slot.
            antecedent_size = 1;
            for i in 0..clause_len {
                let lit = self.arena.literal_at(current_clause_offset, i);
                if let Some(p_lit) = p {
                    if lit == p_lit {
                        continue;
                    }
                }

                let var = lit.variable();
                let var_idx = var.index();
                let var_level = self.var_data[var_idx].level;

                // Every literal in a conflict/reason clause must be falsified
                // under the current assignment. CaDiCaL: analyze.cpp:265,276.
                debug_assert!(
                    self.lit_val(lit) < 0,
                    "BUG: literal {:?} (var={}) in conflict/reason clause is not falsified (val={})",
                    lit,
                    var_idx,
                    self.lit_val(lit),
                );

                // OTFS: count non-level-0 literals toward antecedent_size
                // regardless of seen status. CaDiCaL: analyze.cpp:270.
                if var_level > 0 {
                    antecedent_size += 1;
                }

                if !self.conflict.is_seen(var_idx, &self.var_data) {
                    self.conflict.mark_seen(var_idx, &mut self.var_data);

                    debug_assert!(
                        var_level <= self.decision_level,
                        "BUG: analyzed literal var={} at level {} exceeds decision level {}",
                        var_idx,
                        var_level,
                        self.decision_level,
                    );

                    if var_level > 0 {
                        self.track_level_seen(var_level, var_idx);
                    }

                    if var_level == self.decision_level {
                        counter += 1;
                    } else if var_level > 0 {
                        self.conflict.add_to_learned(lit);
                    } else if self.cold.lrat_enabled {
                        lrat_level0_vars.push(var_idx);
                    }

                    if var_level > 0 {
                        resolvent_size += 1;
                    }
                }
            }

            // CaDiCaL analyze.cpp:1066 invariant: resolvent_size == open + clause.size().
            // In Z4: resolvent_size == counter (current-level seen) + learned_count
            // (non-current-level, non-level-0 literals added to the learned clause).
            // Fires immediately when stale seen marks corrupt the accounting.
            debug_assert_eq!(
                resolvent_size,
                counter + self.conflict.learned_count() as u32,
                "BUG: resolvent_size ({resolvent_size}) != counter ({counter}) + \
                 learned_count ({}) — possible stale seen mark (resolved={resolved})",
                self.conflict.learned_count(),
            );

            // OTFS (#4598): strengthen the previous reason when the current
            // resolvent already subsumes it. Disabled in LRAT mode.
            if let Some(prev_reason) = last_reason_ref {
                // #8105: OTFS enabled in LRAT mode (backward reconstruction handles proofs)
                if resolved > 0
                    && antecedent_size > 2
                    && resolvent_size < antecedent_size
                {
                    self.stats.otfs_candidates += 1;
                    let p_lit = p.expect("conflict analysis: p set for OTFS");

                    // Skip OTFS if strengthening would remove every current-level
                    // literal or violate the watch invariant.
                    let pre_reason_lits = self.arena.literals(prev_reason.0 as usize);
                    let pivot_var = p_lit.variable();
                    let post_otfs_open = pre_reason_lits
                        .iter()
                        .filter(|l| {
                            l.variable() != pivot_var
                                && self.var_data[l.variable().index()].level == self.decision_level
                        })
                        .count();

                    let watch_ok = pre_reason_lits.len() < 2
                        || self.lit_val(pre_reason_lits[0]) > 0
                        || self.lit_val(pre_reason_lits[1]) > 0;

                    if post_otfs_open == 0 || !watch_ok {
                        if post_otfs_open == 0 {
                            self.stats.otfs_blocked_open0 += 1;
                        }
                        if !watch_ok {
                            self.stats.otfs_blocked_watch += 1;
                        }
                        // Don't strengthen — fall through to normal analysis
                    } else if !self.otfs_strengthen(prev_reason, p_lit) {
                        self.stats.otfs_blocked_strengthen += 1;
                        // otfs_strengthen returned false — fall through
                    } else {
                        self.stats.otfs_subsumed += 1;

                        if post_otfs_open == 1 {
                            // Branch B: the strengthened clause is already asserting.
                            let (asserting_lit, bt_level) = {
                                let strengthened_lits = self.arena.literals(prev_reason.0 as usize);
                                let mut forced = None;
                                let mut bt_level: u32 = 0;
                                for &lit in strengthened_lits {
                                    let lv = self.var_data[lit.variable().index()].level;
                                    if lv == self.decision_level {
                                        debug_assert!(
                                            forced.is_none(),
                                            "BUG: OTFS Branch B found 2+ current-level lits"
                                        );
                                        forced = Some(lit);
                                    } else if lv > bt_level {
                                        bt_level = lv;
                                    }
                                }
                                (
                                    forced.expect(
                                        "BUG: OTFS Branch B: no current-level literal found",
                                    ),
                                    bt_level,
                                )
                            };

                            self.conflict.clear(&mut self.var_data);
                            self.clear_level_seen();

                            let branch_b_offset = prev_reason.0 as usize;
                            let branch_b_len = self.arena.len_of(branch_b_offset);
                            self.conflict.set_asserting_literal(asserting_lit);
                            for i in 0..branch_b_len {
                                let lit = self.arena.literal_at(branch_b_offset, i);
                                if lit.variable() != asserting_lit.variable() {
                                    self.conflict.add_to_learned(lit);
                                }
                            }

                            let lbd = self.conflict.compute_lbd(&self.var_data) + 1;
                            let mut result = self.conflict.get_result(bt_level, lbd);
                            crate::conflict::reorder_for_watches(
                                &mut result.learned_clause,
                                &self.var_data,
                                bt_level,
                            );
                            result.otfs_driving_clause = Some(prev_reason);
                            return result;
                        }

                        debug_assert!(
                            post_otfs_open > 1,
                            "BUG: OTFS Branch C reached with open={post_otfs_open} <= 1"
                        );
                        self.conflict.clear(&mut self.var_data);
                        self.clear_level_seen();
                        counter = 0;
                        p = None;
                        index = self.trail.len();
                        resolved = 0;
                        resolvent_size = 0;
                        lrat_level0_vars.clear();
                        last_reason_ref = None;

                        self.bump_clause(prev_reason);

                        if self.cold.lrat_enabled {
                            let id = self.clause_id(prev_reason);
                            if id != 0 {
                                self.conflict.add_to_chain(id);
                            }
                        }

                        current_clause_offset = prev_reason.0 as usize;
                        current_clause_len = self.arena.len_of(current_clause_offset);
                        continue;
                    }
                }
            }

            // Scan backward for the next seen literal at the current level.
            loop {
                debug_assert!(
                    index != 0,
                    "BUG: no current-level seen literal found in trail during \
                     conflict analysis (counter={counter}, decision_level={}, \
                     resolved={resolved})",
                    self.decision_level,
                );
                index -= 1;
                let trail_lit = self.trail[index];
                let var_idx = trail_lit.variable().index();
                if self.conflict.is_seen(var_idx, &self.var_data)
                    && self.var_data[var_idx].level == self.decision_level
                {
                    p = Some(trail_lit);
                    break;
                }
            }

            // Keep seen marks until the end of analysis (#7331).
            debug_assert!(
                counter > 0,
                "BUG: analysis counter underflow before resolving {p:?} \
                 (counter={counter}, decision_level={}, resolved={resolved}, \
                 resolvent_size={resolvent_size})",
                self.decision_level,
            );
            counter -= 1;

            if counter == 0 {
                solver_log!(
                    self,
                    "1UIP: {}",
                    p.expect("invariant: p set in resolution loop").to_dimacs()
                );
                break; // Found 1UIP
            }

            debug_assert!(
                index > 0,
                "BUG: trail exhausted with counter={counter} > 0 — no more seen literals"
            );

            let p_var = p
                .expect("conflict analysis: p set for reason lookup")
                .variable();
            debug_assert!(
                self.lit_val(p.expect("p for val check")) > 0,
                "BUG: resolved literal p (var={}) is not assigned true on trail",
                p_var.index(),
            );
            let reason_kind = self.var_reason_kind(p_var.index());
            match reason_kind {
                ReasonKind::Decision => {
                    self.conflict
                        .add_to_learned(p.expect("conflict analysis: p for decision").negated());
                    debug_assert!(
                        resolvent_size > 0,
                        "BUG: resolvent_size underflow for decision literal var={}",
                        p_var.index(),
                    );
                    resolvent_size -= 1;
                    resolved += 1;
                    last_reason_ref = None;
                    current_clause_len = 0;
                    continue;
                }
                ReasonKind::BinaryLiteral(reason_lit) => {
                    // Binary literal reason (#8034): virtual clause [p, reason_lit].
                    // Resolve the single reason literal inline without arena access.
                    let var_idx = reason_lit.variable().index();
                    let var_level = self.var_data[var_idx].level;

                    debug_assert!(
                        self.lit_val(reason_lit) < 0,
                        "BUG: binary reason literal {:?} (var={}) is not falsified (val={})",
                        reason_lit,
                        var_idx,
                        self.lit_val(reason_lit),
                    );

                    if !self.conflict.is_seen(var_idx, &self.var_data) {
                        self.conflict.mark_seen(var_idx, &mut self.var_data);

                        if var_level > 0 {
                            self.track_level_seen(var_level, var_idx);
                        }

                        if var_level == self.decision_level {
                            counter += 1;
                        } else if var_level > 0 {
                            self.conflict.add_to_learned(reason_lit);
                        } else if self.cold.lrat_enabled {
                            lrat_level0_vars.push(var_idx);
                        }

                        if var_level > 0 {
                            resolvent_size += 1;
                        }
                    }

                    resolved += 1;
                    last_reason_ref = None;
                    assert!(
                        resolvent_size > 0,
                        "BUG: resolvent_size underflow during conflict analysis \
                         (counter={counter}, decision_level={}, resolved={resolved})",
                        self.decision_level,
                    );
                    resolvent_size -= 1;
                    current_clause_len = 0;
                    continue;
                }
                ReasonKind::Clause(reason_ref) => {
                    debug_assert!(
                        {
                            let p_lit = p.expect("conflict analysis: p for reason check");
                            let reason_lits = self.arena.literals(reason_ref.0 as usize);
                            reason_lits.contains(&p_lit)
                        },
                        "BUG: reason clause for var={} does not contain the propagated literal",
                        p_var.index(),
                    );

                    debug_assert!(
                        !self.arena.is_empty_clause(reason_ref.0 as usize),
                        "BUG: reason clause {} for var={} is deleted during analysis",
                        reason_ref.0,
                        p_var.index(),
                    );
                    debug_assert!(
                        self.arena.len_of(reason_ref.0 as usize) >= 2,
                        "BUG: reason clause {} for var={} has len {} < 2",
                        reason_ref.0,
                        p_var.index(),
                        self.arena.len_of(reason_ref.0 as usize),
                    );

                    self.bump_clause(reason_ref);

                    if self.cold.lrat_enabled {
                        let id = self.clause_id(reason_ref);
                        if id != 0 {
                            self.conflict.add_to_chain(id);
                        }
                    }

                    resolved += 1;
                    last_reason_ref = Some(reason_ref);

                    assert!(
                        resolvent_size > 0,
                        "BUG: resolvent_size underflow during conflict analysis \
                         (counter={counter}, decision_level={}, resolved={resolved})",
                        self.decision_level,
                    );
                    resolvent_size -= 1;

                    current_clause_offset = reason_ref.0 as usize;
                    current_clause_len = self.arena.len_of(current_clause_offset);
                }
            }
        }

        debug_assert_eq!(
            counter, 0,
            "BUG: exited analysis loop with counter={counter} != 0"
        );

        let uip = p.expect("conflict analysis: 1UIP found").negated();
        self.finalize_conflict_analysis(uip, lrat_level0_vars)
    }
}
// Post-analysis variable bumping (VSIDS/VMTF) is in conflict_analysis_bumping.rs.

#[cfg(test)]
#[path = "conflict_analysis_tests.rs"]
mod tests;
