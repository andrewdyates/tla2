// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl Solver {
    /// Find the actual conflict level: the maximum assignment level among
    /// all literals in the conflict clause (CaDiCaL analyze.cpp:572-644).
    ///
    /// With chronological backtracking + correct assignment levels, this may
    /// be lower than `decision_level`. Returns `(conflict_level, forced)` where
    /// `forced` is `Some(lit)` if exactly one literal is at the highest level
    /// (the "forced" early-return path from CaDiCaL SAT'18 paper Alg.1 lines 4-6).
    pub(super) fn find_conflict_level(
        &mut self,
        conflict_ref: ClauseRef,
    ) -> (u32, Option<Literal>) {
        let clause_idx = conflict_ref.0 as usize;
        let lits = self.arena.literals(clause_idx);
        let len = lits.len();
        let mut max_level = 0u32;
        let mut count = 0u32;
        let mut forced_lit = lits[0];
        for &lit in lits {
            let lvl = self.var_data[lit.variable().index()].level;
            if lvl > max_level {
                max_level = lvl;
                forced_lit = lit;
                count = 1;
            } else if lvl == max_level {
                count += 1;
            }
        }

        if len >= 2 {
            let target = conflict_ref.0;
            for i in 0..2usize {
                let (best_pos, _best_level) = {
                    let lits_r = self.arena.literals(clause_idx);
                    let mut bp = i;
                    let mut bl = self.var_data[lits_r[i].variable().index()].level;
                    for (j, lit) in lits_r.iter().enumerate().skip(i + 1) {
                        let lvl = self.var_data[lit.variable().index()].level;
                        if lvl > bl {
                            bp = j;
                            bl = lvl;
                            if bl == max_level {
                                break;
                            }
                        }
                    }
                    (bp, bl)
                };
                if best_pos == i {
                    continue;
                }
                if best_pos > 1 {
                    let old_watched = self.arena.literals(clause_idx)[i];
                    let mut wl = self.watches.get_watches_mut(old_watched);
                    let mut wi = 0;
                    while wi < wl.len() {
                        if wl.clause_ref(wi).0 == target {
                            wl.swap_remove(wi);
                        } else {
                            wi += 1;
                        }
                    }
                }
                self.arena.literals_mut(clause_idx).swap(i, best_pos);
                if best_pos > 1 {
                    let new_watched = self.arena.literals(clause_idx)[i];
                    let other = self.arena.literals(clause_idx)[if i == 0 { 1 } else { 0 }];
                    self.watches
                        .add_watch(new_watched, Watcher::new(conflict_ref, other));
                }
            }
        }

        if count == 1 {
            (max_level, Some(forced_lit))
        } else {
            (max_level, None)
        }
    }
}
