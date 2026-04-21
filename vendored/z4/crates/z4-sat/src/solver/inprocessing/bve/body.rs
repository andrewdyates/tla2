// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//\! BVE core elimination loop.

use super::super::super::mutate::ReasonPolicy;
use super::super::super::*;
use super::state::{BveBodyScratch, BveBodyStats};
use super::FASTELIM_OCC_LIMIT;
use crate::gates::BveExtraction;
use crate::solver_log::solver_log;

impl Solver {
    pub(super) fn bve_body(&mut self) -> bool {
        if !self.enter_inprocessing() {
            return false;
        }

        // Skip in incremental mode: BVE rewrites the clause database via
        // resolution, which cannot be reversed across solve boundaries (#5031, #5166).
        if self.cold.has_been_incremental {
            return false;
        }

        // Compute resolution effort limit.
        //
        // CaDiCaL: elimfast.cpp:279-290 / elim.cpp:778-796 — both use
        // `stats.propagations.search * elimeffort / 1000`, clamped to
        // [elimmineff, elimmaxeff]. Critically, CaDiCaL's counter tracks
        // only CDCL search propagations, not probing or preprocessing.
        //
        // Z4's `num_propagations` includes probing propagations. During
        // preprocessing, probing runs BEFORE BVE and can inflate the
        // counter to 100M+, giving BVE an enormous budget that wastes
        // seconds on futile round-2 candidates. CaDiCaL's search counter
        // is 0 at this point, yielding effort = clamped min = 10M.
        //
        // Fix: in fastelim mode (preprocessing), use only the minimum
        // effort. During inprocessing (search), num_propagations reflects
        // actual search work and the formula is correct.
        let effort = if self.inproc.bve.is_fastelim_mode() {
            let base = FASTELIM_EFFORT;
            let active_cls = self.arena.active_clause_count() as u64;
            // Scale down effort for large formulas (#8136).
            if active_cls > FASTELIM_SCALE_CLAUSE_THRESHOLD {
                let scaled =
                    (base as f64 * FASTELIM_SCALE_CLAUSE_THRESHOLD as f64 / active_cls as f64)
                        as u64;
                scaled.max(FASTELIM_MIN_SCALED_EFFORT)
            } else {
                base
            }
        } else {
            let raw = (self.num_propagations as f64 * self.cold.bve_effort_permille as f64 / 1000.0)
                as u64;
            raw.clamp(BVE_MIN_EFFORT, BVE_MAX_EFFORT)
        };
        let active_vars = self
            .num_vars
            .saturating_sub(self.var_lifecycle.count_removed()) as u64;
        let effort = effort.max(2 * active_vars);

        let mut derived_unsat = false;
        let mut stats = BveBodyStats::default();
        #[cfg(z4_logging)]
        let mut gate_eliminations = 0usize;
        #[cfg(z4_logging)]
        let clauses_at_bve_start = self.arena.num_clauses();
        let active_at_bve_start = self.arena.active_clause_count();

        let mut scratch = BveBodyScratch::default();
        let mut pending_gc_indices: Vec<usize> = Vec::new();

        // Ensure there are dirty candidates. In fastelim mode, build_schedule
        // skips the dirty filter. In additive mode, dirty bits are set
        // incrementally by subsumption/vivify/decompose. On the first
        // inprocessing BVE call (or when called directly in tests), no
        // incremental marking has happened. Mark all candidates dirty to
        // avoid an empty schedule.
        if !self.inproc.bve.is_fastelim_mode() && !self.inproc.bve.has_dirty_candidates() {
            self.inproc.bve.mark_all_candidates_dirty();
        }

        if self.cold.lrat_enabled {
            self.materialize_level0_unit_proofs();
        }

        let max_rounds = if self.inproc.bve.is_fastelim_mode() {
            // Reduce rounds for large formulas (#8136).
            let active_cls = self.arena.active_clause_count();
            if active_cls > 3_000_000 {
                1
            } else if active_cls > FASTELIM_SCALE_CLAUSE_THRESHOLD as usize {
                2
            } else {
                PREPROCESS_BVE_ROUNDS
            }
        } else {
            BVE_ROUNDS
        };
        let bve_wall_start = std::time::Instant::now();
        let mut candidates_exhausted = false;
        for round in 0..max_rounds {
            // Wall-clock guard for fastelim on large formulas (#8136).
            if round > 0
                && self.inproc.bve.is_fastelim_mode()
                && bve_wall_start.elapsed().as_secs() >= FASTELIM_WALL_CLOCK_LIMIT_SECS
            {
                break;
            }
            if round > 0 && stats.total_eliminations > 0 {
                for &idx in &pending_gc_indices {
                    if self.arena.is_empty_clause(idx) || !self.arena.is_active(idx) {
                        continue;
                    }
                    let has_eliminated = self
                        .arena
                        .literals(idx)
                        .iter()
                        .any(|lit| self.var_lifecycle.is_removed(lit.variable().index()));
                    if has_eliminated {
                        self.delete_clause_checked(idx, ReasonPolicy::ClearLevel0);
                    }
                }
                pending_gc_indices.clear();
            }

            self.inproc.bve.rebuild_with_vals(&self.arena, &self.vals);

            let mut eliminated_this_round = false;
            let resolution_limit = self.cold.bve_resolutions.saturating_add(effort);
            let elim_cap = if self.inproc.bve.is_fastelim_mode() {
                FASTELIM_MAX_ELIMINATIONS
            } else {
                MAX_BVE_ELIMINATIONS
            };
            // Debug: limit total eliminations for bisection (cached at solver creation)
            let elim_cap = if let Some(limit) = self.cold.bve_limit {
                elim_cap.min(limit)
            } else {
                elim_cap
            };
            candidates_exhausted = false;
            while stats.total_eliminations < elim_cap
                && self.cold.bve_resolutions < resolution_limit
            {
                // Check external interrupt (timeout) every 64 eliminations to
                // avoid spending seconds in BVE after the DPLL timeout fires.
                // This fixes QF_ABV regression on try5_dwp_fmt where the
                // reduced formula (from cached false/true literals) enabled
                // BVE to find 26K+ substitutions taking 18.9s. (#8782)
                if stats.total_eliminations & 63 == 0 && self.is_interrupted() {
                    break;
                }
                let var = match self.inproc.bve.next_candidate(
                    &self.arena,
                    &self.vals,
                    &self.cold.freeze_counts,
                ) {
                    Some(v) => v,
                    None => {
                        candidates_exhausted = true;
                        break;
                    }
                };
                debug_assert!(
                    !self.var_is_assigned(var.index()),
                    "BUG: BVE candidate var {var:?} is assigned",
                );
                debug_assert!(
                    !self.var_lifecycle.is_removed(var.index()),
                    "BUG: BVE candidate var {var:?} is already removed",
                );
                debug_assert!(
                    self.cold
                        .freeze_counts
                        .get(var.index())
                        .copied()
                        .unwrap_or(0)
                        == 0,
                    "BUG: BVE candidate var {var:?} is frozen",
                );

                if self.inproc.bve.is_fastelim_mode() {
                    let pos_occs = self.inproc.bve.get_occs(Literal::positive(var));
                    let neg_occs = self.inproc.bve.get_occs(Literal::negative(var));
                    if pos_occs.len() > FASTELIM_OCC_LIMIT || neg_occs.len() > FASTELIM_OCC_LIMIT {
                        continue;
                    }
                    let has_oversized = pos_occs
                        .iter()
                        .chain(neg_occs.iter())
                        .any(|&idx| self.arena.len_of(idx) > 100);
                    if has_oversized {
                        continue;
                    }
                }

                scratch.pos_occs.clear();
                scratch
                    .pos_occs
                    .extend_from_slice(self.inproc.bve.get_occs(Literal::positive(var)));
                scratch.neg_occs.clear();
                scratch
                    .neg_occs
                    .extend_from_slice(self.inproc.bve.get_occs(Literal::negative(var)));
                let extraction =
                    if self.inproc.bve.is_fastelim_mode() || !self.inproc_ctrl.gate.enabled {
                        None
                    } else {
                        let gate_extractor = &mut self.inproc.gate_extractor;
                        let definition_kitten = &mut self.inproc.definition_kitten;
                        gate_extractor.find_extraction_for_bve_with_marks(
                            definition_kitten,
                            var,
                            &self.arena,
                            &scratch.pos_occs,
                            &scratch.neg_occs,
                            &self.vals,
                            &mut self.lit_marks,
                        )
                    };
                let (gate_defining, resolve_gate_pairs) = match extraction {
                    Some(BveExtraction::RestrictResolution {
                        defining_clauses,
                        resolve_gate_pairs,
                    }) => (Some(defining_clauses), resolve_gate_pairs),
                    Some(BveExtraction::FailedLiteral { unit }) => {
                        if self.var_is_assigned(unit.variable().index()) {
                            debug_assert!(
                                self.lit_val(unit) > 0,
                                "BUG: BVE semantic failed literal {unit:?} conflicts with an existing assignment",
                            );
                            continue;
                        }
                        if self.cold.lrat_enabled {
                            let probe_lit = unit.negated();
                            self.decide(probe_lit);
                            if let Some(conflict_ref) = self.search_propagate() {
                                let lrat_hints = self.collect_probe_conflict_lrat_hints(
                                    conflict_ref,
                                    probe_lit,
                                    Some(unit),
                                );
                                self.backtrack(0);
                                if self.learn_derived_unit(unit, &lrat_hints) {
                                    return true;
                                }
                            } else {
                                self.backtrack(0);
                            }
                        } else if self.learn_derived_unit(unit, &[]) {
                            return true;
                        }
                        continue;
                    }
                    None => (None, false),
                };
                let result = self.inproc.bve.try_eliminate_with_gate_with_marks(
                    var,
                    &self.arena,
                    gate_defining.as_deref(),
                    resolve_gate_pairs,
                    &mut self.lit_marks,
                    &self.vals,
                );
                self.cold.bve_resolutions = self
                    .cold
                    .bve_resolutions
                    .saturating_add(result.resolution_attempts);

                if !result.eliminated {
                    self.inproc.bve.mark_failed(var);
                    continue;
                }
                #[cfg(z4_logging)]
                if gate_defining.is_some() {
                    gate_eliminations += 1;
                }

                eliminated_this_round = true;
                if self.cold.bve_trace {
                    let sp = result.satisfied_parents.len();
                    let st = result.strengthened.len();
                    let rv = result.resolvents.len();
                    let we = result.witness_entries.len();
                    let td = result.to_delete.len();
                    eprintln!(
                        "BVE_TRACE: elim #{} var={} to_delete={} witness={} resolvents={} strengthened={} sat_parents={}",
                        stats.total_eliminations, var.0, td, we, rv, st, sp,
                    );
                    if sp > 0 {
                        for &sp_idx in &result.satisfied_parents {
                            let sp_lits: Vec<i32> = self
                                .arena
                                .literals(sp_idx)
                                .iter()
                                .map(|l| {
                                    let ext = self.externalize(*l);
                                    ext.to_dimacs()
                                })
                                .collect();
                            eprintln!("  SAT_PARENT: idx={sp_idx} lits={sp_lits:?}");
                        }
                    }
                }
                self.apply_bve_elimination_result(
                    &result,
                    &mut scratch,
                    &mut stats,
                    &mut pending_gc_indices,
                    &mut derived_unsat,
                );
                if derived_unsat {
                    break;
                }
            }

            if derived_unsat || !eliminated_this_round {
                break;
            }
            // CaDiCaL fastelim: single pass with dynamic rescheduling. When
            // all candidates are exhausted, further rounds just add rebuild
            // overhead. Break for both fastelim and additive modes.
            if candidates_exhausted {
                break;
            }
            if !self.inproc.bve.is_fastelim_mode() {
                let current = self.arena.active_clause_count();
                let threshold = active_at_bve_start + active_at_bve_start / 20;
                if current > threshold {
                    break;
                }
            }
            if self.cold.bve_resolutions >= resolution_limit {
                break;
            }

            self.subsume();

            // Kissat-style progressive growth bound (#8135, eliminate.c:339-372):
            // after exhausting all candidates at the current bound, increment
            // the bound before the next round so bound progresses 0 -> 1 -> 2.
            if candidates_exhausted && eliminated_this_round {
                self.inproc.bve.increment_growth_bound();
            }
        }

        // CaDiCaL elim.cpp:917-922: collect instantiation candidates while
        // occurrence lists are still live. Must happen before garbage
        // collection deletes clauses with eliminated variables.
        let inst_candidates = if !derived_unsat && stats.total_eliminations > 0 {
            self.collect_instantiation_candidates()
        } else {
            Vec::new()
        };

        if stats.total_eliminations > 0 {
            let all_indices: Vec<usize> = self.arena.indices().collect();
            for idx in all_indices {
                if self.arena.is_empty_clause(idx) {
                    continue;
                }
                let has_eliminated = self
                    .arena
                    .literals(idx)
                    .iter()
                    .any(|lit| self.var_lifecycle.is_removed(lit.variable().index()));
                if has_eliminated {
                    self.delete_clause_checked(idx, ReasonPolicy::ClearLevel0);
                }
            }
        }

        if stats.total_eliminations > 0 && candidates_exhausted {
            self.inproc.bve.increment_growth_bound();
        }

        // CaDiCaL elim.cpp:945-947: run instantiation after occ list
        // cleanup and garbage collection. Instantiation temporarily
        // rebuilds 2WL watches for BCP-based strengthening.
        if !derived_unsat && !inst_candidates.is_empty() {
            if self.instantiate(inst_candidates) {
                derived_unsat = true;
            }
        }

        solver_log!(
            self,
            "BVE: eliminated {} vars ({} gated), {} resolutions, {} clauses (delta {}), bound={} {}",
            stats.total_eliminations,
            gate_eliminations,
            self.cold.bve_resolutions,
            self.arena.num_clauses(),
            self.arena.num_clauses() as i64 - clauses_at_bve_start as i64,
            self.inproc.bve.growth_bound(),
            if self.inproc.bve.is_fastelim_mode() { "fastelim" } else { "additive" },
        );
        tracing::info!(
            eliminated = stats.total_eliminations,
            resolvents = stats.resolvents_total,
            bw_checks = stats.bw_checks_total,
            bw_subsumed = stats.bw_subsumed_total,
            bw_strengthened = stats.bw_strengthened_total,
            active_clauses = self.arena.active_clause_count(),
            mode = if self.inproc.bve.is_fastelim_mode() {
                "fastelim"
            } else {
                "additive"
            },
            "BVE backward subsumption diagnostics"
        );
        self.cold.last_bve_fixed = self.fixed_count;
        self.cold.last_bve_marked = self.cold.bve_marked;
        self.cold.bve_phases += 1;

        #[cfg(debug_assertions)]
        if stats.total_eliminations > 0 {
            for idx in self.arena.indices() {
                if self.arena.is_empty_clause(idx) {
                    continue;
                }
                debug_assert!(
                    !self
                        .arena
                        .literals(idx)
                        .iter()
                        .any(|lit| self.var_lifecycle.is_removed(lit.variable().index())),
                    "BUG: active {} clause {idx} contains a removed variable \
                     after BVE garbage collection",
                    if self.arena.is_learned(idx) {
                        "learned"
                    } else {
                        "irredundant"
                    },
                );
            }
        }

        derived_unsat
    }
}
