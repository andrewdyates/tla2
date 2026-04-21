// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SCC-based equivalent literal substitution (decompose).

use super::super::mutate::ReasonPolicy;
use super::super::*;

impl Solver {
    // ==================== Decompose (SCC Equivalent Literal Substitution) ====================

    /// Run decompose and reschedule with growing backoff.
    ///
    /// Callers are responsible for applying any scheduling gate before entry.
    /// This preserves forced follow-up rewrites after congruence or sweep even
    /// when the regular interval is not due yet.
    ///
    /// Uses growing backoff when unproductive (no equivalences found): the
    /// interval grows 1.5× per idle call, up to DECOMPOSE_MAX_INTERVAL.
    /// Productive calls reset to base interval. This reduces overhead from
    /// repeated no-op SCC traversals on formulas where decompose finds
    /// equivalences only in early rounds (e.g., FmlaEquivChain: 39 rounds
    /// with 976ms total, most rounds finding 0 equivalences).
    pub(in crate::solver) fn decompose(&mut self) {
        let productive = self.decompose_body();
        if productive {
            self.inproc_ctrl
                .decompose
                .reschedule(self.num_conflicts, DECOMPOSE_INTERVAL);
        } else {
            self.inproc_ctrl.decompose.reschedule_growing(
                self.num_conflicts,
                DECOMPOSE_INTERVAL,
                3,
                2, // 1.5× growth
                DECOMPOSE_MAX_INTERVAL,
            );
        }
    }

    /// Decompose body — early returns are safe; wrapper handles rescheduling.
    ///
    /// Builds the binary implication graph, finds SCCs via Tarjan's algorithm,
    /// and substitutes equivalent literals throughout the clause database.
    /// Reference: CaDiCaL `decompose.cpp`.
    ///
    /// Returns `true` if equivalences were found and substituted.
    /// Must be called at decision level 0.
    fn decompose_body(&mut self) -> bool {
        use crate::decompose::rewrite_clauses;
        if !self.require_level_zero() {
            return false;
        }

        // Skip in incremental mode: decompose uses push_equivalence_reconstruction()
        // and rewrites clauses in-place. After pop(), reconstruction entries are
        // truncated but rewritten literals (representatives) persist, causing
        // incorrect model reconstruction (#3710, #3662).
        if self.cold.has_been_incremental {
            return false;
        }

        self.inproc.decompose_engine.ensure_num_vars(self.num_vars);

        let result = self.inproc.decompose_engine.run(
            &self.watches,
            self.num_vars,
            &self.vals,
            &self.cold.freeze_counts,
            self.var_lifecycle.as_slice(),
        );

        if result.unsat {
            // Phase I (#4606): SCC-UNSAT with LRAT hints.
            // When lit and ¬lit are in the same SCC, ¬lit is derivable as a unit.
            // The binary implication chain lit → ... → ¬lit proves it via RUP.
            // CaDiCaL: decompose_conflicting_scc_lrat (decompose.cpp:48-66).
            for unit in &result.units {
                if !self.var_is_assigned(unit.variable().index()) {
                    let hints = if self.cold.lrat_enabled {
                        self.collect_rup_unit_lrat_hints(*unit)
                    } else {
                        Vec::new()
                    };
                    // When hints are empty (unit not RUP under forward checker's
                    // clause DB), fall back to TrustedTransform. Same pattern as
                    // congruence non-contradiction units.
                    let proof_kind = if hints.is_empty() {
                        ProofAddKind::TrustedTransform
                    } else {
                        ProofAddKind::Derived
                    };
                    self.proof_emit_unit(*unit, &hints, proof_kind);
                    self.enqueue(*unit, None);
                }
            }
            // Let BCP detect the contradiction via propagate_check_unsat.
            // This ensures record_level0_conflict_chain constructs the proper
            // LRAT hint chain for the empty clause, instead of emitting it
            // with no hints (#4596).
            if self.propagate_check_unsat() {
                return true;
            }
            // Fallback: SCC says UNSAT but propagation didn't find it
            // (e.g., units were already assigned). Mark explicitly.
            self.mark_empty_clause_with_level0_hints();
            return true;
        }

        if result.substituted == 0 {
            // CaDiCaL deduplicate.cpp: decompose and clause shrinking can leave
            // duplicate binaries / hyper-unary opportunities even when no new
            // substitutions are found in this specific round.
            self.deduplicate_binary_clauses();
            return false;
        }

        // F1 (#4812): Assert no representative is a removed variable.
        // CaDiCaL: decompose.cpp:432-433 asserts !eliminated() && !substituted()
        // for all representatives. This catches bugs where removed variables
        // enter the SCC (e.g., lifecycle marking race in incremental solving).
        #[cfg(debug_assertions)]
        for (lit_idx, &repr) in result.reprs.iter().enumerate() {
            let repr_lit = Literal(repr.0);
            if repr_lit.index() == lit_idx {
                continue; // self-representative, skip
            }
            let repr_vi = repr_lit.variable().index();
            if repr_vi < self.var_lifecycle.as_slice().len() {
                debug_assert!(
                    !self.var_lifecycle.is_removed(repr_vi),
                    "BUG: decompose representative var {repr_vi} is removed (substituting lit {lit_idx})"
                );
            }
        }

        // Rewrite all clauses using the representative mapping.
        // CaDiCaL order: rewrite clauses → propagate units → mark substituted → flush watches.
        let rewrite = rewrite_clauses(&self.arena, &result.reprs, &self.vals);

        // Clear root-satisfied clause snapshots (#5237): conditioning saves clauses
        // satisfied at level 0, but decompose may substitute variables in those clauses.
        // The saved copies become stale — they reference pre-substitution literals that
        // no longer correspond to the rewritten clause DB.
        if !rewrite.actions.is_empty() {
            self.cold.root_satisfied_saved.clear();
        }

        // LRAT guard (#5067 audit): if rewrite would derive UNSAT (empty clause or
        // contradicting units), LRAT needs resolution hints we cannot produce here.
        // Skip the rewrite and let CDCL re-discover the contradiction with proper
        // LRAT chains. Matches the SCC-UNSAT guard (line 52 above).
        //
        // This check MUST happen before push_equivalence_reconstruction and before
        // mutations are applied. If we bail out after pushing reconstruction entries
        // but without rewriting clauses, the reconstruction stack would have entries
        // for substitutions that never happened, corrupting the model on SAT.
        if self.cold.lrat_enabled {
            let has_contradiction = rewrite.is_unsat || {
                // Check for contradicting units: same variable, opposite polarity.
                let mut seen = vec![0i8; self.num_vars]; // 0=unseen, 1=pos, -1=neg
                let mut conflict = false;
                for unit in result.units.iter().chain(rewrite.new_units.iter()) {
                    let vi = unit.variable().index();
                    let polarity: i8 = if unit.is_positive() { 1 } else { -1 };
                    if seen[vi] == -polarity {
                        conflict = true;
                        break;
                    }
                    // Also check against existing level-0 assignments.
                    if let Some(val) = self.var_value_from_vals(vi) {
                        if val != unit.is_positive() {
                            conflict = true;
                            break;
                        }
                    }
                    seen[vi] = polarity;
                }
                conflict
            };
            if has_contradiction {
                // Cannot produce LRAT hints for empty clause derivation from
                // decompose rewriting. Skip; CDCL will find the contradiction.
                return true;
            }
        }

        // No longer needed: substitute_in_existing() was a workaround for the
        // internal-index reconstruction stack. With external indices (#5250),
        // entries use stable external indices that never change during decompose.

        // Push equivalence reconstruction entries for substituted variables.
        // Placed after the LRAT guard: if we bail out above, no reconstruction
        // entries are pushed, avoiding a mismatch between reconstruction stack
        // and actual clause_db state (#5067 audit round 2).
        self.push_equivalence_reconstruction(&result.reprs);

        // Phase G (#4606): Derive equivalence binaries with LRAT hints.
        // For each substituted variable, derive two transient binary clauses:
        //   (repr ∨ ¬lit) — proves lit → repr
        //   (lit ∨ ¬repr) — proves repr → lit
        // These are used as LRAT hints for substituted clauses in Phase H.
        // CaDiCaL: decompose.cpp:436-479 (derive + weaken_minus + extension stack).
        //
        // Uses constructive chain approach (not probe-based): binary clause IDs
        // are collected during SCC BFS traversal in the engine, then mapped to
        // proof IDs here. This is deterministic and never fails.
        let mut decompose_equiv_ids: Vec<u64> = if self.cold.lrat_enabled {
            vec![0; self.num_vars * 2]
        } else {
            Vec::new()
        };
        let mut lrat_equiv_ok = true;
        if self.cold.lrat_enabled {
            for var_idx in 0..self.num_vars {
                let pos = Literal::positive(Variable(var_idx as u32));
                let repr = result.reprs[pos.index()];
                if repr == pos {
                    continue; // self-representative, no substitution
                }
                let lit = pos;

                // Get the pre-computed chains from the engine.
                let chain = if lit.index() < result.equiv_chains.len() {
                    &result.equiv_chains[lit.index()]
                } else {
                    lrat_equiv_ok = false;
                    break;
                };

                // Direction 1: (repr ∨ ¬lit) — proves lit → repr.
                // Hints: binary clause IDs along the path lit → ... → repr.
                let fwd_hints: Vec<u64> = chain
                    .lit_to_repr
                    .iter()
                    .map(|&cref| self.clause_id(ClauseRef(cref)))
                    .filter(|&id| id != 0)
                    .collect();
                if fwd_hints.is_empty() && !chain.lit_to_repr.is_empty() {
                    // Chain exists but all clause IDs are 0 — degenerate case.
                    lrat_equiv_ok = false;
                    break;
                }
                if fwd_hints.is_empty() {
                    lrat_equiv_ok = false;
                    break;
                }
                let id_fwd = self
                    .proof_emit_add(&[repr, lit.negated()], &fwd_hints, ProofAddKind::Derived)
                    .unwrap_or(0);
                decompose_equiv_ids[lit.negated().index()] = id_fwd;

                // Direction 2: (lit ∨ ¬repr) — proves repr → lit.
                // Hints: binary clause IDs along the path repr → ... → lit.
                let bwd_hints: Vec<u64> = chain
                    .repr_to_lit
                    .iter()
                    .map(|&cref| self.clause_id(ClauseRef(cref)))
                    .filter(|&id| id != 0)
                    .collect();
                if bwd_hints.is_empty() && !chain.repr_to_lit.is_empty() {
                    lrat_equiv_ok = false;
                    break;
                }
                if bwd_hints.is_empty() {
                    lrat_equiv_ok = false;
                    break;
                }
                let id_bwd = self
                    .proof_emit_add(&[lit, repr.negated()], &bwd_hints, ProofAddKind::Derived)
                    .unwrap_or(0);
                decompose_equiv_ids[lit.index()] = id_bwd;
            }
        }

        // Emit proof records for clause mutations captured by rewrite_clauses.
        //
        // Two-phase emission: ALL additions first, then ALL deletions.
        // Within a single Replaced/Unit pair, add-before-delete is obvious.
        // But across mutations, an earlier Replaced deletion can remove a clause
        // that a later Unit addition needs for RUP verification. Example:
        //   Replaced { old: (x2,x3), new: (x2,x1) } → delete (x2,x3)
        //   Unit { unit: x1, old: (x3,x1) }          → add (x1)
        // The unit (x1) needs (x2,x3) for its RUP chain, but it's already deleted.
        // Fix: emit all adds while the original formula is intact, then delete.
        // Pre-compute clause IDs before borrowing proof_manager mutably.
        // clause_id() reads self.cold.clause_ids which conflicts with &mut self.proof_manager.
        let mutation_ids: Vec<u64> = rewrite
            .actions
            .iter()
            .map(|m| {
                let ci = match m {
                    crate::decompose::ClauseMutation::Deleted { clause_idx, .. }
                    | crate::decompose::ClauseMutation::Replaced { clause_idx, .. }
                    | crate::decompose::ClauseMutation::Unit { clause_idx, .. } => *clause_idx,
                };
                self.clause_id(ClauseRef(ci as u32))
            })
            .collect();

        if self.cold.lrat_enabled && lrat_equiv_ok {
            // Rewritten clauses can drop literals that are already false at
            // level 0. Materialize those unit proofs before building the LRAT
            // substitution chains so the dropped literals are justified.
            self.materialize_level0_unit_proofs();
        }

        // Collect unit proof IDs; store in unit_proof_id afterward (#4636).
        let mut unit_pids: Vec<(usize, u64)> = Vec::new();
        // Phase 1 / Phase H (#4606): emit all additions while original formula
        // is intact. In LRAT mode (with successful Phase G), collect equivalence
        // binary IDs + unit IDs + original clause ID as hints.
        // CaDiCaL: decompose.cpp:491-576.
        // Also emit SCC units here (before deletions) so the forward checker
        // can still find the original binary clauses forming the SCC cycle
        // for RUP verification (#4966).
        for (mutation, &cid) in rewrite.actions.iter().zip(mutation_ids.iter()) {
            match mutation {
                crate::decompose::ClauseMutation::Replaced {
                    old,
                    new,
                    clause_idx,
                } => {
                    let hints = if self.cold.lrat_enabled && lrat_equiv_ok {
                        self.build_decompose_subst_hints(
                            old,
                            &result.reprs,
                            &decompose_equiv_ids,
                            cid,
                        )
                    } else if cid != 0 {
                        vec![cid]
                    } else {
                        Vec::new()
                    };
                    let kind = if hints.is_empty() {
                        ProofAddKind::TrustedTransform
                    } else {
                        ProofAddKind::Derived
                    };
                    let new_id = self.proof_emit_add(new, &hints, kind).unwrap_or(0);
                    // Update clause_ids so deduplication/later deletions use the
                    // new proof ID, not the stale original that Phase 2 will delete.
                    if new_id != 0 && *clause_idx < self.cold.clause_ids.len() {
                        self.cold.clause_ids[*clause_idx] = new_id;
                    }
                }
                crate::decompose::ClauseMutation::Unit { unit, old, .. } => {
                    let hints = if self.cold.lrat_enabled && lrat_equiv_ok {
                        self.build_decompose_subst_hints(
                            old,
                            &result.reprs,
                            &decompose_equiv_ids,
                            cid,
                        )
                    } else if cid != 0 {
                        vec![cid]
                    } else {
                        Vec::new()
                    };
                    let kind = if hints.is_empty() {
                        ProofAddKind::TrustedTransform
                    } else {
                        ProofAddKind::Derived
                    };
                    let pid = self.proof_emit_unit(*unit, &hints, kind);
                    if pid != 0 {
                        unit_pids.push((unit.variable().index(), pid));
                    }
                }
                crate::decompose::ClauseMutation::Deleted { .. } => {}
            }
        }
        // Phase 1b: emit SCC-derived units while original binary clauses are
        // still present in the forward checker. These units are derived from
        // the binary implication graph (a variable and its negation in the same
        // SCC), so the original binary clauses must exist for RUP to succeed.
        // Only emit the proof entry here; enqueue() happens later after clause
        // mutations are applied (#4966).
        for unit in &result.units {
            if !self.var_is_assigned(unit.variable().index()) {
                let hints = if self.cold.lrat_enabled {
                    self.collect_rup_unit_lrat_hints(*unit)
                } else {
                    Vec::new()
                };
                self.proof_emit_unit(*unit, &hints, ProofAddKind::Derived);
            }
        }
        // Phase 2: emit all deletions with real clause IDs (not 0).
        for (mutation, &cid) in rewrite.actions.iter().zip(mutation_ids.iter()) {
            match mutation {
                crate::decompose::ClauseMutation::Deleted { old, .. } => {
                    let _ = self.proof_emit_delete(old, cid);
                }
                crate::decompose::ClauseMutation::Replaced { old, .. } => {
                    let _ = self.proof_emit_delete(old, cid);
                }
                crate::decompose::ClauseMutation::Unit { old, .. } => {
                    let _ = self.proof_emit_delete(old, cid);
                }
            }
        }
        // Phase J (#4606): delete transient equivalence binaries from proof.
        // CaDiCaL decompose.cpp:651-676. These were derived in Phase G for
        // LRAT hint purposes; not actual clause DB entries.
        if self.cold.lrat_enabled && lrat_equiv_ok {
            for var_idx in 0..self.num_vars {
                let pos = Literal::positive(Variable(var_idx as u32));
                let repr = result.reprs[pos.index()];
                if repr == pos {
                    continue;
                }
                let lit = pos;
                let id_fwd = decompose_equiv_ids[lit.negated().index()];
                if id_fwd != 0 {
                    let _ = self.proof_emit_delete(&[repr, lit.negated()], id_fwd);
                }
                let id_bwd = decompose_equiv_ids[lit.index()];
                if id_bwd != 0 {
                    let _ = self.proof_emit_delete(&[lit, repr.negated()], id_bwd);
                }
            }
        }
        // Apply deferred unit_proof_id stores outside manager borrow (#4636).
        for (var_idx, pid) in unit_pids {
            self.unit_proof_id[var_idx] = pid;
        }

        // Apply clause mutations (#3440).
        // Mark variables in mutated clauses as dirty BVE candidates BEFORE
        // applying the mutation (which may delete the clause). (#7905)
        for action in &rewrite.actions {
            let lits: Option<Vec<Literal>> = match action {
                crate::decompose::ClauseMutation::Deleted { clause_idx, .. }
                | crate::decompose::ClauseMutation::Unit { clause_idx, .. } => {
                    if *clause_idx < self.arena.len()
                        && self.arena.is_active(*clause_idx)
                        && !self.arena.is_learned(*clause_idx)
                    {
                        Some(self.arena.literals(*clause_idx).to_vec())
                    } else {
                        None
                    }
                }
                crate::decompose::ClauseMutation::Replaced {
                    clause_idx, new, ..
                } => {
                    if *clause_idx < self.arena.len()
                        && self.arena.is_active(*clause_idx)
                        && !self.arena.is_learned(*clause_idx)
                    {
                        let old = self.arena.literals(*clause_idx).to_vec();
                        self.inproc.bve.mark_candidates_dirty_clause(new);
                        Some(old)
                    } else {
                        None
                    }
                }
            };
            if let Some(old_lits) = &lits {
                self.inproc.bve.mark_candidates_dirty_clause(old_lits);
            }
            self.apply_decompose_mutation(action);
        }
        self.cold.clause_db_changes += u64::from(rewrite.removed) + u64::from(rewrite.shortened);
        // Mark for BVE re-trigger (CaDiCaL decompose.cpp:613 mark_removed).
        self.cold.bve_marked += u64::from(rewrite.removed) + u64::from(rewrite.shortened);

        if rewrite.is_unsat {
            self.mark_empty_clause_with_level0_hints();
            return true;
        }

        // Propagate new units before marking variables as substituted.
        // CaDiCaL: decompose.cpp:695-698 — propagate MUST happen while substituted
        // variables are still active, so BCP can traverse their watch lists.
        //
        // SCC units (result.units): proof already emitted in Phase 1b (#4966).
        // Rewrite units (rewrite.new_units): already emitted via actions Unit variant.
        //
        // Contradiction detection (#5067): CaDiCaL interleaves unit assignment
        // with clause rewriting (decompose.cpp:538-590), so val() checks during
        // substitution detect contradicting units as empty clauses. Z4 separates
        // rewriting (read-only rewrite_clauses) from assignment (here). When two
        // clauses independently reduce to contradicting units (e.g., [+x] and
        // [−x]), the second enqueue must detect the conflict; otherwise the
        // contradicting unit's original clause was already deleted from the DB
        // and the constraint is permanently lost.
        for unit in &result.units {
            let vi = unit.variable().index();
            if let Some(val) = self.var_value_from_vals(vi) {
                if val != unit.is_positive() {
                    // Contradicting unit: variable already assigned opposite polarity.
                    // LRAT: empty clause = resolve existing unit proof with new unit proof.
                    // Use BFS transitive closure for complete LRAT chain (#7108).
                    if self.cold.lrat_enabled {
                        let new_unit_pid = self.unit_proof_id.get(vi).copied().unwrap_or(0);
                        let hints = self
                            .collect_empty_clause_hints_for_unit_contradiction(new_unit_pid, vi);
                        self.mark_empty_clause_with_hints(&hints);
                    } else {
                        self.mark_empty_clause();
                    }
                    return true;
                }
                // Same polarity: harmless duplicate, skip.
            } else {
                self.enqueue(*unit, None);
            }
        }
        for unit in &rewrite.new_units {
            let vi = unit.variable().index();
            if let Some(val) = self.var_value_from_vals(vi) {
                if val != unit.is_positive() {
                    // Use BFS transitive closure for complete LRAT chain (#7108).
                    if self.cold.lrat_enabled {
                        let new_unit_pid = self.unit_proof_id.get(vi).copied().unwrap_or(0);
                        let hints = self
                            .collect_empty_clause_hints_for_unit_contradiction(new_unit_pid, vi);
                        self.mark_empty_clause_with_hints(&hints);
                    } else {
                        self.mark_empty_clause();
                    }
                    return true;
                }
            } else {
                // Proof ID already captured in actions Unit emission above (#4626).
                self.enqueue(*unit, None);
            }
        }

        // Mark substituted variables as eliminated and remove from VSIDS.
        // CaDiCaL: decompose.cpp:700-714 — marks substituted AFTER propagation.
        // Guard: if the representative is fixed (assigned at level 0), skip marking.
        // CaDiCaL: `if (!flags(other).fixed()) mark_substituted(idx)` at line 712.
        for var_idx in 0..self.num_vars {
            let pos = Literal::positive(Variable(var_idx as u32));
            let repr_pos = result.reprs[pos.index()];
            if repr_pos == pos {
                continue;
            }
            // Skip if already removed (e.g., by BVE in same inprocessing round)
            // or fixed at level 0 (CaDiCaL: `flags(other).fixed()` guard).
            if self.var_lifecycle.is_removed(var_idx) || self.var_lifecycle.is_fixed(var_idx) {
                continue;
            }
            // CaDiCaL fixed() guard: if the representative is assigned at level 0,
            // the substituted variable will get its value through propagation, not
            // through the substitution mechanism. Don't mark as substituted.
            let repr_var = repr_pos.variable().index();
            if repr_var < self.num_vars && self.var_is_assigned(repr_var) {
                continue;
            }

            let var = Variable(var_idx as u32);
            // V4 fix (#3906): decompose marks variables as Substituted, not Eliminated.
            // CaDiCaL: decompose.cpp:712 uses mark_substituted().
            self.var_lifecycle.mark_substituted(var_idx);
            self.vsids.remove_from_heap(var);

            // Diagnostic trace: var_transition active → substituted (Wave 3, #4211)
            if let Some(ref writer) = self.cold.diagnostic_trace {
                writer.emit_var_transition(
                    var.0,
                    crate::diagnostic_trace::VarState::Active,
                    crate::diagnostic_trace::VarState::Substituted,
                    self.cold.diagnostic_pass,
                );
            }
        }

        // GC learned clauses containing substituted variables (#5149).
        // rewrite_clauses processes ALL clauses (learned + irredundant), so
        // this pass is a safety net for learned clauses missed by rewrite.
        // Defer the O(num_vars) stale reason scan during the bulk deletion
        // loop; one pass after the loop handles all stale references.
        self.defer_stale_reason_cleanup = true;
        {
            let all_indices: Vec<usize> = self.arena.indices().collect();
            for idx in all_indices {
                if self.arena.is_empty_clause(idx) || !self.arena.is_active(idx) {
                    continue;
                }
                let has_substituted = self
                    .arena
                    .literals(idx)
                    .iter()
                    .any(|lit| self.var_lifecycle.is_removed(lit.variable().index()));
                if has_substituted {
                    self.delete_clause_checked(idx, ReasonPolicy::ClearLevel0);
                }
            }
        }
        self.defer_stale_reason_cleanup = false;
        self.clear_stale_reasons();

        // Rebuild all watch lists. Clause mutations (replacements, deletions)
        // invalidate watched literal positions. rebuild_watches() also handles
        // qhead rewinding for re-propagation.
        // Decompose rewrites clause literals (substitution), so full re-propagation
        // from position 0 is needed (#8095).
        self.mark_trail_affected(0);
        self.rebuild_watches();

        // CaDiCaL does NOT eagerly assign substituted variables here.
        // Model reconstruction handles it: the BCE entries pushed above
        // ((repr ∨ ¬lit) and (¬repr ∨ lit)) correctly set substituted
        // variables from their representative's value during extend_model.
        // Eager assignment with reason=None created inconsistent state:
        // eliminated variables on the trail without reasons, breaking
        // conflict analysis (#3424, #3466).

        // CaDiCaL deduplicate.cpp: equivalent-literal substitution can leave
        // duplicate binaries and discover hyper-unary units.
        if self.deduplicate_binary_clauses() {
            #[allow(clippy::needless_return)]
            return true;
        }

        // Post-condition: every variable whose representative differs from itself
        // (and whose representative is not fixed at level 0) should be marked eliminated.
        // Without this, substituted-but-not-eliminated variables remain on the VSIDS
        // heap and can be decided, causing propagation over dead watch lists.
        #[cfg(debug_assertions)]
        for var_idx in 0..self.num_vars.min(result.reprs.len() / 2) {
            let pos = Literal::positive(Variable(var_idx as u32));
            let repr_pos = result.reprs[pos.index()];
            if repr_pos == pos {
                continue;
            }
            let repr_var = repr_pos.variable().index();
            // Skip the CaDiCaL fixed() guard case: if repr is assigned at level 0,
            // the variable is propagated rather than eliminated.
            if repr_var < self.num_vars && self.var_is_assigned(repr_var) {
                continue;
            }
            debug_assert!(
                self.var_lifecycle.is_removed(var_idx),
                "BUG: decompose substituted var {var_idx} (repr={repr_pos:?}) \
                 but did not mark it as removed"
            );
        }
        true
    }

    /// Build LRAT hints for a substituted clause in decompose.
    ///
    /// Phase H (#4606): For each literal in the original clause:
    /// - If substituted: include the equivalence binary ID that proves orig → repr
    /// - If false at level 0: include its unit proof ID
    ///
    /// Appends the original clause ID last. CaDiCaL: decompose.cpp:526-576.
    fn build_decompose_subst_hints(
        &self,
        old_lits: &[Literal],
        reprs: &[Literal],
        decompose_equiv_ids: &[u64],
        original_cid: u64,
    ) -> Vec<u64> {
        let mut hints = Vec::new();
        for orig_lit in old_lits {
            let li = orig_lit.index();
            let mapped = reprs.get(li).copied().unwrap_or(*orig_lit);
            // Check if this literal was substituted (repr differs).
            if mapped != *orig_lit {
                // Include the equivalence binary proving orig_lit → repr.
                // The binary (repr ∨ ¬orig_lit) is stored at equiv_ids[orig_lit.negated()].
                let neg_idx = orig_lit.negated().index();
                if neg_idx < decompose_equiv_ids.len() {
                    let equiv_id = decompose_equiv_ids[neg_idx];
                    if equiv_id != 0 {
                        hints.push(equiv_id);
                    }
                }
            }
            // If the rewritten literal is false at level 0, include the proof
            // of its negation. This covers both unchanged literals already
            // falsified at the root and substituted literals whose mapped
            // representative is falsified at level 0.
            if self.lit_val(mapped) < 0 {
                let mapped_var = mapped.variable().index();
                if let Some(uid) = self.level0_var_proof_id(mapped_var) {
                    hints.push(uid);
                }
            }
        }
        // Original clause ID last (CaDiCaL decompose.cpp:576).
        if original_cid != 0 {
            hints.push(original_cid);
        }
        hints
    }
}
