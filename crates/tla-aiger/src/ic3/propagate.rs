// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! IC3 frame propagation: propagate lemmas forward, push_lemma, infinity frame
//! promotion, and core extraction helpers.

use super::config::consecution_verify_interval_full;
use super::engine::Ic3Engine;
use super::frame::Lemma;
use crate::sat_types::{Lit, SatResult, SatSolver, Var};

/// Unforgeable witness that the blocking loop exited via the natural
/// `get_bad() => None` arm, i.e. `F_top ∧ bad` is UNSAT at the current depth.
///
/// Constructed exclusively by [`ConvergenceProof::from_natural_exit`], which is
/// `pub(super)` — only other modules inside `ic3` (specifically `run.rs`'s
/// natural-exit break arm) can mint one. Any other blocking-loop break path
/// (budget, repeated-cube #4139, drop_po discards, cancellation) MUST pass
/// `None` to [`Ic3Engine::propagate`] because it has no way to obtain this
/// witness.
///
/// This replaces the prior `blocking_completed_naturally: bool` parameter
/// (#4310 runtime gate → #4317 type gate), so the soundness precondition for
/// the #4247 trivially-safe convergence shortcut is enforced by the compiler
/// instead of by convention.
#[derive(Debug, Clone, Copy)]
pub(crate) struct ConvergenceProof {
    // Private field prevents external `ConvergenceProof { .. }` construction
    // and keeps the type opaque. The only supported constructor is
    // `from_natural_exit` below.
    _private: (),
}

impl ConvergenceProof {
    /// Mint a convergence witness. Call sites MUST be in the
    /// `get_bad() => None` break arm of the blocking loop (`run.rs`); any
    /// other call site is a soundness bug (#4310, #4317).
    #[inline]
    pub(super) fn from_natural_exit() -> Self {
        Self { _private: () }
    }
}

/// Outcome of a full propagation pass.
///
/// Callers that want to emit `Safe` MUST observe the [`PropagateOutcome::Converged`]
/// variant explicitly (typically via `matches!` or `match`). Adding a new
/// outcome in the future therefore requires explicit handling at every call
/// site, preventing accidental fallthrough like the pre-#4310 `bool` return.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PropagateOutcome {
    /// Propagation reached convergence — the inductive invariant is
    /// witnessed either by a standard frame fixpoint or by the #4247
    /// trivially-safe shortcut (which itself requires a
    /// [`ConvergenceProof`]). The caller may report `Safe` at this depth.
    Converged,
    /// Propagation did not converge. The caller should advance to the next
    /// depth.
    NotYet,
}

impl Ic3Engine {
    /// Push a generalized lemma to higher frames.
    pub(super) fn push_lemma(&mut self, frame: usize, mut cube: Vec<Lit>) -> (usize, Vec<Lit>) {
        let depth = self.frames.depth();
        for f in (frame + 1)..=depth {
            if f > self.solvers.len() {
                break;
            }
            if self.cube_sat_consistent_with_init(&cube) {
                return (f, cube);
            }
            let neg_cube: Vec<Lit> = cube.iter().map(|l| !*l).collect();
            let assumptions = self.prime_cube(&cube);

            // Domain-restricted consecution (#4059, #4091).
            // `build_consecution_domain_solver` gates at >= 20 latches (reverted from 2).
            // Domain returned alongside solver to avoid double-computation (#4081).
            let is_ind = if let Some((mut domain_solver, domain)) =
                self.build_consecution_domain_solver(f, &cube)
            {
                domain_solver.set_cancelled(self.cancelled.clone());
                let domain_result =
                    domain_solver.solve_with_temporary_clause(&assumptions, &neg_cube);
                if domain_result == SatResult::Unsat {
                    true
                } else {
                    let solver_idx = f - 1;
                    if self.solvers[solver_idx].is_poisoned() {
                        if self.solver_rebuild_budget_exceeded(solver_idx) {
                            return (f, cube); // Conservative: stop pushing (#4105)
                        }
                        self.rebuild_solver_at(solver_idx);
                    }
                    // Reuse domain from build_consecution_domain_solver (#4081).
                    let domain_vars: Vec<Var> = (0..=self.max_var)
                        .filter(|&i| domain.contains(Var(i)))
                        .map(Var)
                        .collect();
                    // small_circuit_mode (#4259, z4#8802): skip set_domain so
                    // z4-sat uses search_propagate_standard (plain BCP).
                    if !self.config.small_circuit_mode {
                        self.solvers[solver_idx].set_domain(&domain_vars);
                    }
                    let result = self.solvers[solver_idx]
                        .solve_with_temporary_clause(&assumptions, &neg_cube)
                        == SatResult::Unsat;
                    if !self.config.small_circuit_mode {
                        self.solvers[solver_idx].clear_domain();
                    }
                    result
                }
            } else {
                let solver_idx = f - 1;
                if self.solvers[solver_idx].is_poisoned() {
                    if self.solver_rebuild_budget_exceeded(solver_idx) {
                        return (f, cube); // Conservative: stop pushing (#4105)
                    }
                    self.rebuild_solver_at(solver_idx);
                }
                self.solvers[solver_idx].solve_with_temporary_clause(&assumptions, &neg_cube)
                    == SatResult::Unsat
            };

            if !is_ind {
                return (f, cube);
            }

            // Inductive-subclause generalization during push (#4244).
            //
            // After confirming `cube` is inductive at frame `f`, try to drop
            // individual literals in ascending VSIDS-activity order. Each
            // successful drop yields a strictly stronger lemma at `f` without
            // additional propagation. This mirrors rIC3's push-time
            // generalization and Bradley's `pushForward` in IC3ref.
            //
            // Gated behind `config.push_generalize` (default off) because
            // aggressive push-time drops caused premature convergence
            // failures in the reverted implementation noted in #4244. The
            // conservative guard here uses the SAME solver path that
            // validated inductiveness above (frame solver or domain solver),
            // and every candidate subclause is re-checked for init
            // consistency so no unsound cube is admitted.
            if self.config.push_generalize {
                cube = self.try_push_generalize(f, cube);
            }
        }
        (depth + 1, cube)
    }

    /// Try to drop literals from a cube that has already been shown to be
    /// inductive at `frame`, returning a (possibly) shorter inductive cube.
    ///
    /// The cube must already satisfy `F_{frame-1} AND !cube AND T |= !cube'`.
    /// For each candidate literal (ascending VSIDS activity, low first), this
    /// function:
    ///   1. Removes the literal tentatively.
    ///   2. Rejects the candidate if the shorter cube intersects the initial
    ///      states (which would produce an unsound lemma).
    ///   3. Re-runs a relative-inductiveness check against frame `f`.
    ///   4. Accepts the drop on UNSAT, restores the literal on SAT/Unknown.
    ///
    /// Bounded by `config.push_generalize_budget` accepted drops to keep
    /// per-push work linear in |cube| worst-case. Returns the original cube
    /// unchanged if the budget is zero, if the frame is invalid, or if no
    /// literal can be safely dropped.
    pub(super) fn try_push_generalize(&mut self, frame: usize, cube: Vec<Lit>) -> Vec<Lit> {
        if cube.len() <= 1 {
            return cube;
        }
        let budget = self.config.push_generalize_budget;
        if budget == 0 {
            return cube;
        }
        if frame == 0 || frame > self.solvers.len() {
            return cube;
        }

        // Candidate order: ascending activity (low-activity literals are the
        // most likely to be inessential, so we try them first).
        let mut order: Vec<Lit> = cube.clone();
        self.vsids.sort_by_activity(&mut order);
        // `sort_by_activity` is descending; reverse to try low-activity first.
        order.reverse();

        let mut current: Vec<Lit> = cube;
        let mut dropped: usize = 0;
        for candidate in order {
            if dropped >= budget {
                break;
            }
            if current.len() <= 1 {
                break;
            }
            // Build the subclause with `candidate` removed.
            let trial: Vec<Lit> = current
                .iter()
                .copied()
                .filter(|l| *l != candidate)
                .collect();
            if trial.len() == current.len() {
                // Literal not present (already dropped via a compatible drop).
                continue;
            }
            // Soundness: reject trial cubes that intersect Init.
            if self.cube_sat_consistent_with_init(&trial) {
                continue;
            }
            if self.inductive_at_frame(frame, &trial) {
                current = trial;
                dropped += 1;
            }
        }
        current
    }

    /// Relative-inductiveness check at `frame` using the same solver strategy
    /// as `push_lemma`: domain-restricted mini-solver when available, falling
    /// back to the frame solver with native domain BCP on >= 20 latches.
    ///
    /// Returns true iff `F_{frame-1} AND !cube AND T |= !cube'` under the
    /// current frame/lemma state.
    fn inductive_at_frame(&mut self, frame: usize, cube: &[Lit]) -> bool {
        if frame == 0 || frame > self.solvers.len() {
            return false;
        }
        let neg_cube: Vec<Lit> = cube.iter().map(|l| !*l).collect();
        let assumptions = self.prime_cube(cube);

        if let Some((mut domain_solver, _domain)) =
            self.build_consecution_domain_solver(frame, cube)
        {
            domain_solver.set_cancelled(self.cancelled.clone());
            if domain_solver.solve_with_temporary_clause(&assumptions, &neg_cube)
                == SatResult::Unsat
            {
                return true;
            }
            // Domain result was SAT or Unknown. Fall through to frame solver
            // to match `push_lemma`'s fallback policy.
        }

        let solver_idx = frame - 1;
        if self.solvers[solver_idx].is_poisoned() {
            if self.solver_rebuild_budget_exceeded(solver_idx) {
                // Conservative: can't verify, treat as not inductive so we
                // leave the literal in place.
                return false;
            }
            self.rebuild_solver_at(solver_idx);
        }
        self.solvers[solver_idx].solve_with_temporary_clause(&assumptions, &neg_cube)
            == SatResult::Unsat
    }

    /// Check if a cube is blocked at a frame and return the inductive core.
    ///
    /// Uses `!cube` strengthening (the lemma clause) to match the standard IC3
    /// relative inductiveness check: `F_k AND !cube AND T AND cube' is UNSAT`.
    /// Without strengthening, this function checked a strictly stronger property
    /// (`F_k AND T AND cube' is UNSAT`), which missed valid propagation opportunities
    /// where the cube is relatively inductive but not absolutely inductive.
    ///
    /// This matches `push_lemma()` which correctly uses `solve_with_temporary_clause`
    /// with the `!cube` strengthening clause (#4181).
    pub(super) fn propagation_blocked(&mut self, frame: usize, cube: &[Lit]) -> Option<Vec<Lit>> {
        if frame == 0 {
            return None;
        }
        let solver_idx = frame - 1;
        if solver_idx >= self.solvers.len() {
            return None;
        }
        let assumptions = self.prime_cube(cube);
        // Strengthening clause: !cube = the lemma itself.
        // Adding this to the query means: "assuming the current state satisfies
        // the lemma (does NOT satisfy the cube), can the next state satisfy the
        // cube?" This is the standard IC3 relative inductiveness check.
        let neg_cube: Vec<Lit> = cube.iter().map(|l| !*l).collect();

        // Domain-restricted consecution (#4059, #4091).
        // `build_consecution_domain_solver` gates at >= 20 latches (reverted from 2).
        // Domain returned alongside solver to avoid double-computation (#4081).
        if let Some((mut domain_solver, domain)) = self.build_consecution_domain_solver(frame, cube)
        {
            self.domain_stats
                .record(domain.len(), self.max_var as usize + 1, true);

            domain_solver.set_cancelled(self.cancelled.clone());
            let domain_result = domain_solver.solve_with_temporary_clause(&assumptions, &neg_cube);
            if domain_result == SatResult::Unsat {
                let core = self.core_from_solver(domain_solver.as_ref(), cube);
                return Some(core);
            }
        } else {
            self.domain_stats
                .record(0, self.max_var as usize + 1, false);
        }

        if self.solvers[solver_idx].is_poisoned() {
            if self.solver_rebuild_budget_exceeded(solver_idx) {
                return None; // Conservative: treat as not blocked (#4105)
            }
            self.rebuild_solver_at(solver_idx);
        }

        // Set domain on the full frame solver for z4-sat native domain BCP.
        // Even when the clause-filtered mini-solver didn't return UNSAT (or
        // wasn't built), the frame solver benefits from domain-restricted BCP
        // and VSIDS branching. This matches the pattern in block_one and
        // push_lemma which both set/clear domain on the full solver fallback.
        let domain_computed = self.domain_computer.compute_domain(cube, &self.next_vars);
        let domain_vars: Vec<Var> = (0..=self.max_var)
            .filter(|&i| domain_computed.contains(Var(i)))
            .map(Var)
            .collect();
        // small_circuit_mode (#4259, z4#8802): skip set_domain so z4-sat uses
        // search_propagate_standard (plain BCP) instead of propagate_domain_bcp.
        let use_domain = !self.config.small_circuit_mode
            && self.ts.latch_vars.len() >= 20
            && !domain_vars.is_empty();
        if use_domain {
            self.solvers[solver_idx].set_domain(&domain_vars);
        }

        let result = self.solvers[solver_idx].solve_with_temporary_clause(&assumptions, &neg_cube);
        let ret = match result {
            SatResult::Unsat => {
                let core = self.core_from_solver(self.solvers[solver_idx].as_ref(), cube);
                Some(core)
            }
            SatResult::Unknown => {
                if use_domain {
                    self.solvers[solver_idx].clear_domain();
                }
                if self.solver_rebuild_budget_exceeded(solver_idx) {
                    return None; // Conservative: treat as not blocked (#4105)
                }
                self.rebuild_solver_at(solver_idx);
                if use_domain {
                    self.solvers[solver_idx].set_domain(&domain_vars);
                }
                let retry =
                    self.solvers[solver_idx].solve_with_temporary_clause(&assumptions, &neg_cube);
                if use_domain {
                    self.solvers[solver_idx].clear_domain();
                }
                if retry == SatResult::Unsat {
                    let core = self.core_from_solver(self.solvers[solver_idx].as_ref(), cube);
                    Some(core)
                } else {
                    None
                }
            }
            SatResult::Sat => None,
        };

        if use_domain && result != SatResult::Unknown {
            self.solvers[solver_idx].clear_domain();
        }
        ret
    }

    /// Extract inductive core from a solver after an UNSAT result.
    pub(super) fn core_from_solver(&self, solver: &dyn SatSolver, cube: &[Lit]) -> Vec<Lit> {
        let Some(core) = solver.unsat_core() else {
            return cube.to_vec();
        };
        if core.is_empty() {
            return cube.to_vec();
        }
        let mut core_latch_vars = rustc_hash::FxHashSet::default();
        for &core_lit in &core {
            if let Some(&latch_var) = self.reverse_next.get(&core_lit.var()) {
                core_latch_vars.insert(latch_var);
            }
        }
        let reduced: Vec<Lit> = cube
            .iter()
            .filter(|lit| core_latch_vars.contains(&lit.var()))
            .copied()
            .collect();
        if reduced.is_empty() {
            return cube.to_vec();
        }
        if self.cube_sat_consistent_with_init(&reduced) {
            cube.to_vec()
        } else {
            reduced
        }
    }

    /// Propagate lemmas forward through frames with Counter-To-Propagation (CTP).
    /// Run frame propagation.
    ///
    /// `blocking_witness` carries an unforgeable [`ConvergenceProof`] when the
    /// preceding blocking phase exited via `get_bad() => None` (i.e.,
    /// `F_top ∧ bad` is provably UNSAT at this depth). It is `None` when
    /// blocking exited via any early-out path (blocking budget exhausted,
    /// repeated-cube limit #4139, drop_po discarded obligations, cooperative
    /// cancellation) — in those cases the top frame may still admit reachable
    /// bad cubes that were never blocked.
    ///
    /// The witness gates the "trivially-safe convergence" shortcut (#4247):
    /// that shortcut is only sound when `F_top ∧ bad` is known UNSAT. Since
    /// [`ConvergenceProof`] has no public constructor and the only
    /// `pub(super)` constructor ([`ConvergenceProof::from_natural_exit`]) is
    /// called exclusively from `run.rs`'s natural-exit break arm, the type
    /// system now prevents any other blocking-loop exit path from accidentally
    /// triggering the shortcut (#4310 → #4317).
    ///
    /// Returns [`PropagateOutcome::Converged`] on convergence, or
    /// [`PropagateOutcome::NotYet`] when the caller should advance to the next
    /// depth.
    pub(super) fn propagate(
        &mut self,
        blocking_witness: Option<ConvergenceProof>,
    ) -> PropagateOutcome {
        let depth = self.frames.depth();
        let blocking_completed_naturally = blocking_witness.is_some();
        if depth < 2 {
            return PropagateOutcome::NotYet;
        }
        for k in 1..depth - 1 {
            // Cooperative cancellation (#4096): propagation iterates over all
            // frames and all lemmas within each frame, making SAT calls per
            // lemma. Check cancellation at each frame level so the thread
            // exits promptly after the portfolio signals timeout.
            if self.is_cancelled() {
                return PropagateOutcome::NotYet;
            }
            self.frames.frames[k].lemmas.sort_by_key(|l| l.lits.len());
            let lemmas: Vec<Lemma> = self.frames.frames[k].lemmas.clone();
            let orig_count = lemmas.len();
            let mut pushed_indices = rustc_hash::FxHashSet::default();
            for (idx, lemma) in lemmas.iter().enumerate() {
                let cube: Vec<Lit> = lemma.lits.iter().map(|l| !*l).collect();
                let ctp_max = if self.config.ctp {
                    self.config.ctp_max
                } else {
                    1
                };
                let mut succeeded = false;
                for _ctp_attempt in 0..ctp_max {
                    if let Some(core_cube) = self.propagation_blocked(k + 1, &cube) {
                        if self.cube_sat_consistent_with_init(&core_cube) {
                            break;
                        }
                        self.consecution_verify_counter += 1;
                        let verify_interval = consecution_verify_interval_full(
                            self.ts.trans_clauses.len(),
                            self.ts.constraint_lits.len(),
                            self.ts.latch_vars.len(),
                        );
                        if self.ts.latch_vars.len() <= 60
                            && !self.crosscheck_disabled
                            && self.consecution_verify_counter % verify_interval == 0
                            && !self.verify_consecution_independent(k + 1, &core_cube, true)
                        {
                            break;
                        }
                        let core_lemma = Lemma::from_blocked_cube(&core_cube);
                        self.frames.add_lemma(k + 1, core_lemma.clone());
                        if k + 1 < self.solvers.len() {
                            self.solvers[k + 1].add_clause(&core_lemma.lits);
                        }
                        pushed_indices.insert(idx);
                        succeeded = true;
                        break;
                    }
                    if !self.config.ctp || k == 0 {
                        break;
                    }
                    let pred = self.extract_full_state_from_solver(self.solvers[k].as_ref());
                    if self.cube_consistent_with_init(&pred) {
                        break;
                    }
                    let mut tb_limit = self.config.ctg_limit;
                    if !self.trivial_block(k, pred, &mut tb_limit) {
                        break;
                    }
                }
                if !succeeded {
                    // Lemma stays at frame k.
                }
            }
            if !pushed_indices.is_empty() {
                let new_lemmas: Vec<Lemma> = self.frames.frames[k]
                    .lemmas
                    .iter()
                    .filter(|l| !lemmas.contains(l))
                    .cloned()
                    .collect();
                let mut kept: Vec<Lemma> = lemmas
                    .into_iter()
                    .enumerate()
                    .filter(|(i, _)| !pushed_indices.contains(i))
                    .map(|(_, l)| l)
                    .collect();
                kept.extend(new_lemmas);
                self.frames.frames[k].lemmas = kept;
            }
            if self.frames.frames[k].lemmas.is_empty() && orig_count > 0 {
                // Standard IC3 convergence: all lemmas at frame k pushed to k+1,
                // so F_k = F_{k+1} (inductive). Safety also requires
                // F_top ⇒ ¬bad, which only holds when blocking exited naturally
                // (`get_bad() => None`). If blocking exited via an early-out
                // path (budget, #4139 repeated cube, drop_po), F_top may still
                // admit an unblocked reachable bad cube — returning Safe here
                // would be unsound.
                //
                // SOUNDNESS GATE (#4320): same class as the #4310 fix on the
                // trivially-safe (#4247) path. Observed on
                // `shift_register_top_w16_d16_e0.aig` (R22 canary): depth=2
                // blocking exited via #4139 repeated-cube break, propagate at
                // depth=3 then pushed frame 1's 5 lemmas to frame 2 and
                // returned true — false UNSAT.
                if blocking_witness.is_none() {
                    eprintln!(
                        "IC3 propagate: frame {k} empty (had {orig_count} lemma(s), all pushed to {}) \
                         but blocking did NOT complete naturally — refusing standard convergence \
                         (#4320 soundness gate)",
                        k + 1
                    );
                    // Continue propagating lower frames — do NOT return true.
                    continue;
                }
                eprintln!(
                    "IC3 propagate: frame {k} empty (had {orig_count} lemma(s), all pushed to {})",
                    k + 1
                );
                if cfg!(debug_assertions) || std::env::var("IC3_VERIFY_CONVERGENCE").is_ok() {
                    eprintln!("IC3: verifying convergence at frame {k}...");
                    let f_k_lemmas: Vec<_> = self.frames.frames[k].lemmas.clone();
                    let f_k1_lemmas: Vec<_> = self.frames.frames[k + 1].lemmas.clone();
                    eprintln!(
                        "IC3 convergence check: frame[{k}] has {} lemmas, frame[{}] has {} lemmas",
                        f_k_lemmas.len(),
                        k + 1,
                        f_k1_lemmas.len(),
                    );
                }
                return PropagateOutcome::Converged;
            }
        }
        self.earliest_changed_frame = depth;

        if self.config.inf_frame {
            self.propagate_to_inf();

            // Inf-frame convergence: two consecutive empty frames plus non-empty
            // inf_lemmas implies an inductive invariant. Same soundness precondition
            // as the standard convergence path (#4320): only valid when blocking
            // at this depth exited naturally, so F_top ∧ bad is provably UNSAT.
            if !self.inf_lemmas.is_empty() && depth >= 3 && blocking_witness.is_some() {
                for k in 1..depth - 1 {
                    if self.frames.frames[k].lemmas.is_empty()
                        && self.frames.frames[k + 1].lemmas.is_empty()
                    {
                        return PropagateOutcome::Converged;
                    }
                }
            }
        }

        // Trivially-safe convergence (#4247): if all frames k in [1, depth-1]
        // have no lemmas after the blocking phase completed (get_bad() returned
        // None at F_top), the inductive invariant is `True` (relative to the
        // base formula Trans ∧ constraints). Since F_top ∧ bad is UNSAT (by
        // get_bad() returning None before this propagate call) and init has
        // been checked against bad in init_implies_bad(), the circuit is safe.
        //
        // Without this check, IC3 loops forever on circuits where bad is
        // unreachable via short transition chains: no lemmas ever get added,
        // so the standard convergence condition (`frame empty && orig_count > 0`)
        // never fires. Examples: HWMCC cal14, cal42, loopv3, microban_1 —
        // each solved by rIC3 in <0.15s but TLA2 timed out at 100s+.
        //
        // Soundness: F_k empty ⟺ F_k state set = Trans ∧ constraints (base
        // formula). If all k in [1, depth-1] are empty and F_top ∧ bad is
        // UNSAT, then F_1 = ... = F_top are the same state set. F_1 ⊆ F_0
        // (F_0 = init ∧ Trans ∧ constraints). Init ∧ bad is UNSAT (checked).
        // F_top ∧ bad is UNSAT. All intermediate frames equal → inductive.
        // Therefore Safe.
        //
        // SOUNDNESS GATE (#4310 → #4317): the argument above assumes
        // `F_top ∧ bad` is UNSAT at this depth, which requires the blocking
        // loop to have exited via `get_bad() => None`. If blocking exited
        // early (blocking_budget exhausted, repeated-cube limit from #4139,
        // drop_po discards, cancellation), some reachable bad cube at F_top
        // may be unblocked, so we CANNOT conclude `F_top ∧ bad` is UNSAT.
        // Reporting Safe in that case is a soundness violation — see
        // `circular_pointer_top_w8_d16_e0` which hit the #4139 repeated-
        // cube break and then falsely triggered #4247 at depth 2.
        //
        // #4317: the precondition is now enforced by the type system via
        // [`ConvergenceProof`]. Only `run.rs`'s natural-exit break arm can
        // construct the witness, so no other blocking-loop exit path can
        // accidentally enable this shortcut.
        if depth >= 2 {
            let all_empty = (1..depth).all(|k| self.frames.frames[k].lemmas.is_empty());
            if all_empty {
                if blocking_witness.is_some() {
                    eprintln!(
                        "IC3 propagate: all frames [1..{depth}) empty — trivially-safe convergence (#4247)"
                    );
                    return PropagateOutcome::Converged;
                }
                // #4310 diagnostic: all frames empty but blocking did NOT
                // complete naturally. Refuse the shortcut — F_top may still
                // admit reachable bad cubes.
                eprintln!(
                    "IC3 propagate: all frames [1..{depth}) empty but blocking did NOT complete \
                     naturally — refusing trivially-safe convergence (#4310/#4317 soundness gate)"
                );
            }
        }

        PropagateOutcome::NotYet
    }

    /// Try to push top-frame lemmas to the infinity frame.
    ///
    /// Uses z4-sat native domain restriction on circuits with >= 20 latches,
    /// computing the domain once per cube and applying it via set_domain/clear_domain
    /// on the infinity solver. The infinity solver contains all transition clauses
    /// and infinity lemmas, so domain restriction provides significant per-call
    /// speedup by restricting BCP and VSIDS to the cube's COI.
    pub(super) fn propagate_to_inf(&mut self) {
        let depth = self.frames.depth();
        if depth == 0 {
            return;
        }
        let top = depth - 1;
        let lemmas: Vec<Lemma> = self.frames.frames[top].lemmas.clone();
        let mut promoted_indices = rustc_hash::FxHashSet::default();
        // small_circuit_mode (#4259, z4#8802): skip set_domain on inf_solver so
        // z4-sat uses search_propagate_standard (plain BCP).
        let use_domain = !self.config.small_circuit_mode && self.ts.latch_vars.len() >= 20;
        for (idx, lemma) in lemmas.iter().enumerate() {
            let cube: Vec<Lit> = lemma.lits.iter().map(|l| !*l).collect();
            if self.cube_sat_consistent_with_init(&cube) {
                continue;
            }
            let neg_cube: Vec<Lit> = cube.iter().map(|l| !*l).collect();
            let assumptions = self.prime_cube(&cube);

            // Activate z4-sat native domain restriction for the inf solver.
            if use_domain {
                let domain = self.domain_computer.compute_domain(&cube, &self.next_vars);
                let domain_vars: Vec<Var> = (0..=self.max_var)
                    .filter(|&i| domain.contains(Var(i)))
                    .map(Var)
                    .collect();
                self.inf_solver.set_domain(&domain_vars);
            }

            let is_ind = self
                .inf_solver
                .solve_with_temporary_clause(&assumptions, &neg_cube)
                == SatResult::Unsat;

            if use_domain {
                self.inf_solver.clear_domain();
            }

            if is_ind {
                self.inf_solver.add_clause(&lemma.lits);
                self.inf_lemmas.push(lemma.clone());
                for s in &mut self.solvers {
                    s.add_clause(&lemma.lits);
                }
                promoted_indices.insert(idx);
            }
        }
        if !promoted_indices.is_empty() {
            self.frames.frames[top].lemmas = lemmas
                .into_iter()
                .enumerate()
                .filter(|(i, _)| !promoted_indices.contains(i))
                .map(|(_, l)| l)
                .collect();
        }
    }
}
