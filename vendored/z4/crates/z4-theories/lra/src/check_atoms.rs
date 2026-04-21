// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Atom processing helpers for `LraSolver::check()`.
//!
//! Extracted from the check() method to reduce theory_solver.rs size.
//! Contains: incremental atom trail processing, disequality collection,
//! to_int axiom injection, and post-simplex propagation orchestration.

use super::*;

/// Result of processing newly-asserted atoms in check().
pub(crate) struct CheckAtomStats {
    /// Disequality atoms collected for post-simplex checking.
    pub disequalities: Vec<(TermId, LinearExpr, bool)>,
    /// Number of atoms successfully parsed and asserted.
    pub parsed_count: usize,
    /// Number of atoms skipped (unparseable or Boolean combinations).
    pub skipped_count: usize,
}

impl LraSolver {
    /// Process newly-asserted atoms from the trail, assert bounds into the
    /// simplex tableau, and collect disequality atoms.
    ///
    /// First pass: iterate new atoms (since last check), parse them, assert
    /// bounds, and collect disequalities.
    /// Second pass: collect prior disequalities from the incremental trail.
    ///
    /// Returns `Err(conflict)` if an immediate conflict is detected (e.g.,
    /// asserting `true` as `false`). Otherwise returns statistics and
    /// collected disequalities for post-simplex checking.
    pub(crate) fn process_check_atoms(
        &mut self,
        debug: bool,
    ) -> Result<CheckAtomStats, Box<TheoryResult>> {
        self.process_check_atoms_inner(debug, false)
    }

    /// BCP-time variant: skip re-collecting previously asserted disequalities.
    /// The final full check handles disequality/model-only work.
    pub(crate) fn process_check_atoms_bcp(
        &mut self,
        debug: bool,
    ) -> Result<CheckAtomStats, Box<TheoryResult>> {
        self.process_check_atoms_inner(debug, true)
    }

    fn process_check_atoms_inner(
        &mut self,
        debug: bool,
        bcp_mode: bool,
    ) -> Result<CheckAtomStats, Box<TheoryResult>> {
        let new_start = self.last_check_trail_pos;
        let trail_len = self.asserted_trail.len();

        let mut parsed_count = 0;
        let mut skipped_count = 0;
        let mut _cache_hits = 0;
        // Track disequalities for post-simplex checking.
        // Stores (term, expr, asserted_value) where asserted_value is the value the term was asserted with.
        // Disequalities must be re-collected from ALL asserted atoms (not just new ones)
        // because they are model-dependent and not cached in bound_atoms.
        let mut disequalities: Vec<(TermId, LinearExpr, bool)> = Vec::new();

        // First pass: process NEW atoms for bound assertions + disequality collection
        for i in new_start..trail_len {
            let term = self.asserted_trail[i];
            let Some(&value) = self.asserted.get(&term) else {
                continue;
            };

            // Skip atoms whose bounds have already been asserted into the tableau
            // (can happen if the same atom is re-asserted within the same scope).
            if self.bound_atoms.contains(&(term, value)) {
                continue;
            }

            // Handle constant Bool atoms (e.g., term layer folds `X = X` to `true`).
            // Asserting `true` as false (or `false` as true) is an immediate contradiction.
            // Uses const_bool_cache from register_atom (#6590 Packet 1); falls back
            // to self.terms on cache miss for atoms registered before caching was added.
            let is_const_bool = self
                .const_bool_cache
                .get(&term)
                .copied()
                .unwrap_or_else(|| {
                    if let TermData::Const(Constant::Bool(b)) = self.terms().get(term) {
                        Some(*b)
                    } else {
                        None
                    }
                });
            if let Some(b) = is_const_bool {
                if value != b {
                    self.conflict_count += 1;
                    return Err(Box::new(TheoryResult::Unsat(vec![TheoryLit {
                        term,
                        value,
                    }])));
                }
                continue;
            }

            // Use cached parse result if available
            let cached = self.atom_cache.get(&term).cloned();
            let parsed_info = match cached {
                Some(info) => {
                    _cache_hits += 1;
                    // Re-inject unsupported status from cached parse result (#6167).
                    // register_atom() may have parsed this atom and cached its
                    // unsupported flag. Without this, persistent_unsupported_atoms
                    // won't include atoms first parsed during registration.
                    if info.as_ref().is_some_and(|i| i.has_unsupported) {
                        self.mark_atom_unsupported(term);
                    }
                    info
                }
                None => {
                    // Parse and cache. Set current_parsing_atom so that
                    // parse_linear_expr can track which atom triggered
                    // unsupported sub-expressions (#6167).
                    self.current_parsing_atom = Some(term);
                    if self.debug_intern {
                        safe_eprintln!("[PARSE] atom {:?}", term);
                    }
                    let parsed = self.parse_atom(term).map(|(expr, is_le, strict)| {
                        let is_eq = matches!(self.terms().get(term), TermData::App(Symbol::Named(name), _) if name == "=");
                        let is_distinct = matches!(self.terms().get(term), TermData::App(Symbol::Named(name), _) if name == "distinct");
                        let has_unsupported = self.persistent_unsupported_atoms.contains(&term);
                        ParsedAtomInfo { expr, is_le, strict, is_eq, is_distinct, has_unsupported, compound_slack: None }
                    });
                    self.current_parsing_atom = None;
                    self.atom_cache.insert(term, parsed.clone());
                    parsed
                }
            };

            let Some(info) = parsed_info else {
                skipped_count += 1;
                // Check if the skipped atom is a Boolean combination (or, and, xor, ite).
                // These shouldn't be theory atoms - they indicate the DPLL layer is
                // passing us intermediate CNF expressions instead of just arithmetic predicates.
                // When this happens, we can't trust our SAT result because we're missing constraints.
                match self.terms().get(term) {
                    TermData::App(Symbol::Named(name), _)
                        if name == "or" || name == "and" || name == "xor" || name == "=>" =>
                    {
                        if debug {
                            safe_eprintln!(
                                "[LRA] Skipping Boolean combination {:?} - marking incomplete",
                                term
                            );
                        }
                        self.mark_atom_unsupported(term);
                    }
                    // Bool-sort equality/distinct (e.g., (= x_48 (not x_40))) are
                    // Boolean connectives (iff/xor) handled by the Tseitin layer,
                    // not arithmetic predicates. parse_atom returns None for these
                    // (#4919). Skip without marking unsupported.
                    TermData::App(Symbol::Named(name), args)
                        if (name == "=" || name == "distinct")
                            && args
                                .first()
                                .is_some_and(|&a| self.terms().sort(a) == &Sort::Bool) =>
                    {
                        if debug {
                            safe_eprintln!(
                                "[LRA] Skipping Bool-sort {} {:?} - handled by Tseitin layer",
                                name,
                                term
                            );
                        }
                    }
                    TermData::Ite(_, _, _) => {
                        // Bool-sort ITE atoms (e.g., `(ite cond p q)` where p,q
                        // are Bool) are Boolean circuits handled entirely by the
                        // Tseitin/DPLL layer. The LRA solver need not track them,
                        // and marking them unsupported incorrectly converts SAT
                        // results to Unknown (#4919).
                        //
                        // Non-Bool ITE atoms (Real/Int-valued) should have been
                        // eliminated by lift_arithmetic_ite_all; mark unsupported
                        // to preserve soundness if lifting missed them.
                        let is_bool_ite = self.terms().sort(term) == &Sort::Bool;
                        if !is_bool_ite {
                            if debug {
                                safe_eprintln!(
                                    "[LRA] Skipping non-Bool ITE atom {:?} - marking incomplete",
                                    term
                                );
                            }
                            self.mark_atom_unsupported(term);
                        } else if debug {
                            safe_eprintln!(
                                "[LRA] Skipping Bool ITE atom {:?} - handled by Tseitin layer",
                                term
                            );
                        }
                    }
                    _ => {
                        // Unrecognized atom (e.g., BV comparisons like bvsle).
                        // In standalone mode (not combined_theory_mode), no other
                        // theory handles these, so we must flag as unsupported to
                        // prevent false SAT results from ignored constraints (#5523).
                        if !self.combined_theory_mode {
                            self.mark_atom_unsupported(term);
                        }
                        if debug {
                            safe_eprintln!(
                                "[LRA] Skipping unparseable atom {:?} (term: {:?}), combined_theory_mode={}",
                                term,
                                self.terms().get(term),
                                self.combined_theory_mode,
                            );
                        }
                    }
                }
                continue;
            };
            parsed_count += 1;

            let ParsedAtomInfo {
                expr,
                is_le,
                strict,
                is_eq,
                is_distinct,
                has_unsupported: _,
                compound_slack: _,
            } = info;

            // For all arithmetic atoms, expr is normalized so that the atom is:
            // expr <= 0 (for is_le=true) or expr >= 0 (for is_le=false)
            // The bound is always 0.
            let zero = BigRational::zero();

            if is_eq || is_distinct {
                // For equality (=):
                //   value=true  → assert equality (a = b)
                //   value=false → add disequality (a != b)
                // For distinct:
                //   value=true  → add disequality (a != b) - INVERTED
                //   value=false → assert equality (a = b) - INVERTED
                let is_equality = (is_eq && value) || (is_distinct && !value);

                if is_equality {
                    // Equality: expr = 0 means expr <= 0 AND expr >= 0
                    // Use the actual assertion value for reason_value (important for `distinct` negations)
                    if !expr.is_constant() {
                        self.assert_bound_for_atom(
                            expr.clone(),
                            zero.clone(),
                            BoundType::Upper,
                            false,
                            term,
                            value,
                            (term, value),
                        );
                        self.assert_bound_for_atom(
                            expr,
                            zero,
                            BoundType::Lower,
                            false,
                            term,
                            value,
                            (term, value),
                        );
                    }
                    self.bound_atoms.insert((term, value));
                } else {
                    // Disequality: x != c can't be directly encoded in simplex.
                    // We'll check these after simplex to see if any are violated by the model.
                    // Store (term, expr, asserted_value) for post-simplex checking: if expr evaluates to 0
                    // in the model, the disequality is violated.
                    // NOTE: Disequalities are NOT cached in bound_atoms because they must be
                    // re-checked against the current model on every check() call.
                    if debug {
                        safe_eprintln!("[LRA] Disequality atom {:?}: will check model later", term);
                    }
                    self.disequality_trail.push((term, expr.clone(), value));
                    disequalities.push((term, expr, value));
                }
            } else if value {
                // Positive assertion: expr <= 0 or expr < 0
                if is_le {
                    self.assert_bound_for_atom(
                        expr,
                        zero,
                        BoundType::Upper,
                        strict,
                        term,
                        true,
                        (term, true),
                    );
                } else {
                    // expr >= 0 or expr > 0
                    self.assert_bound_for_atom(
                        expr,
                        zero,
                        BoundType::Lower,
                        strict,
                        term,
                        true,
                        (term, true),
                    );
                }
                self.bound_atoms.insert((term, value));
            } else {
                // Negated assertion: !(expr <= 0) means expr > 0
                if is_le {
                    // !(expr <= 0) => expr > 0
                    self.assert_bound_for_atom(
                        expr,
                        zero,
                        BoundType::Lower,
                        !strict,
                        term,
                        false,
                        (term, false),
                    );
                } else {
                    // !(expr >= 0) => expr < 0
                    self.assert_bound_for_atom(
                        expr,
                        zero,
                        BoundType::Upper,
                        !strict,
                        term,
                        false,
                        (term, false),
                    );
                }
                self.bound_atoms.insert((term, value));
            }

            // #7719 / #6617 D3: interleave implied-bound derivation with atom
            // processing so later atoms in the same batched check can benefit
            // from bounds unlocked by earlier ones. Without this, BCP-time
            // batched checks strand cross-row cascades until a later round.
            let cascade_rounds = if bcp_mode { 5 } else { 10 };
            if !self.touched_rows.is_empty() {
                for _ in 0..cascade_rounds {
                    let newly_bounded = self.compute_implied_bounds();
                    let is_empty = newly_bounded.is_empty();
                    if !is_empty {
                        self.propagation_dirty_vars.extend(&newly_bounded);
                    }
                    drop(newly_bounded);
                    if is_empty {
                        break;
                    }
                }
            }
        }
        // Update incremental position: all atoms up to trail_len are now processed.
        self.last_check_trail_pos = trail_len;

        // Second pass: collect disequalities from previously-processed atoms.
        // Use the incremental disequality_trail instead of scanning all atoms O(trail).
        // The trail already contains (term, expr, value) triples from prior check() calls;
        // we only need to verify they are still asserted (not popped).
        if !bcp_mode {
            for (term, expr, value) in &self.disequality_trail {
                // Verify this disequality is still in the current assertion set
                // (it may have been logically overridden, though pop handles most cases).
                if self.asserted.get(term) == Some(value) {
                    disequalities.push((*term, expr.clone(), *value));
                }
            }
        }

        Ok(CheckAtomStats {
            disequalities,
            parsed_count,
            skipped_count,
        })
    }

    /// Inject floor axioms for to_int terms (#5944):
    ///   to_int(x) <= x < to_int(x) + 1
    /// Expressed as bounds on (x - to_int(x)): 0 <= diff < 1.
    pub(crate) fn inject_to_int_axioms(&mut self) {
        if self.to_int_terms.is_empty() {
            return;
        }
        for i in 0..self.to_int_terms.len() {
            let (to_int_var, inner_arg) = self.to_int_terms[i];
            if !self.injected_to_int_axioms.insert(to_int_var) {
                continue; // Already injected in this scope
            }
            // Parse inner argument to get its linear expression
            let arg_expr = self.parse_linear_expr(inner_arg);
            // diff = x - to_int(x)
            let mut diff = arg_expr;
            diff.add_term(to_int_var, -BigRational::one());
            // Assert diff >= 0 (to_int(x) <= x)
            self.assert_bound_with_reasons(
                diff.clone(),
                BigRational::zero(),
                BoundType::Lower,
                false,
                &[], // Axiom — no reason literals
                None,
            );
            // Assert diff < 1 (x < to_int(x) + 1)
            self.assert_bound_with_reasons(
                diff,
                BigRational::one(),
                BoundType::Upper,
                true, // strict: diff < 1
                &[],  // Axiom — no reason literals
                None,
            );
            self.dirty = true;
        }
    }

    /// Post-simplex propagation: compute implied bounds, wake compound atoms,
    /// discover offset equalities, and queue bound refinements.
    ///
    /// This MUST run after simplex returns Sat and before disequality checking
    /// so that propagate() has finite bounds for compound atoms.
    ///
    /// When `bcp_mode` is true (called from `check_during_propagate`), skip
    /// expensive model-completion work (offset equality discovery, bound
    /// refinement requests) that is only needed at final-check time. This
    /// reduces per-BCP-callback overhead on QF_LRA benchmarks where the theory
    /// callback fires hundreds of times per solve.
    pub(crate) fn run_post_simplex_propagation(
        &mut self,
        need_simplex: bool,
        debug: bool,
        bcp_mode: bool,
    ) {
        self.simplex_sat_count += 1;
        let pre_prop_count = self.pending_propagations.len();
        let has_cascade_rows = !self.touched_rows.is_empty();
        // #7973: In BCP mode, skip compute_implied_bounds when simplex didn't
        // run and no direct bounds changed. Cascade rows would yield same result.
        // The final check_impl() always runs with bcp_mode=false.
        let skip_implied = bcp_mode
            && !need_simplex
            && has_cascade_rows
            && !self.direct_bounds_changed_since_implied;
        if (need_simplex || has_cascade_rows) && !skip_implied {
            if debug {
                // Approach G (#4919): show touched_rows AFTER simplex (includes
                // pivot-modified rows from Approach D).
                safe_eprintln!(
                    "[LRA] PRE compute_implied_bounds: touched_rows={} (includes pivot rows)",
                    self.touched_rows.len(),
                );
            }
            // Snapshot touched rows before compute_implied_bounds clears them.
            // Only needed for offset equality discovery (final-check only).
            let touched_snapshot = if bcp_mode {
                None
            } else {
                Some(self.touched_rows.clone())
            };
            // #7982: Iterative fixpoint for implied bounds. Z3's propagation
            // loop re-enters bound_analyzer_on_row whenever newly-derived bounds
            // enable further derivations. Z4 previously ran a single pass and
            // relied on the DPLL loop to re-enter, leaving transitive cascades
            // stranded until the next check() call.
            //
            // #8003: Reduced from 4 to 2 iterations. compute_implied_bounds()
            // already seeds touched_rows with rows containing newly-bounded
            // variables, so iteration 2 only re-analyzes affected rows (not the
            // full tableau). Empirically, iterations 3-4 rarely produce new
            // bounds — the marginal benefit is negligible compared to the cost.
            // Z3 itself does a single pass per propagate_core() call and relies
            // on the DPLL loop for further cascading. Two iterations capture
            // the common one-hop transitive case while halving worst-case cost.
            let mut all_newly_bounded = HashSet::new();
            let mut fixpoint_iters = 0u32;
            const MAX_FIXPOINT_ITERS: u32 = 2;
            loop {
                let newly_bounded = self.compute_implied_bounds();
                let is_empty = newly_bounded.is_empty();
                if !is_empty {
                    all_newly_bounded.extend(&newly_bounded);
                }
                // Return the buffer for reuse in next iteration.
                drop(newly_bounded);
                if is_empty || fixpoint_iters >= MAX_FIXPOINT_ITERS {
                    break;
                }
                fixpoint_iters += 1;
                // touched_rows was already seeded by compute_implied_bounds for
                // rows containing newly_bounded variables. The next iteration
                // will analyze only those rows, deriving further transitive bounds.
            }
            self.propagate_direct_touched_rows_pending = false;
            if debug {
                safe_eprintln!(
                    "[LRA] compute_implied_bounds fixpoint: {} newly bounded vars, {} iterations",
                    all_newly_bounded.len(),
                    fixpoint_iters,
                );
            }
            // Mark variables with new implied bounds as dirty for propagation.
            // This enables multi-variable interval propagation in propagate() to
            // fire on atoms referencing these variables (#4919 RC2).
            self.propagation_dirty_vars.extend(&all_newly_bounded);

            // Offset equality discovery and bound refinement are model-completion
            // work. During BCP propagation, skip them — they'll run at final check.
            if !bcp_mode {
                // #6617 Packet 1: Discover offset equalities from touched rows.
                if let Some(ref snapshot) = touched_snapshot {
                    self.discover_offset_equalities(snapshot);
                }

                // BP_REFINE (#4919 Step 2): After simplex finds feasible and
                // compute_implied_bounds() derives fresh bounds, scan atoms for
                // variables that gained a tighter implied bound with no matching
                // existing atom. Queue BoundRefinementRequests for the DPLL
                // executor to create new atoms.
                //
                // This MUST run here (not in propagate_var_atoms) because
                // propagate_var_atoms() executes during atom processing BEFORE
                // compute_implied_bounds() refreshes self.implied_bounds. Without
                // this pass, the refinement infrastructure has no fresh data.
                //
                // Reference: Z3 propagate_lp_solver_bound() / refine_bound()
                // at theory_lra.cpp:2463-2504.
                self.queue_post_simplex_refinements(&all_newly_bounded, debug);
            }
        } else if skip_implied {
            // #7973: Skipped compute_implied_bounds. Reset the direct-touched flag.
            self.propagate_direct_touched_rows_pending = false;
        }
        // #7719 D3: Reuse persistent scratch buffer instead of allocating a
        // fresh Vec<u32> per call. On 1000 check() calls with ~5 dirty vars each,
        // this eliminates 1000 small-Vec allocations. Take the buffer out of self
        // to avoid borrow conflicts with &mut self methods, then put it back.
        let mut dirty_vars = std::mem::take(&mut self.dirty_vars_scratch);
        dirty_vars.clear();
        dirty_vars.extend(self.propagation_dirty_vars.iter().copied());
        // #7654: Sort dirty vars for deterministic propagation order.
        // propagation_dirty_vars is a HashSet with RandomState — iteration
        // order varies per process, causing non-deterministic propagation
        // subsets when MAX_IMPLIED_PROPAGATIONS caps the total.
        dirty_vars.sort_unstable();
        let compound_queued = self.queue_compound_propagations_for_dirty_vars(&dirty_vars);
        // Same-variable chain bound propagation (Z3 Component 3).
        // Run even when simplex was skipped: after backtracking, propagated_atoms
        // is cleared, so previously propagated atoms need re-propagation with
        // the existing bounds. Restricting the scan to dirty variables keeps
        // this incremental on large QF_LRA instances (#6582 Packet 4).
        if !self.atom_index.is_empty() && !dirty_vars.is_empty() {
            self.compute_bound_propagations_for_vars(&dirty_vars);
        }
        self.dirty_vars_scratch = dirty_vars;
        if debug {
            let new_props = self.pending_propagations.len() - pre_prop_count;
            safe_eprintln!(
                "[LRA] Post-simplex propagation: atom_index_size={}, compound_use_vars={}, new_propagations={}, compound_queued={}, dirty_vars={}, wake_dirty_hits={}, wake_candidates={}",
                self.atom_index.len(),
                self.compound_use_index.len(),
                new_props,
                compound_queued,
                self.propagation_dirty_vars.len(),
                self.last_compound_wake_dirty_hits,
                self.last_compound_wake_candidates,
            );
        }
    }
}
