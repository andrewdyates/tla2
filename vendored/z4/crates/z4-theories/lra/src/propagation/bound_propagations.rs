// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl LraSolver {
    /// - If `x >= lb` and atom is `x >= k` with `lb >= k`: atom is TRUE
    /// - If `x <= ub` and atom is `x <= k` with `ub <= k`: atom is TRUE
    /// - If `x >= lb` and atom is `x <= k` with `lb > k`: atom is FALSE
    /// - If `x <= ub` and atom is `x >= k` with `ub < k`: atom is FALSE
    ///
    /// For strict bounds, the comparison is adjusted accordingly.
    ///
    /// Reference: Z3 `theory_lra.cpp:2924-2984`
    pub(crate) fn compute_bound_propagations_for_vars(&mut self, dirty_vars: &[u32]) {
        let debug = self.debug_lra;
        for &var in dirty_vars {
            self.compute_direct_bound_propagations_for_var(var);
        }

        // Phase 2: Implied-bound propagation (#4919).
        // For variables with newly-derived implied bounds from compute_implied_bounds(),
        // check their atoms to see if the implied bound enables new propagations.
        // Uses single-level reason collection from the derivation row to avoid
        // the exponential blowup of recursive reason reconstruction.
        // Only checks variables in propagation_dirty_vars to limit overhead.
        //
        // Throttles (matching Z3's propagation control, reference/z3/src/sat/smt/arith_solver.cpp):
        // Cap implied propagations per call to avoid feedback loops.
        const MAX_IMPLIED_PROPAGATIONS: u32 = 4096;
        let mut implied_count = 0u32;
        for &var in dirty_vars {
            // Throttle: stop if we've hit the per-call cap.
            if implied_count >= MAX_IMPLIED_PROPAGATIONS {
                break;
            }
            // #6564: Reasons collected lazily via collect_row_reasons_dedup,
            // which reads current bounds and handles slack variables correctly.
            // Fallback to collect_single_row_reasons for simple single-row cases.
            let _is_slack = self.slack_var_set.contains(&var);
            let vi = var as usize;
            // #7851 D2: Skip variables where all bound atoms are already assigned.
            if vi < self.unassigned_atom_count.len() && self.unassigned_atom_count[vi] == 0 {
                continue;
            }
            let atoms = self.atom_index.get(&var).cloned().unwrap_or_default();
            // Skip variables without implied bounds (avoids to_big() allocation).
            if vi >= self.implied_bounds.len() {
                continue;
            }
            // #6564: Extract strict/row_idx; keep value as Rational (no allocation).
            // Use Rational::cmp_big() for comparisons against atom.bound_value
            // (BigRational) to avoid per-variable to_big() heap allocation.
            let ub_ib_info = if vi < self.implied_bounds.len() {
                self.implied_bounds[vi]
                    .1
                    .as_ref()
                    .filter(|b| b.row_idx != usize::MAX)
                    .map(|b| (&b.value, b.strict, b.row_idx))
            } else {
                None
            };
            let lb_ib_info = if vi < self.implied_bounds.len() {
                self.implied_bounds[vi]
                    .0
                    .as_ref()
                    .filter(|b| b.row_idx != usize::MAX)
                    .map(|b| (&b.value, b.strict, b.row_idx))
            } else {
                None
            };

            // Skip if no implied bounds exist for this variable.
            if ub_ib_info.is_none() && lb_ib_info.is_none() {
                continue;
            }

            let mut saw_upper_implied_atom = false;
            let mut saw_lower_implied_atom = false;
            for atom in &atoms {
                if implied_count >= MAX_IMPLIED_PROPAGATIONS {
                    break;
                }
                if self.asserted.contains_key(&atom.term) {
                    continue;
                }

                if atom.is_upper {
                    // Atom: x <= k — check implied upper bound
                    if !self.propagated_atoms.contains(&(atom.term, true)) {
                        if let Some((ub_val, ub_strict, row_idx)) = ub_ib_info {
                            let cmp = ub_val.cmp_big(&atom.bound_value);
                            let implied = if atom.strict {
                                cmp == std::cmp::Ordering::Less
                                    || (cmp == std::cmp::Ordering::Equal && ub_strict)
                            } else {
                                cmp == std::cmp::Ordering::Less || cmp == std::cmp::Ordering::Equal
                            };
                            if implied {
                                saw_upper_implied_atom = true;
                                self.propagated_atoms.insert((atom.term, true));
                                self.pending_propagations.push(PendingPropagation::deferred(
                                    TheoryLit::new(atom.term, true),
                                    DeferredReason {
                                        var,
                                        need_upper: true,
                                        fallback_row_idx: Some(row_idx),
                                    },
                                ));
                                implied_count += 1;
                                continue;
                            }
                        }
                    }
                    // Atom: x <= k — check implied lower bound for false
                    if !self.propagated_atoms.contains(&(atom.term, false)) {
                        if let Some((lb_val, lb_strict, row_idx)) = lb_ib_info {
                            let cmp = lb_val.cmp_big(&atom.bound_value);
                            let implied_false = if atom.strict {
                                cmp == std::cmp::Ordering::Greater
                                    || cmp == std::cmp::Ordering::Equal
                            } else {
                                cmp == std::cmp::Ordering::Greater
                                    || (cmp == std::cmp::Ordering::Equal && lb_strict)
                            };
                            if implied_false {
                                self.propagated_atoms.insert((atom.term, false));
                                self.pending_propagations.push(PendingPropagation::deferred(
                                    TheoryLit::new(atom.term, false),
                                    DeferredReason {
                                        var,
                                        need_upper: false,
                                        fallback_row_idx: Some(row_idx),
                                    },
                                ));
                                implied_count += 1;
                            }
                        }
                    }
                } else {
                    // Atom: x >= k — check implied lower bound for true
                    if !self.propagated_atoms.contains(&(atom.term, true)) {
                        if let Some((lb_val, lb_strict, row_idx)) = lb_ib_info {
                            let cmp = lb_val.cmp_big(&atom.bound_value);
                            let implied = if atom.strict {
                                cmp == std::cmp::Ordering::Greater
                                    || (cmp == std::cmp::Ordering::Equal && lb_strict)
                            } else {
                                cmp == std::cmp::Ordering::Greater
                                    || cmp == std::cmp::Ordering::Equal
                            };
                            if implied {
                                saw_lower_implied_atom = true;
                                self.propagated_atoms.insert((atom.term, true));
                                self.pending_propagations.push(PendingPropagation::deferred(
                                    TheoryLit::new(atom.term, true),
                                    DeferredReason {
                                        var,
                                        need_upper: false,
                                        fallback_row_idx: Some(row_idx),
                                    },
                                ));
                                implied_count += 1;
                                continue;
                            }
                        }
                    }
                    // Atom: x >= k — check implied upper bound for false
                    if !self.propagated_atoms.contains(&(atom.term, false)) {
                        if let Some((ub_val, ub_strict, row_idx)) = ub_ib_info {
                            let cmp = ub_val.cmp_big(&atom.bound_value);
                            let implied_false = if atom.strict {
                                cmp == std::cmp::Ordering::Less || cmp == std::cmp::Ordering::Equal
                            } else {
                                cmp == std::cmp::Ordering::Less
                                    || (cmp == std::cmp::Ordering::Equal && ub_strict)
                            };
                            if implied_false {
                                self.propagated_atoms.insert((atom.term, false));
                                self.pending_propagations.push(PendingPropagation::deferred(
                                    TheoryLit::new(atom.term, false),
                                    DeferredReason {
                                        var,
                                        need_upper: true,
                                        fallback_row_idx: Some(row_idx),
                                    },
                                ));
                                implied_count += 1;
                            }
                        }
                    }
                }
            }

            // Bound refinement creation lives in queue_post_simplex_refinements().
            // This propagation pass only reasons about atoms that became implied.
            // Re-queuing refinements here uses a weaker "no implied atom fired"
            // condition, which rediscovers bounds already covered by stricter
            // atoms (for example x < 3 covering an implied x <= 3) and causes
            // duplicate refinement churn on real QF_LRA benchmarks (#4919).
            let _ = (
                saw_upper_implied_atom,
                saw_lower_implied_atom,
                ub_ib_info,
                lb_ib_info,
            );
        }

        if debug && !self.pending_propagations.is_empty() {
            safe_eprintln!(
                "[LRA] Computed {} bound propagations ({} from implied bounds)",
                self.pending_propagations.len(),
                implied_count,
            );
        }
        if debug && !self.pending_bound_refinements.is_empty() {
            safe_eprintln!(
                "[LRA] Queued {} bound refinements",
                self.pending_bound_refinements.len(),
            );
        }
    }
}
