// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl LraSolver {
    /// For each variable with indexed atoms, check if the current bounds
    /// imply the truth value of any unasserted atom.
    ///
    /// Same-variable chain propagation (Z3 Component 3):
    /// Eager per-variable bound propagation (#4919 RC2).
    ///
    /// Called immediately when a bound on `var` is tightened. Scans
    /// `atom_index[var]` for single-variable atoms that are now implied by
    /// the new bound, and adds them to `pending_propagations`. This gives
    /// the SAT solver immediate feedback without waiting for the full
    /// simplex round.
    ///
    /// For slack variables, reasons are constructed directly from the bound's
    /// `reason_pairs()` instead of calling `collect_slack_interval_reasons_for_var`
    /// which triggers expensive recursive row-walking (`collect_row_reasons_recursive`,
    /// measured at 15.8% of total solver time). The direct bound reason is sound:
    /// if the slack variable's bound implies the atom, the bound's own reason chain
    /// justifies it. The interval-based reconstruction in propagate() provides
    /// more precise reasons when needed for compound atoms.
    ///
    /// Reference: Z3 `theory_lra.cpp:2924-2984` (eager bound propagation).
    pub(crate) fn propagate_var_atoms(&mut self, var: u32) {
        let atoms = match self.atom_index.get(&var).cloned() {
            Some(a) if !a.is_empty() => a,
            _ => return,
        };
        let vi = var as usize;
        let Some(info) = self.vars.get(vi) else {
            return;
        };

        let ub_direct = info.upper.as_ref();
        let lb_direct = info.lower.as_ref();

        for atom in atoms {
            if self.asserted.contains_key(&atom.term) {
                continue;
            }

            if atom.is_upper {
                // Atom: x <= k (or x < k if strict)
                // TRUE if ub(x) satisfies atom
                let implied_true = if let Some(ub) = ub_direct {
                    if atom.strict {
                        ub.value < atom.bound_value || (ub.value == atom.bound_value && ub.strict)
                    } else {
                        ub.value <= atom.bound_value
                    }
                } else {
                    false
                };

                if implied_true && !self.propagated_atoms.contains(&(atom.term, true)) {
                    if let Some(ub) = ub_direct {
                        // Use direct bound reason_pairs() for all variables
                        // (both slack and non-slack). This avoids the expensive
                        // collect_slack_interval_reasons_for_var → collect_row_reasons_recursive
                        // path which was measured at 15.8% of solver time.
                        // The direct bound reason is sound: if ub(x) <= k,
                        // then whatever caused ub(x) justifies atom x <= k.
                        let reason: Vec<TheoryLit> = ub
                            .reason_pairs()
                            .filter(|(term, _)| !term.is_sentinel())
                            .map(|(term, val)| TheoryLit::new(term, val))
                            .collect();
                        if !reason.is_empty() {
                            self.propagated_atoms.insert((atom.term, true));
                            self.pending_propagations.push(PendingPropagation::eager(
                                TheoryLit::new(atom.term, true),
                                reason,
                            ));
                            continue;
                        }
                    }
                }

                // FALSE if lb(x) contradicts atom.
                // For strict atom x < k: lb >= k contradicts (regardless of lb strictness,
                // since both x >= k and x > k imply NOT x < k). (#6130)
                // For non-strict atom x <= k: lb > k, or lb == k with lb strict (x > k).
                let implied_false = if let Some(lb) = lb_direct {
                    if atom.strict {
                        lb.value >= atom.bound_value
                    } else {
                        lb.value > atom.bound_value || (lb.value == atom.bound_value && lb.strict)
                    }
                } else {
                    false
                };

                if implied_false && !self.propagated_atoms.contains(&(atom.term, false)) {
                    if let Some(lb) = lb_direct {
                        let reason: Vec<TheoryLit> = lb
                            .reason_pairs()
                            .filter(|(term, _)| !term.is_sentinel())
                            .map(|(term, val)| TheoryLit::new(term, val))
                            .collect();
                        if !reason.is_empty() {
                            self.propagated_atoms.insert((atom.term, false));
                            self.pending_propagations.push(PendingPropagation::eager(
                                TheoryLit::new(atom.term, false),
                                reason,
                            ));
                        }
                    }
                }
            } else {
                // Atom: x >= k (or x > k if strict)
                // TRUE if lb(x) satisfies atom
                let implied_true = if let Some(lb) = lb_direct {
                    if atom.strict {
                        lb.value > atom.bound_value || (lb.value == atom.bound_value && lb.strict)
                    } else {
                        lb.value >= atom.bound_value
                    }
                } else {
                    false
                };

                if implied_true && !self.propagated_atoms.contains(&(atom.term, true)) {
                    if let Some(lb) = lb_direct {
                        let reason: Vec<TheoryLit> = lb
                            .reason_pairs()
                            .filter(|(term, _)| !term.is_sentinel())
                            .map(|(term, val)| TheoryLit::new(term, val))
                            .collect();
                        if !reason.is_empty() {
                            self.propagated_atoms.insert((atom.term, true));
                            self.pending_propagations.push(PendingPropagation::eager(
                                TheoryLit::new(atom.term, true),
                                reason,
                            ));
                            continue;
                        }
                    }
                }

                // FALSE if ub(x) contradicts atom.
                // For strict atom x > k: ub <= k contradicts (regardless of ub strictness,
                // since both x <= k and x < k imply NOT x > k). (#6130)
                // For non-strict atom x >= k: ub < k, or ub == k with ub strict (x < k).
                let implied_false = if let Some(ub) = ub_direct {
                    if atom.strict {
                        ub.value <= atom.bound_value
                    } else {
                        ub.value < atom.bound_value || (ub.value == atom.bound_value && ub.strict)
                    }
                } else {
                    false
                };

                if implied_false && !self.propagated_atoms.contains(&(atom.term, false)) {
                    if let Some(ub) = ub_direct {
                        let reason: Vec<TheoryLit> = ub
                            .reason_pairs()
                            .filter(|(term, _)| !term.is_sentinel())
                            .map(|(term, val)| TheoryLit::new(term, val))
                            .collect();
                        if !reason.is_empty() {
                            self.propagated_atoms.insert((atom.term, false));
                            self.pending_propagations.push(PendingPropagation::eager(
                                TheoryLit::new(atom.term, false),
                                reason,
                            ));
                        }
                    }
                }
            }
        }
    }
}
