// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl LraSolver {
    pub(crate) fn compute_direct_bound_propagations_for_var(&mut self, var: u32) {
        // #7851 D2: Skip variables where all bound atoms are already assigned.
        // Matches Z3's m_unassigned_bounds[v]==0 early exit (arith_solver.cpp:149).
        let vi_check = var as usize;
        if vi_check < self.unassigned_atom_count.len() && self.unassigned_atom_count[vi_check] == 0
        {
            return;
        }
        // Clone the atom refs up front so slack-reason reconstruction can
        // stay lazy. Precomputing reasons for every dirty slack variable
        // dominates sc-6 even when none of those atoms become implied.
        let Some(atoms) = self.atom_index.get(&var).cloned() else {
            return;
        };
        // #6564: For slack variables, reconstruct reasons from the
        // original expression instead of direct bound reason_pairs().
        let vi = var as usize;
        let Some(info) = self.vars.get(vi) else {
            return;
        };
        let is_slack = self.slack_var_set.contains(&var);
        let mut slack_upper_reasons: Option<Vec<TheoryLit>> = None;
        let mut slack_lower_reasons: Option<Vec<TheoryLit>> = None;

        // Use direct bounds for propagation when available (#6202).
        // When direct bounds are missing, fall back to implied bounds from
        // compute_implied_bounds(). Reasons are collected lazily via
        // collect_row_reasons_dedup (#6564: stale-reason root cause fix).
        let ub_direct = info.upper.as_ref();
        let lb_direct = info.lower.as_ref();

        // #6564: Implied-bound fallback uses row_idx for lazy reason collection.
        let ub_implied = if ub_direct.is_none() && vi < self.implied_bounds.len() {
            self.implied_bounds[vi]
                .1
                .as_ref()
                .filter(|b| b.row_idx != usize::MAX)
        } else {
            None
        };
        let lb_implied = if lb_direct.is_none() && vi < self.implied_bounds.len() {
            self.implied_bounds[vi]
                .0
                .as_ref()
                .filter(|b| b.row_idx != usize::MAX)
        } else {
            None
        };

        for atom in atoms {
            if self.asserted.contains_key(&atom.term) {
                continue;
            }

            if atom.is_upper {
                // Atom: x <= k (or x < k if strict)
                // TRUE if ub(x) satisfies atom — try direct bound, then implied.
                let (implied_true, implied_ub_row_idx) = if let Some(ub) = ub_direct {
                    let it = if atom.strict {
                        ub.value < atom.bound_value || (ub.value == atom.bound_value && ub.strict)
                    } else {
                        ub.value <= atom.bound_value
                    };
                    (it, None)
                } else if let Some(ib) = ub_implied {
                    // #4919: Fall back to implied upper bound for slack vars.
                    // Use cmp_big to avoid BigRational allocation.
                    let cmp = ib.value.cmp_big(&atom.bound_value);
                    let it = if atom.strict {
                        cmp == std::cmp::Ordering::Less
                            || (cmp == std::cmp::Ordering::Equal && ib.strict)
                    } else {
                        cmp == std::cmp::Ordering::Less || cmp == std::cmp::Ordering::Equal
                    };
                    (it, Some(ib.row_idx))
                } else {
                    (false, None)
                };

                if implied_true && !self.propagated_atoms.contains(&(atom.term, true)) {
                    if let Some(row_idx) = implied_ub_row_idx {
                        self.propagated_atoms.insert((atom.term, true));
                        self.pending_propagations.push(PendingPropagation::deferred(
                            TheoryLit::new(atom.term, true),
                            DeferredReason {
                                var,
                                need_upper: true,
                                fallback_row_idx: Some(row_idx),
                            },
                        ));
                        continue;
                    }
                    let reason: Vec<TheoryLit> = if is_slack {
                        if slack_upper_reasons.is_none() {
                            slack_upper_reasons =
                                self.collect_slack_interval_reasons_for_var(var, true);
                        }
                        // Fall through to ub_direct if slack reason collection
                        // returned None (e.g., atom_cache miss). The old eager
                        // code had this fallthrough; the lazy rewrite must preserve it.
                        if let Some(ref sr) = slack_upper_reasons {
                            sr.clone()
                        } else {
                            Vec::new()
                        }
                    } else if let Some(ub) = ub_direct {
                        ub.reason_pairs()
                            .filter(|(term, _)| !term.is_sentinel())
                            .map(|(term, val)| TheoryLit::new(term, val))
                            .collect()
                    } else {
                        Vec::new()
                    };
                    if !reason.is_empty() {
                        self.propagated_atoms.insert((atom.term, true));
                        self.pending_propagations.push(PendingPropagation::eager(
                            TheoryLit::new(atom.term, true),
                            reason,
                        ));
                        continue;
                    }
                }

                // FALSE if lb(x) contradicts atom — try direct, then implied.
                // For strict atom x < k: FALSE if lb >= k. (#6130)
                // For non-strict x <= k: FALSE if lb > k, or lb == k and strict.
                let (implied_false, implied_lb_row_idx) = if let Some(lb) = lb_direct {
                    let f = if atom.strict {
                        lb.value >= atom.bound_value
                    } else {
                        lb.value > atom.bound_value || (lb.value == atom.bound_value && lb.strict)
                    };
                    (f, None)
                } else if let Some(ib) = lb_implied {
                    // #4919: Fall back to implied lower bound for slack vars.
                    // Use cmp_big to avoid BigRational allocation.
                    let cmp = ib.value.cmp_big(&atom.bound_value);
                    let f = if atom.strict {
                        cmp == std::cmp::Ordering::Greater || cmp == std::cmp::Ordering::Equal
                    } else {
                        cmp == std::cmp::Ordering::Greater
                            || (cmp == std::cmp::Ordering::Equal && ib.strict)
                    };
                    (f, Some(ib.row_idx))
                } else {
                    (false, None)
                };

                if implied_false && !self.propagated_atoms.contains(&(atom.term, false)) {
                    if let Some(row_idx) = implied_lb_row_idx {
                        self.propagated_atoms.insert((atom.term, false));
                        self.pending_propagations.push(PendingPropagation::deferred(
                            TheoryLit::new(atom.term, false),
                            DeferredReason {
                                var,
                                need_upper: false,
                                fallback_row_idx: Some(row_idx),
                            },
                        ));
                    } else {
                        let reason: Vec<TheoryLit> = if is_slack {
                            if slack_lower_reasons.is_none() {
                                slack_lower_reasons =
                                    self.collect_slack_interval_reasons_for_var(var, false);
                            }
                            if let Some(ref sr) = slack_lower_reasons {
                                sr.clone()
                            } else {
                                Vec::new()
                            }
                        } else if let Some(lb) = lb_direct {
                            lb.reason_pairs()
                                .filter(|(term, _)| !term.is_sentinel())
                                .map(|(term, val)| TheoryLit::new(term, val))
                                .collect()
                        } else {
                            Vec::new()
                        };
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
                // TRUE if lb(x) satisfies atom — try direct, then implied.
                let (implied_true, implied_lb_row_idx) = if let Some(lb) = lb_direct {
                    let it = if atom.strict {
                        lb.value > atom.bound_value || (lb.value == atom.bound_value && lb.strict)
                    } else {
                        lb.value >= atom.bound_value
                    };
                    (it, None)
                } else if let Some(ib) = lb_implied {
                    // #4919: Fall back to implied lower bound for slack vars.
                    // Use cmp_big to avoid BigRational allocation.
                    let cmp = ib.value.cmp_big(&atom.bound_value);
                    let it = if atom.strict {
                        cmp == std::cmp::Ordering::Greater
                            || (cmp == std::cmp::Ordering::Equal && ib.strict)
                    } else {
                        cmp == std::cmp::Ordering::Greater || cmp == std::cmp::Ordering::Equal
                    };
                    (it, Some(ib.row_idx))
                } else {
                    (false, None)
                };

                if implied_true && !self.propagated_atoms.contains(&(atom.term, true)) {
                    if let Some(row_idx) = implied_lb_row_idx {
                        self.propagated_atoms.insert((atom.term, true));
                        self.pending_propagations.push(PendingPropagation::deferred(
                            TheoryLit::new(atom.term, true),
                            DeferredReason {
                                var,
                                need_upper: false,
                                fallback_row_idx: Some(row_idx),
                            },
                        ));
                        continue;
                    }
                    let reason: Vec<TheoryLit> = if is_slack {
                        if slack_lower_reasons.is_none() {
                            slack_lower_reasons =
                                self.collect_slack_interval_reasons_for_var(var, false);
                        }
                        if let Some(ref sr) = slack_lower_reasons {
                            sr.clone()
                        } else {
                            Vec::new()
                        }
                    } else if let Some(lb) = lb_direct {
                        lb.reason_pairs()
                            .filter(|(term, _)| !term.is_sentinel())
                            .map(|(term, val)| TheoryLit::new(term, val))
                            .collect()
                    } else {
                        Vec::new()
                    };
                    if !reason.is_empty() {
                        self.propagated_atoms.insert((atom.term, true));
                        self.pending_propagations.push(PendingPropagation::eager(
                            TheoryLit::new(atom.term, true),
                            reason,
                        ));
                        continue;
                    }
                }

                // FALSE if ub(x) contradicts atom — try direct, then implied.
                // For strict atom x > k: FALSE if ub <= k. (#6130)
                // For non-strict x >= k: FALSE if ub < k, or ub == k and strict.
                let (implied_false, implied_ub_row_idx) = if let Some(ub) = ub_direct {
                    let f = if atom.strict {
                        ub.value <= atom.bound_value
                    } else {
                        ub.value < atom.bound_value || (ub.value == atom.bound_value && ub.strict)
                    };
                    (f, None)
                } else if let Some(ib) = ub_implied {
                    // #4919: Fall back to implied upper bound for slack vars.
                    // Use cmp_big to avoid BigRational allocation.
                    let cmp = ib.value.cmp_big(&atom.bound_value);
                    let f = if atom.strict {
                        cmp == std::cmp::Ordering::Less || cmp == std::cmp::Ordering::Equal
                    } else {
                        cmp == std::cmp::Ordering::Less
                            || (cmp == std::cmp::Ordering::Equal && ib.strict)
                    };
                    (f, Some(ib.row_idx))
                } else {
                    (false, None)
                };

                if implied_false && !self.propagated_atoms.contains(&(atom.term, false)) {
                    if let Some(row_idx) = implied_ub_row_idx {
                        self.propagated_atoms.insert((atom.term, false));
                        self.pending_propagations.push(PendingPropagation::deferred(
                            TheoryLit::new(atom.term, false),
                            DeferredReason {
                                var,
                                need_upper: true,
                                fallback_row_idx: Some(row_idx),
                            },
                        ));
                    } else {
                        let reason: Vec<TheoryLit> = if is_slack {
                            if slack_upper_reasons.is_none() {
                                slack_upper_reasons =
                                    self.collect_slack_interval_reasons_for_var(var, true);
                            }
                            if let Some(ref sr) = slack_upper_reasons {
                                sr.clone()
                            } else {
                                Vec::new()
                            }
                        } else if let Some(ub) = ub_direct {
                            ub.reason_pairs()
                                .filter(|(term, _)| !term.is_sentinel())
                                .map(|(term, val)| TheoryLit::new(term, val))
                                .collect()
                        } else {
                            Vec::new()
                        };
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
