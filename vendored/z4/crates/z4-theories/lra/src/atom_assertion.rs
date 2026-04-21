// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bound assertion, slack variable management, and compound atom propagation.
//!
//! Complements `atom_parsing` (variable interning and expression parsing) with:
//! - Bound assertion with atom-level slack caching
//! - Slack variable creation and tableau row setup
//! - Compound atom propagation via direct bounds, implied bounds, and intervals

use super::*;

impl LraSolver {
    /// Assert a bound on a linear expression
    /// For expr <= c: create slack variable s, add row s = expr, then s <= c
    pub(crate) fn assert_bound(
        &mut self,
        expr: LinearExpr,
        bound: BigRational,
        bound_type: BoundType,
        strict: bool,
        reason: TermId,
        reason_value: bool,
    ) {
        let single_reason = [(reason, reason_value)];
        self.assert_bound_with_reasons(expr, bound, bound_type, strict, &single_reason, None);
    }

    /// Assert a bound with atom-level slack variable caching.
    ///
    /// When an atom is re-asserted after push/pop, the slack variable from the
    /// previous assertion is reused. This prevents the tableau from growing
    /// unboundedly across DPLL(T) backtracking cycles (#4919).
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn assert_bound_for_atom(
        &mut self,
        expr: LinearExpr,
        bound: BigRational,
        bound_type: BoundType,
        strict: bool,
        reason: TermId,
        reason_value: bool,
        atom_key: (TermId, bool),
    ) {
        let single_reason = [(reason, reason_value)];
        self.assert_bound_with_reasons(
            expr,
            bound,
            bound_type,
            strict,
            &single_reason,
            Some(atom_key),
        );
    }

    /// Get or create a slack variable for a multi-variable linear expression.
    ///
    /// If a slack already exists for this expression (via `expr_to_slack`), returns it.
    /// Otherwise creates a new slack variable, adds a tableau row `slack = expr`,
    /// sets the initial value, and registers the row for implied-bound analysis.
    ///
    /// This is the core mechanism for atom normalization (#4919): by creating slack
    /// variables at registration time, compound atoms like `x + y - z <= 5` become
    /// single-variable atoms `s <= 5` that participate in same-variable chain
    /// propagation via `atom_index`.
    /// Returns (slack_var, original_constant) — the original constant is needed so callers
    /// can adjust bounds when the reused slack was created with a different constant offset (#6193).
    pub(crate) fn get_or_create_slack(&mut self, expr: &LinearExpr) -> (u32, Rational) {
        // Normalize key: sorted coefficients (without constant — the constant is
        // part of the slack definition, not the key).
        let mut key: Vec<(u32, Rational)> =
            expr.coeffs.iter().map(|(v, c)| (*v, c.clone())).collect();
        key.sort_by_key(|(v, _)| *v);

        if let Some(&(existing, ref orig_constant)) = self.expr_to_slack.get(&key) {
            return (existing, orig_constant.clone());
        }

        let new_slack = self.next_var;
        self.next_var += 1;
        while self.vars.len() <= new_slack as usize {
            self.vars.push(VarInfo::default());
        }

        let row_idx = self.rows.len();
        self.vars[new_slack as usize].status = Some(VarStatus::Basic(row_idx));

        // Substitute any basic variables with their row equations so that
        // row coefficients only reference non-basic variables (#4842).
        let mut new_coeffs: Vec<(u32, Rational)> = Vec::new();
        let mut new_constant = expr.constant.clone();
        for &(v, ref c) in &expr.coeffs {
            if let Some(VarStatus::Basic(basic_row_idx)) =
                self.vars.get(v as usize).and_then(|info| info.status)
            {
                let basic_row = &self.rows[basic_row_idx];
                for &(rv, ref rc) in &basic_row.coeffs {
                    types::add_sparse_term_rat(&mut new_coeffs, rv, c * rc);
                }
                new_constant = &new_constant + &(c * &basic_row.constant);
            } else {
                types::add_sparse_term_rat(&mut new_coeffs, v, c.clone());
            }
        }

        let row = TableauRow::new_rat(new_slack, new_coeffs, new_constant);
        self.rows.push(row);
        self.heap_stale = true; // #8782: new row → full heap rebuild needed

        let new_row_ref = &self.rows[row_idx];
        for &(v, _) in &new_row_ref.coeffs {
            let vi = v as usize;
            if vi >= self.col_index.len() {
                self.col_index.resize(vi + 1, Vec::new());
            }
            self.col_index[vi].push(row_idx);
        }
        self.basic_var_to_row.insert(new_slack, row_idx);
        self.touched_rows.insert(row_idx);

        // Set initial value for slack based on current variable values.
        let mut slack_val = InfRational::from_rat(expr.constant.clone());
        for &(v, ref c) in &expr.coeffs {
            if let Some(info) = self.vars.get(v as usize) {
                slack_val += &info.value.mul_rat(c);
            }
        }
        self.vars[new_slack as usize].value = slack_val;

        // Mark non-basic variables used in this row.
        let row_ref = &self.rows[row_idx];
        let row_vars: Vec<u32> = row_ref.coeffs.iter().map(|(v, _)| *v).collect();
        for v in row_vars {
            if let Some(info) = self.vars.get_mut(v as usize) {
                if info.status.is_none() {
                    info.status = Some(VarStatus::NonBasic);
                }
            }
        }

        self.slack_var_set.insert(new_slack);
        let orig_constant = expr.constant.clone();
        self.expr_to_slack
            .insert(key, (new_slack, Rational::from(&orig_constant)));
        (new_slack, orig_constant)
    }

    pub(crate) fn compound_atom_ref(&self, compound: CompoundAtomRef) -> Option<AtomRef> {
        self.atom_index
            .get(&compound.slack)
            .and_then(|atoms| atoms.iter().find(|atom| atom.term == compound.term))
            .cloned()
    }

    pub(crate) fn queue_compound_propagations_for_dirty_vars(&mut self, dirty: &[u32]) -> usize {
        if dirty.is_empty() || self.compound_use_index.is_empty() {
            self.last_compound_propagations_queued = 0;
            self.last_compound_wake_dirty_hits = 0;
            self.last_compound_wake_candidates = 0;
            return 0;
        }

        let mut seen = HashSet::new();
        let mut queued = 0usize;
        let mut dirty_hits = 0usize;
        let mut candidates = 0usize;
        for &var in dirty {
            let Some(compounds) = self.compound_use_index.get(&var).cloned() else {
                continue;
            };
            dirty_hits += 1;
            for compound in compounds {
                if !seen.insert(compound.term) {
                    continue;
                }
                candidates += 1;
                if self.try_queue_compound_propagation(compound) {
                    queued += 1;
                }
            }
        }
        self.last_compound_propagations_queued = queued;
        self.last_compound_wake_dirty_hits = dirty_hits;
        self.last_compound_wake_candidates = candidates;
        queued
    }

    pub(crate) fn try_queue_compound_propagation(&mut self, compound: CompoundAtomRef) -> bool {
        if self.asserted.contains_key(&compound.term) {
            return false;
        }

        let Some(atom) = self.compound_atom_ref(compound) else {
            return false;
        };
        let slack_vi = compound.slack as usize;
        // Same-expression compound atoms share one slack variable. A stronger
        // asserted slack bound is therefore a sound direct witness for a weaker
        // atom over that same slack, and it must stay available when source-var
        // interval reconstruction comes back empty.

        let direct_upper = self
            .vars
            .get(slack_vi)
            .and_then(|info| info.upper.as_ref())
            .map(|bound| {
                (
                    bound.value.clone(),
                    bound.strict,
                    bound
                        .reason_pairs()
                        .filter(|(term, _)| !term.is_sentinel())
                        .map(|(term, value)| TheoryLit::new(term, value))
                        .collect::<Vec<_>>(),
                )
            });
        let direct_lower = self
            .vars
            .get(slack_vi)
            .and_then(|info| info.lower.as_ref())
            .map(|bound| {
                (
                    bound.value.clone(),
                    bound.strict,
                    bound
                        .reason_pairs()
                        .filter(|(term, _)| !term.is_sentinel())
                        .map(|(term, value)| TheoryLit::new(term, value))
                        .collect::<Vec<_>>(),
                )
            });
        // #6564: Extract value/strict from implied bounds, collect reasons lazily.
        // Clone the Rational value instead of converting to BigRational via to_big().
        // Rational::Small clone is a 16-byte memcpy (no heap allocation), whereas
        // to_big() always allocates a BigRational on the heap. Use cmp_big() below
        // for comparisons against atom.bound_value (BigRational).
        let implied_upper = if slack_vi < self.implied_bounds.len() {
            self.implied_bounds[slack_vi]
                .1
                .as_ref()
                .filter(|bound| bound.row_idx != usize::MAX)
                .map(|bound| (bound.value.clone(), bound.strict, bound.row_idx))
        } else {
            None
        };
        let implied_lower = if slack_vi < self.implied_bounds.len() {
            self.implied_bounds[slack_vi]
                .0
                .as_ref()
                .filter(|bound| bound.row_idx != usize::MAX)
                .map(|bound| (bound.value.clone(), bound.strict, bound.row_idx))
        } else {
            None
        };

        let direct_true_reason = if atom.is_upper {
            direct_upper.as_ref().and_then(|(value, strict, reason)| {
                let implied = if atom.strict {
                    value < &atom.bound_value || (value == &atom.bound_value && *strict)
                } else {
                    value <= &atom.bound_value
                };
                (implied && !reason.is_empty()).then(|| reason.clone())
            })
        } else {
            direct_lower.as_ref().and_then(|(value, strict, reason)| {
                let implied = if atom.strict {
                    value > &atom.bound_value || (value == &atom.bound_value && *strict)
                } else {
                    value >= &atom.bound_value
                };
                (implied && !reason.is_empty()).then(|| reason.clone())
            })
        };
        let implied_true_row = if atom.is_upper {
            implied_upper.as_ref().and_then(|(value, strict, row_idx)| {
                let cmp = value.cmp_big(&atom.bound_value);
                let implied = if atom.strict {
                    cmp == std::cmp::Ordering::Less || (cmp == std::cmp::Ordering::Equal && *strict)
                } else {
                    cmp == std::cmp::Ordering::Less || cmp == std::cmp::Ordering::Equal
                };
                implied.then_some(*row_idx)
            })
        } else {
            implied_lower.as_ref().and_then(|(value, strict, row_idx)| {
                let cmp = value.cmp_big(&atom.bound_value);
                let implied = if atom.strict {
                    cmp == std::cmp::Ordering::Greater
                        || (cmp == std::cmp::Ordering::Equal && *strict)
                } else {
                    cmp == std::cmp::Ordering::Greater || cmp == std::cmp::Ordering::Equal
                };
                implied.then_some(*row_idx)
            })
        };

        if !self.propagated_atoms.contains(&(compound.term, true)) {
            let interval_true_reason = if direct_true_reason.is_none() && implied_true_row.is_none()
            {
                match self.atom_cache.get(&compound.term) {
                    Some(Some(info)) => {
                        let expr = info.expr.clone();
                        let (lb, ub) = self.compute_expr_interval(&expr);
                        // is_le=true: atom true when expr <= 0 → check UB <= 0
                        // is_le=false: atom true when expr >= 0 → check LB >= 0
                        let implied = if info.is_le {
                            ub.as_ref().is_some_and(|ep| {
                                Self::endpoint_implies_le_zero(ep, compound.strict)
                            })
                        } else {
                            lb.as_ref().is_some_and(|ep| {
                                Self::endpoint_implies_ge_zero(ep, compound.strict)
                            })
                        };
                        if implied {
                            let reason = self.collect_interval_reasons(&expr, info.is_le);
                            (!reason.is_empty()).then_some(reason)
                        } else {
                            None
                        }
                    }
                    _ => None,
                }
            } else {
                None
            };
            if let Some(reason) = direct_true_reason {
                self.propagated_atoms.insert((compound.term, true));
                self.pending_propagations.push(PendingPropagation::eager(
                    TheoryLit::new(compound.term, true),
                    reason,
                ));
                return true;
            }
            if let Some(row_idx) = implied_true_row {
                self.propagated_atoms.insert((compound.term, true));
                self.pending_propagations.push(PendingPropagation::deferred(
                    TheoryLit::new(compound.term, true),
                    DeferredReason {
                        var: compound.slack,
                        need_upper: atom.is_upper,
                        fallback_row_idx: Some(row_idx),
                    },
                ));
                return true;
            }
            if let Some(reason) = interval_true_reason {
                self.propagated_atoms.insert((compound.term, true));
                self.pending_propagations.push(PendingPropagation::eager(
                    TheoryLit::new(compound.term, true),
                    reason,
                ));
                return true;
            }
        }

        let direct_false_reason = if atom.is_upper {
            direct_lower.as_ref().and_then(|(value, strict, reason)| {
                let implied = if atom.strict {
                    value >= &atom.bound_value
                } else {
                    value > &atom.bound_value || (value == &atom.bound_value && *strict)
                };
                (implied && !reason.is_empty()).then(|| reason.clone())
            })
        } else {
            direct_upper.as_ref().and_then(|(value, strict, reason)| {
                let implied = if atom.strict {
                    value <= &atom.bound_value
                } else {
                    value < &atom.bound_value || (value == &atom.bound_value && *strict)
                };
                (implied && !reason.is_empty()).then(|| reason.clone())
            })
        };
        let implied_false_row = if atom.is_upper {
            implied_lower.as_ref().and_then(|(value, strict, row_idx)| {
                let cmp = value.cmp_big(&atom.bound_value);
                let implied = if atom.strict {
                    cmp == std::cmp::Ordering::Greater || cmp == std::cmp::Ordering::Equal
                } else {
                    cmp == std::cmp::Ordering::Greater
                        || (cmp == std::cmp::Ordering::Equal && *strict)
                };
                implied.then_some(*row_idx)
            })
        } else {
            implied_upper.as_ref().and_then(|(value, strict, row_idx)| {
                let cmp = value.cmp_big(&atom.bound_value);
                let implied = if atom.strict {
                    cmp == std::cmp::Ordering::Less || cmp == std::cmp::Ordering::Equal
                } else {
                    cmp == std::cmp::Ordering::Less || (cmp == std::cmp::Ordering::Equal && *strict)
                };
                implied.then_some(*row_idx)
            })
        };

        if !self.propagated_atoms.contains(&(compound.term, false)) {
            let interval_false_reason =
                if direct_false_reason.is_none() && implied_false_row.is_none() {
                    match self.atom_cache.get(&compound.term) {
                        Some(Some(info)) => {
                            let expr = info.expr.clone();
                            let (lb, ub) = self.compute_expr_interval(&expr);
                            // is_le=true: atom false when expr > 0 → check LB > 0
                            // is_le=false: atom false when expr < 0 → check UB < 0
                            let implied = if info.is_le {
                                lb.as_ref().is_some_and(|ep| {
                                    Self::endpoint_implies_not_le_zero(ep, compound.strict)
                                })
                            } else {
                                ub.as_ref().is_some_and(|ep| {
                                    Self::endpoint_implies_not_ge_zero(ep, compound.strict)
                                })
                            };
                            if implied {
                                let reason = self.collect_interval_reasons(&expr, !info.is_le);
                                (!reason.is_empty()).then_some(reason)
                            } else {
                                None
                            }
                        }
                        _ => None,
                    }
                } else {
                    None
                };
            if let Some(reason) = direct_false_reason {
                self.propagated_atoms.insert((compound.term, false));
                self.pending_propagations.push(PendingPropagation::eager(
                    TheoryLit::new(compound.term, false),
                    reason,
                ));
                return true;
            }
            if let Some(row_idx) = implied_false_row {
                self.propagated_atoms.insert((compound.term, false));
                self.pending_propagations.push(PendingPropagation::deferred(
                    TheoryLit::new(compound.term, false),
                    DeferredReason {
                        var: compound.slack,
                        need_upper: !atom.is_upper,
                        fallback_row_idx: Some(row_idx),
                    },
                ));
                return true;
            }
            if let Some(reason) = interval_false_reason {
                self.propagated_atoms.insert((compound.term, false));
                self.pending_propagations.push(PendingPropagation::eager(
                    TheoryLit::new(compound.term, false),
                    reason,
                ));
                return true;
            }
        }

        false
    }
}
