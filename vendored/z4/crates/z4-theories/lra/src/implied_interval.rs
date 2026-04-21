// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Interval computation and endpoint predicates for implied bounds.
//!
//! Extracted from `implied_bounds.rs` to reduce file size.
//! Contains: `compute_expr_interval`, endpoint implication predicates,
//! `collect_interval_reasons`, and `collect_slack_interval_reasons_for_var`.

use super::*;

impl LraSolver {
    /// Compute interval `[lb, ub]` of a linear expression from current bounds.
    ///
    /// Direct bounds are preferred because their witnesses are read directly
    /// from asserted atoms. When a direct bound is absent, the interval falls
    /// back to the current implied bound so compound propagation still has a
    /// finite endpoint to reason about. Endpoint strictness is preserved so
    /// callers can distinguish closed `0` from open `0` (`#6582`).
    pub(crate) fn compute_expr_interval(&self, expr: &LinearExpr) -> ExprInterval {
        let mut lb = expr.constant.to_big();
        let mut ub = expr.constant.to_big();
        let mut lb_finite = true;
        let mut ub_finite = true;
        let mut lb_strict = false;
        let mut ub_strict = false;

        for &(var, ref coeff) in &expr.coeffs {
            let vi = var as usize;
            if vi >= self.vars.len() {
                return (None, None);
            }
            let info = &self.vars[vi];

            // Use direct bounds first, fall back to implied bounds (#4919).
            // Implied bounds from compute_implied_bounds() provide tighter
            // intervals for variables that only have row-derived bounds,
            // enabling multi-variable atom propagation on compound atoms.
            let direct_lb = info.lower.as_ref().map(|b| (b.value_big(), b.strict));
            let direct_ub = info.upper.as_ref().map(|b| (b.value_big(), b.strict));
            let implied_lb = if direct_lb.is_none() && vi < self.implied_bounds.len() {
                self.implied_bounds[vi]
                    .0
                    .as_ref()
                    .map(|ib| (ib.value.to_big(), ib.strict))
            } else {
                None
            };
            let implied_ub = if direct_ub.is_none() && vi < self.implied_bounds.len() {
                self.implied_bounds[vi]
                    .1
                    .as_ref()
                    .map(|ib| (ib.value.to_big(), ib.strict))
            } else {
                None
            };

            if coeff.is_positive() {
                // c > 0: ub += c * ub(x), lb += c * lb(x)
                if ub_finite {
                    if let Some((ref bv, strict)) = direct_ub {
                        ub += coeff.mul_bigrational(bv);
                        ub_strict |= strict;
                    } else if let Some((ref bv, strict)) = implied_ub {
                        ub += coeff.mul_bigrational(bv);
                        ub_strict |= strict;
                    } else {
                        ub_finite = false;
                    }
                }
                if lb_finite {
                    if let Some((ref bv, strict)) = direct_lb {
                        lb += coeff.mul_bigrational(bv);
                        lb_strict |= strict;
                    } else if let Some((ref bv, strict)) = implied_lb {
                        lb += coeff.mul_bigrational(bv);
                        lb_strict |= strict;
                    } else {
                        lb_finite = false;
                    }
                }
            } else {
                // c < 0: ub += c * lb(x), lb += c * ub(x)
                if ub_finite {
                    if let Some((ref bv, strict)) = direct_lb {
                        ub += coeff.mul_bigrational(bv);
                        ub_strict |= strict;
                    } else if let Some((ref bv, strict)) = implied_lb {
                        ub += coeff.mul_bigrational(bv);
                        ub_strict |= strict;
                    } else {
                        ub_finite = false;
                    }
                }
                if lb_finite {
                    if let Some((ref bv, strict)) = direct_ub {
                        lb += coeff.mul_bigrational(bv);
                        lb_strict |= strict;
                    } else if let Some((ref bv, strict)) = implied_ub {
                        lb += coeff.mul_bigrational(bv);
                        lb_strict |= strict;
                    } else {
                        lb_finite = false;
                    }
                }
            }
            // #8800: Early exit when both bounds are infinite — no more arithmetic needed.
            if !lb_finite && !ub_finite {
                return (None, None);
            }
        }

        (
            lb_finite.then(|| IntervalEndpoint::new(lb, lb_strict)),
            ub_finite.then(|| IntervalEndpoint::new(ub, ub_strict)),
        )
    }

    pub(crate) fn endpoint_implies_le_zero(ep: &IntervalEndpoint, strict_atom: bool) -> bool {
        if strict_atom {
            ep.value.is_negative() || (ep.value.is_zero() && ep.strict)
        } else {
            !ep.value.is_positive()
        }
    }

    pub(crate) fn endpoint_implies_ge_zero(ep: &IntervalEndpoint, strict_atom: bool) -> bool {
        if strict_atom {
            ep.value.is_positive() || (ep.value.is_zero() && ep.strict)
        } else {
            !ep.value.is_negative()
        }
    }

    pub(crate) fn endpoint_implies_not_le_zero(ep: &IntervalEndpoint, strict_atom: bool) -> bool {
        if strict_atom {
            !ep.value.is_negative()
        } else {
            ep.value.is_positive() || (ep.value.is_zero() && ep.strict)
        }
    }

    pub(crate) fn endpoint_implies_not_ge_zero(ep: &IntervalEndpoint, strict_atom: bool) -> bool {
        if strict_atom {
            !ep.value.is_positive()
        } else {
            ep.value.is_negative() || (ep.value.is_zero() && ep.strict)
        }
    }

    /// Collect the reason literals for an interval bound on an expression.
    /// `for_upper`: if true, collect reasons for the upper bound (used when
    /// propagating atom=true); if false, for the lower bound (atom=false).
    ///
    /// When a variable lacks a direct bound but has an implied bound from a
    /// tableau row, transitively collects reasons from the nonbasic variables
    /// in that row (#4919).
    ///
    /// When an implied bound was derived from a tableau row (row_idx != usize::MAX),
    /// uses the derivation chain to collect complete reasons (#6202).
    pub(crate) fn collect_interval_reasons(
        &self,
        expr: &LinearExpr,
        for_upper: bool,
    ) -> Vec<TheoryLit> {
        let mut reasons = Vec::new();
        let mut seen = HashSet::new();
        // #6590: Share visited_vars across all recursive reason collections in
        // this expression. Previously each coefficient variable created a fresh
        // visited_vars, causing redundant re-exploration of shared derivation
        // chains. Sharing prevents O(coeffs × depth) re-exploration.
        let mut visited_vars = HashSet::new();
        let mut complete = true;
        for &(var, ref coeff) in &expr.coeffs {
            let vi = var as usize;
            if vi >= self.vars.len() {
                complete = false;
                break;
            }
            // For upper bound: c>0 → use ub(x), c<0 → use lb(x)
            // For lower bound: c>0 → use lb(x), c<0 → use ub(x)
            let need_upper = coeff.is_positive() == for_upper;

            let info = &self.vars[vi];
            let bound = if need_upper { &info.upper } else { &info.lower };
            if let Some(b) = bound {
                for (term, val) in b.reason_pairs() {
                    if !term.is_sentinel() && seen.insert((term, val)) {
                        reasons.push(TheoryLit::new(term, val));
                    }
                }
            } else if vi < self.implied_bounds.len() {
                // #8782: Try eager explanation first (matching collect_row_reasons_dedup).
                // collect_row_reasons_recursive produced incomplete reasons when the
                // simplex basis changed since the implied bound was derived, or when
                // the depth limit was hit. BoundExplanation captures the contributing
                // variables at derivation time and is always complete.
                let ib = if need_upper {
                    &self.implied_bounds[vi].1
                } else {
                    &self.implied_bounds[vi].0
                };
                let mut used_explanation = false;
                if let Some(ib) = ib {
                    if let Some(ref expl) = ib.explanation {
                        if self.collect_reasons_from_explanation(
                            expl,
                            &mut reasons,
                            &mut seen,
                            &mut visited_vars,
                        ) {
                            used_explanation = true;
                        }
                    }
                }
                if !used_explanation
                    && !self.collect_row_reasons_recursive(
                        var,
                        need_upper,
                        &mut reasons,
                        &mut seen,
                        &mut visited_vars,
                        0,
                    )
                {
                    complete = false;
                    break;
                }
            } else if !self.collect_row_reasons_recursive(
                var,
                need_upper,
                &mut reasons,
                &mut seen,
                &mut visited_vars,
                0,
            ) {
                complete = false;
                break;
            }
        }
        if !complete {
            reasons.clear();
        }
        reasons
    }

    /// For a slack variable, reconstruct sound reasons from the original linear
    /// expression rather than using the slack bound's own witness list (#6564).
    ///
    /// Slack variables represent compound atoms (e.g., `s = x + y` for `x+y<=10`).
    /// Their direct bound `reason_pairs()` only witness the slack bound itself,
    /// not the contributing original-variable bounds. This helper looks up the
    /// atom's original expression via `atom_index`/`atom_cache` and delegates to
    /// `collect_interval_reasons` which walks the original variables.
    ///
    /// Returns `None` if the variable is not a slack, or if the expression lookup
    /// fails. Returns `Some(vec![])` if reconstruction was attempted but produced
    /// no reasons (caller should skip the propagation).
    pub(crate) fn collect_slack_interval_reasons_for_var(
        &self,
        var: u32,
        for_upper: bool,
    ) -> Option<Vec<TheoryLit>> {
        if !self.slack_var_set.contains(&var) {
            return None;
        }

        let atoms = self.atom_index.get(&var)?;
        let first_atom = atoms.first()?;
        let info = self.atom_cache.get(&first_atom.term)?.as_ref()?;

        Some(self.collect_interval_reasons(&info.expr, for_upper))
    }
}
