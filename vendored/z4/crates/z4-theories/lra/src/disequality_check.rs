// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl LraSolver {
    /// Check regular disequalities against the current model.
    pub(crate) fn check_disequalities(
        &mut self,
        disequalities: &[(TermId, LinearExpr, bool)],
        debug: bool,
    ) -> Option<TheoryResult> {
        // Reset violation flag at start of disequality check. Will be set
        // to true if any violation triggers a split request.
        self.last_diseq_check_had_violation = false;
        // Clear stale batch splits from previous check() invocations (#6269).
        // Without this, splits buffered before a NeedExpressionSplit early
        // return survive into the next check() call, causing duplicates.
        self.pending_diseq_splits.clear();
        if debug {
            safe_eprintln!("[LRA] Before disequality check, var bounds:");
            for (i, info) in self.vars.iter().enumerate() {
                safe_eprintln!(
                    "  var {}: lb={:?}, ub={:?}, value={}",
                    i,
                    info.lower.as_ref().map(|b| &b.value),
                    info.upper.as_ref().map(|b| &b.value),
                    info.value
                );
            }
        }
        // Evaluate each disequality in the current model
        // A disequality (term, expr, asserted_value) with expr = LHS - RHS is violated if expr == 0
        for (term, expr, asserted_value) in disequalities {
            // Evaluate the expression in the current model using InfRational
            // to account for epsilon components from strict bounds (#6020).
            // Using only the rational part (BigRational) discards ε, causing
            // values like x = 0+ε, y = 0 to evaluate as x - y = 0 instead
            // of x - y = ε ≠ 0, leading to spurious NeedExpressionSplit.
            let mut eval_inf = InfRational::from_rat(expr.constant.clone());
            for &(var, ref coeff) in &expr.coeffs {
                if let Some(info) = self.vars.get(var as usize) {
                    let scaled = info.value.mul_rat(coeff);
                    eval_inf += &scaled;
                }
            }
            let eval_value = eval_inf.rational();

            if debug {
                safe_eprintln!(
                    "[LRA] Checking disequality {:?}: expr value = {} (inf: {:?})",
                    term,
                    eval_value,
                    eval_inf
                );
            }

            // If expr == 0 (including epsilon), the disequality is violated.
            // A non-zero epsilon means the values differ infinitesimally,
            // which satisfies the disequality in the real-valued model.
            if eval_inf.is_zero() {
                // First check if the expression is forced to 0 by equality constraints.
                // This handles cases like `A = B` making `A - B` identically 0, even if
                // the individual variables A and B have slack.
                if let Some((equality_reasons, is_forced)) =
                    self.is_expression_forced_to_value(expr, &BigRational::zero())
                {
                    if is_forced {
                        debug!(
                            target: "z4::lra",
                            reason = "forced_equality",
                            "Disequality violated — UNSAT"
                        );
                        if debug {
                            safe_eprintln!(
                                "[LRA] Disequality {:?} is VIOLATED (expression forced to 0 by equality constraint) - returning Unsat",
                                term
                            );
                        }
                        let mut conflict = vec![TheoryLit {
                            term: *term,
                            value: *asserted_value,
                        }];
                        conflict.extend(equality_reasons);
                        self.conflict_count += 1;
                        return Some(TheoryResult::Unsat(conflict));
                    }
                }

                // Fallback: Check if all individual variables in the expression are pinned.
                // This handles cases where the expression doesn't match a tableau row.
                let all_vars_pinned = expr.coeffs.iter().all(|&(var, _)| {
                    if let Some(info) = self.vars.get(var as usize) {
                        // Variable is pinned if lower == upper == value
                        let pinned = info
                            .lower
                            .as_ref()
                            .is_some_and(|lb| lb.value == info.value.rational())
                            && info
                                .upper
                                .as_ref()
                                .is_some_and(|ub| ub.value == info.value.rational());
                        if debug && !pinned {
                            safe_eprintln!(
                                "[LRA] Var {} has slack: value={}, lb={:?}, ub={:?}",
                                var,
                                info.value,
                                info.lower.as_ref().map(|b| &b.value),
                                info.upper.as_ref().map(|b| &b.value)
                            );
                        }
                        pinned
                    } else {
                        false // Unknown variable - conservative: assume not pinned
                    }
                });

                if all_vars_pinned || expr.coeffs.is_empty() {
                    debug!(
                        target: "z4::lra",
                        reason = "pinned_vars",
                        "Disequality violated — UNSAT"
                    );
                    if debug {
                        safe_eprintln!(
                            "[LRA] Disequality {:?} is VIOLATED with forced model - returning Unsat",
                            term
                        );
                    }
                    // All variables are pinned, so the model is forced and violates disequality
                    // Build conflict clause: disequality + all bound reasons that pinned the variables
                    let seed_lit = TheoryLit {
                        term: *term,
                        value: *asserted_value,
                    };
                    let mut conflict = vec![seed_lit];
                    let mut seen: HashSet<TheoryLit> = HashSet::new();
                    seen.insert(seed_lit);
                    // Add all bound reasons that contributed to pinning the variables.
                    // Use HashSet for O(1) dedup instead of Vec::contains() (#938).
                    for &(var, _) in &expr.coeffs {
                        if let Some(info) = self.vars.get(var as usize) {
                            if let Some(ref lb) = info.lower {
                                for (term, val) in lb.reason_pairs() {
                                    if !term.is_sentinel() {
                                        let lit = TheoryLit::new(term, val);
                                        if seen.insert(lit) {
                                            conflict.push(lit);
                                        }
                                    }
                                }
                            }
                            if let Some(ref ub) = info.upper {
                                for (term, val) in ub.reason_pairs() {
                                    if !term.is_sentinel() {
                                        let lit = TheoryLit::new(term, val);
                                        if seen.insert(lit) {
                                            conflict.push(lit);
                                        }
                                    }
                                }
                            }
                        }
                    }
                    self.conflict_count += 1;
                    return Some(TheoryResult::Unsat(conflict));
                } else {
                    // Some variables have slack, so other solutions might exist.
                    // Request a split on (expr < 0) OR (expr > 0) to explore both regions.
                    // For a simple disequality like x != 0, this becomes (x < 0) OR (x > 0).

                    // Find a variable to split on.
                    // For single-variable disequalities (x != c), we split on x.
                    // For multi-variable disequalities (x - y != 0), we pick any variable with slack.
                    if expr.coeffs.len() == 1 {
                        let (var, coeff) = &expr.coeffs[0];
                        if let Some(&var_term) = self.var_to_term.get(var) {
                            // For expr = coeff*x + const = 0, the excluded value is -const/coeff.
                            // Previously this incorrectly used -const (ignoring coeff), which
                            // caused wrong split clauses for scaled disequalities like
                            // (distinct (* 2 x) 6) → should exclude x=3, not x=6 (#6155).
                            let excluded = (-expr.constant.clone() / coeff.clone()).to_big();
                            if debug {
                                safe_eprintln!(
                                    "[LRA] Disequality {:?} violated with slack - buffering split on var {:?} != {}",
                                    term,
                                    var_term,
                                    excluded
                                );
                            }
                            // Batch collect all single-var disequality splits (#6259).
                            // Instead of returning immediately on the first violation,
                            // collect all violated disequalities so the DPLL(T) split
                            // loop can process them in a single iteration. This avoids
                            // O(N) solver restarts for N violated disequalities.
                            self.pending_diseq_splits.push(DisequalitySplitRequest {
                                variable: var_term,
                                excluded_value: excluded,
                                disequality_term: Some(*term),
                                is_distinct: *asserted_value,
                            });
                            // Continue to check remaining disequalities
                            continue;
                        }
                    } else {
                        // Multi-variable disequality (e.g., E - F != 0, i.e., E != F).
                        //
                        // Always use expression splits for multi-variable disequalities.
                        // Single-variable enumeration is UNSOUND here (#5671): the clause
                        // `~distinct(E,F) OR var <= c-1 OR var >= c+1` doesn't capture
                        // constraints on the other variables, so it over-constrains the
                        // search space and can cause false UNSAT. The correct split is
                        // on the full expression: `E < F OR E > F`.
                        if debug {
                            safe_eprintln!(
                                "[LRA] Multi-var disequality {:?} violated - requesting expression split",
                                term
                            );
                        }
                        // Keep dirty so next check() re-evaluates disequalities (#5511).
                        self.dirty = true;
                        self.last_diseq_check_had_violation = true;
                        return Some(TheoryResult::NeedExpressionSplit(ExpressionSplitRequest {
                            disequality_term: *term,
                        }));
                    }

                    // Fallback for complex expressions where no variable has slack: return Unknown
                    if debug {
                        safe_eprintln!(
                            "[LRA] Disequality {:?} is VIOLATED but no splittable var found - returning Unknown",
                            term
                        );
                    }
                    // Keep dirty so next check() re-evaluates disequalities (#5511).
                    self.dirty = true;
                    return Some(TheoryResult::Unknown);
                }
            }
        }
        // After scanning all disequalities, return the first batched split (#6259).
        // Remaining splits are available via drain_pending_diseq_splits().
        if !self.pending_diseq_splits.is_empty() {
            let first = self.pending_diseq_splits.remove(0);
            if debug {
                safe_eprintln!(
                    "[LRA] Returning first of {} batched diseq splits (var {:?} != {})",
                    self.pending_diseq_splits.len() + 1,
                    first.variable,
                    first.excluded_value,
                );
            }
            self.dirty = true;
            self.last_diseq_check_had_violation = true;
            return Some(TheoryResult::NeedDisequalitySplit(first));
        }
        if debug {
            safe_eprintln!("[LRA] All disequalities satisfied");
        }
        None
    }

    /// Check shared disequalities from Nelson-Oppen.
    pub(crate) fn check_shared_disequalities(&mut self, debug: bool) -> Option<TheoryResult> {
        for (expr, reasons, eq_term) in &self.shared_disequality_trail {
            let mut eval_inf = InfRational::from_rat(expr.constant.clone());
            for &(var, ref coeff) in &expr.coeffs {
                if let Some(info) = self.vars.get(var as usize) {
                    let scaled = info.value.mul_rat(coeff);
                    eval_inf += &scaled;
                }
            }

            if debug {
                safe_eprintln!(
                    "[LRA] Checking shared disequality: expr value = {} (inf: {:?}, {} reasons)",
                    eval_inf.rational(),
                    eval_inf,
                    reasons.len()
                );
            }

            if eval_inf.is_zero() {
                // Shared disequality violated: model satisfies lhs = rhs but
                // the other theory asserted lhs != rhs.

                // Check if expression is forced to zero.
                if let Some((equality_reasons, is_forced)) =
                    self.is_expression_forced_to_value(expr, &BigRational::zero())
                {
                    if is_forced {
                        if debug {
                            safe_eprintln!(
                                "[LRA] Shared disequality VIOLATED (forced to 0) - returning Unsat"
                            );
                        }
                        let mut conflict: Vec<TheoryLit> = reasons.clone();
                        conflict.extend(equality_reasons);
                        self.conflict_count += 1;
                        return Some(TheoryResult::Unsat(conflict));
                    }
                }

                // Check if all variables are pinned.
                let all_vars_pinned = expr.coeffs.iter().all(|&(var, _)| {
                    self.vars.get(var as usize).is_some_and(|info| {
                        info.lower
                            .as_ref()
                            .is_some_and(|lb| lb.value == info.value.rational())
                            && info
                                .upper
                                .as_ref()
                                .is_some_and(|ub| ub.value == info.value.rational())
                    })
                });

                if all_vars_pinned || expr.coeffs.is_empty() {
                    if debug {
                        safe_eprintln!(
                            "[LRA] Shared disequality VIOLATED with pinned vars - returning Unsat"
                        );
                    }
                    let mut conflict: Vec<TheoryLit> = reasons.clone();
                    let mut seen: HashSet<TheoryLit> = conflict.iter().copied().collect();
                    // Use HashSet for O(1) dedup instead of Vec::contains() (#938).
                    for &(var, _) in &expr.coeffs {
                        if let Some(info) = self.vars.get(var as usize) {
                            if let Some(ref lb) = info.lower {
                                for (term, val) in lb.reason_pairs() {
                                    if !term.is_sentinel() {
                                        let lit = TheoryLit::new(term, val);
                                        if seen.insert(lit) {
                                            conflict.push(lit);
                                        }
                                    }
                                }
                            }
                            if let Some(ref ub) = info.upper {
                                for (term, val) in ub.reason_pairs() {
                                    if !term.is_sentinel() {
                                        let lit = TheoryLit::new(term, val);
                                        if seen.insert(lit) {
                                            conflict.push(lit);
                                        }
                                    }
                                }
                            }
                        }
                    }
                    self.conflict_count += 1;
                    return Some(TheoryResult::Unsat(conflict));
                }

                // Variables have slack — request a split.
                if expr.coeffs.len() == 1 {
                    let (var, coeff) = &expr.coeffs[0];
                    if let Some(&var_term) = self.var_to_term.get(var) {
                        // For expr = coeff*x + const = 0, excluded value is -const/coeff.
                        // Previously used -const (ignoring coeff), same bug as #6155.
                        let excluded = (-expr.constant.clone() / coeff.clone()).to_big();
                        if debug {
                            safe_eprintln!(
                                "[LRA] Shared disequality violated with slack - split on {:?} != {}",
                                var_term,
                                excluded
                            );
                        }
                        self.dirty = true;
                        self.last_diseq_check_had_violation = true;
                        // #6131: Pass the original equality term so the DPLL(T)
                        // layer creates a conditional split clause:
                        //   `term OR (x < c) OR (x > c)`
                        // Without this, the split is unconditional and survives
                        // backtracking, potentially causing false UNSAT.
                        return Some(TheoryResult::NeedDisequalitySplit(
                            DisequalitySplitRequest {
                                variable: var_term,
                                excluded_value: excluded,
                                disequality_term: *eq_term,
                                is_distinct: false,
                            },
                        ));
                    }
                }
                // Multi-variable shared disequality: use expression split
                // (same as regular disequality handler).
                // Without this, multi-var shared disequalities like f(x) - f(y) != 0
                // fall through to Unknown, causing completeness failures (#6148).
                if let Some(diseq_term) = eq_term {
                    if debug {
                        safe_eprintln!(
                            "[LRA] Multi-var shared disequality violated - requesting expression split"
                        );
                    }
                    self.dirty = true;
                    self.last_diseq_check_had_violation = true;
                    return Some(TheoryResult::NeedExpressionSplit(ExpressionSplitRequest {
                        disequality_term: *diseq_term,
                    }));
                }
                // No equality term available: keep dirty for re-evaluation.
                if debug {
                    safe_eprintln!(
                        "[LRA] Shared disequality violated - no eq_term for split, returning Unknown"
                    );
                }
                self.dirty = true;
                return Some(TheoryResult::Unknown);
            }
        }
        if debug {
            safe_eprintln!("[LRA] All shared disequalities satisfied");
        }
        None
    }
}
