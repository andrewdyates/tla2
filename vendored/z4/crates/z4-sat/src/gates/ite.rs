// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! ITE (if-then-else) gate detection.
//!
//! ITE gate y = ITE(c, t, e) = (c ∧ t) ∨ (¬c ∧ e) is encoded as 4 ternary clauses:
//!   (y ∨ c ∨ ¬e), (y ∨ ¬c ∨ ¬t), (¬y ∨ c ∨ e), (¬y ∨ ¬c ∨ t)

use super::{Gate, GateExtractor, GateType};
use crate::clause_arena::ClauseArena;
use crate::literal::{Literal, Variable};

impl GateExtractor {
    pub(super) fn find_ite_gate_db(
        &self,
        pivot: Variable,
        clauses: &ClauseArena,
        pos_occs: &[usize],
        neg_occs: &[usize],
    ) -> Option<Gate> {
        let pivot_pos = Literal::positive(pivot);
        let pivot_neg = Literal::negative(pivot);

        // Two positive ternaries define candidates for (cond, then, else):
        //   (pivot ∨ cond ∨ ¬else), (pivot ∨ ¬cond ∨ ¬then)
        for (i, &ci) in pos_occs.iter().enumerate() {
            if ci >= clauses.len() || clauses.is_empty_clause(ci) {
                continue;
            }
            let c1 = clauses.literals(ci);
            let Some((a1, b1)) = Self::get_ternary_others(c1, pivot_pos) else {
                continue;
            };

            for &cj in &pos_occs[i + 1..] {
                if cj >= clauses.len() || clauses.is_empty_clause(cj) {
                    continue;
                }
                let c2 = clauses.literals(cj);
                let Some((a2, b2)) = Self::get_ternary_others(c2, pivot_pos) else {
                    continue;
                };

                // (cond, then_neg, else_neg)
                let patterns = [
                    (a1, b2, b1, a1 == a2.negated()),
                    (a1, a2, b1, a1 == b2.negated()),
                    (b1, b2, a1, b1 == a2.negated()),
                    (b1, a2, a1, b1 == b2.negated()),
                ];

                for (cond, then_neg, else_neg, enabled) in patterns {
                    if !enabled {
                        continue;
                    }

                    let then_lit = then_neg.negated();
                    let else_lit = else_neg.negated();
                    let mut neg_idx_else = None;
                    let mut neg_idx_then = None;

                    for &nk in neg_occs {
                        if nk >= clauses.len() || clauses.is_empty_clause(nk) {
                            continue;
                        }
                        let cn = clauses.literals(nk);
                        let Some((x, y)) = Self::get_ternary_others(cn, pivot_neg) else {
                            continue;
                        };

                        if (x == cond && y == else_lit) || (x == else_lit && y == cond) {
                            neg_idx_else = Some(nk);
                        } else if (x == cond.negated() && y == then_lit)
                            || (x == then_lit && y == cond.negated())
                        {
                            neg_idx_then = Some(nk);
                        }
                    }

                    if let (Some(n1), Some(n2)) = (neg_idx_else, neg_idx_then) {
                        debug_assert!(
                            cond.variable() != pivot
                                && then_lit.variable() != pivot
                                && else_lit.variable() != pivot,
                            "BUG: ITE semantic inputs must not include output variable"
                        );
                        debug_assert!(
                            {
                                let mut ids = [ci, cj, n1, n2];
                                ids.sort_unstable();
                                ids.windows(2).all(|w| w[0] != w[1])
                            },
                            "BUG: ITE witness clauses must be distinct"
                        );
                        return Some(Gate {
                            output: pivot,
                            gate_type: GateType::Ite,
                            inputs: vec![cond, then_lit, else_lit],
                            defining_clauses: vec![ci, cj, n1, n2],
                            negated_output: false,
                        });
                    }
                }
            }
        }

        None
    }
}
