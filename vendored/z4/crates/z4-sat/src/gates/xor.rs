// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! XOR gate detection for BVE and congruence.
//!
//! XOR gate y = x1 ⊕ x2 ⊕ ... ⊕ xk (up to arity 5) is encoded as 2^k
//! clauses with all even-parity sign patterns.

use super::{bit_parity, sorted_lit_pair, Gate, GateExtractor, GateType};
use crate::clause_arena::ClauseArena;
use crate::literal::{Literal, Variable};

/// Maximum XOR arity for gate detection. CaDiCaL default: `elimxorlim=5`.
/// A k-arity XOR requires finding `2^k` clauses, so cost is exponential in arity.
const XOR_ARITY_LIMIT: usize = 5;

impl GateExtractor {
    pub(super) fn find_xor_gate_db(
        &self,
        pivot: Variable,
        clauses: &ClauseArena,
        pos_occs: &[usize],
        neg_occs: &[usize],
    ) -> Option<Gate> {
        let pivot_pos = Literal::positive(pivot);
        let pivot_neg = Literal::negative(pivot);

        for &clause_idx in pos_occs {
            if clause_idx >= clauses.len() || clauses.is_empty_clause(clause_idx) {
                continue;
            }
            let clause = clauses.literals(clause_idx);
            let Some((a, b)) = Self::get_ternary_others(clause, pivot_pos) else {
                continue;
            };

            let needed_pos = sorted_lit_pair(a.negated(), b.negated());
            let needed_neg1 = sorted_lit_pair(a.negated(), b);
            let needed_neg2 = sorted_lit_pair(a, b.negated());

            let mut pos_idx2 = None;
            for &ci in pos_occs {
                if ci == clause_idx || ci >= clauses.len() || clauses.is_empty_clause(ci) {
                    continue;
                }
                let c = clauses.literals(ci);
                if let Some((x, y)) = Self::get_ternary_others(c, pivot_pos) {
                    if sorted_lit_pair(x, y) == needed_pos {
                        pos_idx2 = Some(ci);
                        break;
                    }
                }
            }

            if pos_idx2.is_none() {
                continue;
            }

            let mut neg_idx1 = None;
            let mut neg_idx2 = None;
            for &ci in neg_occs {
                if ci >= clauses.len() || clauses.is_empty_clause(ci) {
                    continue;
                }
                let c = clauses.literals(ci);
                if let Some((x, y)) = Self::get_ternary_others(c, pivot_neg) {
                    let candidate = sorted_lit_pair(x, y);
                    if candidate == needed_neg1 {
                        neg_idx1 = Some(ci);
                    } else if candidate == needed_neg2 {
                        neg_idx2 = Some(ci);
                    }
                }
            }

            if let (Some(neg1), Some(neg2)) = (neg_idx1, neg_idx2) {
                if let Some(pos2) = pos_idx2 {
                    debug_assert!(
                        {
                            let mut ids = [clause_idx, pos2, neg1, neg2];
                            ids.sort_unstable();
                            ids.windows(2).all(|w| w[0] != w[1])
                        },
                        "BUG: XOR arity-2 witness clauses must be distinct"
                    );
                    debug_assert_ne!(
                        a.variable(),
                        b.variable(),
                        "BUG: XOR-2 inputs share variable"
                    );
                    // CaDiCaL-style RHS normalization: all XOR inputs stored
                    // as positive literals. Parity of negated input literals
                    // in the seed clause determines XOR vs XNOR.
                    // CaDiCaL: `if (!negated) lhs = -lhs` — even parity of
                    // negated inputs means XNOR (#6997, #7137).
                    let neg_inputs = u32::from(!a.is_positive()) + u32::from(!b.is_positive());
                    return Some(Gate {
                        output: pivot,
                        gate_type: GateType::Xor,
                        inputs: vec![
                            Literal::positive(a.variable()),
                            Literal::positive(b.variable()),
                        ],
                        defining_clauses: vec![clause_idx, pos2, neg1, neg2],
                        negated_output: neg_inputs % 2 == 0,
                    });
                }
            }
        }

        // Arity-2 fast path didn't find a gate. Try higher arities (3..=XOR_ARITY_LIMIT)
        // using CaDiCaL's generalized even-parity sign enumeration.
        self.find_xor_gate_higher_arity(pivot, clauses, pos_occs, neg_occs)
    }

    /// Higher-arity XOR gate detection (arity 3..=XOR_ARITY_LIMIT).
    ///
    /// Uses CaDiCaL's even-parity sign enumeration algorithm from `gates.cpp:632-711`.
    /// Only called as fallback when the arity-2 fast path doesn't find a gate.
    fn find_xor_gate_higher_arity(
        &self,
        pivot: Variable,
        clauses: &ClauseArena,
        pos_occs: &[usize],
        neg_occs: &[usize],
    ) -> Option<Gate> {
        let pivot_pos = Literal::positive(pivot);

        for &clause_idx in pos_occs {
            if clause_idx >= clauses.len() || clauses.is_empty_clause(clause_idx) {
                continue;
            }
            let clause = clauses.literals(clause_idx);
            let size = clause.len();
            // Arity 2 (size 3) is handled by the fast path above. Start at arity 3.
            if size < 4 {
                continue;
            }
            let arity = size - 1;
            if arity > XOR_ARITY_LIMIT {
                continue;
            }

            // Build working literal buffer: lits[0] = pivot_pos, rest from clause.
            let mut lits: Vec<Literal> = Vec::with_capacity(size);
            lits.push(pivot_pos);
            for &lit in clause {
                if lit.variable() != pivot {
                    lits.push(lit);
                }
            }
            if lits.len() != size {
                continue;
            }

            // Enumerate the remaining 2^arity - 1 even-parity sign patterns.
            // CaDiCaL reference: gates.cpp:663-680.
            let needed_total = (1u32 << arity) - 1;
            let mut remaining = needed_total;
            let mut signs: u32 = 0;
            let mut gate_clauses: Vec<usize> = Vec::with_capacity(1 << arity);
            let mut found_all = true;

            while remaining > 0 {
                let prev = signs;
                signs += 1;
                // Skip odd-parity patterns.
                while bit_parity(signs) {
                    signs += 1;
                }

                // Flip literals whose sign bit changed.
                for (j, lit) in lits.iter_mut().enumerate() {
                    let bit = 1u32 << j;
                    if (prev & bit) != (signs & bit) {
                        *lit = lit.negated();
                    }
                }

                // Search the appropriate occurrence list based on pivot polarity.
                let search_occs = if lits[0] == pivot_pos {
                    pos_occs
                } else {
                    neg_occs
                };

                if let Some(idx) = self.find_clause_by_lits(&lits, clauses, search_occs) {
                    gate_clauses.push(idx);
                } else {
                    found_all = false;
                    break;
                }

                remaining -= 1;
            }

            if !found_all {
                continue;
            }

            // Add seed clause.
            gate_clauses.push(clause_idx);
            debug_assert_eq!(gate_clauses.len(), 1 << arity);

            let raw_inputs: Vec<Literal> = clause
                .iter()
                .filter(|lit| lit.variable() != pivot)
                .copied()
                .collect();
            debug_assert!(
                !raw_inputs.is_empty(),
                "BUG: XOR gate extraction must produce at least one input literal"
            );
            debug_assert_eq!(
                raw_inputs.len(),
                arity,
                "BUG: XOR gate extraction arity must match input literal count"
            );
            debug_assert!(
                raw_inputs.len() >= 3 && raw_inputs.len() <= XOR_ARITY_LIMIT,
                "BUG: higher-arity XOR inputs.len()={}, expected 3..={XOR_ARITY_LIMIT}",
                raw_inputs.len()
            );

            // CaDiCaL-style RHS normalization: store all inputs as positive.
            // Even negated count = XNOR (#6997, #7137).
            let neg_inputs: u32 = raw_inputs.iter().map(|l| u32::from(!l.is_positive())).sum();
            let inputs: Vec<Literal> = raw_inputs
                .iter()
                .map(|l| Literal::positive(l.variable()))
                .collect();
            return Some(Gate {
                output: pivot,
                gate_type: GateType::Xor,
                inputs,
                defining_clauses: gate_clauses,
                negated_output: neg_inputs.is_multiple_of(2),
            });
        }

        None
    }

    /// Find a clause in `occs` that matches the given literal set exactly.
    /// CaDiCaL reference: `gates.cpp:617-629`.
    fn find_clause_by_lits(
        &self,
        lits: &[Literal],
        clauses: &ClauseArena,
        occs: &[usize],
    ) -> Option<usize> {
        let target_size = lits.len();
        'next_clause: for &ci in occs {
            if ci >= clauses.len() || clauses.is_empty_clause(ci) {
                continue;
            }
            let c = clauses.literals(ci);
            if c.len() != target_size {
                continue;
            }
            for &want in lits {
                if !c.contains(&want) {
                    continue 'next_clause;
                }
            }
            return Some(ci);
        }
        None
    }
}
