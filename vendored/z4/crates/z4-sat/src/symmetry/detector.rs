// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! BreakID-style symmetry detector: iterative refinement + orbit extraction.
//!
//! Orchestrates the full symmetry-breaking pipeline:
//! 1. Iterative color refinement on the clause-variable incidence graph.
//! 2. Swap verification within refined color classes.
//! 3. Orbit extraction from verified swaps via union-find.
//! 4. Lex-leader SBP clause generation per orbit.
//!
//! This replaces the coarse single-pass color grouping in the original
//! `detect_binary_swaps` with multi-round Weisfeiler-Leman refinement,
//! producing tighter candidate groups and fewer false-positive swap checks.
//!
//! Reference: Devriendt, Bogaerts, Bruynooghe, Denecker. "Improved Static
//! Symmetry Breaking for SAT." (BreakID, SAT 2016).

use std::collections::BTreeMap;

use crate::Literal;

use super::orbits;
use super::refinement;
use super::{build_formula_counts, canonical_clause_key, BinarySwap};

/// BreakID-style symmetry detector.
///
/// Orchestrates the full pipeline:
/// 1. Iterative color refinement on the clause-variable incidence graph.
/// 2. Swap verification within refined color classes.
/// 3. Orbit extraction from verified swaps via union-find.
/// 4. Lex-leader SBP clause generation.
pub(crate) struct SymmetryDetector {
    /// Maximum number of swap pairs to verify.
    max_pairs: usize,
    /// Maximum size of a single color class to consider.
    max_group_size: usize,
}

/// Statistics produced by the detector pipeline.
#[derive(Debug, Clone, Default)]
pub(crate) struct DetectorStats {
    /// Number of iterative refinement rounds.
    pub(crate) refinement_rounds: u64,
    /// Number of candidate pairs considered.
    pub(crate) candidate_pairs: u64,
    /// Number of verified swap pairs.
    pub(crate) pairs_detected: u64,
    /// Number of orbits (connected components of swap graph) detected.
    pub(crate) orbits_detected: u64,
}

impl SymmetryDetector {
    /// Create a new detector with the given budget limits.
    pub(crate) fn new(max_pairs: usize, max_group_size: usize) -> Self {
        Self {
            max_pairs,
            max_group_size,
        }
    }

    /// Run the full detection pipeline and return symmetry-breaking clauses.
    ///
    /// Returns `(breaking_clauses, stats)` where each breaking clause
    /// is a `Vec<Literal>`. The caller is responsible for adding these to the
    /// solver's clause database.
    pub(crate) fn detect_and_encode(
        &self,
        clauses: &[Vec<Literal>],
    ) -> (Vec<Vec<Literal>>, DetectorStats) {
        let mut stats = DetectorStats::default();

        // Phase 1: Iterative color refinement.
        let refined = refinement::iterative_color_refinement(clauses);
        stats.refinement_rounds = refined.rounds as u64;

        // Phase 2: Within each refined color class, verify swaps.
        let formula_counts = build_formula_counts(clauses);
        let groups = refined.candidate_groups();
        let mut verified_swaps: Vec<BinarySwap> = Vec::new();

        for variables in groups.into_values() {
            if variables.len() < 2 || variables.len() > self.max_group_size {
                continue;
            }
            for i in 0..variables.len() {
                for j in (i + 1)..variables.len() {
                    if verified_swaps.len() >= self.max_pairs {
                        break;
                    }
                    stats.candidate_pairs += 1;
                    let pair = BinarySwap::ordered(variables[i], variables[j]);
                    if swap_preserves_formula(&formula_counts, pair) {
                        stats.pairs_detected += 1;
                        verified_swaps.push(pair);
                    }
                }
                if verified_swaps.len() >= self.max_pairs {
                    break;
                }
            }
        }

        if verified_swaps.is_empty() {
            return (Vec::new(), stats);
        }

        // Phase 3: Extract orbits from verified swaps using union-find.
        let orbit_list = orbits::extract_orbits(&verified_swaps);
        stats.orbits_detected = orbit_list.len() as u64;

        // Phase 4: Generate lex-leader SBP clauses for each orbit.
        let mut all_clauses = Vec::new();
        for orbit in &orbit_list {
            let sbp_clauses = orbits::encode_orbit_lex_leader_sbp(orbit);
            all_clauses.extend(sbp_clauses);
        }

        (all_clauses, stats)
    }
}

/// Check whether swapping `pair.lhs <-> pair.rhs` in every clause preserves
/// the formula as a multiset of canonical clause keys.
fn swap_preserves_formula(formula_counts: &BTreeMap<Vec<u32>, u32>, pair: BinarySwap) -> bool {
    formula_counts.iter().all(|(clause, count)| {
        formula_counts
            .get(&swap_clause_key(clause, pair))
            .is_some_and(|swapped_count| swapped_count == count)
    })
}

/// Apply a variable swap to a canonical clause key and re-sort.
fn swap_clause_key(clause: &[u32], pair: BinarySwap) -> Vec<u32> {
    let mut swapped = Vec::with_capacity(clause.len());
    for &raw in clause {
        let lit = Literal(raw);
        let mapped_var = if lit.variable() == pair.lhs {
            pair.rhs
        } else if lit.variable() == pair.rhs {
            pair.lhs
        } else {
            lit.variable()
        };
        let mapped_lit = if lit.is_positive() {
            Literal::positive(mapped_var)
        } else {
            Literal::negative(mapped_var)
        };
        swapped.push(mapped_lit.raw());
    }
    swapped.sort_unstable();
    swapped
}

/// Deduplicate SBP clauses against existing formula clauses.
pub(crate) fn deduplicate_sbp_clauses(
    sbp_clauses: Vec<Vec<Literal>>,
    existing: &BTreeMap<Vec<u32>, u32>,
) -> Vec<Vec<Literal>> {
    sbp_clauses
        .into_iter()
        .filter(|clause| {
            let key = canonical_clause_key(clause);
            !existing.contains_key(&key)
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Literal, Variable};

    #[test]
    fn test_detector_symmetric_pigeonhole_fragment() {
        // Minimal pigeonhole-like symmetric formula:
        // x0 and x1 are interchangeable, x2 and x3 are interchangeable.
        let x0 = Variable(0);
        let x1 = Variable(1);
        let x2 = Variable(2);
        let x3 = Variable(3);
        let z = Variable(4);

        let clauses = vec![
            // x0 <-> x1 symmetry group
            vec![Literal::positive(x0), Literal::positive(z)],
            vec![Literal::positive(x1), Literal::positive(z)],
            vec![Literal::negative(x0), Literal::negative(z)],
            vec![Literal::negative(x1), Literal::negative(z)],
            // x2 <-> x3 symmetry group (separate from x0,x1)
            vec![Literal::positive(x2), Literal::negative(z)],
            vec![Literal::positive(x3), Literal::negative(z)],
            vec![Literal::negative(x2), Literal::positive(z)],
            vec![Literal::negative(x3), Literal::positive(z)],
        ];

        let detector = SymmetryDetector::new(128, 64);
        let (sbp_clauses, stats) = detector.detect_and_encode(&clauses);

        // Should detect symmetries and emit SBP clauses.
        assert!(
            stats.refinement_rounds > 0,
            "should have performed refinement"
        );
        // At minimum, x0<->x1 and x2<->x3 should be detected.
        assert!(
            stats.pairs_detected >= 2,
            "expected at least 2 swap pairs, got {}",
            stats.pairs_detected
        );
        assert!(
            !sbp_clauses.is_empty(),
            "expected SBP clauses to be generated"
        );

        // All generated clauses should be binary (lex-leader encoding).
        for clause in &sbp_clauses {
            assert_eq!(clause.len(), 2, "lex-leader SBP clauses should be binary");
        }
    }

    #[test]
    fn test_detector_no_symmetry() {
        // Asymmetric formula: x0 and x1 have different occurrence patterns.
        let x0 = Variable(0);
        let x1 = Variable(1);
        let clauses = vec![
            vec![Literal::positive(x0)],
            vec![Literal::positive(x0), Literal::positive(x1)],
        ];

        let detector = SymmetryDetector::new(128, 64);
        let (sbp_clauses, stats) = detector.detect_and_encode(&clauses);

        assert!(
            sbp_clauses.is_empty(),
            "asymmetric formula should produce no SBP"
        );
        assert_eq!(stats.pairs_detected, 0);
    }

    #[test]
    fn test_detector_orbit_merging() {
        // Formula where x0, x1, x2 are all interchangeable: full S3 orbit.
        let x0 = Variable(0);
        let x1 = Variable(1);
        let x2 = Variable(2);
        let z = Variable(3);

        let clauses = vec![
            vec![Literal::positive(x0), Literal::positive(z)],
            vec![Literal::positive(x1), Literal::positive(z)],
            vec![Literal::positive(x2), Literal::positive(z)],
            vec![Literal::negative(x0), Literal::negative(z)],
            vec![Literal::negative(x1), Literal::negative(z)],
            vec![Literal::negative(x2), Literal::negative(z)],
        ];

        let detector = SymmetryDetector::new(128, 64);
        let (sbp_clauses, stats) = detector.detect_and_encode(&clauses);

        // All three swaps (0,1), (0,2), (1,2) should be detected.
        assert_eq!(stats.pairs_detected, 3, "S3 has 3 transpositions");
        // Single orbit of size 3 -> 2 lex-leader clauses.
        assert_eq!(stats.orbits_detected, 1, "should detect 1 orbit");
        assert_eq!(sbp_clauses.len(), 2, "orbit of size 3 needs 2 SBP clauses");
    }
}
