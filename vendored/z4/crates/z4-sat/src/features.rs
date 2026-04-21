// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Static SAT instance feature extraction for algorithm selection.
//!
//! Computes SATzilla-style syntactic features from a CNF formula in O(n) time
//! where n is the total number of literal occurrences. These features are used
//! by the portfolio solver to select the best strategy per instance.
//!
//! ## Feature Set
//!
//! The feature vector captures:
//! - **Size features**: variable count, clause count, clause/variable ratio
//! - **Clause size distribution**: mean, std, min, max, fraction binary/ternary/horn
//! - **Variable-clause graph**: positive/negative literal balance, variable degree stats
//! - **Structure indicators**: pure literal count, unit clause count
//!
//! ## References
//!
//! - Xu, Hutter, Hoos, Leyton-Brown. "SATzilla: Portfolio-based Algorithm
//!   Selection for SAT." JAIR 2008.
//! - designs/2026-03-25-learned-algorithm-selection.md (Phase 1a: Static
//!   Syntactic Features)

use crate::literal::Literal;

/// Static syntactic features extracted from a CNF formula.
///
/// All features are computed in a single pass over the clause database.
/// The feature vector is designed for algorithm selection: different
/// portfolio strategies perform differently on formulas with different
/// structural properties.
#[derive(Debug, Clone, PartialEq)]
pub struct SatFeatures {
    // --- Size features ---
    /// Number of variables in the formula.
    pub(crate) num_vars: usize,
    /// Number of clauses in the formula.
    pub(crate) num_clauses: usize,
    /// Clause-to-variable ratio (num_clauses / num_vars).
    /// High ratios (>4.26 for 3-SAT) indicate over-constrained instances.
    pub(crate) clause_var_ratio: f64,

    // --- Clause size distribution ---
    /// Number of unit clauses (size 1).
    pub(crate) num_unit: usize,
    /// Number of binary clauses (size 2).
    pub(crate) num_binary: usize,
    /// Number of ternary clauses (size 3).
    pub(crate) num_ternary: usize,
    /// Number of horn clauses (at most one positive literal).
    pub(crate) num_horn: usize,
    /// Fraction of clauses that are binary.
    pub(crate) frac_binary: f64,
    /// Fraction of clauses that are ternary.
    pub(crate) frac_ternary: f64,
    /// Fraction of clauses that are horn.
    pub(crate) frac_horn: f64,
    /// Mean clause size.
    pub(crate) clause_size_mean: f64,
    /// Standard deviation of clause sizes.
    pub(crate) clause_size_std: f64,
    /// Minimum clause size (0 if no clauses).
    pub(crate) clause_size_min: usize,
    /// Maximum clause size.
    pub(crate) clause_size_max: usize,

    // --- Variable polarity balance ---
    /// Mean ratio of positive to total occurrences per variable.
    /// 0.5 = balanced, near 0 or 1 = highly polarized.
    pub(crate) pos_neg_balance_mean: f64,
    /// Standard deviation of the positive/total ratio across variables.
    pub(crate) pos_neg_balance_std: f64,

    // --- Variable degree features ---
    /// Mean variable degree (number of clause occurrences per variable).
    pub(crate) var_degree_mean: f64,
    /// Standard deviation of variable degrees.
    pub(crate) var_degree_std: f64,
    /// Maximum variable degree.
    pub(crate) var_degree_max: usize,

    // --- Structural indicators ---
    /// Number of pure literals (appearing in only one polarity).
    pub(crate) num_pure_literals: usize,
    /// Fraction of variables that are pure.
    pub(crate) frac_pure: f64,
}

impl SatFeatures {
    /// Extract features from a set of clauses.
    ///
    /// Runs in O(total_literals) time with O(num_vars) auxiliary space.
    pub fn extract(num_vars: usize, clauses: &[Vec<Literal>]) -> Self {
        let num_clauses = clauses.len();

        if num_vars == 0 || num_clauses == 0 {
            return Self::empty(num_vars, num_clauses);
        }

        // Per-variable occurrence counts.
        let mut pos_count: Vec<u32> = vec![0; num_vars];
        let mut neg_count: Vec<u32> = vec![0; num_vars];

        // Clause size stats.
        let mut num_unit = 0usize;
        let mut num_binary = 0usize;
        let mut num_ternary = 0usize;
        let mut num_horn = 0usize;
        let mut clause_size_min = usize::MAX;
        let mut clause_size_max = 0usize;
        let mut size_sum = 0u64;
        let mut size_sq_sum = 0u64;

        for clause in clauses {
            let len = clause.len();
            size_sum += len as u64;
            size_sq_sum += (len as u64) * (len as u64);
            if len < clause_size_min {
                clause_size_min = len;
            }
            if len > clause_size_max {
                clause_size_max = len;
            }

            match len {
                1 => num_unit += 1,
                2 => num_binary += 1,
                3 => num_ternary += 1,
                _ => {}
            }

            // Count positive literals for horn clause detection.
            let mut pos_in_clause = 0u32;
            for &lit in clause {
                let var_idx = lit.variable().index();
                if var_idx < num_vars {
                    if lit.is_positive() {
                        pos_count[var_idx] += 1;
                        pos_in_clause += 1;
                    } else {
                        neg_count[var_idx] += 1;
                    }
                }
            }
            // Horn clause: at most one positive literal.
            if pos_in_clause <= 1 {
                num_horn += 1;
            }
        }

        if clause_size_min == usize::MAX {
            clause_size_min = 0;
        }

        let n = num_clauses as f64;
        let clause_size_mean = size_sum as f64 / n;
        let variance = clause_size_mean.mul_add(-clause_size_mean, size_sq_sum as f64 / n);
        let clause_size_std = if variance > 0.0 { variance.sqrt() } else { 0.0 };

        // Variable degree and polarity balance.
        let mut degree_sum = 0u64;
        let mut degree_sq_sum = 0u64;
        let mut var_degree_max = 0usize;
        let mut balance_sum = 0.0f64;
        let mut balance_sq_sum = 0.0f64;
        let mut num_pure_literals = 0usize;
        let mut active_vars = 0usize;

        for i in 0..num_vars {
            let p = u64::from(pos_count[i]);
            let ng = u64::from(neg_count[i]);
            let total = p + ng;
            if total == 0 {
                continue;
            }
            active_vars += 1;
            let degree = total as usize;
            degree_sum += total;
            degree_sq_sum += total * total;
            if degree > var_degree_max {
                var_degree_max = degree;
            }

            let balance = p as f64 / total as f64;
            balance_sum += balance;
            balance_sq_sum += balance * balance;

            if p == 0 || ng == 0 {
                num_pure_literals += 1;
            }
        }

        let active = active_vars.max(1) as f64;
        let var_degree_mean = degree_sum as f64 / active;
        let var_degree_variance =
            var_degree_mean.mul_add(-var_degree_mean, degree_sq_sum as f64 / active);
        let var_degree_std = if var_degree_variance > 0.0 {
            var_degree_variance.sqrt()
        } else {
            0.0
        };

        let pos_neg_balance_mean = balance_sum / active;
        let balance_variance =
            pos_neg_balance_mean.mul_add(-pos_neg_balance_mean, balance_sq_sum / active);
        let pos_neg_balance_std = if balance_variance > 0.0 {
            balance_variance.sqrt()
        } else {
            0.0
        };

        Self {
            num_vars,
            num_clauses,
            clause_var_ratio: num_clauses as f64 / num_vars.max(1) as f64,
            num_unit,
            num_binary,
            num_ternary,
            num_horn,
            frac_binary: num_binary as f64 / n,
            frac_ternary: num_ternary as f64 / n,
            frac_horn: num_horn as f64 / n,
            clause_size_mean,
            clause_size_std,
            clause_size_min,
            clause_size_max,
            pos_neg_balance_mean,
            pos_neg_balance_std,
            var_degree_mean,
            var_degree_std,
            var_degree_max,
            num_pure_literals,
            frac_pure: num_pure_literals as f64 / active,
        }
    }

    /// Features for an empty or trivial formula.
    fn empty(num_vars: usize, num_clauses: usize) -> Self {
        Self {
            num_vars,
            num_clauses,
            clause_var_ratio: if num_vars > 0 {
                num_clauses as f64 / num_vars as f64
            } else {
                0.0
            },
            num_unit: 0,
            num_binary: 0,
            num_ternary: 0,
            num_horn: 0,
            frac_binary: 0.0,
            frac_ternary: 0.0,
            frac_horn: 0.0,
            clause_size_mean: 0.0,
            clause_size_std: 0.0,
            clause_size_min: 0,
            clause_size_max: 0,
            pos_neg_balance_mean: 0.5,
            pos_neg_balance_std: 0.0,
            var_degree_mean: 0.0,
            var_degree_std: 0.0,
            var_degree_max: 0,
            num_pure_literals: 0,
            frac_pure: 0.0,
        }
    }
}

/// Instance class derived from static features.
///
/// Used by the portfolio strategy selector to route instances to the best
/// portfolio configuration. Classes are based on structural properties that
/// empirically correlate with solver strategy performance:
///
/// - **Random3Sat**: High clause/variable ratio, mostly ternary clauses.
///   These benefit from aggressive inprocessing and strong BVE.
/// - **RandomKSat**: Uniform k-SAT with k != 3 (e.g., 5-SAT, 7-SAT).
///   Same strategy as Random3Sat: no exploitable structure.
/// - **Structured**: High fraction of binary/horn clauses, moderate density.
///   Gate extraction, congruence closure, and BVE are critical.
/// - **Industrial**: Very large formulas with heterogeneous structure.
///   Conservative search with targeted inprocessing works best.
/// - **Small**: Few variables. Any strategy works; use the default.
/// - **Unknown**: Formulas that don't match any recognized pattern.
///   Uses default strategy (no special rules).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InstanceClass {
    /// Random 3-SAT near the phase transition.
    Random3Sat,
    /// Random k-SAT (k != 3) with uniform clause widths.
    RandomKSat,
    /// Structured/combinatorial instance (circuit, crypto, scheduling).
    Structured,
    /// Large industrial/application instance with heterogeneous structure.
    Industrial,
    /// Small instance (<1000 variables) where strategy matters little.
    Small,
    /// Unclassified formula that doesn't match any recognized pattern.
    Unknown,
}

impl InstanceClass {
    /// Classify an instance from its features.
    ///
    /// The thresholds are based on SATzilla feature analysis and CaDiCaL's
    /// internal heuristics. They are intentionally conservative: better to
    /// default to a robust strategy than to over-classify.
    pub fn classify(features: &SatFeatures) -> Self {
        // Small instances: strategy selection overhead exceeds benefit.
        if features.num_vars < 1000 {
            return Self::Small;
        }

        // Random 3-SAT: high clause/var ratio, mostly ternary, low horn fraction.
        // The phase transition for random 3-SAT is at ratio ~4.26.
        if features.frac_ternary > 0.8
            && features.clause_var_ratio > 3.5
            && features.frac_horn < 0.5
        {
            return Self::Random3Sat;
        }

        // Random k-SAT (k != 3): uniform clause widths (all same length),
        // non-binary, non-ternary, balanced polarity, high clause/var ratio.
        // These formulas are generated uniformly at random and have no
        // exploitable structure (same as Random3Sat).
        if features.clause_size_std < 0.1
            && features.clause_size_min == features.clause_size_max
            && features.clause_size_min > 3
            && features.clause_var_ratio > 2.0
            && (features.pos_neg_balance_mean - 0.5).abs() < 0.15
        {
            return Self::RandomKSat;
        }

        // Structured: high binary fraction, or high horn fraction, or
        // high clause size variance (mixed clause sizes typical of circuits).
        if features.frac_binary > 0.5
            || features.frac_horn > 0.7
            || (features.clause_size_std > 2.0 && features.clause_size_max > 10)
        {
            return Self::Structured;
        }

        // Industrial: very large formulas with heterogeneous structure.
        // Pure size alone is insufficient — large combinatorial puzzles have
        // uniform structure. Require structural heterogeneity: high variable-
        // degree variance OR high clause-width variance.
        if features.num_vars > 50_000 || features.num_clauses > 200_000 {
            let coeff_of_var_degree = if features.var_degree_mean > 0.0 {
                features.var_degree_std / features.var_degree_mean
            } else {
                0.0
            };
            let has_structural_heterogeneity =
                coeff_of_var_degree > 0.5 || features.clause_size_std > 1.0;
            if has_structural_heterogeneity {
                return Self::Industrial;
            }
            // Large but uniform → Unknown (not Industrial, not Structured).
            return Self::Unknown;
        }

        // Medium formulas that don't match any specific pattern.
        Self::Unknown
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::literal::{Literal, Variable};

    /// Helper: create a positive literal for variable index `v`.
    fn pos(v: u32) -> Literal {
        Literal::positive(Variable(v))
    }

    /// Helper: create a negative literal for variable index `v`.
    fn neg(v: u32) -> Literal {
        Literal::negative(Variable(v))
    }

    #[test]
    fn test_features_empty_formula() {
        let features = SatFeatures::extract(10, &[]);
        assert_eq!(features.num_vars, 10);
        assert_eq!(features.num_clauses, 0);
        assert_eq!(features.clause_size_mean, 0.0);
        assert_eq!(features.num_binary, 0);
    }

    #[test]
    fn test_features_single_unit_clause() {
        let clauses = vec![vec![pos(0)]];
        let features = SatFeatures::extract(1, &clauses);
        assert_eq!(features.num_unit, 1);
        assert_eq!(features.num_binary, 0);
        assert_eq!(features.clause_size_mean, 1.0);
        assert_eq!(features.clause_size_min, 1);
        assert_eq!(features.clause_size_max, 1);
        assert_eq!(features.clause_size_std, 0.0);
    }

    #[test]
    fn test_features_all_binary() {
        // 3 binary clauses over 3 variables.
        let clauses = vec![
            vec![pos(0), neg(1)],
            vec![pos(1), neg(2)],
            vec![neg(0), pos(2)],
        ];
        let features = SatFeatures::extract(3, &clauses);
        assert_eq!(features.num_binary, 3);
        assert_eq!(features.frac_binary, 1.0);
        assert_eq!(features.clause_size_mean, 2.0);
        assert_eq!(features.clause_size_std, 0.0);
    }

    #[test]
    fn test_features_horn_detection() {
        // Horn clause: at most 1 positive literal.
        let clauses = vec![
            vec![pos(0), neg(1), neg(2)], // 1 positive -> horn
            vec![neg(0), neg(1)],         // 0 positive -> horn
            vec![pos(0), pos(1), neg(2)], // 2 positive -> not horn
        ];
        let features = SatFeatures::extract(3, &clauses);
        assert_eq!(features.num_horn, 2);
    }

    #[test]
    fn test_features_pure_literal_detection() {
        // Variable 0: only positive. Variable 1: only negative. Variable 2: both.
        let clauses = vec![
            vec![pos(0), neg(1)],
            vec![pos(0), pos(2)],
            vec![neg(1), neg(2)],
        ];
        let features = SatFeatures::extract(3, &clauses);
        assert_eq!(features.num_pure_literals, 2); // var 0 and var 1 are pure
    }

    #[test]
    fn test_features_polarity_balance() {
        // Variable 0: 2 positive, 0 negative -> balance = 1.0
        // Variable 1: 0 positive, 2 negative -> balance = 0.0
        let clauses = vec![vec![pos(0), neg(1)], vec![pos(0), neg(1)]];
        let features = SatFeatures::extract(2, &clauses);
        // Mean of 1.0 and 0.0 = 0.5
        assert!((features.pos_neg_balance_mean - 0.5).abs() < 1e-10);
        // Std of [1.0, 0.0] = 0.5
        assert!((features.pos_neg_balance_std - 0.5).abs() < 1e-10);
    }

    #[test]
    fn test_features_clause_var_ratio() {
        // 4 clauses, 2 vars -> ratio 2.0
        let clauses = vec![vec![pos(0)], vec![neg(0)], vec![pos(1)], vec![neg(1)]];
        let features = SatFeatures::extract(2, &clauses);
        assert!((features.clause_var_ratio - 2.0).abs() < 1e-10);
    }

    #[test]
    fn test_classify_small() {
        let features = SatFeatures::extract(100, &vec![vec![pos(0), neg(1)]; 200]);
        assert_eq!(InstanceClass::classify(&features), InstanceClass::Small);
    }

    #[test]
    fn test_classify_random3sat() {
        // Build a large random-3-SAT-like instance: all ternary, high ratio.
        let num_vars = 2000;
        let num_clauses = 8000; // ratio ~4.0
        let clauses: Vec<Vec<Literal>> = (0..num_clauses)
            .map(|i| {
                let v0 = (i * 3) as u32 % num_vars as u32;
                let v1 = (i * 3 + 1) as u32 % num_vars as u32;
                let v2 = (i * 3 + 2) as u32 % num_vars as u32;
                vec![pos(v0), neg(v1), pos(v2)]
            })
            .collect();
        let features = SatFeatures::extract(num_vars, &clauses);
        assert!(features.frac_ternary > 0.8);
        assert!(features.clause_var_ratio > 3.5);
        assert_eq!(
            InstanceClass::classify(&features),
            InstanceClass::Random3Sat
        );
    }

    #[test]
    fn test_classify_structured_binary_heavy() {
        // Mostly binary clauses -> structured.
        let num_vars = 2000;
        let clauses: Vec<Vec<Literal>> = (0..4000)
            .map(|i| {
                let v0 = (i * 2) as u32 % num_vars as u32;
                let v1 = (i * 2 + 1) as u32 % num_vars as u32;
                vec![pos(v0), neg(v1)]
            })
            .collect();
        let features = SatFeatures::extract(num_vars, &clauses);
        assert!(features.frac_binary > 0.5);
        assert_eq!(
            InstanceClass::classify(&features),
            InstanceClass::Structured
        );
    }

    #[test]
    fn test_classify_industrial_large() {
        // Very large formula with heterogeneous clause sizes (mixed 2-8 literals).
        // Industrial formulas have high variable-degree variance or clause-width variance.
        let num_vars = 100_000;
        let clauses: Vec<Vec<Literal>> = (0..300_000)
            .map(|i| {
                let base_v = (i * 5) as u32 % num_vars as u32;
                // Vary clause length: 2, 3, 4, 5, 6, 7, 8 based on index
                let len = 2 + (i % 7);
                (0..len)
                    .map(|j| {
                        let v = (base_v + j as u32) % num_vars as u32;
                        if j % 2 == 0 { pos(v) } else { neg(v) }
                    })
                    .collect()
            })
            .collect();
        let features = SatFeatures::extract(num_vars, &clauses);
        assert!(features.clause_size_std > 1.0, "need clause size heterogeneity");
        assert_eq!(
            InstanceClass::classify(&features),
            InstanceClass::Industrial
        );
    }

    #[test]
    fn test_classify_random_ksat() {
        // Uniform 5-SAT: all clauses have exactly 5 literals, balanced polarity.
        let num_vars = 2000;
        let num_clauses = 6000; // ratio 3.0
        let clauses: Vec<Vec<Literal>> = (0..num_clauses)
            .map(|i| {
                (0..5)
                    .map(|j| {
                        let v = ((i * 5 + j) as u32) % num_vars as u32;
                        if (i + j) % 2 == 0 { pos(v) } else { neg(v) }
                    })
                    .collect()
            })
            .collect();
        let features = SatFeatures::extract(num_vars, &clauses);
        assert_eq!(features.clause_size_min, 5);
        assert_eq!(features.clause_size_max, 5);
        assert!(features.clause_size_std < 0.1);
        assert_eq!(
            InstanceClass::classify(&features),
            InstanceClass::RandomKSat
        );
    }

    #[test]
    fn test_classify_large_uniform_is_unknown() {
        // Large uniform ternary formula (no structural heterogeneity) -> Unknown.
        let num_vars = 100_000;
        let clauses: Vec<Vec<Literal>> = (0..300_000)
            .map(|i| {
                let v0 = (i * 3) as u32 % num_vars as u32;
                let v1 = (i * 3 + 1) as u32 % num_vars as u32;
                let v2 = (i * 3 + 2) as u32 % num_vars as u32;
                vec![pos(v0), neg(v1), pos(v2)]
            })
            .collect();
        let features = SatFeatures::extract(num_vars, &clauses);
        assert_eq!(
            InstanceClass::classify(&features),
            InstanceClass::Unknown
        );
    }

    #[test]
    fn test_features_var_degree_stats() {
        // Variable 0 appears in 3 clauses, variable 1 in 2, variable 2 in 1.
        let clauses = vec![
            vec![pos(0), neg(1)],
            vec![pos(0), pos(1)],
            vec![neg(0), pos(2)],
        ];
        let features = SatFeatures::extract(3, &clauses);
        // Degrees: var0=3, var1=2, var2=1. Mean = 2.0
        assert!((features.var_degree_mean - 2.0).abs() < 1e-10);
        assert_eq!(features.var_degree_max, 3);
    }

    #[test]
    fn test_features_clause_size_stats_mixed() {
        let clauses = vec![
            vec![pos(0)],                         // size 1
            vec![pos(0), neg(1)],                 // size 2
            vec![pos(0), neg(1), pos(2)],         // size 3
            vec![pos(0), neg(1), pos(2), neg(3)], // size 4
        ];
        let features = SatFeatures::extract(4, &clauses);
        assert_eq!(features.clause_size_min, 1);
        assert_eq!(features.clause_size_max, 4);
        assert!((features.clause_size_mean - 2.5).abs() < 1e-10);
        assert_eq!(features.num_unit, 1);
        assert_eq!(features.num_binary, 1);
        assert_eq!(features.num_ternary, 1);
    }
}
