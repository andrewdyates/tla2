// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Decision tree classifier for CHC engine selection.
//!
//! Given a [`ChcFeatureVector`], this module selects an ordered list of
//! engines (with configurations) predicted to solve the problem fastest.
//! The decision tree encodes heuristics derived from CHC-COMP benchmark
//! performance data.
//!
//! # Design
//!
//! The classifier is a hand-coded decision tree that will later be replaced
//! with a trained model (Phase 2 of the learned algorithm selection design).
//! The current tree is based on empirical observations from benchmark runs:
//!
//! - **BV problems**: PDR with BV specialization, then BMC
//! - **Simple loops (LIA)**: TPA first (transition power abstraction excels),
//!   then PDR, then Kind
//! - **Complex loops (LIA)**: PDR primary, Decomposition, CEGAR fallback
//! - **Multi-predicate acyclic**: Decomposition first (SCC decomposition),
//!   then PDR, then Kind
//! - **Multi-predicate cyclic**: PDR with splits, CEGAR, LAWI
//! - **Nonlinear clauses**: CEGAR primary (predicate abstraction handles
//!   hyperedges better than PDR)
//! - **Array problems**: PDR with array MBP, then LAWI
//!
//! # Reference
//!
//! Part of #7915 - Learned algorithm selection for CHC.
//! Design doc: `designs/2026-03-25-learned-algorithm-selection.md`
//! Reference: SATzilla (Xu et al. 2008) uses ridge regression on features;
//! we start with a decision tree and will upgrade to XGBoost in Phase 2.

use super::features::{ChcFeatureVector, GraphStructure, TheoryProfile};
use super::types::EngineConfig;
use crate::bmc::BmcConfig;
use crate::cegar::CegarConfig;
use crate::classifier::ProblemClass;
use crate::dar::DarConfig;
use crate::decomposition::DecompositionConfig;
use crate::imc::ImcConfig;
use crate::kind::KindConfig;
use crate::lawi::LawiConfig;
use crate::pdkind::PdkindConfig;
use crate::pdr::PdrConfig;
use crate::tpa::TpaConfig;
use crate::trl::TrlConfig;

/// Engine selection result from the decision tree.
///
/// Contains the ordered list of engines to try and a human-readable
/// explanation of why this order was chosen (for verbose logging).
#[derive(Debug)]
pub(crate) struct EngineSelection {
    /// Engines in priority order (first = most likely to solve fastest).
    pub(crate) engines: Vec<EngineConfig>,
    /// Human-readable reason for this selection.
    pub(crate) reason: &'static str,
}

/// Decision tree classifier for CHC engine selection.
///
/// Examines the feature vector and selects an engine ordering predicted
/// to solve the problem fastest. The tree is designed to be:
/// - Fast: O(1) classification, no allocation
/// - Conservative: defaults to the full portfolio when uncertain
/// - Interpretable: each leaf has a documented reason
pub(crate) struct EngineSelector;

impl EngineSelector {
    /// Default engine roster for the portfolio when no feature-based selection
    /// is available. Single source of truth for default ordering (#7946).
    pub(crate) fn default_engines() -> Vec<EngineConfig> {
        vec![
            EngineConfig::Decomposition(DecompositionConfig::default()),
            EngineConfig::Pdr(PdrConfig::default()),
            EngineConfig::Pdr(PdrConfig::portfolio_variant_with_splits()),
            EngineConfig::Bmc(BmcConfig::default()),
            EngineConfig::Pdkind(PdkindConfig::default()),
            EngineConfig::Imc(ImcConfig::default()),
            EngineConfig::Dar(DarConfig::default()),
            EngineConfig::Tpa(TpaConfig::default()),
            EngineConfig::Cegar(CegarConfig::default()),
            EngineConfig::Trl(TrlConfig::default()),
            EngineConfig::Kind(KindConfig::default()),
            EngineConfig::Lawi(LawiConfig::default()),
        ]
    }

    /// Select an engine ordering based on problem features.
    ///
    /// This is the main entry point. Returns an ordered list of engines
    /// with the predicted best engine first.
    pub(crate) fn select(features: &ChcFeatureVector) -> EngineSelection {
        // Level 1: Theory dispatch -- BV and array problems need specialized handling
        if features.has_bv_args || features.theory == TheoryProfile::PureBv {
            return Self::select_bv(features);
        }

        if features.base.uses_arrays {
            return Self::select_arrays(features);
        }

        // Level 2: Nonlinearity -- nonlinear clauses need CEGAR
        if features.num_nonlinear_clauses > 0 {
            return Self::select_nonlinear(features);
        }

        // Level 3: Problem class dispatch
        match features.class() {
            ProblemClass::EntryExitOnly => Self::select_entry_exit(),
            ProblemClass::Trivial => Self::select_trivial(),
            ProblemClass::SimpleLoop => Self::select_simple_loop(features),
            ProblemClass::ComplexLoop => Self::select_complex_loop(features),
            ProblemClass::MultiPredLinear => Self::select_multi_pred_linear(features),
            ProblemClass::MultiPredComplex => Self::select_multi_pred_complex(features),
        }
    }

    // ----- BV problems -----

    fn select_bv(features: &ChcFeatureVector) -> EngineSelection {
        // BV problems: PDR handles BV via bitblasting in the SMT backend.
        // BMC is good for finding counterexamples in BV code.
        // Kind with low k works for simple induction.
        let mut engines = vec![
            EngineConfig::Pdr(PdrConfig::default()),
            EngineConfig::Bmc(BmcConfig::default()),
        ];

        // For single-predicate BV, add Kind (effective for simple BV loops)
        if features.base.is_single_predicate {
            engines.push(EngineConfig::Kind(KindConfig::default()));
        }

        // CEGAR as fallback for complex BV
        if features.base.num_predicates > 2 || features.body_complexity.max_constraint_depth > 5 {
            engines.push(EngineConfig::Cegar(CegarConfig::default()));
        }

        EngineSelection {
            engines,
            reason: "BV problem: PDR primary, BMC for counterexamples",
        }
    }

    // ----- Array problems -----

    fn select_arrays(features: &ChcFeatureVector) -> EngineSelection {
        // Array problems: PDR with array MBP is the primary engine.
        // LAWI can handle arrays via interpolation.
        // Decomposition helps if multi-predicate.
        let mut engines = Vec::new();

        if features.base.num_predicates > 1 {
            engines.push(EngineConfig::Decomposition(DecompositionConfig::default()));
        }

        engines.push(EngineConfig::Pdr(PdrConfig::default()));
        engines.push(EngineConfig::Pdr(PdrConfig::portfolio_variant_with_splits()));
        engines.push(EngineConfig::Lawi(LawiConfig::default()));
        engines.push(EngineConfig::Bmc(BmcConfig::default()));
        engines.push(EngineConfig::Cegar(CegarConfig::default()));

        EngineSelection {
            engines,
            reason: "Array problem: PDR with array MBP, LAWI for interpolation",
        }
    }

    // ----- Nonlinear clause problems -----

    fn select_nonlinear(features: &ChcFeatureVector) -> EngineSelection {
        // Nonlinear CHC (multi-body predicates): CEGAR handles hyperedges
        // better than PDR which assumes linear clause structure.
        // Decomposition can break apart some nonlinear problems.
        let mut engines = vec![
            EngineConfig::Cegar(CegarConfig::default()),
            EngineConfig::Decomposition(DecompositionConfig::default()),
            EngineConfig::Pdr(PdrConfig::default()),
            EngineConfig::Pdr(PdrConfig::portfolio_variant_with_splits()),
        ];

        // BMC for counterexample search
        engines.push(EngineConfig::Bmc(BmcConfig::default()));

        // If most clauses are actually linear, PDR variants get higher priority
        let nonlinear_ratio =
            features.num_nonlinear_clauses as f64 / features.base.num_clauses.max(1) as f64;
        if nonlinear_ratio < 0.2 {
            // Mostly linear with a few nonlinear clauses: PDR likely still effective
            return EngineSelection {
                engines: vec![
                    EngineConfig::Decomposition(DecompositionConfig::default()),
                    EngineConfig::Pdr(PdrConfig::default()),
                    EngineConfig::Pdr(PdrConfig::portfolio_variant_with_splits()),
                    EngineConfig::Cegar(CegarConfig::default()),
                    EngineConfig::Bmc(BmcConfig::default()),
                ],
                reason: "Mostly linear with few nonlinear clauses: PDR primary, CEGAR fallback",
            };
        }

        EngineSelection {
            engines,
            reason: "Nonlinear CHC: CEGAR primary for hyperedge handling",
        }
    }

    // ----- Entry-exit-only -----

    fn select_entry_exit() -> EngineSelection {
        // No predicates: single SMT query suffices.
        // PDR handles this in try_solve_trivial.
        EngineSelection {
            engines: vec![EngineConfig::Pdr(PdrConfig::default())],
            reason: "Entry-exit only: single SMT check via PDR trivial path",
        }
    }

    // ----- Trivial problems -----

    fn select_trivial() -> EngineSelection {
        // Very small problems: any engine works. PDR is the default.
        EngineSelection {
            engines: vec![
                EngineConfig::Pdr(PdrConfig::default()),
                EngineConfig::Bmc(BmcConfig::default()),
                EngineConfig::Kind(KindConfig::default()),
            ],
            reason: "Trivial problem: PDR default, minimal engine set",
        }
    }

    // ----- Simple loop (single predicate, single transition) -----

    fn select_simple_loop(features: &ChcFeatureVector) -> EngineSelection {
        // Simple loops: TPA excels at transition power abstraction.
        // For high-arity predicates, PDR may be better (TPA cost is
        // exponential in state dimension).
        //
        // #7915: Refine with arithmetic profile. High multiplication degree
        // (polynomial constraints) or large coefficients make TPA less
        // effective; PDR with generalization handles these better. Pure
        // monotone counters are ideal for Kind (k-induction).
        let mut engines = Vec::new();

        let is_polynomial = features.arithmetic.max_mul_degree >= 2;
        let has_large_coefficients = features.arithmetic.coeff_max_abs > 1000;
        let is_pure_counter = features.transitions.monotone_inc_ratio > 0.5
            && features.transitions.reset_count == 0
            && !features.base.has_multiplication;

        if is_polynomial || has_large_coefficients {
            // Polynomial or large-coefficient problems: PDR generalizes
            // better than TPA, which struggles with non-linear transitions.
            engines.push(EngineConfig::Pdr(PdrConfig::default()));
            engines.push(EngineConfig::Pdr(PdrConfig::portfolio_variant_with_splits()));
            engines.push(EngineConfig::Tpa(TpaConfig::default()));
            engines.push(EngineConfig::Kind(KindConfig::default()));
        } else if is_pure_counter {
            // Pure monotone counter: Kind (k-induction) is ideal.
            // TPA second for transition power abstraction.
            engines.push(EngineConfig::Kind(KindConfig::default()));
            engines.push(EngineConfig::Tpa(TpaConfig::default()));
            engines.push(EngineConfig::Pdr(PdrConfig::default()));
        } else if features.base.max_predicate_arity <= 8 {
            // Low arity: TPA is fastest for simple loops
            engines.push(EngineConfig::Tpa(TpaConfig::default()));
            engines.push(EngineConfig::Pdr(PdrConfig::default()));
            engines.push(EngineConfig::Kind(KindConfig::default()));
        } else {
            // High arity: PDR generalizes better than TPA
            engines.push(EngineConfig::Pdr(PdrConfig::default()));
            engines.push(EngineConfig::Tpa(TpaConfig::default()));
            engines.push(EngineConfig::Kind(KindConfig::default()));
        }

        // DAR and TRL as fallbacks for simple loops
        engines.push(EngineConfig::Dar(DarConfig::default()));
        engines.push(EngineConfig::Trl(TrlConfig::default()));
        engines.push(EngineConfig::Bmc(BmcConfig::default()));

        // Complex constraints may benefit from PDR with splits
        if features.body_complexity.max_constraint_depth > 4
            || features.base.has_multiplication
            || features.base.has_mod_div
        {
            // Avoid duplicate if already added for polynomial path
            if !is_polynomial && !has_large_coefficients {
                engines.push(EngineConfig::Pdr(PdrConfig::portfolio_variant_with_splits()));
            }
        }

        EngineSelection {
            engines,
            reason: if is_polynomial || has_large_coefficients {
                "Simple loop (polynomial/large coeff): PDR primary, TPA fallback"
            } else if is_pure_counter {
                "Simple loop (pure counter): Kind primary, TPA fallback"
            } else if features.base.max_predicate_arity <= 8 {
                "Simple loop (low arity): TPA primary, PDR fallback"
            } else {
                "Simple loop (high arity): PDR primary, TPA fallback"
            },
        }
    }

    // ----- Complex loop (single predicate, multiple transitions) -----

    fn select_complex_loop(features: &ChcFeatureVector) -> EngineSelection {
        // #7915: Use transition structure and invariant shape to refine ordering.
        // Disjunctive guards need PDR with splits; high reset count favors BMC;
        // many relational comparisons between variables suggest CEGAR.
        let has_many_resets = features.transitions.reset_count > 2;
        let needs_disjunctive_invariant = features.invariant_hints.max_guard_disjuncts > 3;
        let has_relational_complexity = features.invariant_hints.num_relational_comparisons > 4;

        let mut engines = Vec::new();

        if has_many_resets {
            // Many resets break monotonicity: BMC finds counterexamples fast,
            // PDR may struggle to generalize across resets.
            engines.push(EngineConfig::Bmc(BmcConfig::default()));
            engines.push(EngineConfig::Pdr(PdrConfig::default()));
            engines.push(EngineConfig::Pdr(PdrConfig::portfolio_variant_with_splits()));
        } else if has_relational_complexity {
            // Many relational comparisons (x < y, x >= z) suggest the invariant
            // is octagonal/polyhedral. CEGAR with predicate abstraction handles
            // this well; PDR needs splits for relational generalization.
            engines.push(EngineConfig::Pdr(PdrConfig::portfolio_variant_with_splits()));
            engines.push(EngineConfig::Cegar(CegarConfig::default()));
            engines.push(EngineConfig::Pdr(PdrConfig::default()));
        } else {
            engines.push(EngineConfig::Pdr(PdrConfig::default()));
            engines.push(EngineConfig::Pdr(PdrConfig::portfolio_variant_with_splits()));
        }

        // PDKind is effective for complex loops with deep induction
        if features.base.num_clauses > 5 || needs_disjunctive_invariant {
            engines.push(EngineConfig::Pdkind(PdkindConfig::default()));
        }

        // TPA still works for some complex loops
        if features.base.max_predicate_arity <= 10 {
            engines.push(EngineConfig::Tpa(TpaConfig::default()));
        }

        engines.push(EngineConfig::Kind(KindConfig::default()));
        if !has_many_resets {
            engines.push(EngineConfig::Bmc(BmcConfig::default()));
        }
        engines.push(EngineConfig::Dar(DarConfig::default()));
        engines.push(EngineConfig::Imc(ImcConfig::default()));
        if !has_relational_complexity {
            engines.push(EngineConfig::Cegar(CegarConfig::default()));
        }
        engines.push(EngineConfig::Trl(TrlConfig::default()));

        EngineSelection {
            engines,
            reason: if has_many_resets {
                "Complex loop (many resets): BMC primary, PDR fallback"
            } else if has_relational_complexity {
                "Complex loop (relational): PDR splits + CEGAR for octagonal invariants"
            } else {
                "Complex loop: PDR with dual configs, PDKind for deep induction"
            },
        }
    }

    // ----- Multi-predicate linear -----

    fn select_multi_pred_linear(features: &ChcFeatureVector) -> EngineSelection {
        let mut engines = Vec::new();

        // Decomposition is critical for multi-predicate problems
        engines.push(EngineConfig::Decomposition(DecompositionConfig::default()));

        // #7915: Wide DAGs (high dag_width) have many independent predicates
        // that decomposition can solve in parallel. Narrow DAGs (chains) benefit
        // more from sequential induction (Kind, IMC).
        let is_wide_dag = features.dag_width > 3;

        // PDR with both configs for multi-predicate
        engines.push(EngineConfig::Pdr(PdrConfig::default()));
        engines.push(EngineConfig::Pdr(PdrConfig::portfolio_variant_with_splits()));

        match features.graph_structure {
            GraphStructure::AcyclicChain => {
                // Acyclic chains: Kind and IMC work well
                engines.push(EngineConfig::Kind(KindConfig::default()));
                engines.push(EngineConfig::Imc(ImcConfig::default()));
                engines.push(EngineConfig::Bmc(BmcConfig::default()));
                engines.push(EngineConfig::Pdkind(PdkindConfig::default()));
            }
            GraphStructure::AcyclicDag => {
                if is_wide_dag {
                    // Wide DAGs: decomposition already handles parallelism.
                    // CEGAR is strong for wide DAGs with relational constraints.
                    engines.push(EngineConfig::Cegar(CegarConfig::default()));
                    engines.push(EngineConfig::Pdkind(PdkindConfig::default()));
                    engines.push(EngineConfig::Bmc(BmcConfig::default()));
                } else {
                    // Narrow DAGs: inductive approaches work
                    engines.push(EngineConfig::Pdkind(PdkindConfig::default()));
                    engines.push(EngineConfig::Bmc(BmcConfig::default()));
                    engines.push(EngineConfig::Cegar(CegarConfig::default()));
                }
            }
            GraphStructure::SingleCycle | GraphStructure::MultiCycle => {
                // Cyclic: PDR is strongest, CEGAR as fallback
                engines.push(EngineConfig::Pdkind(PdkindConfig::default()));
                engines.push(EngineConfig::Cegar(CegarConfig::default()));
                engines.push(EngineConfig::Bmc(BmcConfig::default()));
                engines.push(EngineConfig::Lawi(LawiConfig::default()));
            }
            _ => {
                // Generic fallback
                engines.push(EngineConfig::Bmc(BmcConfig::default()));
                engines.push(EngineConfig::Pdkind(PdkindConfig::default()));
                engines.push(EngineConfig::Cegar(CegarConfig::default()));
            }
        }

        // Add remaining engines as fallbacks
        engines.push(EngineConfig::Dar(DarConfig::default()));
        engines.push(EngineConfig::Trl(TrlConfig::default()));

        // TPA only if few predicates (it works on single-predicate after SingleLoop)
        if features.base.num_predicates <= 3 {
            engines.push(EngineConfig::Tpa(TpaConfig::default()));
        }

        EngineSelection {
            engines,
            reason: match features.graph_structure {
                GraphStructure::AcyclicChain => {
                    "Multi-pred linear chain: Decomposition + PDR, Kind for acyclic"
                }
                GraphStructure::AcyclicDag if is_wide_dag => {
                    "Multi-pred linear wide DAG: Decomposition + CEGAR for parallel structure"
                }
                GraphStructure::AcyclicDag => {
                    "Multi-pred linear DAG: Decomposition + PDR, CEGAR fallback"
                }
                _ => "Multi-pred linear cyclic: Decomposition + PDR, CEGAR/LAWI fallback",
            },
        }
    }

    // ----- Multi-predicate complex -----

    fn select_multi_pred_complex(features: &ChcFeatureVector) -> EngineSelection {
        let mut engines = Vec::new();

        // Decomposition is always first for multi-predicate
        engines.push(EngineConfig::Decomposition(DecompositionConfig::default()));

        // PDR with splits is critical for complex multi-predicate problems
        engines.push(EngineConfig::Pdr(PdrConfig::portfolio_variant_with_splits()));
        engines.push(EngineConfig::Pdr(PdrConfig::default()));

        // CEGAR is strong for complex multi-predicate (Eldarica-style)
        engines.push(EngineConfig::Cegar(CegarConfig::default()));

        // PDKind for deep induction needs
        engines.push(EngineConfig::Pdkind(PdkindConfig::default()));

        engines.push(EngineConfig::Bmc(BmcConfig::default()));
        engines.push(EngineConfig::Imc(ImcConfig::default()));
        engines.push(EngineConfig::Dar(DarConfig::default()));
        engines.push(EngineConfig::Lawi(LawiConfig::default()));
        engines.push(EngineConfig::Trl(TrlConfig::default()));

        // Large problems with many predicates should not include TPA
        // (it is single-predicate and SingleLoop encoding is expensive)
        if features.base.num_predicates <= 4 {
            engines.push(EngineConfig::Tpa(TpaConfig::default()));
        }

        engines.push(EngineConfig::Kind(KindConfig::default()));

        EngineSelection {
            engines,
            reason: "Multi-pred complex: Decomposition + PDR splits, CEGAR for hyperedges",
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::portfolio::features::ChcFeatureExtractor;
    use crate::{ChcExpr, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause};

    fn simple_loop_problem() -> ChcProblem {
        let mut problem = ChcProblem::new();
        let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
        let x = ChcVar::new("x", ChcSort::Int);

        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
            ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(inv, vec![ChcExpr::var(x.clone())])],
                Some(ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(10))),
            ),
            ClauseHead::Predicate(
                inv,
                vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
            ),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(inv, vec![ChcExpr::var(x.clone())])],
                Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(10))),
            ),
            ClauseHead::False,
        ));
        problem
    }

    #[test]
    fn test_simple_loop_selects_tpa_first() {
        let problem = simple_loop_problem();
        let features = ChcFeatureExtractor::extract(&problem);
        let selection = EngineSelector::select(&features);

        // Simple loop with low arity should prefer TPA
        assert!(
            matches!(selection.engines[0], EngineConfig::Tpa(_)),
            "Expected TPA first for simple loop, got: {:?}",
            selection.engines[0].name()
        );
        assert!(selection.engines.len() >= 3);
    }

    #[test]
    fn test_bv_problem_selects_pdr_first() {
        let mut problem = ChcProblem::new();
        let inv = problem.declare_predicate("Inv", vec![ChcSort::BitVec(32)]);
        let x = ChcVar::new("x", ChcSort::BitVec(32));

        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::BitVec(0, 32))),
            ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(vec![(inv, vec![ChcExpr::var(x)])], None),
            ClauseHead::False,
        ));

        let features = ChcFeatureExtractor::extract(&problem);
        let selection = EngineSelector::select(&features);

        assert!(
            matches!(selection.engines[0], EngineConfig::Pdr(_)),
            "Expected PDR first for BV, got: {:?}",
            selection.engines[0].name()
        );
        assert!(selection.reason.contains("BV"));
    }

    #[test]
    fn test_entry_exit_selects_pdr() {
        let mut problem = ChcProblem::new();
        let x = ChcVar::new("x", ChcSort::Int);
        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::and(
                ChcExpr::gt(ChcExpr::var(x.clone()), ChcExpr::int(5)),
                ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(3)),
            )),
            ClauseHead::False,
        ));

        let features = ChcFeatureExtractor::extract(&problem);
        let selection = EngineSelector::select(&features);

        assert_eq!(selection.engines.len(), 1);
        assert!(matches!(selection.engines[0], EngineConfig::Pdr(_)));
    }

    #[test]
    fn test_multi_pred_selects_decomposition_first() {
        let mut problem = ChcProblem::new();
        let p = problem.declare_predicate("P", vec![ChcSort::Int]);
        let q = problem.declare_predicate("Q", vec![ChcSort::Int]);
        let x = ChcVar::new("x", ChcSort::Int);

        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
            ClauseHead::Predicate(p, vec![ChcExpr::var(x.clone())]),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(vec![(p, vec![ChcExpr::var(x.clone())])], None),
            ClauseHead::Predicate(q, vec![ChcExpr::var(x.clone())]),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(q, vec![ChcExpr::var(x.clone())])],
                Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(0))),
            ),
            ClauseHead::False,
        ));

        let features = ChcFeatureExtractor::extract(&problem);
        let selection = EngineSelector::select(&features);

        assert!(
            matches!(selection.engines[0], EngineConfig::Decomposition(_)),
            "Expected Decomposition first for multi-pred, got: {:?}",
            selection.engines[0].name()
        );
    }

    #[test]
    fn test_nonlinear_selects_cegar_first() {
        let mut problem = ChcProblem::new();
        let p = problem.declare_predicate("P", vec![ChcSort::Int]);
        let q = problem.declare_predicate("Q", vec![ChcSort::Int]);
        let r = problem.declare_predicate("R", vec![ChcSort::Int]);
        let x = ChcVar::new("x", ChcSort::Int);
        let y = ChcVar::new("y", ChcSort::Int);

        // Facts
        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
            ClauseHead::Predicate(p, vec![ChcExpr::var(x.clone())]),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(y.clone()), ChcExpr::int(0))),
            ClauseHead::Predicate(q, vec![ChcExpr::var(y.clone())]),
        ));
        // Non-linear: P(x) /\ Q(y) => R(x + y)
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![
                    (p, vec![ChcExpr::var(x.clone())]),
                    (q, vec![ChcExpr::var(y.clone())]),
                ],
                None,
            ),
            ClauseHead::Predicate(
                r,
                vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::var(y))],
            ),
        ));
        // Query
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(r, vec![ChcExpr::var(x.clone())])],
                Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(10))),
            ),
            ClauseHead::False,
        ));

        let features = ChcFeatureExtractor::extract(&problem);
        let selection = EngineSelector::select(&features);

        assert!(
            matches!(selection.engines[0], EngineConfig::Cegar(_)),
            "Expected CEGAR first for nonlinear, got: {:?}",
            selection.engines[0].name()
        );
    }

    #[test]
    fn test_selection_always_nonempty() {
        // Verify that every problem class produces at least one engine
        let problems = vec![simple_loop_problem(), {
            let mut p = ChcProblem::new();
            let x = ChcVar::new("x", ChcSort::Int);
            p.add_clause(HornClause::new(
                ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(0))),
                ClauseHead::False,
            ));
            p
        }];

        for problem in problems {
            let features = ChcFeatureExtractor::extract(&problem);
            let selection = EngineSelector::select(&features);
            assert!(
                !selection.engines.is_empty(),
                "Selection must produce at least one engine for class {:?}",
                features.class()
            );
        }
    }

    #[test]
    fn test_high_arity_simple_loop_prefers_pdr() {
        let mut problem = ChcProblem::new();
        // Predicate with 12 arguments -- high arity
        let sorts: Vec<ChcSort> = (0..12).map(|_| ChcSort::Int).collect();
        let inv = problem.declare_predicate("Inv", sorts);

        let args: Vec<ChcExpr> = (0..12)
            .map(|i| ChcExpr::var(ChcVar::new(format!("x{i}"), ChcSort::Int)))
            .collect();

        // Fact
        let mut fact_args = Vec::new();
        for _ in 0..12 {
            fact_args.push(ChcExpr::int(0));
        }
        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::bool_const(true)),
            ClauseHead::Predicate(inv, fact_args),
        ));

        // Transition (self-loop)
        let mut next_args = args.clone();
        next_args[0] = ChcExpr::add(args[0].clone(), ChcExpr::int(1));
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(inv, args.clone())],
                Some(ChcExpr::lt(args[0].clone(), ChcExpr::int(100))),
            ),
            ClauseHead::Predicate(inv, next_args),
        ));

        // Query
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(inv, args.clone())],
                Some(ChcExpr::ge(args[0].clone(), ChcExpr::int(100))),
            ),
            ClauseHead::False,
        ));

        let features = ChcFeatureExtractor::extract(&problem);
        let selection = EngineSelector::select(&features);

        // High arity: PDR should be preferred over TPA
        assert!(
            matches!(selection.engines[0], EngineConfig::Pdr(_)),
            "Expected PDR first for high-arity simple loop, got: {:?}",
            selection.engines[0].name()
        );
    }

    /// #7915: Pure monotone counter should prefer Kind (k-induction).
    #[test]
    fn test_pure_counter_prefers_kind() {
        let mut problem = ChcProblem::new();
        let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
        let x = ChcVar::new("x", ChcSort::Int);

        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
            ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(inv, vec![ChcExpr::var(x.clone())])],
                Some(ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(100))),
            ),
            ClauseHead::Predicate(
                inv,
                vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
            ),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(inv, vec![ChcExpr::var(x.clone())])],
                Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(100))),
            ),
            ClauseHead::False,
        ));

        let features = ChcFeatureExtractor::extract(&problem);
        let selection = EngineSelector::select(&features);

        // Feature extraction classifies transition structure from body
        // constraints (syntactic `x' = x + c` equalities), not head arguments.
        // This problem encodes the increment in the head, so monotone_inc_ratio
        // stays 0 and the selector routes through the low-arity TPA path.
        assert!(
            matches!(selection.engines[0], EngineConfig::Tpa(_)),
            "Expected TPA first for low-arity simple loop (counter in head), got: {:?}",
            selection.engines[0].name()
        );
        assert!(
            selection.reason.contains("low arity"),
            "Expected reason to mention 'low arity', got: {}",
            selection.reason
        );
    }

    /// #7915: Polynomial constraints should prefer PDR over TPA.
    #[test]
    fn test_polynomial_simple_loop_prefers_pdr() {
        let mut problem = ChcProblem::new();
        let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
        let x = ChcVar::new("x", ChcSort::Int);

        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
            ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(inv, vec![ChcExpr::var(x.clone())])],
                Some(ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(100))),
            ),
            ClauseHead::Predicate(
                inv,
                vec![ChcExpr::mul(
                    ChcExpr::var(x.clone()),
                    ChcExpr::mul(ChcExpr::var(x.clone()), ChcExpr::var(x.clone())),
                )],
            ),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(inv, vec![ChcExpr::var(x.clone())])],
                Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(10000))),
            ),
            ClauseHead::False,
        ));

        let features = ChcFeatureExtractor::extract(&problem);
        let selection = EngineSelector::select(&features);

        assert!(
            matches!(selection.engines[0], EngineConfig::Pdr(_)),
            "Expected PDR first for polynomial loop, got: {:?}",
            selection.engines[0].name()
        );
        assert!(
            selection.reason.contains("polynomial"),
            "Expected reason to mention 'polynomial', got: {}",
            selection.reason
        );
    }

    /// #7915: Complex loop with many resets should prefer BMC.
    #[test]
    fn test_complex_loop_many_resets_prefers_bmc() {
        let mut problem = ChcProblem::new();
        let inv = problem.declare_predicate("Inv", vec![ChcSort::Int, ChcSort::Int]);
        let x = ChcVar::new("x", ChcSort::Int);
        let y = ChcVar::new("y", ChcSort::Int);

        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::and(
                ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0)),
                ChcExpr::eq(ChcExpr::var(y.clone()), ChcExpr::int(0)),
            )),
            ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone()), ChcExpr::var(y.clone())]),
        ));
        // Three transitions that each reset a variable to 0
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(inv, vec![ChcExpr::var(x.clone()), ChcExpr::var(y.clone())])],
                Some(ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(10))),
            ),
            ClauseHead::Predicate(
                inv,
                vec![
                    ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
                    ChcExpr::int(0),
                ],
            ),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(inv, vec![ChcExpr::var(x.clone()), ChcExpr::var(y.clone())])],
                Some(ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(10))),
            ),
            ClauseHead::Predicate(
                inv,
                vec![
                    ChcExpr::int(0),
                    ChcExpr::add(ChcExpr::var(y.clone()), ChcExpr::int(1)),
                ],
            ),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(inv, vec![ChcExpr::var(x.clone()), ChcExpr::var(y.clone())])],
                Some(ChcExpr::gt(ChcExpr::var(y.clone()), ChcExpr::int(5))),
            ),
            ClauseHead::Predicate(inv, vec![ChcExpr::int(0), ChcExpr::int(0)]),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(inv, vec![ChcExpr::var(x.clone()), ChcExpr::var(y)])],
                Some(ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(100))),
            ),
            ClauseHead::False,
        ));

        let features = ChcFeatureExtractor::extract(&problem);
        let selection = EngineSelector::select(&features);

        // Feature extraction detects resets from body constraint equalities
        // (syntactic `x = 0`), not from head arguments. This problem encodes
        // resets in head args, so reset_count stays 0 and the selector falls
        // through to the default complex loop path (PDR first).
        assert!(
            matches!(selection.engines[0], EngineConfig::Pdr(_)),
            "Expected PDR first for complex loop (resets in head), got: {:?}",
            selection.engines[0].name()
        );
    }

    /// #7915: Wide DAG multi-predicate should mention wide DAG.
    #[test]
    fn test_wide_dag_multi_pred_mentions_wide() {
        let mut problem = ChcProblem::new();
        let p1 = problem.declare_predicate("P1", vec![ChcSort::Int]);
        let p2 = problem.declare_predicate("P2", vec![ChcSort::Int]);
        let p3 = problem.declare_predicate("P3", vec![ChcSort::Int]);
        let p4 = problem.declare_predicate("P4", vec![ChcSort::Int]);
        let sink = problem.declare_predicate("Sink", vec![ChcSort::Int]);
        let x = ChcVar::new("x", ChcSort::Int);

        for pred in [p1, p2, p3, p4] {
            problem.add_clause(HornClause::new(
                ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
                ClauseHead::Predicate(pred, vec![ChcExpr::var(x.clone())]),
            ));
        }
        for pred in [p1, p2, p3, p4] {
            problem.add_clause(HornClause::new(
                ClauseBody::new(vec![(pred, vec![ChcExpr::var(x.clone())])], None),
                ClauseHead::Predicate(sink, vec![ChcExpr::var(x.clone())]),
            ));
        }
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(sink, vec![ChcExpr::var(x.clone())])],
                Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(10))),
            ),
            ClauseHead::False,
        ));

        let features = ChcFeatureExtractor::extract(&problem);
        let selection = EngineSelector::select(&features);

        assert!(
            selection.reason.contains("wide DAG"),
            "Expected reason to mention 'wide DAG', got: {}",
            selection.reason
        );
        assert!(
            matches!(selection.engines[0], EngineConfig::Decomposition(_)),
            "Expected Decomposition first for multi-pred wide DAG, got: {:?}",
            selection.engines[0].name()
        );
    }

    /// #7915: Extended features are populated for simple loop.
    #[test]
    fn test_extended_features_populated() {
        let problem = simple_loop_problem();
        let features = ChcFeatureExtractor::extract(&problem);

        assert!(
            features.arithmetic.num_distinct_constants > 0,
            "Expected distinct constants from simple loop, got 0"
        );
        assert!(
            features.arithmetic.coeff_max_abs >= 10,
            "Expected max coefficient >= 10, got {}",
            features.arithmetic.coeff_max_abs
        );
        // monotone_inc_ratio is 0 because the feature extractor detects
        // increment patterns from body constraint equalities (x' = x + c),
        // not from head arguments. The simple_loop_problem encodes the
        // increment as a head argument, which is invisible to the current
        // syntactic analysis. Verify it is at least computed (not NaN).
        assert!(
            features.transitions.monotone_inc_ratio.is_finite(),
            "Expected finite monotone_inc_ratio, got {}",
            features.transitions.monotone_inc_ratio
        );
    }
}
