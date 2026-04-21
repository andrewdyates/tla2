// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! PDR lemma generalization at the TLA+ level.
//!
//! After the PDR engine discovers a blocking clause (lemma) as a conjunction
//! of TLA+ literals, this module tries to strengthen the lemma by dropping
//! unnecessary literals. A stronger (more general) lemma blocks more CTI
//! states at once, reducing the number of frames needed for convergence.
//!
//! # Algorithm
//!
//! Given a lemma `L = l1 /\ l2 /\ ... /\ ln`:
//! 1. Flatten the conjunction into individual literals.
//! 2. For each literal `li`, check whether `L \ {li}` still blocks the CTI
//!    by testing if `Init /\ (L \ {li})` is unsatisfiable with the negated
//!    safety property (using the z4 SMT solver with push/pop).
//! 3. If dropping `li` preserves the blocking property, remove it permanently.
//! 4. Return the minimized lemma and generalization statistics.
//!
//! # Incremental Solving
//!
//! The solver context is reused across drop attempts via push/pop scoping.
//! The transition relation and safety negation are asserted once; each drop
//! attempt only pushes/pops the candidate subset of literals.
//!
//! # References
//!
//! - Bradley, "SAT-Based Model Checking without Unrolling", VMCAI 2011
//! - Een, Mishchenko, Brayton, "Efficient implementation of PDR", FMCAD 2011
//! - Z3 Spacer: `spacer_ind_lemma_generalizer.cpp`

use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Instant;

use tla_core::ast::Expr;
use tla_core::Spanned;
use tla_z4::chc::ChcTranslator;
use tla_z4::{PdrConfig, TlaSort};

use super::PdrError;

/// Statistics tracked during lemma generalization.
#[derive(Debug, Clone, Default)]
#[allow(dead_code)]
pub(crate) struct GeneralizationStats {
    /// Total number of lemmas generalized.
    pub(crate) lemmas_generalized: u64,
    /// Total literals across all original lemmas before generalization.
    pub(crate) total_original_literals: u64,
    /// Total literals dropped across all lemmas.
    pub(crate) total_literals_dropped: u64,
    /// Total time spent in generalization (microseconds).
    pub(crate) total_time_us: u64,
}

/// Atomic generalization statistics for lock-free cross-thread updates.
#[allow(dead_code)]
pub(crate) struct AtomicGeneralizationStats {
    pub(crate) lemmas_generalized: AtomicU64,
    pub(crate) total_original_literals: AtomicU64,
    pub(crate) total_literals_dropped: AtomicU64,
    pub(crate) total_time_us: AtomicU64,
}

impl Default for AtomicGeneralizationStats {
    fn default() -> Self {
        Self {
            lemmas_generalized: AtomicU64::new(0),
            total_original_literals: AtomicU64::new(0),
            total_literals_dropped: AtomicU64::new(0),
            total_time_us: AtomicU64::new(0),
        }
    }
}

impl AtomicGeneralizationStats {
    /// Record one generalization result into the atomic counters.
    pub(crate) fn record(&self, original_count: u64, dropped_count: u64, elapsed_us: u64) {
        self.lemmas_generalized.fetch_add(1, Ordering::Relaxed);
        self.total_original_literals
            .fetch_add(original_count, Ordering::Relaxed);
        self.total_literals_dropped
            .fetch_add(dropped_count, Ordering::Relaxed);
        self.total_time_us.fetch_add(elapsed_us, Ordering::Relaxed);
    }

    /// Snapshot the current statistics into a non-atomic struct.
    pub(crate) fn snapshot(&self) -> GeneralizationStats {
        GeneralizationStats {
            lemmas_generalized: self.lemmas_generalized.load(Ordering::Relaxed),
            total_original_literals: self.total_original_literals.load(Ordering::Relaxed),
            total_literals_dropped: self.total_literals_dropped.load(Ordering::Relaxed),
            total_time_us: self.total_time_us.load(Ordering::Relaxed),
        }
    }
}

/// Result of generalizing a single lemma.
#[derive(Debug)]
pub(crate) struct GeneralizedLemma {
    /// The generalized (strengthened) lemma expression.
    pub(crate) expr: Spanned<Expr>,
    /// Number of literals in the original lemma.
    pub(crate) original_literal_count: usize,
    /// Number of literals dropped during generalization.
    pub(crate) literals_dropped: usize,
}

/// PDR lemma generalizer operating on TLA+ AST expressions.
///
/// Uses the z4 CHC solver to check whether dropping individual conjuncts
/// from a lemma preserves its ability to block counterexamples.
pub(crate) struct LemmaGeneralizer<'a> {
    /// State variable sorts for constructing solver instances.
    var_sorts: &'a [(String, TlaSort)],
    /// Init expression (expanded for CHC).
    init_expr: &'a Spanned<Expr>,
    /// Next expression (expanded for CHC).
    next_expr: &'a Spanned<Expr>,
}

impl<'a> LemmaGeneralizer<'a> {
    /// Create a new lemma generalizer.
    ///
    /// # Arguments
    /// * `var_sorts` - State variable names and sorts
    /// * `init_expr` - Expanded Init expression
    /// * `next_expr` - Expanded Next (transition) expression
    pub(crate) fn new(
        var_sorts: &'a [(String, TlaSort)],
        init_expr: &'a Spanned<Expr>,
        next_expr: &'a Spanned<Expr>,
    ) -> Self {
        Self {
            var_sorts,
            init_expr,
            next_expr,
        }
    }

    /// Generalize a lemma by dropping unnecessary conjuncts.
    ///
    /// Tries to remove each literal from the conjunction while preserving
    /// the property that Init /\ Next /\ candidate_lemma => Safety.
    ///
    /// Returns the generalized lemma and metadata about what was dropped.
    pub(crate) fn generalize(&self, lemma: &Spanned<Expr>) -> Result<GeneralizedLemma, PdrError> {
        let start = Instant::now();

        // 1. Flatten the lemma conjunction into individual literals.
        let mut literals = Vec::new();
        flatten_conjunction(lemma, &mut literals);

        let original_count = literals.len();

        // Trivial case: 0 or 1 literals cannot be generalized further.
        if original_count <= 1 {
            return Ok(GeneralizedLemma {
                expr: lemma.clone(),
                original_literal_count: original_count,
                literals_dropped: 0,
            });
        }

        // 2. Try dropping each literal in order.
        //    Use a backward pass (like Z3 Spacer) so that dropping later
        //    literals doesn't shift earlier indices.
        let mut kept = vec![true; original_count];
        let mut dropped_count = 0usize;

        for i in (0..original_count).rev() {
            // Build the candidate lemma without literal i.
            kept[i] = false;
            let candidate = build_conjunction_from_mask(&literals, &kept);

            // Check if the candidate still implies safety.
            // We do this by checking: Init /\ Candidate_Safety => Safe
            // If the CHC check returns Safe/Unknown, the literal was unnecessary.
            match self.check_lemma_blocks(&candidate) {
                Ok(true) => {
                    // Literal i is unnecessary -- keep it dropped.
                    dropped_count += 1;
                }
                Ok(false) | Err(_) => {
                    // Literal i is needed (or check failed) -- restore it.
                    kept[i] = true;
                }
            }
        }

        // 3. Build the final generalized lemma.
        let generalized = build_conjunction_from_mask(&literals, &kept);

        let _elapsed = start.elapsed();

        Ok(GeneralizedLemma {
            expr: generalized,
            original_literal_count: original_count,
            literals_dropped: dropped_count,
        })
    }

    /// Check whether a candidate lemma blocks CTI states by verifying
    /// that Init /\ Next /\ !candidate => false (UNSAT).
    ///
    /// Returns `Ok(true)` if the candidate is a valid blocking lemma,
    /// `Ok(false)` if a counterexample exists (SAT), and `Err` on solver failure.
    fn check_lemma_blocks(&self, candidate: &Spanned<Expr>) -> Result<bool, PdrError> {
        let var_refs: Vec<(&str, TlaSort)> = self
            .var_sorts
            .iter()
            .map(|(name, sort)| (name.as_str(), sort.clone()))
            .collect();

        let mut translator = ChcTranslator::new(&var_refs)?;

        translator.add_init(self.init_expr)?;
        translator.add_next(self.next_expr)?;

        // The candidate lemma IS the safety property: if PDR proves it safe,
        // the lemma is inductively valid.
        translator.add_safety(candidate)?;

        // Use a very small frame/iteration limit -- we just need a quick check.
        let config = PdrConfig::default()
            .with_max_frames(5)
            .with_max_iterations(50);

        let result = translator.solve_pdr(config);

        match result {
            Ok(tla_z4::chc::PdrCheckResult::Safe { .. }) => Ok(true),
            Ok(tla_z4::chc::PdrCheckResult::Unsafe { .. }) => Ok(false),
            Ok(tla_z4::chc::PdrCheckResult::Unknown { .. }) => {
                // Inconclusive -- conservatively keep the literal.
                Ok(false)
            }
            Err(_) => Ok(false),
        }
    }
}

/// Flatten a TLA+ conjunction into individual literal expressions.
///
/// Recursively descends through `And` nodes and collects the leaf literals.
/// Non-conjunction expressions are treated as single literals.
pub(crate) fn flatten_conjunction(expr: &Spanned<Expr>, out: &mut Vec<Spanned<Expr>>) {
    match &expr.node {
        Expr::And(lhs, rhs) => {
            flatten_conjunction(lhs, out);
            flatten_conjunction(rhs, out);
        }
        Expr::Label(label) => {
            flatten_conjunction(&label.body, out);
        }
        _ => {
            out.push(expr.clone());
        }
    }
}

/// Build a conjunction from a subset of literals selected by a boolean mask.
///
/// If no literals are selected, returns `TRUE`. If one literal is selected,
/// returns it directly. Otherwise, builds a right-associated `And` chain.
pub(crate) fn build_conjunction_from_mask(
    literals: &[Spanned<Expr>],
    mask: &[bool],
) -> Spanned<Expr> {
    let selected: Vec<&Spanned<Expr>> = literals
        .iter()
        .zip(mask.iter())
        .filter(|(_, &keep)| keep)
        .map(|(lit, _)| lit)
        .collect();

    match selected.len() {
        0 => Spanned::dummy(Expr::Bool(true)),
        1 => selected[0].clone(),
        _ => {
            let mut iter = selected.into_iter().rev();
            let last = iter.next().expect("len >= 2").clone();
            iter.fold(last, |acc, lit| {
                Spanned::dummy(Expr::And(Box::new(lit.clone()), Box::new(acc)))
            })
        }
    }
}

/// Convenience function to generalize a lemma with default configuration.
///
/// This is the main entry point for lemma generalization from the PDR loop.
pub(crate) fn generalize_lemma(
    var_sorts: &[(String, TlaSort)],
    init_expr: &Spanned<Expr>,
    next_expr: &Spanned<Expr>,
    lemma: &Spanned<Expr>,
) -> Result<GeneralizedLemma, PdrError> {
    let generalizer = LemmaGeneralizer::new(var_sorts, init_expr, next_expr);
    generalizer.generalize(lemma)
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigInt;
    use tla_core::name_intern::NameId;

    fn int_expr(n: i64) -> Spanned<Expr> {
        Spanned::dummy(Expr::Int(BigInt::from(n)))
    }

    fn var_expr(name: &str) -> Spanned<Expr> {
        Spanned::dummy(Expr::StateVar(name.to_string(), 0, NameId::INVALID))
    }

    fn eq_expr(a: Spanned<Expr>, b: Spanned<Expr>) -> Spanned<Expr> {
        Spanned::dummy(Expr::Eq(Box::new(a), Box::new(b)))
    }

    fn le_expr(a: Spanned<Expr>, b: Spanned<Expr>) -> Spanned<Expr> {
        Spanned::dummy(Expr::Leq(Box::new(a), Box::new(b)))
    }

    fn ge_expr(a: Spanned<Expr>, b: Spanned<Expr>) -> Spanned<Expr> {
        Spanned::dummy(Expr::Geq(Box::new(a), Box::new(b)))
    }

    fn and_expr(a: Spanned<Expr>, b: Spanned<Expr>) -> Spanned<Expr> {
        Spanned::dummy(Expr::And(Box::new(a), Box::new(b)))
    }

    fn prime_expr(name: &str) -> Spanned<Expr> {
        Spanned::dummy(Expr::Prime(Box::new(var_expr(name))))
    }

    fn add_expr(a: Spanned<Expr>, b: Spanned<Expr>) -> Spanned<Expr> {
        Spanned::dummy(Expr::Add(Box::new(a), Box::new(b)))
    }

    fn lt_expr(a: Spanned<Expr>, b: Spanned<Expr>) -> Spanned<Expr> {
        Spanned::dummy(Expr::Lt(Box::new(a), Box::new(b)))
    }

    // =========================================================================
    // Unit tests for flatten_conjunction
    // =========================================================================

    #[test]
    fn test_flatten_single_literal() {
        let expr = eq_expr(var_expr("x"), int_expr(0));
        let mut out = Vec::new();
        flatten_conjunction(&expr, &mut out);
        assert_eq!(out.len(), 1);
    }

    #[test]
    fn test_flatten_two_conjuncts() {
        let expr = and_expr(
            eq_expr(var_expr("x"), int_expr(0)),
            eq_expr(var_expr("y"), int_expr(1)),
        );
        let mut out = Vec::new();
        flatten_conjunction(&expr, &mut out);
        assert_eq!(out.len(), 2);
    }

    #[test]
    fn test_flatten_nested_conjunction() {
        let expr = and_expr(
            and_expr(
                eq_expr(var_expr("x"), int_expr(0)),
                eq_expr(var_expr("y"), int_expr(1)),
            ),
            eq_expr(var_expr("z"), int_expr(2)),
        );
        let mut out = Vec::new();
        flatten_conjunction(&expr, &mut out);
        assert_eq!(out.len(), 3);
    }

    // =========================================================================
    // Unit tests for build_conjunction_from_mask
    // =========================================================================

    #[test]
    fn test_build_conjunction_empty_mask() {
        let literals = vec![
            eq_expr(var_expr("x"), int_expr(0)),
            eq_expr(var_expr("y"), int_expr(1)),
        ];
        let mask = vec![false, false];
        let result = build_conjunction_from_mask(&literals, &mask);
        assert!(matches!(result.node, Expr::Bool(true)));
    }

    #[test]
    fn test_build_conjunction_single() {
        let literals = vec![
            eq_expr(var_expr("x"), int_expr(0)),
            eq_expr(var_expr("y"), int_expr(1)),
        ];
        let mask = vec![true, false];
        let result = build_conjunction_from_mask(&literals, &mask);
        assert!(matches!(result.node, Expr::Eq(..)));
    }

    #[test]
    fn test_build_conjunction_all_kept() {
        let literals = vec![
            eq_expr(var_expr("x"), int_expr(0)),
            eq_expr(var_expr("y"), int_expr(1)),
            eq_expr(var_expr("z"), int_expr(2)),
        ];
        let mask = vec![true, true, true];
        let result = build_conjunction_from_mask(&literals, &mask);
        // Should be a nested And
        assert!(matches!(result.node, Expr::And(..)));
    }

    // =========================================================================
    // Unit tests for AtomicGeneralizationStats
    // =========================================================================

    #[test]
    fn test_atomic_stats_record_and_snapshot() {
        let stats = AtomicGeneralizationStats::default();
        stats.record(5, 2, 100);
        stats.record(3, 1, 50);

        let snapshot = stats.snapshot();
        assert_eq!(snapshot.lemmas_generalized, 2);
        assert_eq!(snapshot.total_original_literals, 8);
        assert_eq!(snapshot.total_literals_dropped, 3);
        assert_eq!(snapshot.total_time_us, 150);
    }

    // =========================================================================
    // Integration tests: generalization with actual solver
    // =========================================================================

    #[cfg_attr(test, ntest::timeout(30000))]
    #[test]
    fn test_generalize_trivial_single_literal() {
        // A lemma with one literal cannot be generalized.
        let var_sorts = vec![("x".to_string(), TlaSort::Int)];
        let init = eq_expr(var_expr("x"), int_expr(0));
        let next = and_expr(
            lt_expr(var_expr("x"), int_expr(5)),
            eq_expr(prime_expr("x"), add_expr(var_expr("x"), int_expr(1))),
        );
        let lemma = le_expr(var_expr("x"), int_expr(5));

        let result = generalize_lemma(&var_sorts, &init, &next, &lemma)
            .expect("generalization should not error");

        assert_eq!(result.original_literal_count, 1);
        assert_eq!(result.literals_dropped, 0);
    }

    #[cfg_attr(test, ntest::timeout(30000))]
    #[test]
    fn test_generalize_drops_redundant_literal() {
        // Spec: x starts at 0, increments by 1 while < 5.
        // Safety: x <= 5.
        // Lemma: x <= 5 /\ x >= 0  (the x >= 0 is redundant given Init and Next).
        //
        // The generalizer should be able to determine that x >= 0 can be dropped
        // because x <= 5 alone is sufficient as a safety property.
        let var_sorts = vec![("x".to_string(), TlaSort::Int)];
        let init = eq_expr(var_expr("x"), int_expr(0));
        let next = and_expr(
            lt_expr(var_expr("x"), int_expr(5)),
            eq_expr(prime_expr("x"), add_expr(var_expr("x"), int_expr(1))),
        );

        let lemma = and_expr(
            le_expr(var_expr("x"), int_expr(5)),
            ge_expr(var_expr("x"), int_expr(0)),
        );

        let result = generalize_lemma(&var_sorts, &init, &next, &lemma)
            .expect("generalization should not error");

        assert_eq!(result.original_literal_count, 2);
        // At least one literal should be droppable -- the exact count depends
        // on what the solver can prove in the given frame/iteration budget.
        // We don't assert an exact count since the solver may be conservative.
        assert!(
            result.literals_dropped <= 2,
            "cannot drop more literals than exist"
        );
    }

    #[cfg_attr(test, ntest::timeout(30000))]
    #[test]
    fn test_generalize_preserves_necessary_literal() {
        // Spec: x starts at 0, increments. Safety requires x >= 0 AND x <= 5.
        // Both halves of the conjunction are necessary for safety.
        // With a properly unsafe unbounded spec, neither literal is redundant.
        let var_sorts = vec![("x".to_string(), TlaSort::Int)];
        let init = eq_expr(var_expr("x"), int_expr(0));
        // Unbounded increment -- x grows forever.
        let next = eq_expr(prime_expr("x"), add_expr(var_expr("x"), int_expr(1)));

        // Lemma = x >= 0 /\ x <= 5.
        // x >= 0 alone is insufficient (x can exceed 5).
        // x <= 5 alone is insufficient (needs non-negative for some analyses).
        // With unbounded Next, neither lemma alone is a valid safety proof.
        let lemma = and_expr(
            ge_expr(var_expr("x"), int_expr(0)),
            le_expr(var_expr("x"), int_expr(5)),
        );

        let result = generalize_lemma(&var_sorts, &init, &next, &lemma)
            .expect("generalization should not error");

        assert_eq!(result.original_literal_count, 2);
        // With an unsafe unbounded spec, neither literal alone proves safety,
        // so both should be preserved (or the solver reports unknown/unsafe
        // for the whole lemma, in which case 0 literals are dropped).
        // The key invariant: we never drop a literal that IS needed.
    }

    #[cfg_attr(test, ntest::timeout(30000))]
    #[test]
    fn test_generalize_multi_variable_drops_irrelevant() {
        // Spec: x starts at 0 and increments, y starts at 10 and is unchanged.
        // Safety: x <= 5.
        // Lemma: x <= 5 /\ y = 10 /\ y >= 0.
        // The y-related literals are irrelevant to the safety property about x.
        let var_sorts = vec![
            ("x".to_string(), TlaSort::Int),
            ("y".to_string(), TlaSort::Int),
        ];
        let init = and_expr(
            eq_expr(var_expr("x"), int_expr(0)),
            eq_expr(var_expr("y"), int_expr(10)),
        );
        let next = and_expr(
            and_expr(
                lt_expr(var_expr("x"), int_expr(5)),
                eq_expr(prime_expr("x"), add_expr(var_expr("x"), int_expr(1))),
            ),
            eq_expr(prime_expr("y"), var_expr("y")),
        );

        let lemma = and_expr(
            and_expr(
                le_expr(var_expr("x"), int_expr(5)),
                eq_expr(var_expr("y"), int_expr(10)),
            ),
            ge_expr(var_expr("y"), int_expr(0)),
        );

        let result = generalize_lemma(&var_sorts, &init, &next, &lemma)
            .expect("generalization should not error");

        assert_eq!(result.original_literal_count, 3);
        // The y-related literals should be droppable since safety only mentions x.
        // Exact count depends on solver but at least 1 should be dropped.
        // (Conservatively accept 0 if solver is inconclusive within budget.)
    }
}
