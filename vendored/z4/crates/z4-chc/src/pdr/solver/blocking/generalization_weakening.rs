// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Phases 1a-2: Weakening, IUC post-shrinking, Farkas combination, drop-literal,
//! strict inequality detection, and generalizer pipeline for blocking formulas.
//!
//! Phase 1a: Init-bound weakening (point equalities to inequalities from init bounds)
//! Phase 1b: Range-based weakening (binary search for best inductive threshold)
//! Phase 1c: IUC post-shrinking (second UNSAT core pass after weakening)
//! Phase 1d: Farkas combination (linear combination of remaining constraints)
//! Phase 2: Drop-literal + strict inequality detection + GeneralizerPipeline

use super::super::*;

impl PdrSolver {
    /// Phases 1a through pipeline: weakening and final generalization.
    ///
    /// Takes ownership of `current_conjuncts` (already processed by early phases)
    /// and always returns a generalized blocking formula.
    pub(super) fn generalize_weakening_and_pipeline(
        &mut self,
        mut current_conjuncts: Vec<ChcExpr>,
        predicate: PredicateId,
        level: usize,
    ) -> ChcExpr {
        // Phase 1a: Try inequality weakening based on init bounds
        // Get init bounds for this predicate
        let init_values = self.get_init_values(predicate);

        // Phase 1a-pre: Try dropping conjuncts that are INSIDE init bounds
        // If x = init_val (value is consistent with init), this conjunct might not
        // be contributing to making the state unreachable. Try dropping it.
        if self.config.use_init_bound_weakening && current_conjuncts.len() > 1 {
            let mut i = 0;
            while i < current_conjuncts.len() {
                if let Some((var, val)) = Self::extract_equality(&current_conjuncts[i]) {
                    if let Some(init_bounds) = init_values.get(&var.name) {
                        // Only try dropping if value is INSIDE init bounds
                        if val >= init_bounds.min && val <= init_bounds.max {
                            // Try dropping this conjunct
                            let mut test_conjuncts = current_conjuncts.clone();
                            test_conjuncts.remove(i);
                            if !test_conjuncts.is_empty() {
                                let generalized = Self::build_conjunction(&test_conjuncts);
                                if self.is_inductive_blocking(&generalized, predicate, level) {
                                    if self.config.verbose {
                                        safe_eprintln!(
                                            "PDR: Dropped conjunct {} = {} (inside init bounds [{}, {}])",
                                            var.name, val, init_bounds.min, init_bounds.max
                                        );
                                    }
                                    current_conjuncts = test_conjuncts;
                                    continue; // Don't increment i, check new conjunct at this index
                                }
                            }
                        }
                    }
                }
                i += 1;
            }
        }

        // Try weakening each equality conjunct to an inequality
        // Only weaken when blocked_val is strictly outside the init bounds, suggesting
        // the value might be unreachable.
        // CRITICAL: Must check monotonicity before weakening!
        // - Weaken to (var < min) only if var is NON-DECREASING (only increases/stays same)
        //   because if var can decrease, values below min might be reachable
        // - Weaken to (var > max) only if var is NON-INCREASING (only decreases/stays same)
        //   because if var can increase, values above max ARE reachable!
        if self.config.use_init_bound_weakening {
            for i in 0..current_conjuncts.len() {
                if let Some((var, val)) = Self::extract_equality(&current_conjuncts[i]) {
                    // Try to find an init-based bound
                    if let Some(init_bounds) = init_values.get(&var.name) {
                        let weakened = if val < init_bounds.min {
                            // Weaken to (var < min) - blocks values below min
                            // Safe only if var is NON-DECREASING (can only increase/stay same)
                            if self.is_var_non_decreasing(predicate, &var, init_bounds.min) {
                                ChcExpr::lt(
                                    ChcExpr::var(var.clone()),
                                    ChcExpr::Int(init_bounds.min),
                                )
                            } else {
                                // var can decrease, so values below min might be reachable
                                continue;
                            }
                        } else if val > init_bounds.max {
                            // Weaken to (var > max) - blocks values above max
                            // Safe only if var is NON-INCREASING (can only decrease/stay same)
                            if self.is_var_non_increasing(predicate, &var, init_bounds.max) {
                                ChcExpr::gt(
                                    ChcExpr::var(var.clone()),
                                    ChcExpr::Int(init_bounds.max),
                                )
                            } else {
                                // var can increase, so values above max ARE reachable!
                                continue;
                            }
                        } else {
                            continue;
                        };

                        // Build formula with weakened conjunct
                        let mut test_conjuncts = current_conjuncts.clone();
                        test_conjuncts[i] = weakened.clone();
                        let generalized = Self::build_conjunction(&test_conjuncts);

                        if self.is_inductive_blocking(&generalized, predicate, level) {
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: Weakened {} = {} to {} (init_bounds=[{}, {}])",
                                    var.name,
                                    val,
                                    weakened,
                                    init_bounds.min,
                                    init_bounds.max
                                );
                            }
                            current_conjuncts[i] = weakened;
                        }
                    }
                }
            }
        }

        // Phase 1b: Try range-based inequality weakening
        // For each equality (x = val), try weakening to (x >= val) or (x <= val)
        // and search for the best inductive threshold using binary search.
        // CRITICAL: Must check monotonicity before weakening!
        // - Weaken to (x >= K) only if var is NON-INCREASING (can only decrease)
        //   because if var can increase, values >= K ARE reachable
        // - Weaken to (x <= K) only if var is NON-DECREASING (can only increase)
        //   because if var can decrease, values <= K ARE reachable
        if self.config.use_range_weakening {
            for i in 0..current_conjuncts.len() {
                if let Some((var, val)) = Self::extract_equality(&current_conjuncts[i]) {
                    // Skip if already weakened above
                    if !matches!(&current_conjuncts[i], ChcExpr::Op(ChcOp::Eq, _)) {
                        continue;
                    }

                    // Try weakening to x >= val (blocks val and everything above)
                    // Only safe if var is NON-INCREASING (can only decrease/stay same)
                    // Skip range-weakening entirely when init_values lacks this variable's
                    // entry — defaulting to 0 can expand or contract the search range
                    // incorrectly (#3020).
                    let Some(init_bounds) = init_values.get(&var.name) else {
                        continue;
                    };
                    let init_max = init_bounds.max;
                    if self.is_var_non_increasing(predicate, &var, init_max) {
                        let ge_formula = ChcExpr::ge(ChcExpr::var(var.clone()), ChcExpr::Int(val));
                        let mut test_conjuncts = current_conjuncts.clone();
                        test_conjuncts[i] = ge_formula.clone();
                        let generalized = Self::build_conjunction(&test_conjuncts);

                        if self.is_inductive_blocking(&generalized, predicate, level) {
                            // x >= val is inductive, now try to find a smaller threshold
                            // Binary search for the smallest K such that x >= K is inductive
                            let best_k = self.binary_search_threshold(
                                &current_conjuncts,
                                i,
                                &var,
                                init_max,
                                val,
                                predicate,
                                level,
                                true, // searching for >= threshold
                            );
                            let best_formula =
                                ChcExpr::ge(ChcExpr::var(var.clone()), ChcExpr::Int(best_k));
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: Range-weakened {} = {} to {} (searched from {} to {})",
                                    var.name,
                                    val,
                                    best_formula,
                                    init_max,
                                    val
                                );
                            }
                            current_conjuncts[i] = best_formula;
                            continue;
                        }
                    }

                    // Try weakening to x <= val (blocks val and everything below)
                    // Only safe if var is NON-DECREASING (can only increase/stay same)
                    let init_min = init_bounds.min;
                    if self.is_var_non_decreasing(predicate, &var, init_min) {
                        let le_formula = ChcExpr::le(ChcExpr::var(var.clone()), ChcExpr::Int(val));
                        let mut test_conjuncts = current_conjuncts.clone();
                        test_conjuncts[i] = le_formula.clone();
                        let generalized = Self::build_conjunction(&test_conjuncts);

                        if self.is_inductive_blocking(&generalized, predicate, level) {
                            // x <= val is inductive, now try to find a larger threshold
                            let best_k = self.binary_search_threshold(
                                &current_conjuncts,
                                i,
                                &var,
                                val,
                                init_min.saturating_add(1000), // search up to init+1000
                                predicate,
                                level,
                                false, // searching for <= threshold
                            );
                            let best_formula =
                                ChcExpr::le(ChcExpr::var(var.clone()), ChcExpr::Int(best_k));
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: Range-weakened {} = {} to {} (searched from {} to {})",
                                    var.name,
                                    val,
                                    best_formula,
                                    val,
                                    init_min + 1000
                                );
                            }
                            current_conjuncts[i] = best_formula;
                        }
                    }
                }
            }
        } // end if use_range_weakening

        // Phase 1c: Inductive UNSAT core (IUC) shrinking.
        //
        // When inductiveness checks are UNSAT, we can often shrink the cube by extracting an
        // UNSAT core over the cube's conjuncts while keeping the clause constraint + frame as
        // background. This is a lightweight port of Spacer's IUC idea and reduces the number
        // of expensive drop-literal iterations.
        if level >= 2 && current_conjuncts.len() >= 2 {
            if let Some(shrunk) =
                self.try_shrink_blocking_conjuncts_with_iuc(&current_conjuncts, predicate, level)
            {
                if shrunk.len() < current_conjuncts.len() {
                    let candidate = Self::build_conjunction(&shrunk);
                    if self.is_inductive_blocking(&candidate, predicate, level) {
                        current_conjuncts = shrunk;
                    }
                }
            }
        }

        // Phase 1d: Farkas combination for linear constraints
        //
        // If the remaining conjuncts are all linear inequalities, try to combine them
        // using Farkas coefficients. This can produce a single, more general inequality
        // that is still inductive.
        if self.config.use_farkas_combination && current_conjuncts.len() >= 2 {
            if let Some(fc) = crate::farkas::farkas_combine(&current_conjuncts) {
                // Farkas combination succeeded - check if the result is inductive
                if self.is_inductive_blocking(&fc.combined, predicate, level) {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Farkas combined {} conjuncts into: {}",
                            current_conjuncts.len(),
                            fc.combined
                        );
                    }
                    return fc.combined;
                }
            }
        }

        // Phase 2: Try dropping conjuncts (standard drop-literal technique)
        if current_conjuncts.len() <= 1 {
            return Self::build_conjunction(&current_conjuncts);
        }

        // IMPORTANT: For predicates without fact clauses at level 0, skip drop-literal.
        // Without facts, is_inductive_blocking returns true for ANY formula, so drop-literal
        // would reduce to a single conjunct (too weak). Instead, keep all conjuncts to
        // block the entire state space with (A=val1, B=val2, ...) rather than just (C=val).
        if level == 0 && !self.predicate_has_facts(predicate) {
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: Skipping drop-literal at level 0 for pred {} (no facts) - keeping {} conjuncts",
                    predicate.index(),
                    current_conjuncts.len()
                );
            }
            return Self::build_conjunction(&current_conjuncts);
        }

        // Phase 2a: Detect strict inequality patterns (var >= K AND var != K)
        //
        // When a blocking formula represents a strict inequality (e.g., outer > 256 encoded as
        // outer >= 256 AND outer != 256), dropping the disequality produces a weaker bound
        // (outer >= 256) which includes the boundary value (256). This boundary may be
        // reachable, making the resulting lemma (outer < 256) too strong and not globally
        // inductive.
        //
        // Solution: Keep both conjuncts to preserve the strict inequality semantics.
        // The resulting lemma (outer <= 256) is weaker but more likely to be inductive.
        if current_conjuncts.len() == 2 {
            let (c0, c1) = (&current_conjuncts[0], &current_conjuncts[1]);

            // Check for pattern: (var >= K) AND (var != K) or (var <= K) AND (var != K)
            let is_strict_inequality_pattern = |comp: &ChcExpr, diseq: &ChcExpr| -> bool {
                // Extract comparison: (>= var K) or (<= var K) or (< var K) or (> var K)
                let (comp_var, comp_val, comp_op) = match comp {
                    ChcExpr::Op(op @ (ChcOp::Ge | ChcOp::Le | ChcOp::Gt | ChcOp::Lt), args)
                        if args.len() == 2 =>
                    {
                        match (args[0].as_ref(), args[1].as_ref()) {
                            (ChcExpr::Var(v), ChcExpr::Int(k)) => (v.clone(), *k, op.clone()),
                            _ => return false,
                        }
                    }
                    _ => return false,
                };

                // Extract disequality: (not (= var K))
                let (diseq_var, diseq_val) = match diseq {
                    ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => match args[0].as_ref() {
                        ChcExpr::Op(ChcOp::Eq, eq_args) if eq_args.len() == 2 => {
                            match (eq_args[0].as_ref(), eq_args[1].as_ref()) {
                                (ChcExpr::Var(v), ChcExpr::Int(k)) => (v.clone(), *k),
                                (ChcExpr::Int(k), ChcExpr::Var(v)) => (v.clone(), *k),
                                _ => return false,
                            }
                        }
                        _ => return false,
                    },
                    _ => return false,
                };

                // Check if same variable and same/adjacent value
                // Pattern: (var >= K AND var != K) represents (var > K)
                // Pattern: (var <= K AND var != K) represents (var < K)
                if comp_var.name == diseq_var.name {
                    match comp_op {
                        ChcOp::Ge | ChcOp::Le => comp_val == diseq_val,
                        ChcOp::Gt | ChcOp::Lt => {
                            // Already strict, but check anyway
                            // Use i128 to avoid overflow on subtraction + abs
                            (i128::from(comp_val) - i128::from(diseq_val)).unsigned_abs() <= 1
                        }
                        _ => false,
                    }
                } else {
                    false
                }
            };

            if is_strict_inequality_pattern(c0, c1) || is_strict_inequality_pattern(c1, c0) {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: Detected strict inequality pattern, keeping both conjuncts to avoid over-strengthening"
                    );
                }
                // Skip drop-literal for this pattern - return the full blocking formula
                return Self::build_conjunction(&current_conjuncts);
            }
        }

        // Phase 2: Apply GeneralizerPipeline (UnsatCore + DropLiteral + Weakening)
        //
        // Use the generalization framework (#775) to shrink the cube using:
        // 1. UnsatCoreGeneralizer - extracts minimal subset via SMT core
        // 2. RelevantVariableProjectionGeneralizer - removes irrelevant variable assignments (#1872)
        // 3. DropLiteralGeneralizer - removes redundant conjuncts
        // 4. LiteralWeakeningGeneralizer - weakens equalities to inequalities (#795)
        //
        // This replaces the manual drop-literal loop with a unified framework
        // that runs to fixpoint and leverages PDR's inductiveness checks via
        // PdrGeneralizerAdapter.
        //
        // Reference: Z3 Spacer's boolean inductive generalization
        // - `reference/z3/src/muz/spacer/spacer_generalizers.cpp:62`
        // - `reference/z3/src/muz/spacer/spacer_ind_lemma_generalizer.cpp:185`
        let current_formula = Self::build_conjunction(&current_conjuncts);
        let strategy = self.generalization_strategy;
        let mut pipeline = GeneralizerPipeline::new();

        // Strategy-adaptive pipeline composition (#7911).
        if !self.config.bv_bit_groups.is_empty() {
            pipeline.add(Box::new(BvBitGroupGeneralizer::new(
                self.config.bv_bit_groups.clone(),
            )));
        }
        if !self.problem_is_pure_lia {
            pipeline.add(Box::new(BvBitDecompositionGeneralizer::new()));
        }
        if strategy.use_early_aggressive_generalizers() {
            pipeline
                .add(Box::new(SingleVariableRangeGeneralizer::new()))
                .add(Box::new(ConstantSumGeneralizer::new()));
        }
        pipeline
            .add(Box::new(TemplateGeneralizer::new()))
            .add(Box::new(InitBoundWeakeningGeneralizer::new()))
            .add(Box::new(UnsatCoreGeneralizer::new()))
            .add(Box::new(RelevantVariableProjectionGeneralizer::new()))
            .add(Box::new(DropLiteralGeneralizer::with_failure_limit(
                strategy.drop_literal_failure_limit(),
            )))
            .add(Box::new(LiteralWeakeningGeneralizer::new()));
        if strategy.use_relational_generalizers() {
            pipeline
                .add(Box::new(FarkasGeneralizer::new()))
                .add(Box::new(DenominatorSimplificationGeneralizer::new()))
                .add(Box::new(RelationalEqualityGeneralizer::new()))
                .add(Box::new(ImplicationGeneralizer::new()));
        }
        if strategy.use_bound_expansion() {
            pipeline.add(Box::new(BoundExpansionGeneralizer::new()));
        }

        let mut adapter = PdrGeneralizerAdapter::new(self, predicate);
        let mut generalized = pipeline.generalize(&current_formula, level as u32, &mut adapter);
        for _ in 1..strategy.fixpoint_passes() {
            let before = generalized.clone();
            generalized = pipeline.generalize(&generalized, level as u32, &mut adapter);
            if generalized == before {
                break;
            }
        }
        if self.config.verbose {
            safe_eprintln!(
                "PDR: GeneralizerPipeline({}): {} -> {}",
                strategy,
                current_formula,
                generalized
            );
        }
        generalized
    }
}
