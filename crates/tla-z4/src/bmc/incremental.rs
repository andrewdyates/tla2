// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Incremental BMC loop for iterative deepening.
//!
//! Reuses the z4 solver across increasing bound depths so that conflict clauses
//! learned at depth k carry forward to depth k+1, making iterative BMC
//! significantly faster than k separate solver invocations.
//!
//! # Architecture
//!
//! The incremental loop wraps a [`BmcTranslator`] (pre-allocated to `max_k`)
//! and manages the depth ladder:
//!
//! ```text
//! Assert Init(s0)                          -- persistent
//! for k in 0..=max_k:
//!     if k > 0: Assert Next(s[k-1], s[k]) -- persistent (transition)
//!     push_scope()
//!         Assert ¬Safety(s[k])             -- scoped (retracted after check)
//!         check_sat()
//!         if SAT: extract counterexample, return
//!     pop_scope()
//! return UNSAT (safe up to max_k)
//! ```
//!
//! Transition constraints are asserted persistently (outside push/pop) so the
//! solver accumulates knowledge about the reachable state space. Only the
//! safety violation query is scoped, since we only want to check `¬Safety` at
//! the *current* frontier step, not at all prior steps.
//!
//! Part of #3724.

use tla_core::ast::Expr;
use tla_core::Spanned;

use super::{BmcState, BmcTranslator};
use crate::error::Z4Result;
use crate::TlaSort;

/// Result of an incremental BMC run.
#[derive(Debug)]
pub enum IncrementalBmcResult {
    /// Counterexample found at depth `k`.
    ///
    /// The trace contains states from step 0 through the violation step.
    Counterexample {
        /// Depth at which the violation was found.
        depth: usize,
        /// Full state trace from Init to the violating state.
        trace: Vec<BmcState>,
    },
    /// No violation found up to `max_k`.
    ///
    /// Safety holds for all reachable states within the bound.
    Safe {
        /// Maximum depth checked.
        max_depth: usize,
    },
    /// Solver returned Unknown at depth `k`.
    Unknown {
        /// Depth at which the solver gave up.
        depth: usize,
    },
}

/// Incremental BMC engine that reuses learned clauses across depths.
///
/// Wraps a [`BmcTranslator`] and drives the depth-iterating BMC loop with
/// push/pop scoping for the safety check at each step.
///
/// # Usage
///
/// ```no_run
/// use tla_z4::bmc::incremental::IncrementalBmc;
/// use tla_z4::{TlaSort, Z4Result};
/// use tla_core::Spanned;
/// use tla_core::ast::Expr;
///
/// fn example() -> Z4Result<()> {
///     let vars = vec![("count".to_string(), TlaSort::Int)];
///     let mut bmc = IncrementalBmc::new(10, &vars)?;
///     // ... set up init/next/safety expressions, then run
///     Ok(())
/// }
/// ```
pub struct IncrementalBmc {
    /// The underlying BMC translator (pre-allocated to max_k).
    translator: BmcTranslator,
    /// Maximum bound to check.
    max_k: usize,
    /// Current depth that has been fully asserted (transitions).
    current_depth: usize,
    /// Whether Init has been asserted.
    init_asserted: bool,
}

impl IncrementalBmc {
    /// Create a new incremental BMC engine.
    ///
    /// Pre-allocates SMT variables for all steps 0..=max_k via the
    /// underlying `BmcTranslator`.
    ///
    /// # Errors
    /// Returns error if `max_k` exceeds the BMC bound limit.
    pub fn new(max_k: usize, vars: &[(String, TlaSort)]) -> Z4Result<Self> {
        let mut translator = BmcTranslator::new(max_k)?;
        for (name, sort) in vars {
            translator.declare_var(name, sort.clone())?;
        }
        Ok(Self {
            translator,
            max_k,
            current_depth: 0,
            init_asserted: false,
        })
    }

    /// Create a new incremental BMC engine with array support.
    ///
    /// Uses QF_AUFLIA logic for specs with Set or Function variables.
    ///
    /// # Errors
    /// Returns error if `max_k` exceeds the BMC bound limit.
    pub fn new_with_arrays(max_k: usize, vars: &[(String, TlaSort)]) -> Z4Result<Self> {
        let mut translator = BmcTranslator::new_with_arrays(max_k)?;
        for (name, sort) in vars {
            translator.declare_var(name, sort.clone())?;
        }
        Ok(Self {
            translator,
            max_k,
            current_depth: 0,
            init_asserted: false,
        })
    }

    /// Run the incremental BMC loop.
    ///
    /// Iterates from depth 0 to `max_k`:
    /// - At depth 0: asserts Init, checks `¬Safety(s0)`
    /// - At depth k > 0: asserts `Next(s[k-1], s[k])`, checks `¬Safety(s[k])`
    ///
    /// Transition constraints are persistent (learned clauses carry forward).
    /// The safety violation query is scoped via push/pop.
    ///
    /// Returns the first counterexample found, or `Safe` if no violation
    /// exists within the bound.
    pub fn run(
        &mut self,
        init: &Spanned<Expr>,
        next: &Spanned<Expr>,
        safety: &Spanned<Expr>,
    ) -> Z4Result<IncrementalBmcResult> {
        // Assert Init(s0) persistently.
        if !self.init_asserted {
            let init_term = self.translator.translate_init(init)?;
            self.translator.assert(init_term);
            self.init_asserted = true;
        }

        for k in 0..=self.max_k {
            // Assert transition for this step (persistent).
            if k > 0 {
                let next_term = self.translator.translate_next(next, k - 1)?;
                self.translator.assert(next_term);
            }

            // Push scope for safety check.
            self.translator.push_scope()?;

            // Assert ¬Safety(s[k]) — only at the current frontier.
            let not_safety = self.translator.translate_not_safety_at_step(safety, k)?;
            self.translator.assert(not_safety);

            // Check satisfiability.
            let result = self.translator.try_check_sat()?;
            match result {
                z4_dpll::api::SolveResult::Sat => {
                    // Found a counterexample at depth k.
                    let model = self.translator.try_get_model()?;
                    let full_trace = self.translator.extract_trace(&model);
                    // Trim trace to only steps 0..=k.
                    let trace: Vec<BmcState> =
                        full_trace.into_iter().filter(|s| s.step <= k).collect();

                    // Pop before returning to leave solver in clean state.
                    self.translator.pop_scope()?;
                    self.current_depth = k;

                    return Ok(IncrementalBmcResult::Counterexample { depth: k, trace });
                }
                z4_dpll::api::SolveResult::Unsat(_) => {
                    // Safety holds at depth k. Pop and continue to k+1.
                    self.translator.pop_scope()?;
                    self.current_depth = k;
                }
                _ => {
                    // Unknown — solver gave up.
                    self.translator.pop_scope()?;
                    self.current_depth = k;
                    return Ok(IncrementalBmcResult::Unknown { depth: k });
                }
            }
        }

        Ok(IncrementalBmcResult::Safe {
            max_depth: self.max_k,
        })
    }

    /// Run the incremental BMC loop checking safety at ALL steps up to each
    /// depth, not just the frontier.
    ///
    /// At each depth k, asserts `¬Safety(s0) \/ ... \/ ¬Safety(s[k])`.
    /// This is more expensive per iteration but catches violations at any
    /// step, not just the newest one. Useful when the Init predicate itself
    /// might violate safety.
    pub fn run_all_steps(
        &mut self,
        init: &Spanned<Expr>,
        next: &Spanned<Expr>,
        safety: &Spanned<Expr>,
    ) -> Z4Result<IncrementalBmcResult> {
        // Assert Init(s0) persistently.
        if !self.init_asserted {
            let init_term = self.translator.translate_init(init)?;
            self.translator.assert(init_term);
            self.init_asserted = true;
        }

        for k in 0..=self.max_k {
            // Assert transition for this step (persistent).
            if k > 0 {
                let next_term = self.translator.translate_next(next, k - 1)?;
                self.translator.assert(next_term);
            }

            // Push scope for safety check.
            self.translator.push_scope()?;

            // Assert ¬Safety at all steps 0..=k.
            let not_safety_all = self.translator.translate_not_safety_all_steps(safety, k)?;
            self.translator.assert(not_safety_all);

            // Check satisfiability.
            let result = self.translator.try_check_sat()?;
            match result {
                z4_dpll::api::SolveResult::Sat => {
                    let model = self.translator.try_get_model()?;
                    let full_trace = self.translator.extract_trace(&model);
                    let trace: Vec<BmcState> =
                        full_trace.into_iter().filter(|s| s.step <= k).collect();

                    self.translator.pop_scope()?;
                    self.current_depth = k;

                    return Ok(IncrementalBmcResult::Counterexample { depth: k, trace });
                }
                z4_dpll::api::SolveResult::Unsat(_) => {
                    self.translator.pop_scope()?;
                    self.current_depth = k;
                }
                _ => {
                    self.translator.pop_scope()?;
                    self.current_depth = k;
                    return Ok(IncrementalBmcResult::Unknown { depth: k });
                }
            }
        }

        Ok(IncrementalBmcResult::Safe {
            max_depth: self.max_k,
        })
    }

    /// Get the current depth that has been checked.
    pub fn current_depth(&self) -> usize {
        self.current_depth
    }

    /// Get a reference to the underlying translator.
    ///
    /// Useful for advanced scenarios like asserting concrete states or
    /// accessing the solver model.
    pub fn translator(&self) -> &BmcTranslator {
        &self.translator
    }

    /// Get a mutable reference to the underlying translator.
    pub fn translator_mut(&mut self) -> &mut BmcTranslator {
        &mut self.translator
    }
}
