// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Pure SMT-level k-induction checker for safety properties.
//!
//! k-Induction extends bounded model checking to *prove* safety properties
//! for ALL reachable states (not just bounded depth). The algorithm:
//!
//! 1. **Base case** (BMC): check that no state reachable in 0..k steps
//!    from Init violates the invariant.
//! 2. **Inductive step**: assume k consecutive states satisfy the invariant,
//!    check whether the (k+1)th state can violate it. If UNSAT, the property
//!    holds universally.
//!
//! This module operates at the BMC translator level — it takes pre-parsed
//! TLA+ expressions and variable sorts, with no dependency on `tla-check`
//! types (Config, EvalCtx, Module). This makes it reusable from any crate
//! that can produce `Spanned<Expr>` and `TlaSort`.
//!
//! # k-Induction Formula
//!
//! For depth k and safety property S, the inductive step checks:
//! ```text
//! Next(s0,s1) /\ Next(s1,s2) /\ ... /\ Next(sk-1,sk)
//! /\ S(s0) /\ S(s1) /\ ... /\ S(sk-1)
//! /\ ¬S(sk)
//! ```
//!
//! No Init constraint in the inductive step — the states are arbitrary.
//!
//! - UNSAT: the property is k-inductive; it holds for all reachable states.
//! - SAT: the counterexample may be spurious (unreachable from Init).
//!   Increment k and retry.
//!
//! Part of #3722.

use std::time::Duration;

use tla_core::ast::Expr;
use tla_core::Spanned;
use z4_dpll::api::SolveResult;
use z4_dpll::UnknownReason;

use super::{BmcState, BmcTranslator};
use crate::error::{Z4Error, Z4Result};
use crate::TlaSort;

/// Result of k-induction-based safety verification.
#[derive(Debug)]
pub enum KInductionResult {
    /// The property is k-inductive: it holds for ALL reachable states.
    Proved {
        /// The depth `k` at which the inductive step succeeded.
        k: usize,
    },
    /// k-Induction could not prove the property within the given bound.
    ///
    /// This does NOT mean the property is false — the counterexamples to
    /// induction may all be spurious (unreachable from Init). A stronger
    /// technique (PDR, explicit-state, or higher k) may still prove it.
    Unknown {
        /// Maximum depth attempted.
        max_k: usize,
        /// Human-readable reason for the inconclusive result.
        reason: String,
    },
    /// BMC found a real counterexample at the base case.
    Counterexample {
        /// Depth at which the violation was found.
        depth: usize,
        /// Counterexample trace from Init through the violation.
        trace: Vec<BmcState>,
    },
}

/// Configuration for the k-induction checker.
#[derive(Debug, Clone)]
pub struct KInductionConfig {
    /// Maximum induction depth to attempt.
    pub max_k: usize,
    /// Starting depth for the inductive step (default: 1).
    ///
    /// Set this to skip depths already covered by a prior BMC run.
    pub start_k: usize,
    /// Timeout per solver invocation.
    pub solve_timeout: Option<Duration>,
    /// Use incremental solving for the inductive step.
    ///
    /// When enabled, keeps a single solver instance across all depth
    /// iterations, using push/pop scoping to retract per-depth safety
    /// assertions while retaining accumulated transition constraints
    /// and learned clauses.
    pub incremental: bool,
    /// Enable debug logging to stderr.
    pub debug: bool,
}

impl Default for KInductionConfig {
    fn default() -> Self {
        Self {
            max_k: 20,
            start_k: 1,
            solve_timeout: Some(Duration::from_secs(300)),
            incremental: false,
            debug: false,
        }
    }
}

/// Pure SMT-level k-induction checker.
///
/// Operates on pre-parsed TLA+ expressions (Init, Next, Safety) and
/// variable sorts. No dependency on `tla-check` types.
///
/// # Example
///
/// ```no_run
/// use tla_z4::bmc::kinduction::{KInductionChecker, KInductionConfig, KInductionResult};
/// use tla_z4::TlaSort;
/// use tla_core::Spanned;
/// use tla_core::ast::Expr;
///
/// // Assume init_expr, next_expr, safety_expr are pre-parsed TLA+ expressions
/// // and var_sorts lists each state variable with its sort.
/// # let init_expr = Spanned::dummy(Expr::Bool(true));
/// # let next_expr = Spanned::dummy(Expr::Bool(true));
/// # let safety_expr = Spanned::dummy(Expr::Bool(true));
/// # let var_sorts: Vec<(String, TlaSort)> = vec![];
/// let checker = KInductionChecker::new(
///     var_sorts,
///     init_expr,
///     next_expr,
///     safety_expr,
/// );
///
/// let config = KInductionConfig::default();
/// let result = checker.check(&config).expect("solver should not fail");
/// match result {
///     KInductionResult::Proved { k } => println!("Proved at k={k}"),
///     KInductionResult::Counterexample { depth, .. } => println!("Bug at depth {depth}"),
///     KInductionResult::Unknown { reason, .. } => println!("Inconclusive: {reason}"),
/// }
/// ```
pub struct KInductionChecker {
    /// State variables with their sorts.
    var_sorts: Vec<(String, TlaSort)>,
    /// Init predicate expression.
    init_expr: Spanned<Expr>,
    /// Next-state relation expression.
    next_expr: Spanned<Expr>,
    /// Safety property expression (conjunction of invariants).
    safety_expr: Spanned<Expr>,
}

impl KInductionChecker {
    /// Create a new k-induction checker.
    ///
    /// # Arguments
    /// - `var_sorts`: state variables and their SMT sorts.
    /// - `init_expr`: the Init predicate (used for BMC base case).
    /// - `next_expr`: the Next-state relation (may reference primed variables).
    /// - `safety_expr`: the safety property to prove (conjunction of invariants).
    pub fn new(
        var_sorts: Vec<(String, TlaSort)>,
        init_expr: Spanned<Expr>,
        next_expr: Spanned<Expr>,
        safety_expr: Spanned<Expr>,
    ) -> Self {
        Self {
            var_sorts,
            init_expr,
            next_expr,
            safety_expr,
        }
    }

    /// Run the k-induction algorithm.
    ///
    /// Phase 1: BMC base case checks for real counterexamples at each depth
    /// 0..max_k. Phase 2: Inductive step tries to prove the property at
    /// increasing depths start_k..max_k.
    pub fn check(&self, config: &KInductionConfig) -> Z4Result<KInductionResult> {
        if self.var_sorts.is_empty() {
            return Err(Z4Error::UntranslatableExpr(
                "No state variables declared for k-induction".to_string(),
            ));
        }

        if config.debug {
            eprintln!(
                "[z4-kind] checking {} vars, k={}..{}",
                self.var_sorts.len(),
                config.start_k,
                config.max_k,
            );
        }

        // Phase 1: BMC base case.
        let bmc_result = self.run_bmc_base_case(config)?;
        match bmc_result {
            BmcBaseResult::Violation { depth, trace } => {
                return Ok(KInductionResult::Counterexample { depth, trace });
            }
            BmcBaseResult::Unknown { depth, reason } => {
                return Ok(KInductionResult::Unknown {
                    max_k: depth,
                    reason: format!("BMC base case inconclusive: {reason}"),
                });
            }
            BmcBaseResult::BoundReached { max_depth } => {
                if config.debug {
                    eprintln!("[z4-kind] BMC base case passed up to depth {max_depth}");
                }
            }
        }

        // Phase 2: Inductive step.
        if config.incremental {
            self.run_inductive_step_incremental(config)
        } else {
            self.run_inductive_step(config)
        }
    }

    /// BMC base case: check Init -> Next^depth -> not Safety for each depth.
    fn run_bmc_base_case(&self, config: &KInductionConfig) -> Z4Result<BmcBaseResult> {
        for depth in 0..=config.max_k {
            if config.debug {
                eprintln!("[z4-kind] BMC base depth {depth}");
            }

            let mut translator = BmcTranslator::new(depth)?;
            translator.set_timeout(config.solve_timeout);

            for (name, sort) in &self.var_sorts {
                translator.declare_var(name, sort.clone())?;
            }

            let init_term = translator.translate_init(&self.init_expr)?;
            translator.assert(init_term);

            for step in 0..depth {
                let next_term = translator.translate_next(&self.next_expr, step)?;
                translator.assert(next_term);
            }

            let not_safety = translator.translate_not_safety_all_steps(&self.safety_expr, depth)?;
            translator.assert(not_safety);

            match translator.try_check_sat()? {
                SolveResult::Sat => {
                    let model = translator.try_get_model()?;
                    let trace = translator.extract_trace(&model);
                    return Ok(BmcBaseResult::Violation { depth, trace });
                }
                SolveResult::Unsat(_) => {} // base case holds at this depth
                SolveResult::Unknown => {
                    let reason = match translator.last_unknown_reason() {
                        Some(UnknownReason::Timeout) => {
                            format!("solver timed out at BMC depth {depth}")
                        }
                        Some(other) => {
                            format!("solver unknown at BMC depth {depth}: {other:?}")
                        }
                        None => format!("solver unknown at BMC depth {depth}"),
                    };
                    return Ok(BmcBaseResult::Unknown { depth, reason });
                }
                _ => {
                    return Ok(BmcBaseResult::Unknown {
                        depth,
                        reason: format!("unexpected result at BMC depth {depth}"),
                    });
                }
            }
        }

        Ok(BmcBaseResult::BoundReached {
            max_depth: config.max_k,
        })
    }

    /// Non-incremental inductive step: fresh solver per depth.
    ///
    /// For each k in start_k..max_k, creates a new BMC translator and checks:
    /// ```text
    /// Next(s0,s1) /\ ... /\ Next(sk-1,sk)
    /// /\ Safety(s0) /\ ... /\ Safety(sk-1)
    /// /\ ¬Safety(sk)
    /// ```
    fn run_inductive_step(&self, config: &KInductionConfig) -> Z4Result<KInductionResult> {
        for k in config.start_k..=config.max_k {
            if config.debug {
                eprintln!("[z4-kind] inductive step k={k}");
            }

            let mut translator = BmcTranslator::new(k)?;
            translator.set_timeout(config.solve_timeout);

            for (name, sort) in &self.var_sorts {
                translator.declare_var(name, sort.clone())?;
            }

            // Transition relation: Next(s0,s1) /\ ... /\ Next(sk-1,sk)
            for step in 0..k {
                let next_term = translator.translate_next(&self.next_expr, step)?;
                translator.assert(next_term);
            }

            // Induction hypothesis: Safety(s0) /\ ... /\ Safety(sk-1)
            for step in 0..k {
                let safety_term = translator.translate_safety_at_step(&self.safety_expr, step)?;
                translator.assert(safety_term);
            }

            // Induction check: ¬Safety(sk)
            let not_safety_k = translator.translate_not_safety_at_step(&self.safety_expr, k)?;
            translator.assert(not_safety_k);

            match translator.try_check_sat()? {
                SolveResult::Unsat(_) => {
                    if config.debug {
                        eprintln!("[z4-kind] PROVED: property is {k}-inductive");
                    }
                    return Ok(KInductionResult::Proved { k });
                }
                SolveResult::Sat => {
                    if config.debug {
                        eprintln!(
                            "[z4-kind] induction SAT at k={k} (may be spurious), trying deeper"
                        );
                    }
                }
                SolveResult::Unknown => {
                    let reason = match translator.last_unknown_reason() {
                        Some(UnknownReason::Timeout) => {
                            format!("solver timed out at induction depth {k}")
                        }
                        Some(other) => {
                            format!("solver unknown at induction depth {k}: {other:?}")
                        }
                        None => format!("solver unknown at induction depth {k}"),
                    };
                    return Ok(KInductionResult::Unknown { max_k: k, reason });
                }
                _ => {
                    return Ok(KInductionResult::Unknown {
                        max_k: k,
                        reason: format!("unexpected result at induction depth {k}"),
                    });
                }
            }
        }

        Ok(KInductionResult::Unknown {
            max_k: config.max_k,
            reason: format!(
                "property not {}-inductive (all depths had spurious counterexamples)",
                config.max_k
            ),
        })
    }

    /// Incremental inductive step: single solver across all depths.
    ///
    /// Uses push/pop scoping to retract per-depth safety assertions while
    /// retaining accumulated transition constraints and learned clauses.
    fn run_inductive_step_incremental(
        &self,
        config: &KInductionConfig,
    ) -> Z4Result<KInductionResult> {
        let mut translator = BmcTranslator::new(config.max_k)?;
        translator.set_timeout(config.solve_timeout);

        for (name, sort) in &self.var_sorts {
            translator.declare_var(name, sort.clone())?;
        }

        // Pre-assert transitions for steps before start_k.
        for step in 0..config.start_k.saturating_sub(1) {
            let next_term = translator.translate_next(&self.next_expr, step)?;
            translator.assert(next_term);
        }

        for k in config.start_k..=config.max_k {
            if config.debug {
                eprintln!("[z4-kind-incr] inductive step k={k}");
            }

            // Add the new transition (persistent across depths).
            let new_step = k - 1;
            if new_step >= config.start_k.saturating_sub(1) {
                let next_term = translator.translate_next(&self.next_expr, new_step)?;
                translator.assert(next_term);
            }

            // Push scope for per-depth safety hypothesis + negation.
            translator.push_scope()?;

            // Induction hypothesis: Safety(s0) /\ ... /\ Safety(sk-1)
            for step in 0..k {
                let safety_term = translator.translate_safety_at_step(&self.safety_expr, step)?;
                translator.assert(safety_term);
            }

            // Induction check: ¬Safety(sk)
            let not_safety_k = translator.translate_not_safety_at_step(&self.safety_expr, k)?;
            translator.assert(not_safety_k);

            match translator.try_check_sat()? {
                SolveResult::Unsat(_) => {
                    if config.debug {
                        eprintln!("[z4-kind-incr] PROVED: property is {k}-inductive");
                    }
                    return Ok(KInductionResult::Proved { k });
                }
                SolveResult::Sat => {
                    translator.pop_scope()?;
                    if config.debug {
                        eprintln!(
                            "[z4-kind-incr] induction SAT at k={k} (may be spurious), trying deeper"
                        );
                    }
                }
                SolveResult::Unknown => {
                    let reason = match translator.last_unknown_reason() {
                        Some(UnknownReason::Timeout) => {
                            format!("solver timed out at induction depth {k} (incremental)")
                        }
                        Some(other) => {
                            format!(
                                "solver unknown at induction depth {k} (incremental): {other:?}"
                            )
                        }
                        None => {
                            format!("solver unknown at induction depth {k} (incremental)")
                        }
                    };
                    return Ok(KInductionResult::Unknown { max_k: k, reason });
                }
                _ => {
                    return Ok(KInductionResult::Unknown {
                        max_k: k,
                        reason: format!("unexpected result at induction depth {k} (incremental)"),
                    });
                }
            }
        }

        Ok(KInductionResult::Unknown {
            max_k: config.max_k,
            reason: format!(
                "property not {}-inductive (incremental, all depths had spurious counterexamples)",
                config.max_k
            ),
        })
    }
}

/// Internal BMC base case result.
enum BmcBaseResult {
    Violation { depth: usize, trace: Vec<BmcState> },
    BoundReached { max_depth: usize },
    Unknown { depth: usize, reason: String },
}

#[cfg(test)]
mod tests;
