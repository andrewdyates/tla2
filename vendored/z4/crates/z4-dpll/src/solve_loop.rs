// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Core DPLL(T) solve-loop implementations shared across public entrypoints.

#[cfg(not(kani))]
use hashbrown::HashMap;
use std::time::{Duration, Instant};
#[cfg(kani)]
use z4_core::kani_compat::DetHashMap as HashMap;
use z4_core::{TermId, TheorySolver};
use z4_sat::{AssumeResult, Literal, SatResult};

use crate::{
    dpll_support::PhaseTimer, proof_tracker, DpllError, DpllT, FinalCheckResult, TheoryDispatch,
};

impl<T: TheorySolver> DpllT<'_, T> {
    /// Internal solve loop used by `solve`, `solve_with_assumptions`, and
    /// their proof-tracking variants.
    ///
    /// Returns `AssumeResult` to propagate unsat core when using assumptions.
    /// When `tracking` is `Some`, records theory conflict steps into the proof tracker.
    pub(crate) fn solve_loop(
        &mut self,
        assumptions: Option<&[Literal]>,
        mut tracking: Option<(&mut proof_tracker::ProofTracker, &HashMap<TermId, TermId>)>,
    ) -> Result<AssumeResult, DpllError> {
        let mut refinements = 0usize;
        loop {
            self.timings.round_trips += 1;
            let round = self.timings.round_trips;

            let sat_start = Instant::now();
            let result = match assumptions {
                Some(a) => {
                    self.apply_theory_phase_hints();
                    let _t = PhaseTimer::new(&mut self.timings.sat_solve);
                    self.sat.solve_with_assumptions(a).into_inner()
                }
                None if self.sat.scope_depth() == 0 => {
                    let _t = PhaseTimer::new(&mut self.timings.sat_solve);
                    let mut ext = crate::extension::PhaseHintExtension::new(
                        &self.theory,
                        &self.var_to_term,
                        &self.term_to_var,
                        &self.theory_atoms,
                    );
                    match self.sat.solve_with_extension(&mut ext).into_inner() {
                        SatResult::Sat(m) => AssumeResult::Sat(m),
                        SatResult::Unsat => AssumeResult::Unsat(vec![]),
                        SatResult::Unknown => AssumeResult::Unknown,
                        #[allow(unreachable_patterns)]
                        _ => return Err(DpllError::UnexpectedTheoryResult),
                    }
                }
                None => {
                    self.apply_theory_phase_hints();
                    let _t = PhaseTimer::new(&mut self.timings.sat_solve);
                    match self.sat.solve().into_inner() {
                        SatResult::Sat(m) => AssumeResult::Sat(m),
                        SatResult::Unsat => AssumeResult::Unsat(vec![]),
                        SatResult::Unknown => AssumeResult::Unknown,
                        #[allow(unreachable_patterns)]
                        _ => return Err(DpllError::UnexpectedTheoryResult),
                    }
                }
            };
            let sat_duration = sat_start.elapsed();

            match result {
                AssumeResult::Sat(model) => {
                    if self.debug_dpll {
                        safe_eprintln!("[DPLL] SAT returned model with {} vars", model.len());
                    }
                    let sync_start = Instant::now();
                    self.sync_theory(&model);
                    let sync_duration = sync_start.elapsed();
                    self.timings.theory_sync += sync_duration;

                    let check_start = Instant::now();
                    let check =
                        self.check_theory_core(tracking.as_mut().map(|(t, n)| (&mut **t, *n)));
                    let check_duration = check_start.elapsed();
                    self.timings.theory_check += check_duration;
                    let (propagations_added, conflict_size) = Self::check_metrics(&check);
                    let dispatch = self.dispatch_theory_check(check, false);
                    let (check_label, action) = Self::dispatch_label(&dispatch);
                    self.emit_dpll_round_event(
                        round,
                        "sat",
                        sat_duration,
                        sync_duration,
                        check_label,
                        check_duration,
                        propagations_added,
                        conflict_size,
                        action,
                    );
                    match dispatch {
                        TheoryDispatch::Accept => match self.run_final_check_if_needed() {
                            FinalCheckResult::Accept => {
                                return Ok(AssumeResult::Sat(model));
                            }
                            FinalCheckResult::Unknown => {
                                self.exit_model_scope_if_active();
                                return Ok(AssumeResult::Unknown);
                            }
                            FinalCheckResult::Conflict => {
                                self.theory_conflict_count += 1;
                                refinements += 1;
                                if refinements >= Self::MAX_THEORY_REFINEMENTS {
                                    self.exit_model_scope_if_active();
                                    return Ok(AssumeResult::Unknown);
                                }
                                continue;
                            }
                        },
                        TheoryDispatch::Unknown => {
                            self.exit_model_scope_if_active();
                            return Ok(AssumeResult::Unknown);
                        }
                        TheoryDispatch::Continue => {
                            refinements += 1;
                            if refinements >= Self::MAX_THEORY_REFINEMENTS {
                                self.exit_model_scope_if_active();
                                return Ok(AssumeResult::Unknown);
                            }
                            continue;
                        }
                        _ => return Err(DpllError::UnexpectedTheoryResult),
                    }
                }
                AssumeResult::Unsat(core) => {
                    self.exit_model_scope_if_active();
                    self.emit_dpll_round_event(
                        round,
                        "unsat",
                        sat_duration,
                        Duration::ZERO,
                        "sat_unsat",
                        Duration::ZERO,
                        0,
                        0,
                        Some("DeclareUnsat"),
                    );
                    return Ok(AssumeResult::Unsat(core));
                }
                AssumeResult::Unknown => {
                    self.exit_model_scope_if_active();
                    self.emit_dpll_round_event(
                        round,
                        "unknown",
                        sat_duration,
                        Duration::ZERO,
                        "sat_unknown",
                        Duration::ZERO,
                        0,
                        0,
                        Some("DeclareUnknown"),
                    );
                    return Ok(AssumeResult::Unknown);
                }
                #[allow(unreachable_patterns)]
                _ => return Err(DpllError::UnexpectedTheoryResult),
            }
        }
    }
}
