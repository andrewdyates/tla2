// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! IC3 invariant validation: validate_invariant_budgeted, validate_invariant,
//! verify_consecution_independent, consecution_simple_fallback.

use std::sync::atomic::Ordering;

use super::config::ValidationStrategy;
use super::engine::Ic3Engine;
use crate::sat_types::{Lit, SatResult, SatSolver, SimpleSolver};

impl Ic3Engine {
    /// Validate the claimed inductive invariant using an independent SAT check.
    ///
    /// After IC3 converges, collect ALL lemmas from all frames and check:
    /// 1. Init => Inv  (initial state satisfies the invariant)
    /// 2. Inv AND T AND constraints => Inv'  (inductiveness: invariant is preserved)
    /// 3. Inv => !Bad  (invariant implies safety)
    ///
    /// Returns `Some(true)` if valid, `Some(false)` if unsound, `None` if
    /// the time budget was exhausted or portfolio cancellation was triggered.
    pub(super) fn validate_invariant_budgeted(&self) -> Option<bool> {
        // Strategy::None skips all validation — assume correct (#4121).
        // ONLY safe when another portfolio member validates with Auto.
        if self.config.validation_strategy == ValidationStrategy::None {
            eprintln!("IC3 validate: SKIPPING all validation (strategy=None)");
            return Some(true);
        }

        let validate_start = std::time::Instant::now();

        // Compute constraint-to-latch ratio for tier selection (#4121).
        // This uses constraint_lits (AIGER environment constraints), not
        // trans_clauses (Tseitin encoding). High constraint_lits/latch ratios
        // indicate circuits like qspiflash where the constraint propagation
        // overhead dominates solver time.
        let num_latches = self.ts.latch_vars.len();
        let constraint_ratio = if num_latches > 0 {
            self.ts.constraint_lits.len() as f64 / num_latches as f64
        } else {
            0.0
        };
        let is_high_constraint_ratio = constraint_ratio > 5.0;

        // Budget scales with circuit size. When proof verification is
        // explicitly enabled (#4216), use more generous budgets for larger
        // circuits since this is the primary defense-in-depth mechanism.
        let proof_verify = super::config::proof_verification_enabled();
        let base_budget_secs: f64 = if num_latches < 60 {
            10.0
        } else if num_latches <= 200 {
            if proof_verify {
                45.0
            } else {
                30.0
            }
        } else {
            if proof_verify {
                90.0
            } else {
                60.0
            }
        };
        // Budget selection: high-ratio circuits get tighter budgets (#4121),
        // but only as a cap. Small circuits keep their existing 10s budget.
        let budget_secs: f64 = if is_high_constraint_ratio {
            base_budget_secs.min(15.0)
        } else {
            base_budget_secs
        };
        let should_abort = |start: &std::time::Instant| -> bool {
            start.elapsed().as_secs_f64() > budget_secs || self.cancelled.load(Ordering::Relaxed)
        };

        // Collect ALL lemmas (clauses) from all frames.
        let mut all_lemmas: Vec<Vec<Lit>> = Vec::new();
        for frame in &self.frames.frames {
            for lemma in &frame.lemmas {
                all_lemmas.push(lemma.lits.clone());
            }
        }
        for lemma in &self.inf_lemmas {
            all_lemmas.push(lemma.lits.clone());
        }
        eprintln!(
            "IC3 validate: {} total lemmas across {} frames + inf (constraint_ratio={:.1}, strategy={:?})",
            all_lemmas.len(),
            self.frames.frames.len(),
            constraint_ratio,
            self.config.validation_strategy,
        );

        // Check 1: Init => Inv
        {
            let mut init_solver = self.make_fast_validation_solver();
            init_solver.add_clause(&[Lit::TRUE]);
            for clause in &self.ts.init_clauses {
                init_solver.add_clause(&clause.lits);
            }
            for clause in &self.ts.trans_clauses {
                init_solver.add_clause(&clause.lits);
            }
            for &constraint in &self.ts.constraint_lits {
                init_solver.add_clause(&[constraint]);
            }

            for (i, lemma) in all_lemmas.iter().enumerate() {
                if i > 0 && i % 50 == 0 && should_abort(&validate_start) {
                    eprintln!(
                        "IC3 validate: BUDGET EXCEEDED at Init=>Inv check lemma {}/{} ({:.1}s)",
                        i,
                        all_lemmas.len(),
                        validate_start.elapsed().as_secs_f64(),
                    );
                    return None;
                }
                let neg_lits: Vec<Lit> = lemma.iter().map(|l| !*l).collect();
                if init_solver.solve(&neg_lits) == SatResult::Sat {
                    eprintln!(
                        "IC3 VALIDATE FAIL: Init does NOT satisfy lemma {}: {:?}",
                        i, lemma
                    );
                    return Some(false);
                }
            }
            eprintln!("IC3 validate: Init => Inv OK");
        }

        // Check 2: Inv AND T AND constraints => Inv'
        //
        // Strategy::SkipConsecution skips this check entirely (#4121).
        // For Auto strategy, consecution is ALWAYS checked -- skipping it
        // is unsound when z4-sat has bugs that cause IC3 to converge on
        // non-inductive invariants. The solver tier is selected based on
        // circuit characteristics:
        //
        // - high ratio (>5x): Z4NoPreprocess (skip SimpleSolver overhead)
        // - <= 60 latches AND low ratio: SimpleSolver (max independence)
        // - all others: Z4NoPreprocess (faster, no BVE risk)
        //
        // For large circuits (>200 latches), we use Z4NoPreprocess with a
        // generous budget. If the budget is exhausted, we return None
        // (indeterminate) rather than trusting an unvalidated invariant.
        #[allow(deprecated)]
        let skip_consecution =
            self.config.validation_strategy == ValidationStrategy::SkipConsecution;
        let skip_check2 = skip_consecution;

        if !skip_check2 {
            // For high-ratio circuits, never use SimpleSolver even for small
            // latch counts — the constraint propagation overhead is too high.
            let use_simple = num_latches <= 60 && !is_high_constraint_ratio;

            if use_simple {
                // Self-inductiveness debug info (SimpleSolver path only).
                for (i, lemma) in all_lemmas.iter().enumerate() {
                    let mut base_solver = self.make_validation_solver();
                    base_solver.add_clause(&[Lit::TRUE]);
                    for clause in &self.ts.trans_clauses {
                        base_solver.add_clause(&clause.lits);
                    }
                    for &constraint in &self.ts.constraint_lits {
                        base_solver.add_clause(&[constraint]);
                    }
                    for clause in &self.next_link_clauses {
                        base_solver.add_clause(clause);
                    }
                    base_solver.add_clause(lemma);

                    let neg_primed: Vec<Lit> = lemma
                        .iter()
                        .map(|l| {
                            let var = l.var();
                            if let Some(&next_var) = self.next_vars.get(&var) {
                                if l.is_positive() {
                                    Lit::neg(next_var)
                                } else {
                                    Lit::pos(next_var)
                                }
                            } else {
                                !*l
                            }
                        })
                        .collect();

                    if base_solver.solve(&neg_primed) == SatResult::Sat {
                        eprintln!(
                            "IC3 validate: lemma {} NOT self-inductive (base only): {:?}",
                            i, lemma
                        );
                    }
                }
            }

            // Build the validation solver: SimpleSolver for small low-ratio,
            // Z4NoPreprocess for medium or high-ratio circuits.
            let mut trans_solver = if use_simple {
                self.make_validation_solver()
            } else {
                self.make_fast_validation_solver()
            };
            trans_solver.add_clause(&[Lit::TRUE]);
            for clause in &self.ts.trans_clauses {
                trans_solver.add_clause(&clause.lits);
            }
            for &constraint in &self.ts.constraint_lits {
                trans_solver.add_clause(&[constraint]);
            }
            for clause in &self.next_link_clauses {
                trans_solver.add_clause(clause);
            }
            for lemma in &all_lemmas {
                trans_solver.add_clause(lemma);
            }

            for (i, lemma) in all_lemmas.iter().enumerate() {
                if should_abort(&validate_start) {
                    eprintln!(
                        "IC3 validate: BUDGET EXCEEDED at Inv=>Inv' check lemma {}/{} ({:.1}s)",
                        i,
                        all_lemmas.len(),
                        validate_start.elapsed().as_secs_f64(),
                    );
                    return None;
                }
                let neg_primed: Vec<Lit> = lemma
                    .iter()
                    .map(|l| {
                        let var = l.var();
                        if let Some(&next_var) = self.next_vars.get(&var) {
                            if l.is_positive() {
                                Lit::neg(next_var)
                            } else {
                                Lit::pos(next_var)
                            }
                        } else {
                            !*l
                        }
                    })
                    .collect();

                if trans_solver.solve(&neg_primed) == SatResult::Sat {
                    eprintln!(
                        "IC3 VALIDATE FAIL: Inv AND T does NOT preserve lemma {}: {:?}",
                        i, lemma
                    );
                    for &latch in &self.ts.latch_vars {
                        let val = trans_solver.value(Lit::pos(latch));
                        if let Some(v) = val {
                            eprint!("v{}={} ", latch.0, if v { "T" } else { "F" });
                        }
                    }
                    eprintln!();
                    for &latch in &self.ts.latch_vars {
                        if let Some(&next_var) = self.next_vars.get(&latch) {
                            let val = trans_solver.value(Lit::pos(next_var));
                            if let Some(v) = val {
                                eprint!("v{}'={} ", latch.0, if v { "T" } else { "F" });
                            }
                        }
                    }
                    eprintln!();
                    return Some(false);
                }
            }
            let solver_kind = if use_simple {
                "SimpleSolver"
            } else {
                "Z4NoPreprocess"
            };
            eprintln!(
                "IC3 validate: Inv AND T => Inv' OK ({:.3}s, {})",
                validate_start.elapsed().as_secs_f64(),
                solver_kind,
            );
        } else {
            eprintln!(
                "IC3 validate: SKIPPING Inv=>Inv' check (validation_strategy=SkipConsecution, latches={}, constraint_ratio={:.1})",
                num_latches, constraint_ratio,
            );
        }

        // Check 3: Inv => !Bad
        {
            let mut bad_solver = self.make_fast_validation_solver();
            bad_solver.add_clause(&[Lit::TRUE]);
            for clause in &self.ts.trans_clauses {
                bad_solver.add_clause(&clause.lits);
            }
            for &constraint in &self.ts.constraint_lits {
                bad_solver.add_clause(&[constraint]);
            }
            for lemma in &all_lemmas {
                bad_solver.add_clause(lemma);
            }

            for &bad_lit in &self.ts.bad_lits {
                if should_abort(&validate_start) {
                    eprintln!(
                        "IC3 validate: BUDGET EXCEEDED at Inv=>!Bad check ({:.1}s)",
                        validate_start.elapsed().as_secs_f64(),
                    );
                    return None;
                }
                if bad_solver.solve(&[bad_lit]) == SatResult::Sat {
                    eprintln!(
                        "IC3 VALIDATE FAIL: Inv allows bad state! bad_lit={:?}",
                        bad_lit
                    );
                    for &latch in &self.ts.latch_vars {
                        let val = bad_solver.value(Lit::pos(latch));
                        if let Some(v) = val {
                            eprint!("v{}={} ", latch.0, if v { "T" } else { "F" });
                        }
                    }
                    eprintln!();
                    return Some(false);
                }
            }
            eprintln!(
                "IC3 validate: Inv => !Bad OK ({:.3}s)",
                validate_start.elapsed().as_secs_f64()
            );
        }

        let validate_elapsed = validate_start.elapsed();
        eprintln!(
            "IC3 validate: ALL CHECKS PASSED -- invariant is valid ({:.3}s, {} lemmas)",
            validate_elapsed.as_secs_f64(),
            all_lemmas.len(),
        );
        Some(true)
    }

    /// Wrapper for backward compatibility — returns bool.
    #[allow(dead_code)]
    pub(super) fn validate_invariant(&self) -> bool {
        self.validate_invariant_budgeted().unwrap_or(false)
    }

    /// Independent consecution verification using a fresh SimpleSolver.
    pub(super) fn verify_consecution_independent(
        &self,
        frame: usize,
        cube: &[Lit],
        strengthen: bool,
    ) -> bool {
        let mut solver = SimpleSolver::new();
        solver.add_clause(&[Lit::TRUE]);
        for clause in &self.ts.trans_clauses {
            solver.add_clause(&clause.lits);
        }
        for &constraint in &self.ts.constraint_lits {
            solver.add_clause(&[constraint]);
        }
        for clause in &self.next_link_clauses {
            solver.add_clause(clause);
        }
        if frame >= 2 {
            let upper = (frame - 1).min(self.frames.depth().saturating_sub(1));
            for f in 1..=upper {
                if f < self.frames.frames.len() {
                    for lemma in &self.frames.frames[f].lemmas {
                        solver.add_clause(&lemma.lits);
                    }
                }
            }
        }
        for lemma in &self.inf_lemmas {
            solver.add_clause(&lemma.lits);
        }
        if strengthen {
            let neg_cube: Vec<Lit> = cube.iter().map(|l| !*l).collect();
            solver.add_clause(&neg_cube);
        }
        let assumptions = self.prime_cube(cube);
        solver.solve(&assumptions) == SatResult::Unsat
    }

    /// Verify that a single generalized lemma satisfies the consecution property
    /// at a given frame, using a fresh solver independent of the IC3 frame solvers.
    ///
    /// Checks: F_{frame-1} AND Inv_inf AND T AND constraints AND next_link AND
    ///         !(cube) AND cube' is UNSAT.
    ///
    /// This is the per-lemma equivalent of Check 2 in `validate_invariant_budgeted`,
    /// but applied immediately before a lemma is added to the frame sequence. It
    /// catches z4-sat false UNSAT in the consecution query before the unsound lemma
    /// can propagate to higher frames.
    ///
    /// Returns `true` if the lemma passes consecution (UNSAT), `false` if it fails
    /// (SAT, meaning the lemma is NOT inductive relative to the frame).
    ///
    /// Uses Z4NoPreprocess for circuits with > 60 latches (SimpleSolver is too slow)
    /// and SimpleSolver for small circuits (maximum independence from z4-sat bugs).
    pub(super) fn verify_lemma_consecution(&self, frame: usize, cube: &[Lit]) -> bool {
        // Build a fresh solver with the transition relation.
        let use_simple = self.ts.latch_vars.len() <= 60
            && !super::config::is_high_constraint_circuit(
                self.ts.trans_clauses.len(),
                self.ts.constraint_lits.len(),
                self.ts.latch_vars.len(),
            );
        let mut solver = if use_simple {
            self.make_validation_solver()
        } else {
            self.make_fast_validation_solver()
        };

        solver.add_clause(&[Lit::TRUE]);

        // Transition relation.
        for clause in &self.ts.trans_clauses {
            solver.add_clause(&clause.lits);
        }
        // Constraints.
        for &constraint in &self.ts.constraint_lits {
            solver.add_clause(&[constraint]);
        }
        // Next-state linking clauses.
        for clause in &self.next_link_clauses {
            solver.add_clause(clause);
        }

        // Frame lemmas: add all lemmas from frames 1..=frame.
        // IC3 consecution is *relative inductive*: the lemma is inductive
        // relative to OTHER lemmas at the same frame level. We include lemmas
        // from the current frame (not just lower frames) to match the actual
        // IC3 frame solver's clause set.
        {
            let upper = frame.min(self.frames.depth().saturating_sub(1));
            for f in 1..=upper {
                if f < self.frames.frames.len() {
                    for lemma in &self.frames.frames[f].lemmas {
                        solver.add_clause(&lemma.lits);
                    }
                }
            }
        }
        // Infinity lemmas.
        for lemma in &self.inf_lemmas {
            solver.add_clause(&lemma.lits);
        }

        // Strengthening: add !(cube) as a clause. This ensures the current
        // state does NOT satisfy the cube, matching the standard IC3 consecution
        // check F_k AND T AND !(cube) AND cube'.
        let neg_cube: Vec<Lit> = cube.iter().map(|l| !*l).collect();
        solver.add_clause(&neg_cube);

        // Check cube' (primed cube) as assumptions.
        let assumptions = self.prime_cube(cube);
        solver.solve(&assumptions) == SatResult::Unsat
    }

    /// Perform consecution using SimpleSolver as a fallback when z4-sat produces
    /// false UNSAT (#4105).
    pub(super) fn consecution_simple_fallback(
        &self,
        frame: usize,
        cube: &[Lit],
    ) -> Option<Vec<Lit>> {
        let mut solver = SimpleSolver::new();
        solver.add_clause(&[Lit::TRUE]);
        for clause in &self.ts.trans_clauses {
            solver.add_clause(&clause.lits);
        }
        for &constraint in &self.ts.constraint_lits {
            solver.add_clause(&[constraint]);
        }
        for clause in &self.next_link_clauses {
            solver.add_clause(clause);
        }
        if frame >= 2 {
            let upper = (frame - 1).min(self.frames.depth().saturating_sub(1));
            for f in 1..=upper {
                if f < self.frames.frames.len() {
                    for lemma in &self.frames.frames[f].lemmas {
                        solver.add_clause(&lemma.lits);
                    }
                }
            }
        }
        for lemma in &self.inf_lemmas {
            solver.add_clause(&lemma.lits);
        }
        let assumptions = self.prime_cube(cube);
        if solver.solve(&assumptions) == SatResult::Sat {
            Some(Self::extract_state_from_solver(
                &solver,
                &self.ts.latch_vars,
            ))
        } else {
            None
        }
    }
}
