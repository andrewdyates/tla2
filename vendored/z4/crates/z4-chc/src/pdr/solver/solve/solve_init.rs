// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! PDR solve initialization: problem validation, init safety check,
//! must-summary initialization, symbolic equality propagation, and
//! startup invariant discovery.

use super::*;

impl PdrSolver {
    /// Initialize the solver state and run pre-loop checks.
    ///
    /// Returns `Some(result)` for early termination (init unsafe, acyclic safety,
    /// invalid problem, startup discovery proved safety). Returns `None` to
    /// proceed to the main PDR loop.
    pub(super) fn solve_init(&mut self) -> Option<PdrResult> {
        // Set the solve deadline from config (bounds total solve time including startup).
        if let Some(timeout) = self.config.solve_timeout {
            self.solve_deadline = Some(std::time::Instant::now() + timeout);
        }

        // Import cross-engine lemma pool hints (#7919).
        // Convert SharedLemma entries to LemmaHint and merge into user_hints
        // so they flow through the standard hint validation pipeline.
        if let Some(pool) = self.config.lemma_hints.take() {
            if !pool.is_empty() {
                let hint_count = pool.len();
                let hints = pool.to_hint_vec();
                self.config.user_hints.extend(hints);
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: Imported {} cross-engine lemma hints from LemmaPool (#7919)",
                        hint_count
                    );
                }
            }
        }

        // Validate problem first
        if let Err(e) = self.problem.validate() {
            if self.config.verbose {
                safe_eprintln!("PDR: Invalid CHC problem: {}", e);
            }
            return Some(self.finish_with_result_trace(PdrResult::Unknown));
        }

        // Reject problems with unsupported predicate sorts. PDR's SMT backend
        // supports Int/Real/Bool/BV/Array/Datatype; other sorts are not yet supported.
        // BV was previously rejected (#5523) but BV evaluation support was
        // added (sign_extend, zero_extend, repeat). Portfolio validation catches
        // unsound results, so PDR can attempt BV problems safely (#5595, #5644).
        // Array sorts are accepted (#6047): the underlying z4-dpll solver handles
        // array theory (select/store axioms, extensionality). Array-sorted state
        // vars are excluded from cubes/lemmas; the scalarization preprocessing
        // pass converts constant-index arrays to scalars before PDR runs.
        // Variable-index arrays pass through as Array-sorted state variables
        // and are handled via model-value substitution in MBP.
        for pred in self.problem.predicates() {
            for sort in &pred.arg_sorts {
                match sort {
                    ChcSort::Int
                    | ChcSort::Real
                    | ChcSort::Bool
                    | ChcSort::BitVec(_)
                    | ChcSort::Array(_, _)
                    | ChcSort::Datatype { .. } => {}
                    unsupported => {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: Unsupported predicate sort {:?} in {}, returning Unknown",
                                unsupported,
                                pred.name
                            );
                        }
                        return Some(self.finish_with_result_trace(PdrResult::Unknown));
                    }
                }
            }
        }

        // Configuration preconditions — programmer errors, must always fire (#3095).
        assert!(self.config.max_frames > 0, "PDR: max_frames must be >= 1");
        assert!(
            self.config.max_iterations > 0,
            "PDR: max_iterations must be >= 1"
        );
        assert!(
            self.config.max_obligations > 0,
            "PDR: max_obligations must be >= 1"
        );

        // Initialize: check if initial states satisfy safety
        match self.init_safe() {
            InitResult::Safe => {}
            InitResult::Unsafe => {
                if self.config.verbose {
                    safe_eprintln!("PDR: Initial state violates safety");
                }
                let cex = self.build_trivial_cex();
                // INVARIANT: Trivial CEX (init violates safety) has no transition
                // steps — the initial state directly violates the safety property.
                // Must be checked in release builds (#3095).
                assert!(
                    cex.steps.is_empty(),
                    "BUG: Trivial counterexample should have empty steps, got {}",
                    cex.steps.len()
                );
                return Some(self.finish_with_result_trace(PdrResult::Unsafe(cex)));
            }
        }

        // #6047: Acyclic safety check for problems with no transitions.
        // After inlining, zani-generated CHC problems often reduce to a single
        // predicate with only fact and query clauses (no self-loop transitions).
        // For such problems, `Inv = true` is trivially inductive (no transitions
        // to violate it). Safety reduces to checking each query constraint alone.
        //
        // Standard PDR fails here because:
        // 1. strengthen() finds no bad states (queries are independently Unsat)
        // 2. No lemmas are learned (no blocking needed)
        // 3. check_fixed_point rejects empty-frame equality
        // 4. check_invariants_prove_safety requires at least one lemma
        //
        // This check directly verifies each query constraint and returns Safe
        // with the trivial `true` model when all queries are contradictory.
        if self.problem.transitions().next().is_none() {
            if self.config.verbose {
                safe_eprintln!("PDR: No transition clauses — trying acyclic safety check");
            }
            if let Some(model) = self.try_acyclic_safety_proof() {
                return Some(self.finish_with_result_trace(PdrResult::Safe(model)));
            }
        }

        // Initialize must-summaries at level 0 from fact clauses (Spacer technique)
        // For each predicate, add the initial constraints as must-reachable states
        if self.config.use_must_summaries || self.config.use_mixed_summaries {
            if !self.init_must_summaries_from_facts() {
                return Some(self.finish_with_result_trace(PdrResult::Unknown));
            }
        }

        // Enrich must-summaries with self-loop closure states (#1613).
        // For phase-chain benchmarks (gj2007, s_mutants), the init must-summary cannot
        // satisfy inter-predicate transition guards. This adds exit guards as additional
        // must-summary disjuncts, enabling forward propagation through phase chains.
        self.enrich_must_summaries_with_loop_closure();

        // Propagate symbolic equality constraints (B = C) to derived predicates (#1613).
        // The forward must-summary propagation only propagates concrete points; this fills
        // the gap by propagating symbolic constraints that are preserved through transitions.
        // NOTE: Also called inside the startup fixpoint loop (#2248) to propagate equalities
        // discovered by discover_equality_invariants().
        self.propagate_symbolic_equalities_to_derived_predicates();

        // IMPORTANT: For predicates that are TRULY unreachable, frame[0] should be empty.
        // A predicate is truly unreachable if it has no fact clauses AND is not reachable
        // via transitions from predicates with facts. (#1419)
        //
        // Previously, we blocked ALL predicates without facts, which was overly conservative
        // for phase-chain benchmarks like gj2007_m_* where predicates are reachable via
        // transitions even though they lack direct init clauses.
        //
        // A lemma formula represents the invariant (NOT the blocking formula).
        // To block all states, we add lemma.formula = false, which means:
        // - The invariant is "false" (no states satisfy it)
        // - All states at level 0 are blocked for this predicate
        self.block_unreachable_predicates_at_frame0();

        // Run startup invariant discovery pipeline and direct safety check.
        // Returns Some(result) if solver should return early (discovery proved safety
        // or cancelled). See startup.rs for the full pipeline.
        if let Some(result) = self.run_startup_discovery() {
            return Some(result);
        }

        None
    }

    /// Initialize must-summaries at level 0 from fact clauses.
    /// Returns `true` on success, `false` if reach-fact capacity was exceeded.
    fn init_must_summaries_from_facts(&mut self) -> bool {
        for (clause_index, clause) in self.problem.clauses().iter().enumerate() {
            // Fact clause: no body predicates, just a constraint leading to head
            if clause.body.predicates.is_empty() {
                if let crate::ClauseHead::Predicate(pred, head_args) = &clause.head {
                    // Get the constraint on initial state (if any)
                    let constraint = clause
                        .body
                        .constraint
                        .clone()
                        .unwrap_or(ChcExpr::Bool(true));

                    // Map clause variables to canonical predicate variables
                    if let Some(canonical_vars) = self.canonical_vars(*pred) {
                        if head_args.len() == canonical_vars.len() {
                            // Build substitution from clause vars to canonical vars
                            let mut rewritten = constraint.clone();
                            // #2492: Also extract constituent vars from expression head args
                            for (arg, canon_var) in head_args.iter().zip(canonical_vars.iter()) {
                                match arg {
                                    ChcExpr::Var(arg_var) => {
                                        rewritten = rewritten.substitute(&[(
                                            arg_var.clone(),
                                            ChcExpr::var(canon_var.clone()),
                                        )]);
                                    }
                                    expr => {
                                        for v in expr.vars() {
                                            rewritten = rewritten.substitute(&[(
                                                v.clone(),
                                                ChcExpr::var(v.clone()),
                                            )]);
                                        }
                                    }
                                }
                            }
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: Init must-summary for pred {} at level 0: {}",
                                    pred.index(),
                                    rewritten
                                );
                            }
                            // Create ReachFact FIRST to get id for backed must-summary
                            let mut instances = FxHashMap::default();
                            cube::extract_equalities_from_formula(&rewritten, &mut instances);
                            let Some(id) = Self::insert_reach_fact_bounded(
                                &mut self.reachability,
                                self.config.verbose,
                                ReachFact {
                                    id: ReachFactId(0),
                                    predicate: *pred,
                                    level: 0,
                                    state: rewritten.clone(),
                                    incoming_clause: Some(clause_index),
                                    premises: Vec::new(),
                                    instances,
                                },
                            ) else {
                                // Capacity exceeded — abort gracefully (caller
                                // returns Unknown via the Option path).
                                return false;
                            };

                            // Add to must-summaries as BACKED (proven reachable via fact clause)
                            let added = self.reachability.must_summaries.add_backed(
                                0,
                                *pred,
                                rewritten.clone(),
                                id,
                            );
                            if added {
                                // Add to reach solver as BACKED entry for fast short-circuit
                                self.reachability
                                    .reach_solvers
                                    .add_backed(*pred, id, rewritten);
                            }
                        }
                    }
                }
            }
        }
        true
    }
}
