// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use z4_core::{Sort, TermId, TermStore, TheoryLit, TheoryPropagation, TheoryResult, TheorySolver};
use z4_euf::{EufModel, EufSolver};
use z4_lia::{LiaModel, LiaSolver};
use z4_strings::StringModel;

use crate::combined_solvers::check_loops::{assert_fixpoint_convergence, debug_nelson_oppen};
use crate::combined_solvers::interface_bridge::{lia_get_int_value_with_reasons, InterfaceBridge};
use crate::term_helpers::contains_arithmetic_ops;

/// Combined Strings + EUF + LIA theory solver for QF_SLIA.
///
/// Wraps `StringSolver`, `EufSolver`, and `LiaSolver` with Nelson-Oppen
/// style theory combination. The StringSolver handles string equalities
/// and disequalities. LIA handles integer arithmetic including `str.len`
/// terms (which LIA treats as opaque Int variables). EUF handles
/// congruence reasoning. Length axioms are injected by the executor
/// before Tseitin encoding.
pub(crate) struct StringsLiaSolver<'a> {
    terms: &'a TermStore,
    strings: z4_strings::StringSolver<'a>,
    euf: EufSolver<'a>,
    lia: LiaSolver<'a>,
    /// Shared Nelson-Oppen interface term tracking (#3788).
    interface: InterfaceBridge,
    /// Scope depth counter for push/pop symmetry checking (#4995).
    scope_depth: usize,
}

fn equality_propagation_conflict_result(
    conflict: Vec<TheoryLit>,
    label: &'static str,
) -> TheoryResult {
    if !conflict.is_empty() {
        return TheoryResult::Unsat(conflict);
    }

    // A theory reported a conflict but with zero reasons. Treat this as
    // incomplete rather than silently dropping the conflict.
    tracing::warn!(
        "BUG: {label} propagate_equalities returned conflict with 0 reasons — \
         returning Unknown instead of silently dropping"
    );
    TheoryResult::Unknown
}

impl<'a> StringsLiaSolver<'a> {
    pub(crate) fn new(terms: &'a TermStore) -> Self {
        let mut lia = LiaSolver::new(terms);
        lia.set_combined_theory_mode(true);
        Self {
            terms,
            strings: z4_strings::StringSolver::new(terms),
            euf: EufSolver::new(terms),
            lia,
            interface: InterfaceBridge::new(),
            scope_depth: 0,
        }
    }

    /// Pre-register the empty string term in the inner string solver.
    pub(crate) fn set_empty_string_id(&mut self, id: TermId) {
        self.strings.set_empty_string_id(id);
    }

    /// Mark a term as having been reduced via DPLL-level reduction lemmas.
    pub(crate) fn mark_reduced(&mut self, term: TermId) {
        self.strings.mark_reduced(term);
    }

    /// Extract EUF, LIA, and String models for model generation.
    pub(crate) fn extract_all_models(&mut self) -> (EufModel, Option<LiaModel>, StringModel) {
        let euf_model = self.euf.extract_model();
        let lia_model = self.lia.extract_model();
        let string_model = self.strings.extract_model();
        (euf_model, lia_model, string_model)
    }

    #[cfg(test)]
    pub(crate) fn has_interface_term(&self, term: TermId) -> bool {
        self.interface.contains_arith_term(&term)
    }

    #[cfg(test)]
    pub(crate) fn sorted_interface_terms(&self) -> Vec<TermId> {
        self.interface.sorted_arith_terms()
    }

    /// Replay learned LIA cuts into the freshly-created theory.
    pub(crate) fn replay_learned_cuts(&mut self) {
        self.lia.replay_learned_cuts();
    }

    /// Identity accessor for macro compatibility (mirrors LiraSolver/AufLiraSolver pattern).
    #[expect(dead_code, reason = "used by incremental split-loop conflict macros")]
    pub(crate) fn lra_solver(&self) -> &Self {
        self
    }

    /// Collect all bound conflicts from the inner LIA solver.
    #[expect(dead_code, reason = "used by incremental split-loop conflict macros")]
    pub(crate) fn collect_all_bound_conflicts(
        &self,
        skip_first: bool,
    ) -> Vec<z4_core::TheoryConflict> {
        self.lia.collect_all_bound_conflicts(skip_first)
    }

    /// Export learned LIA state (Gomory cuts, HNF cuts) for cross-iteration persistence.
    pub(crate) fn take_learned_state(
        &mut self,
    ) -> (
        Vec<z4_lia::StoredCut>,
        hashbrown::HashSet<z4_lia::HnfCutKey>,
    ) {
        self.lia.take_learned_state()
    }

    /// Import learned LIA state from a previous iteration.
    pub(crate) fn import_learned_state(
        &mut self,
        cuts: Vec<z4_lia::StoredCut>,
        seen: hashbrown::HashSet<z4_lia::HnfCutKey>,
    ) {
        self.lia.import_learned_state(cuts, seen);
    }

    /// Export Diophantine solver state for cross-iteration persistence.
    pub(crate) fn take_dioph_state(&mut self) -> z4_lia::DiophState {
        self.lia.take_dioph_state()
    }

    /// Import Diophantine solver state from a previous iteration.
    pub(crate) fn import_dioph_state(&mut self, state: z4_lia::DiophState) {
        self.lia.import_dioph_state(state);
    }
}

impl TheorySolver for StringsLiaSolver<'_> {
    fn register_atom(&mut self, atom: TermId) {
        self.lia.register_atom(atom);
    }

    fn assert_literal(&mut self, literal: TermId, value: bool) {
        self.euf.assert_literal(literal, value);
        self.strings.assert_literal(literal, value);
        if contains_arithmetic_ops(self.terms, literal)
            || crate::term_helpers::contains_string_ops(self.terms, literal)
        {
            self.lia.assert_literal(literal, value);
        }
        // Track interface terms from all literals, including negated equalities (#4767).
        self.interface.track_interface_term(self.terms, literal);
        self.interface.collect_int_constants(self.terms, literal);
    }

    fn check(&mut self) -> TheoryResult {
        let debug = debug_nelson_oppen();

        #[cfg(debug_assertions)]
        if std::env::var("Z4_DBG_LIA_ONLY").is_ok() {
            return self.lia.check();
        }

        // Check strings first for string-level conflicts.
        let str_result = self.strings.check();
        let mut strings_incomplete = matches!(&str_result, TheoryResult::Unknown);
        if debug {
            safe_eprintln!(
                "[SLIA check] strings.check() => {:?}",
                match &str_result {
                    TheoryResult::Sat => "Sat".to_string(),
                    TheoryResult::Unsat(r) => format!("Unsat({} reasons)", r.len()),
                    TheoryResult::Unknown => "Unknown".to_string(),
                    TheoryResult::NeedStringLemma(l) => format!("NeedStringLemma({:?})", l.kind),
                    TheoryResult::NeedLemmas(_) => "NeedLemmas".to_string(),
                    TheoryResult::NeedSplit(_) => "NeedSplit".to_string(),
                    TheoryResult::NeedDisequalitySplit(_) => "NeedDisequalitySplit".to_string(),
                    TheoryResult::NeedExpressionSplit(_) => "NeedExpressionSplit".to_string(),
                    TheoryResult::UnsatWithFarkas(_) => "UnsatWithFarkas".to_string(),
                    TheoryResult::NeedModelEquality(_) | TheoryResult::NeedModelEqualities(_) =>
                        "NeedModelEquality".to_string(),
                    // All current TheoryResult variants handled above (#4906, #6149).
                    // Wildcard covers future variants from #[non_exhaustive].
                    _ => unreachable!("unhandled TheoryResult variant — update this match"),
                }
            );
        }
        match &str_result {
            TheoryResult::Unsat(reasons) => {
                if self.strings.is_ground_conflict() || self.strings.is_cycle_based_conflict() {
                    // Ground conflicts (constant mismatches, extf predicate
                    // evaluation) and cycle-based conflicts (I_CYCLE: x=y++x
                    // → y="") are always trustworthy — return immediately.
                    // Cycle detection is a sound inference rule (CVC5
                    // STRINGS_I_CYCLE), so NF conflicts derived from
                    // cycle-inferred equalities are reliable (#3875).
                    return TheoryResult::Unsat(reasons.clone());
                }
                // Soundness guard (#6261, #6275): NF-dependent conflicts from
                // process_simple_neq can be spurious on multi-variable word
                // equations. Treat as Unknown so the CEGAR loop adds split
                // lemmas until the conflict is provable at the SAT level.
                strings_incomplete = true;
            }
            TheoryResult::Unknown | TheoryResult::Sat => {}
            TheoryResult::NeedStringLemma(_) => {
                let lia_result = self.lia.check();
                match &lia_result {
                    TheoryResult::Unsat(reasons) => return TheoryResult::Unsat(reasons.clone()),
                    TheoryResult::UnsatWithFarkas(conflict) => {
                        return TheoryResult::UnsatWithFarkas(conflict.clone())
                    }
                    TheoryResult::Sat
                    | TheoryResult::Unknown
                    | TheoryResult::NeedSplit(_)
                    | TheoryResult::NeedDisequalitySplit(_)
                    | TheoryResult::NeedExpressionSplit(_)
                    | TheoryResult::NeedStringLemma(_)
                    | TheoryResult::NeedLemmas(_)
                    | TheoryResult::NeedModelEquality(_)
                    | TheoryResult::NeedModelEqualities(_) => return str_result,
                    // All current TheoryResult variants handled above (#4906, #6149, #6303).
                    // Wildcard covers future variants from #[non_exhaustive].
                    _ => unreachable!("unhandled TheoryResult variant — update this match"),
                }
            }
            TheoryResult::NeedSplit(_)
            | TheoryResult::NeedDisequalitySplit(_)
            | TheoryResult::NeedExpressionSplit(_)
            | TheoryResult::NeedLemmas(_)
            | TheoryResult::UnsatWithFarkas(_)
            | TheoryResult::NeedModelEquality(_)
            | TheoryResult::NeedModelEqualities(_) => return str_result,
            // All current TheoryResult variants handled above (#4906, #6149, #6303).
            // Wildcard covers future variants from #[non_exhaustive].
            _ => unreachable!("unhandled TheoryResult variant — update this match"),
        }

        const MAX_ITERATIONS: usize = 100;

        for iteration in 0..MAX_ITERATIONS {
            let lia_result = self.lia.check();
            let lia_is_unknown = matches!(&lia_result, TheoryResult::Unknown);
            if debug {
                safe_eprintln!(
                    "[SLIA check] N-O iter {}: lia.check() => {:?}",
                    iteration,
                    match &lia_result {
                        TheoryResult::Sat => "Sat".to_string(),
                        TheoryResult::Unsat(r) => format!("Unsat({} reasons)", r.len()),
                        TheoryResult::Unknown => "Unknown".to_string(),
                        TheoryResult::UnsatWithFarkas(_) => "UnsatWithFarkas".to_string(),
                        _ => format!("{:?}", "other"),
                    }
                );
            }
            match &lia_result {
                TheoryResult::Unsat(reasons) => return TheoryResult::Unsat(reasons.clone()),
                TheoryResult::UnsatWithFarkas(conflict) => {
                    return TheoryResult::UnsatWithFarkas(conflict.clone())
                }
                TheoryResult::Unknown => {}
                TheoryResult::NeedSplit(split) => return TheoryResult::NeedSplit(split.clone()),
                TheoryResult::NeedDisequalitySplit(split) => {
                    return TheoryResult::NeedDisequalitySplit(split.clone())
                }
                TheoryResult::NeedExpressionSplit(split) => {
                    return TheoryResult::NeedExpressionSplit(split.clone())
                }
                TheoryResult::NeedStringLemma(lemma) => {
                    return TheoryResult::NeedStringLemma(lemma.clone())
                }
                TheoryResult::NeedLemmas(lemmas) => {
                    return TheoryResult::NeedLemmas(lemmas.clone())
                }
                TheoryResult::NeedModelEquality(eq) => {
                    return TheoryResult::NeedModelEquality(eq.clone())
                }
                TheoryResult::NeedModelEqualities(eqs) => {
                    return TheoryResult::NeedModelEqualities(eqs.clone())
                }
                TheoryResult::Sat => {}
                // All current TheoryResult variants handled above (#4906, #6149).
                // Wildcard covers future variants from #[non_exhaustive].
                _ => unreachable!("unhandled TheoryResult variant — update this match"),
            }

            // Propagate equalities from LIA to EUF and Strings.
            let eq_result = self.lia.propagate_equalities();
            if let Some(conflict) = eq_result.conflict {
                return equality_propagation_conflict_result(conflict, "SLIA LIA");
            }
            let mut has_new_equalities = !eq_result.equalities.is_empty();
            if debug && has_new_equalities {
                safe_eprintln!(
                    "[SLIA N-O] Iteration {}: LIA discovered {} equalities",
                    iteration,
                    eq_result.equalities.len()
                );
            }
            for eq in eq_result.equalities {
                // Self-equality guard: propagate_equalities_to() checks this
                // centrally, but SLIA propagates directly to multiple targets.
                debug_assert!(
                    eq.lhs != eq.rhs,
                    "BUG: SLIA LIA propagated trivial self-equality ({:?} = {:?})",
                    eq.lhs,
                    eq.rhs
                );
                self.euf.assert_shared_equality(eq.lhs, eq.rhs, &eq.reason);
                self.strings
                    .assert_shared_equality(eq.lhs, eq.rhs, &eq.reason);
            }

            // Evaluate interface terms and propagate to EUF and Strings (#4068).
            // Bridge equalities now carry LIA tight-bound reasons when
            // available, improving proof provenance for conflict explanations.
            let lia = &self.lia;
            let (new_eqs, _speculative) = self.interface.evaluate_and_propagate(
                self.terms,
                &|t| lia_get_int_value_with_reasons(lia, t),
                debug,
                "SLIA",
            );
            for eq in &new_eqs {
                self.euf.assert_shared_equality(eq.lhs, eq.rhs, &eq.reason);
                self.strings
                    .assert_shared_equality(eq.lhs, eq.rhs, &eq.reason);
            }
            has_new_equalities |= !new_eqs.is_empty();

            // Check EUF.
            let euf_result = self.euf.check();
            match &euf_result {
                TheoryResult::Unsat(reasons) => return TheoryResult::Unsat(reasons.clone()),
                TheoryResult::Unknown => return TheoryResult::Unknown,
                TheoryResult::Sat => {}
                TheoryResult::NeedSplit(_)
                | TheoryResult::NeedDisequalitySplit(_)
                | TheoryResult::NeedExpressionSplit(_)
                | TheoryResult::UnsatWithFarkas(_)
                | TheoryResult::NeedStringLemma(_)
                | TheoryResult::NeedLemmas(_)
                | TheoryResult::NeedModelEquality(_)
                | TheoryResult::NeedModelEqualities(_) => return euf_result,
                // All current TheoryResult variants handled above (#4906, #6149, #6303).
                // Wildcard covers future variants from #[non_exhaustive].
                _ => unreachable!("unhandled TheoryResult variant — update this match"),
            }

            // Propagate equalities from EUF to LIA and Strings.
            let euf_eq_result = self.euf.propagate_equalities();
            if let Some(conflict) = euf_eq_result.conflict {
                return equality_propagation_conflict_result(conflict, "SLIA EUF");
            }
            let has_euf_equalities = !euf_eq_result.equalities.is_empty();
            if debug && has_euf_equalities {
                safe_eprintln!(
                    "[SLIA N-O] Iteration {}: EUF discovered {} equalities",
                    iteration,
                    euf_eq_result.equalities.len()
                );
            }
            for eq in euf_eq_result.equalities {
                // Self-equality guard: matches propagate_equalities_to() invariant.
                debug_assert!(
                    eq.lhs != eq.rhs,
                    "BUG: SLIA EUF propagated trivial self-equality ({:?} = {:?})",
                    eq.lhs,
                    eq.rhs
                );
                // #7451: Sort-filter EUF→LIA propagation. EUF is sort-agnostic
                // and can discover equalities between terms of any sort (e.g.,
                // String = String from congruence closure). Sending these to LIA
                // causes LIA to misinterpret non-arithmetic terms as opaque
                // variables with value 0, producing spurious cross-sort
                // equalities (e.g., x:String = 0:Int) that cause false UNSAT.
                // Only propagate Int/Real-sorted equalities to LIA.
                let lhs_sort = self.terms.sort(eq.lhs);
                if matches!(lhs_sort, Sort::Int | Sort::Real) {
                    self.lia.assert_shared_equality(eq.lhs, eq.rhs, &eq.reason);
                }
                self.strings
                    .assert_shared_equality(eq.lhs, eq.rhs, &eq.reason);
            }

            // Re-check strings after N-O equality propagation.
            if has_new_equalities || has_euf_equalities {
                let str_recheck = self.strings.check();
                if debug {
                    safe_eprintln!(
                        "[SLIA check] strings re-check => {:?}",
                        match &str_recheck {
                            TheoryResult::Sat => "Sat".to_string(),
                            TheoryResult::Unsat(r) => format!("Unsat({} reasons)", r.len()),
                            TheoryResult::Unknown => "Unknown".to_string(),
                            TheoryResult::NeedStringLemma(l) =>
                                format!("NeedStringLemma({:?})", l.kind),
                            TheoryResult::NeedLemmas(_) => "NeedLemmas".to_string(),
                            TheoryResult::NeedSplit(_) => "NeedSplit".to_string(),
                            TheoryResult::NeedDisequalitySplit(_) =>
                                "NeedDisequalitySplit".to_string(),
                            TheoryResult::NeedExpressionSplit(_) =>
                                "NeedExpressionSplit".to_string(),
                            TheoryResult::UnsatWithFarkas(_) => "UnsatWithFarkas".to_string(),
                            TheoryResult::NeedModelEquality(_)
                            | TheoryResult::NeedModelEqualities(_) =>
                                "NeedModelEquality".to_string(),
                            // All current TheoryResult variants handled above (#4906, #6149).
                            // Wildcard covers future variants from #[non_exhaustive].
                            _ => unreachable!("unhandled TheoryResult variant — update this match"),
                        }
                    );
                }
                match &str_recheck {
                    TheoryResult::Unsat(reasons) => {
                        if self.strings.is_ground_conflict()
                            || self.strings.is_cycle_based_conflict()
                        {
                            // Ground and cycle-based conflicts after N-O
                            // propagation are trustworthy (#3875).
                            return TheoryResult::Unsat(reasons.clone());
                        }
                        // Soundness guard (#3826, #4068, #6275): NF-dependent
                        // string conflicts after N-O propagation may be spurious.
                        // Bridge-derived EQC merges can cause incorrect NF
                        // conflicts. Treat as Unknown; the CEGAR loop will add
                        // split lemmas until the conflict is provable.
                        strings_incomplete = true;
                    }
                    TheoryResult::Unknown => {
                        strings_incomplete = true;
                    }
                    TheoryResult::Sat => {
                        strings_incomplete = false;
                    }
                    TheoryResult::NeedStringLemma(lemma) => {
                        return TheoryResult::NeedStringLemma(lemma.clone())
                    }
                    TheoryResult::NeedLemmas(lemmas) => {
                        return TheoryResult::NeedLemmas(lemmas.clone())
                    }
                    TheoryResult::NeedSplit(_)
                    | TheoryResult::NeedDisequalitySplit(_)
                    | TheoryResult::NeedExpressionSplit(_)
                    | TheoryResult::UnsatWithFarkas(_)
                    | TheoryResult::NeedModelEquality(_)
                    | TheoryResult::NeedModelEqualities(_) => return str_recheck,
                    // All current TheoryResult variants handled above (#4906, #6149, #6303).
                    // Wildcard covers future variants from #[non_exhaustive].
                    _ => unreachable!("unhandled TheoryResult variant — update this match"),
                }
            }

            if !has_new_equalities && !has_euf_equalities {
                if debug && iteration > 0 {
                    safe_eprintln!("[SLIA N-O] Fixpoint after {} iterations", iteration + 1);
                }
                if strings_incomplete || lia_is_unknown {
                    return TheoryResult::Unknown;
                }
                assert_fixpoint_convergence("SLIA", &mut [&mut self.lia, &mut self.euf]);
                return TheoryResult::Sat;
            }

            // Monotonicity: non-fixpoint iterations must discover new equalities
            debug_assert!(
                has_new_equalities || has_euf_equalities,
                "BUG: SLIA N-O iteration {iteration} continued past fixpoint with 0 new equalities"
            );

            // Non-convergence is a solver bug — assert in all build modes.
            assert!(
                iteration < MAX_ITERATIONS - 1,
                "BUG: SLIA Nelson-Oppen loop did not converge in {MAX_ITERATIONS} iterations"
            );
        }

        TheoryResult::Unknown
    }

    fn propagate(&mut self) -> Vec<TheoryPropagation> {
        let mut props = self.strings.propagate();
        props.extend(self.euf.propagate());
        props.extend(self.lia.propagate());
        props
    }

    fn supports_theory_aware_branching(&self) -> bool {
        self.lia.supports_theory_aware_branching()
    }

    fn suggest_phase(&self, atom: TermId) -> Option<bool> {
        self.lia.suggest_phase(atom)
    }

    fn sort_atom_index(&mut self) {
        self.lia.sort_atom_index();
    }

    fn generate_bound_axiom_terms(&self) -> Vec<(TermId, bool, TermId, bool)> {
        self.lia.generate_bound_axiom_terms()
    }

    fn generate_incremental_bound_axioms(&self, atom: TermId) -> Vec<(TermId, bool, TermId, bool)> {
        self.lia.generate_incremental_bound_axioms(atom)
    }

    fn push(&mut self) {
        self.scope_depth += 1;
        self.strings.push();
        self.euf.push();
        self.lia.push();
        self.interface.push();
    }

    fn pop(&mut self) {
        if self.scope_depth == 0 {
            // Graceful no-op: pop at depth 0 is a caller error but not fatal.
            return;
        }
        self.scope_depth -= 1;
        self.strings.pop();
        self.euf.pop();
        self.lia.pop();
        self.interface.pop();
    }

    fn reset(&mut self) {
        assert!(
            self.scope_depth == 0,
            "BUG: StringsLiaSolver::reset() called with non-zero scope depth {} (unbalanced push/pop)",
            self.scope_depth,
        );
        self.strings.reset();
        self.euf.reset();
        self.lia.reset();
        self.interface.reset();
    }

    fn soft_reset(&mut self) {
        assert!(
            self.scope_depth == 0,
            "BUG: StringsLiaSolver::soft_reset() called with non-zero scope depth {} (unbalanced push/pop)",
            self.scope_depth,
        );
        self.strings.soft_reset();
        self.euf.soft_reset();
        self.lia.soft_reset();
        self.interface.reset();
    }
}

#[allow(clippy::panic)]
#[cfg(test)]
mod tests;
