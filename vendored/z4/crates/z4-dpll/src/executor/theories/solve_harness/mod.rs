// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared theory solve helpers and preprocessing artifacts.
//!
//! Hosts the shared model bundle plus preprocessing outputs reused by the
//! incremental and split-loop solver entry points.

use crate::executor::mod_div_elim::eliminate_int_mod_div_by_constant;
use crate::executor::Executor;
use crate::preprocess::{NormalizeArithSom, PreprocessingPass, VariableSubstitution};
#[cfg(not(kani))]
use hashbrown::{HashMap, HashSet};
use z4_arrays::ArrayModel;
#[cfg(kani)]
use z4_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use z4_core::TermId;
use z4_euf::EufModel;
use z4_lia::LiaModel;
use z4_lra::LraModel;
use z4_seq::SeqModel;
use z4_strings::StringModel;

/// Theory models extracted from a SAT result.
///
/// Bundles the optional model for each theory, replacing the 6 positional
/// `Option<T>` parameters to `solve_and_store_model_full`.
#[derive(Default)]
pub(in crate::executor) struct TheoryModels {
    pub(in crate::executor) euf: Option<EufModel>,
    pub(in crate::executor) array: Option<ArrayModel>,
    pub(in crate::executor) lra: Option<LraModel>,
    pub(in crate::executor) lia: Option<LiaModel>,
    pub(in crate::executor) bv: Option<z4_bv::BvModel>,
    pub(in crate::executor) fp: Option<z4_fp::FpModel>,
    pub(in crate::executor) string: Option<StringModel>,
    pub(in crate::executor) seq: Option<SeqModel>,
}

/// Structured LIA preprocessing output for the incremental path.
pub(in crate::executor) struct LiaPreprocessArtifacts {
    pub(in crate::executor) assertions: Vec<TermId>,
    pub(in crate::executor) var_subst: VariableSubstitution,
    pub(in crate::executor) assertion_sources: HashMap<TermId, Vec<Vec<TermId>>>,
}

/// Structured output from LIA assumption preprocessing (#6728).
pub(in crate::executor) struct LiaAssumptionPreprocessResult {
    /// Additional constraint assertions from mod/div elimination of assumptions.
    pub(in crate::executor) extra_assertions: Vec<TermId>,
    /// Preprocessed assumptions as `(preprocessed, original)` pairs.
    pub(in crate::executor) assumptions: Vec<(TermId, TermId)>,
}

/// Structured output from mixed arithmetic assumption preprocessing (#6737).
///
/// Bundles the preprocessed assertions, preprocessed `(rewritten, original)`
/// assumption pairs, and the `VariableSubstitution` needed for model recovery.
pub(in crate::executor) struct MixedArithAssumptionArtifacts {
    pub(in crate::executor) assertions: Vec<TermId>,
    pub(in crate::executor) assumptions: Vec<(TermId, TermId)>,
    pub(in crate::executor) var_subst: VariableSubstitution,
    pub(in crate::executor) assertion_sources: HashMap<TermId, Vec<Vec<TermId>>>,
}

/// Proof-facing provenance for temporary combined-theory assertion windows.
///
/// `problem_assertions` lists the temporary assertions that should still export
/// as original-problem premises. `assertion_sources` records which original
/// assertions justify each temporary term so proof rewriting can recover the
/// parsed surface syntax. Purely derived constraints (array axioms, mod/div aux
/// constraints, propagation-only consequences) are intentionally omitted.
#[derive(Clone, Default)]
pub(in crate::executor) struct ProofProblemAssertionProvenance {
    pub(in crate::executor) original_problem_assertions: Vec<TermId>,
    pub(in crate::executor) problem_assertions: Vec<TermId>,
    pub(in crate::executor) assertion_sources: HashMap<TermId, Vec<Vec<TermId>>>,
}

impl Executor {
    /// Preprocess LIA assertions with provenance for incremental scope handling.
    pub(in crate::executor) fn preprocess_lia_artifacts(&mut self) -> LiaPreprocessArtifacts {
        let flattened = flatten_assertions_with_sources(&self.ctx.terms, &self.ctx.assertions);
        let original_flattened: Vec<TermId> = flattened.iter().map(|(term, _)| *term).collect();
        let mut assertions = original_flattened.clone();
        let mut source_sets: Vec<Vec<TermId>> =
            flattened.into_iter().map(|(_, sources)| sources).collect();

        let mut var_subst = VariableSubstitution::new();
        let var_subst_changed = var_subst.apply(&mut self.ctx.terms, &mut assertions);
        augment_lia_source_sets_with_substitutions(
            &self.ctx.terms,
            &original_flattened,
            &mut source_sets,
            &var_subst,
        );

        if var_subst_changed {
            let mut reflattened = Vec::new();
            for (&assertion, source_set) in assertions.iter().zip(source_sets.iter()) {
                flatten_assertion_with_source(
                    &self.ctx.terms,
                    assertion,
                    source_set,
                    &mut reflattened,
                );
            }
            assertions = reflattened.iter().map(|(term, _)| *term).collect();
            source_sets = reflattened
                .into_iter()
                .map(|(_, sources)| sources)
                .collect();
        }

        // SOM normalization: distribute multiplication over addition (#4919).
        let mut som_pass = NormalizeArithSom::new();
        som_pass.apply(&mut self.ctx.terms, &mut assertions);

        // Lift ITEs from arithmetic expressions before Tseitin (fixes #297)
        let lifted = self.ctx.terms.lift_arithmetic_ite_all(&assertions);

        let mut preprocessed = Vec::new();
        let mut assertion_sources: HashMap<TermId, Vec<Vec<TermId>>> = HashMap::new();
        for (&assertion, source_set) in lifted.iter().zip(source_sets.iter()) {
            let mut normalized_sources = source_set.clone();
            normalized_sources.sort_by_key(|term| term.index());
            normalized_sources.dedup();

            let mod_elim = eliminate_int_mod_div_by_constant(&mut self.ctx.terms, &[assertion]);
            for derived in mod_elim
                .constraints
                .into_iter()
                .chain(mod_elim.rewritten.into_iter())
            {
                preprocessed.push(derived);
                let entry = assertion_sources.entry(derived).or_default();
                if !entry.contains(&normalized_sources) {
                    entry.push(normalized_sources.clone());
                }
            }
        }

        LiaPreprocessArtifacts {
            assertions: preprocessed,
            var_subst,
            assertion_sources,
        }
    }

    /// Preprocess LIA assumptions through the same normalization family as assertions (#6728).
    ///
    /// Applies the assertion-derived `VariableSubstitution` to each assumption,
    /// then runs SOM normalization, ITE lifting, and mod/div elimination.
    /// Returns `(preprocessed, original)` pairs plus any extra constraint assertions
    /// generated by mod/div elimination.
    pub(in crate::executor) fn preprocess_lia_assumptions(
        &mut self,
        assumptions: &[TermId],
        var_subst: &mut VariableSubstitution,
    ) -> LiaAssumptionPreprocessResult {
        let mut extra_assertions = Vec::new();
        let mut result_assumptions = Vec::new();

        for &original in assumptions {
            // Apply assertion-derived substitutions (e.g., y -> (+ x 1))
            let substituted = var_subst.apply_to_term(&mut self.ctx.terms, original);

            // SOM normalization
            let mut som_terms = vec![substituted];
            let mut som_pass = NormalizeArithSom::new();
            som_pass.apply(&mut self.ctx.terms, &mut som_terms);
            let normalized = som_terms[0];

            // ITE lifting
            let lifted = self.ctx.terms.lift_arithmetic_ite(normalized);

            // mod/div elimination: constraints define aux vars (permanent),
            // rewritten term is the preprocessed assumption (temporary)
            let mod_elim = eliminate_int_mod_div_by_constant(&mut self.ctx.terms, &[lifted]);
            extra_assertions.extend(mod_elim.constraints);
            let final_assumption = mod_elim.rewritten.into_iter().next().unwrap_or(lifted);

            result_assumptions.push((final_assumption, original));
        }

        LiaAssumptionPreprocessResult {
            extra_assertions,
            assumptions: result_assumptions,
        }
    }

    /// Preprocess mixed arithmetic assumptions through the full LIA normalization
    /// family (#6737).
    ///
    /// Wrapper around [`preprocess_lia_artifacts`] + [`preprocess_lia_assumptions`]
    /// for combined-theory assumption routes (LIRA, AUFLIA, AUFLIRA). Temporarily
    /// replaces `self.ctx.assertions` with the provided slice to reuse the same
    /// preprocessing pipeline that dedicated QF_LIA uses.
    pub(in crate::executor) fn preprocess_mixed_arith_assumptions(
        &mut self,
        assertions: &[TermId],
        assumptions: &[TermId],
    ) -> MixedArithAssumptionArtifacts {
        // Temporarily install the caller's assertions for preprocess_lia_artifacts()
        let saved_assertions = std::mem::replace(&mut self.ctx.assertions, assertions.to_vec());

        let mut artifacts = self.preprocess_lia_artifacts();

        // Restore original assertions
        self.ctx.assertions = saved_assertions;

        // Preprocess assumptions using the assertion-derived substitution
        let assume_result = self.preprocess_lia_assumptions(assumptions, &mut artifacts.var_subst);

        // Merge constraint assertions from mod/div elimination of assumptions
        artifacts.assertions.extend(assume_result.extra_assertions);

        MixedArithAssumptionArtifacts {
            assertions: artifacts.assertions,
            assumptions: assume_result.assumptions,
            var_subst: artifacts.var_subst,
            assertion_sources: artifacts.assertion_sources,
        }
    }

    /// Preprocess mod/div-only combined assertions with proof-premise provenance.
    ///
    /// Rewritten assertions inherit the original assertion as a proof source.
    /// Auxiliary quotient/remainder constraints are derived-only and therefore
    /// excluded from problem-scope provenance.
    pub(in crate::executor) fn preprocess_mod_div_assertions_with_proof_provenance(
        &mut self,
        assertions: &[TermId],
    ) -> (Vec<TermId>, ProofProblemAssertionProvenance) {
        let mut preprocessed = Vec::new();
        let mut assertion_sources = HashMap::new();
        for &assertion in assertions {
            let mod_elim = eliminate_int_mod_div_by_constant(&mut self.ctx.terms, &[assertion]);
            preprocessed.extend(mod_elim.constraints);
            for rewritten in mod_elim.rewritten {
                preprocessed.push(rewritten);
                push_assertion_source_set(&mut assertion_sources, rewritten, vec![assertion]);
            }
        }
        let provenance = ProofProblemAssertionProvenance::from_sources(
            assertions.to_vec(),
            &preprocessed,
            assertion_sources,
        );
        (preprocessed, provenance)
    }

    /// Build AUFLIA's temporary assertion window together with proof provenance.
    ///
    /// This is conservative around `PropagateValues`: if the pass rewrites an
    /// assertion, we drop provenance for that assertion because it may now
    /// depend on multiple source assertions. Provenance is preserved only for
    /// transformations whose source identity remains explicit.
    pub(in crate::executor) fn preprocess_auflia_assertions_with_proof_provenance(
        &mut self,
    ) -> (Vec<TermId>, ProofProblemAssertionProvenance) {
        let original_assertions = self.ctx.assertions.clone();
        let flattened = flatten_assertions_with_sources(&self.ctx.terms, &original_assertions);
        let mut preprocessed_assertions = Vec::new();
        let mut source_sets: Vec<Option<Vec<Vec<TermId>>>> = Vec::new();

        for (assertion, sources) in flattened {
            let mut normalized_sources = sources;
            normalized_sources.sort_by_key(|term| term.index());
            normalized_sources.dedup();

            let mod_elim = eliminate_int_mod_div_by_constant(&mut self.ctx.terms, &[assertion]);
            let constraint_count = mod_elim.constraints.len();
            preprocessed_assertions.extend(mod_elim.constraints);
            source_sets.extend(std::iter::repeat_with(|| None).take(constraint_count));
            for rewritten in mod_elim.rewritten {
                preprocessed_assertions.push(rewritten);
                source_sets.push(Some(vec![normalized_sources.clone()]));
            }
        }

        // #7024: Do NOT apply substitute_store_flat_equalities in the AUFLIA
        // preprocessor. The AUFLIA path uses with_deferred_postprocessing, which
        // restores the original (unsubstituted) assertions before model validation.
        // Store-flat substitution removes defining equalities like (= v (store w i 1)),
        // so the inner solve never builds array model entries for those variables.
        // The outer model validator then cannot evaluate the original assertions and
        // degrades SAT to Unknown.
        //
        // The substitution remains in solve_array_euf() (euf.rs) where it works
        // because that path does not use deferred postprocessing — validation runs
        // on the substituted assertions directly.

        let saved_assertions =
            std::mem::replace(&mut self.ctx.assertions, preprocessed_assertions.clone());
        let axiom_start = self.ctx.assertions.len();
        self.run_array_axiom_fixpoint_at(
            axiom_start,
            super::euf::ArrayAxiomMode::LazyRow2FinalCheck,
        );
        let generated_axioms: Vec<_> = self.ctx.assertions.drain(axiom_start..).collect();
        self.ctx.assertions = saved_assertions;
        let generated_axioms = self.ctx.terms.expand_select_store_all(&generated_axioms);
        preprocessed_assertions.extend(generated_axioms.iter().copied());
        source_sets.extend(std::iter::repeat_with(|| None).take(generated_axioms.len()));

        let mut flatten = crate::preprocess::FlattenAnd::new();
        let mut propagate = crate::preprocess::PropagateValues::new();
        for _ in 0..100 {
            let flattened_pass = flatten_assertions_with_optional_sources(
                &self.ctx.terms,
                &preprocessed_assertions,
                &source_sets,
            );
            let before_propagate: Vec<TermId> =
                flattened_pass.iter().map(|(term, _)| *term).collect();
            let mut flattened_sources: Vec<Option<Vec<Vec<TermId>>>> = flattened_pass
                .into_iter()
                .map(|(_, sources)| sources)
                .collect();
            preprocessed_assertions = before_propagate;

            let f = flatten.apply(&mut self.ctx.terms, &mut preprocessed_assertions);
            debug_assert!(
                !f,
                "FlattenAnd provenance helper must mirror structural flattening before pass application"
            );

            let before_values = preprocessed_assertions.clone();
            let p = propagate.apply(&mut self.ctx.terms, &mut preprocessed_assertions);
            if p {
                for (slot, (before, after)) in flattened_sources
                    .iter_mut()
                    .zip(before_values.iter().zip(preprocessed_assertions.iter()))
                {
                    if before != after {
                        *slot = None;
                    }
                }
            }

            source_sets = flattened_sources;

            if !p {
                break;
            }
            flatten.reset();
            propagate.reset();
        }

        let lifted = self
            .ctx
            .terms
            .lift_arithmetic_ite_all(&preprocessed_assertions);
        preprocessed_assertions = lifted;

        let mut assertion_sources = HashMap::new();
        for (&assertion, maybe_sources) in preprocessed_assertions.iter().zip(source_sets.iter()) {
            let Some(source_sets) = maybe_sources else {
                continue;
            };
            for source_set in source_sets {
                push_assertion_source_set(&mut assertion_sources, assertion, source_set.clone());
            }
        }

        let provenance = ProofProblemAssertionProvenance::from_sources(
            original_assertions,
            &preprocessed_assertions,
            assertion_sources,
        );
        (preprocessed_assertions, provenance)
    }
}

impl ProofProblemAssertionProvenance {
    pub(in crate::executor) fn from_sources(
        original_problem_assertions: Vec<TermId>,
        temporary_assertions: &[TermId],
        assertion_sources: HashMap<TermId, Vec<Vec<TermId>>>,
    ) -> Self {
        let original_problem_set: HashSet<TermId> =
            original_problem_assertions.iter().copied().collect();
        let problem_assertions = temporary_assertions
            .iter()
            .copied()
            .filter(|assertion| {
                original_problem_set.contains(assertion)
                    && assertion_sources.contains_key(assertion)
            })
            .collect();
        Self {
            original_problem_assertions,
            problem_assertions,
            assertion_sources,
        }
    }

    /// Identity provenance for routes whose temporary assertion window
    /// consists of the original assertions plus purely derived constraints
    /// (e.g., generated array axioms).
    ///
    /// Each original assertion maps to itself as its sole source. Derived
    /// constraints are left unmapped so the proof bootstrap registers them
    /// as unlabeled Assumes (proof-visible but not exportable premises).
    pub(in crate::executor) fn passthrough(
        original_problem_assertions: &[TermId],
        temporary_assertions: &[TermId],
    ) -> Self {
        let mut assertion_sources = HashMap::new();
        for &assertion in original_problem_assertions {
            assertion_sources.insert(assertion, vec![vec![assertion]]);
        }
        Self::from_sources(
            original_problem_assertions.to_vec(),
            temporary_assertions,
            assertion_sources,
        )
    }
}

// Assertion flattening, store-flat substitution, and proof source tracking
// helpers are in solve_harness_helpers.rs.
use super::solve_harness_helpers::{
    augment_lia_source_sets_with_substitutions, flatten_assertion_with_source,
    flatten_assertions_with_optional_sources, flatten_assertions_with_sources,
    push_assertion_source_set,
};

// Re-export substitute_store_flat_equalities so `euf/array_fixpoint.rs` can use
// `super::super::solve_harness::substitute_store_flat_equalities`.
pub(super) use super::solve_harness_helpers::substitute_store_flat_equalities;

mod split_atoms;
pub(in crate::executor) use split_atoms::{
    check_split_oscillation, create_disequality_split_atoms, create_int_split_atoms,
    DisequalitySplitAtoms, SplitOscillationMap,
};

#[allow(clippy::panic)]
#[cfg(test)]
mod tests;
