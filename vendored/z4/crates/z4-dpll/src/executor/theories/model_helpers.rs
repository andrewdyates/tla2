// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model storage and proof building helpers.

#[cfg(not(kani))]
use hashbrown::HashMap;
use z4_arrays::ArrayModel;
use z4_bv::BvModel;
#[cfg(kani)]
use z4_core::kani_compat::DetHashMap as HashMap;
use z4_core::term::{Constant, TermData};
use z4_core::{Sort, TermId, TseitinResult};
use z4_euf::EufModel;
use z4_fp::FpModel;
use z4_lia::LiaModel;
use z4_lra::LraModel;
use z4_sat::{SatResult, SatUnknownReason};
use z4_strings::StringModel;

use crate::executor_types::{Result, SolveResult, UnknownReason};

use super::super::model::Model;
use super::super::Executor;

impl Executor {
    /// Record SAT-side `Unknown` reason if one was reported by z4-sat.
    ///
    /// Takes a mutable reference to the `last_unknown_reason` field directly
    /// (rather than `&mut self`) so callers can invoke this while other fields
    /// of `Executor` (e.g. `ctx.terms`) are borrowed by a `DpllT` instance.
    pub(in crate::executor) fn record_sat_unknown_reason(
        target: &mut Option<UnknownReason>,
        reason: Option<SatUnknownReason>,
    ) {
        if let Some(reason) = reason {
            *target = Some(Self::map_sat_unknown_reason(reason));
        }
    }

    pub(in crate::executor) fn map_sat_unknown_reason(reason: SatUnknownReason) -> UnknownReason {
        match reason {
            SatUnknownReason::Interrupted => UnknownReason::Interrupted,
            SatUnknownReason::TheoryStop | SatUnknownReason::ExtensionUnknown => {
                UnknownReason::Incomplete
            }
            SatUnknownReason::UnsupportedConfig => UnknownReason::Unsupported,
            SatUnknownReason::EmptyTheoryConflict
            | SatUnknownReason::Unspecified
            | SatUnknownReason::AssumptionUnknown
            | SatUnknownReason::InvalidSatModel => UnknownReason::Unknown,
            #[allow(unreachable_patterns)]
            _ => UnknownReason::Unknown,
        }
    }

    /// Process solve result and store model if SAT
    pub(in crate::executor) fn solve_and_store_model(
        &mut self,
        result: SatResult,
        tseitin_result: &TseitinResult,
        euf_model: Option<EufModel>,
        array_model: Option<ArrayModel>,
    ) -> Result<SolveResult> {
        self.solve_and_store_model_full(
            result,
            tseitin_result,
            euf_model,
            array_model,
            None,
            None,
            None,
            None,
            None,
            None,
        )
    }

    /// Process solve result and store model if SAT, taking a `TheoryModels`
    /// struct instead of individual model parameters.
    ///
    /// This is the preferred call site for pipeline macros — it avoids the
    /// 8-argument field-by-field expansion at every return point.
    pub(in crate::executor) fn solve_and_store_model_with_theories(
        &mut self,
        result: SatResult,
        tseitin_result: &TseitinResult,
        models: super::solve_harness::TheoryModels,
    ) -> Result<SolveResult> {
        self.solve_and_store_model_full(
            result,
            tseitin_result,
            models.euf,
            models.array,
            models.lra,
            models.lia,
            models.bv,
            models.fp,
            models.string,
            models.seq,
        )
    }

    /// Process solve result and store model if SAT (with all theory models)
    #[allow(clippy::too_many_arguments)]
    pub(in crate::executor) fn solve_and_store_model_full(
        &mut self,
        result: SatResult,
        tseitin_result: &TseitinResult,
        euf_model: Option<EufModel>,
        array_model: Option<ArrayModel>,
        lra_model: Option<LraModel>,
        lia_model: Option<LiaModel>,
        bv_model: Option<BvModel>,
        fp_model: Option<FpModel>,
        string_model: Option<StringModel>,
        seq_model: Option<z4_seq::SeqModel>,
    ) -> Result<SolveResult> {
        // Tseitin var_to_term must be consistent with term_to_var (#4661)
        debug_assert_eq!(
            tseitin_result.var_to_term.len(),
            tseitin_result.term_to_var.len(),
            "BUG: Tseitin var_to_term ({}) and term_to_var ({}) have different sizes",
            tseitin_result.var_to_term.len(),
            tseitin_result.term_to_var.len()
        );

        match result {
            SatResult::Sat(model) => {
                // SAT model must be non-empty when assertions exist (#4714)
                debug_assert!(
                    !model.is_empty() || self.ctx.assertions.is_empty(),
                    "SAT result has empty model but {} assertions exist",
                    self.ctx.assertions.len()
                );

                // Store the model with mappings (convert from 1-indexed CNF vars to 0-indexed)
                let term_to_var: HashMap<TermId, u32> = tseitin_result
                    .term_to_var
                    .iter()
                    .map(|(&t, &v)| (t, v - 1))
                    .collect();

                // All mapped vars must be valid model indices (#4714)
                debug_assert!(
                    term_to_var.values().all(|&v| (v as usize) < model.len()),
                    "term_to_var contains index {} but model has only {} vars",
                    term_to_var.values().max().unwrap_or(&0),
                    model.len()
                );

                // Store the model first with original values
                self.last_model = Some(Model {
                    sat_model: model,
                    term_to_var,
                    euf_model,
                    array_model,
                    lra_model,
                    lia_model,
                    bv_model,
                    fp_model,
                    string_model,
                    seq_model,
                });

                // SAT-preserving minimization: try smaller values for each
                // variable and keep only those that pass assertion re-evaluation.
                // Skip when assumptions are active: minimization only checks
                // permanent assertions, not assumptions, so it can produce models
                // that violate assumption constraints (#5121).
                if self.minimize_counterexamples_enabled()
                    && self.last_assumptions.is_none()
                    && !self.defer_counterexample_minimization
                {
                    self.minimize_model_sat_preserving();
                }

                // Soundness guard for known string tautology patterns that should
                // never appear as SAT when negated.
                if self.has_negated_string_equivalence_tautology() {
                    self.last_model = None;
                    self.last_result = Some(SolveResult::Unknown);
                    return Ok(SolveResult::Unknown);
                }
                self.pending_sat_unknown_reason = None;
                self.last_result = Some(SolveResult::Sat);
                debug_assert!(
                    self.last_model.is_some(),
                    "BUG: SAT result must populate last_model before finalize_sat_model_validation"
                );
                self.finalize_sat_model_validation()
            }
            SatResult::Unsat => {
                // Build proof if proof production is enabled
                if self.produce_proofs_enabled() {
                    self.build_unsat_proof();
                    debug_assert!(
                        self.last_proof.is_some(),
                        "BUG: UNSAT with proofs enabled but build_unsat_proof did not populate last_proof"
                    );
                }
                self.pending_sat_unknown_reason = None;
                self.last_result = Some(SolveResult::Unsat);
                Ok(SolveResult::Unsat)
            }
            SatResult::Unknown => {
                // Map SAT-level unknown reason to DPLL-level reason if the
                // theory executor hasn't already set one (#4622).
                if self.last_unknown_reason.is_none() {
                    if let Some(sat_reason) = self.pending_sat_unknown_reason.take() {
                        self.last_unknown_reason = Some(Self::map_sat_unknown_reason(sat_reason));
                    } else {
                        self.last_unknown_reason = Some(UnknownReason::Incomplete);
                    }
                }
                self.last_result = Some(SolveResult::Unknown);
                Ok(SolveResult::Unknown)
            }
            #[allow(unreachable_patterns)]
            _ => unreachable!("BUG: SatResult variant not handled in check_sat dispatch"),
        }
    }

    // Proof functions moved to executor/proof.rs

    // get_info, format_statistics_smt2, get_option_value, get_assertions,
    // simplify, format_term moved to executor/commands.rs

    /// Detect `(not (= A B))` where `A` and `B` are structurally equivalent
    /// Boolean string predicates/equalities. These formulas are UNSAT by
    /// string semantics; returning SAT here is unsound.
    pub(super) fn has_negated_string_equivalence_tautology(&self) -> bool {
        if self.bypass_string_tautology_guard {
            return false;
        }
        self.ctx
            .assertions
            .iter()
            .any(|&a| self.is_negated_string_equivalence_tautology(a))
    }

    fn is_negated_string_equivalence_tautology(&self, assertion: TermId) -> bool {
        // Pattern 1: (not (= A B)) — direct negated equality.
        if let TermData::Not(inner) = self.ctx.terms.get(assertion) {
            if let TermData::App(sym, args) = self.ctx.terms.get(*inner) {
                if sym.name() == "="
                    && args.len() == 2
                    && *self.ctx.terms.sort(args[0]) == Sort::Bool
                    && *self.ctx.terms.sort(args[1]) == Sort::Bool
                    && self.bool_terms_structurally_equivalent(args[0], args[1])
                {
                    return true;
                }
            }
        }
        // Pattern 2: (ite A (not B) B) — term store may rewrite
        // (not (= A B)) into ITE form for Boolean sorts (#6688).
        if let TermData::Ite(cond, then_br, else_br) = self.ctx.terms.get(assertion) {
            if *self.ctx.terms.sort(*cond) == Sort::Bool
                && *self.ctx.terms.sort(*else_br) == Sort::Bool
            {
                // Check: then_br = (not else_br), i.e., (ite A (not B) B)
                if let TermData::Not(neg_inner) = self.ctx.terms.get(*then_br) {
                    if *neg_inner == *else_br {
                        return self.bool_terms_structurally_equivalent(*cond, *else_br);
                    }
                }
                // Also check: (ite A B (not B)) which is (= A B) — but as
                // a top-level assertion this is NOT a negated tautology.
                // And: (ite (not A) B (not B)) ≡ (not (= A B))
                if let TermData::Not(neg_cond) = self.ctx.terms.get(*cond) {
                    if let TermData::Not(neg_else) = self.ctx.terms.get(*else_br) {
                        if *neg_else == *then_br {
                            // (ite (not A) B (not B)) ≡ (not (= A B))
                            return self.bool_terms_structurally_equivalent(*neg_cond, *then_br);
                        }
                    }
                }
            }
        }
        false
    }

    /// Structural Boolean equivalence checks for string rewrite tautologies.
    fn bool_terms_structurally_equivalent(&self, lhs: TermId, rhs: TermId) -> bool {
        self.contains_equivalent_to_string_equality_term(lhs, rhs)
            || self.contains_equivalent_to_string_equality_term(rhs, lhs)
            || self.self_concat_equalities_equivalent_term(lhs, rhs)
    }

    /// Check equivalence: `str.contains(h, n)` ↔ `(= h n)` for structural cases.
    fn contains_equivalent_to_string_equality_term(
        &self,
        contains_term: TermId,
        eq_term: TermId,
    ) -> bool {
        let TermData::App(c_sym, c_args) = self.ctx.terms.get(contains_term) else {
            return false;
        };
        if c_sym.name() != "str.contains" || c_args.len() != 2 {
            return false;
        }
        let h = c_args[0];
        let n = c_args[1];

        let TermData::App(eq_sym, eq_args) = self.ctx.terms.get(eq_term) else {
            return false;
        };
        if eq_sym.name() != "=" || eq_args.len() != 2 {
            return false;
        }

        let eq_matches =
            (eq_args[0] == h && eq_args[1] == n) || (eq_args[1] == h && eq_args[0] == n);
        if !eq_matches {
            return false;
        }

        self.contains_has_equality_semantics_term(h, n)
    }

    /// Whether `str.contains(h, n)` is structurally equivalent to `h = n`.
    fn contains_has_equality_semantics_term(&self, h: TermId, n: TermId) -> bool {
        if h == n {
            return true;
        }
        if matches!(
            self.ctx.terms.get(h),
            TermData::Const(Constant::String(s)) if s.is_empty()
        ) {
            return true;
        }

        let mut components = Vec::new();
        self.flatten_concat_term(n, &mut components);
        components.len() >= 2 && components.contains(&h)
    }

    /// Check equivalence of self-concat equalities:
    /// `(= x (str.++ y x))` and `(= x (str.++ x y))`.
    fn self_concat_equalities_equivalent_term(&self, lhs: TermId, rhs: TermId) -> bool {
        let Some((lx, ly)) = self.extract_self_concat_pair_term(lhs) else {
            return false;
        };
        let Some((rx, ry)) = self.extract_self_concat_pair_term(rhs) else {
            return false;
        };
        lx == rx && ly == ry
    }

    /// Extract `(x, y)` from equality `x = str.++(x, y)` or `x = str.++(y, x)`.
    fn extract_self_concat_pair_term(&self, term: TermId) -> Option<(TermId, TermId)> {
        let TermData::App(eq_sym, eq_args) = self.ctx.terms.get(term) else {
            return None;
        };
        if eq_sym.name() != "=" || eq_args.len() != 2 {
            return None;
        }
        if *self.ctx.terms.sort(eq_args[0]) != Sort::String
            || *self.ctx.terms.sort(eq_args[1]) != Sort::String
        {
            return None;
        }

        for &(x, other) in &[(eq_args[0], eq_args[1]), (eq_args[1], eq_args[0])] {
            let mut components = Vec::new();
            self.flatten_concat_term(other, &mut components);
            if components.len() != 2 {
                continue;
            }
            if components[0] == x {
                return Some((x, components[1]));
            }
            if components[1] == x {
                return Some((x, components[0]));
            }
        }
        None
    }

    /// Flatten a concat term into syntactic leaf components.
    fn flatten_concat_term(&self, term: TermId, out: &mut Vec<TermId>) {
        let TermData::App(sym, args) = self.ctx.terms.get(term) else {
            out.push(term);
            return;
        };
        if sym.name() != "str.++" {
            out.push(term);
            return;
        }
        for &arg in args {
            self.flatten_concat_term(arg, out);
        }
    }
}

#[cfg(test)]
#[path = "model_helpers_tests.rs"]
mod tests;
