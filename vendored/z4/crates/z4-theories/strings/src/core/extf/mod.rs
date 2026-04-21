// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Extended function checking for the string core solver.
//
// Top-level check pipelines: check_extf_predicates, check_extf_reductions,
// simplify_singleton_concats, and check_extf_int_reductions.
//
// Reference: `reference/cvc5/src/theory/strings/core_solver.cpp`
// Reference: `reference/cvc5/src/theory/strings/ext_theory.cpp`

mod effort1;
mod eval;
mod util;

use z4_core::{Sort, TermData, TermId, TermStore};

use crate::infer::{InferenceKind, InferenceManager};
use crate::state::SolverState;

use super::{CoreSolver, DEBUG_STRING_CORE};

impl CoreSolver {
    /// Phase C soundness bridge: if a predicate atom (for example,
    /// `str.contains(x, "abc")`) has arguments that resolve to concrete strings
    /// via EQC constants, evaluate it and detect truth-value contradictions.
    pub(super) fn check_extf_predicates(
        &mut self,
        terms: &TermStore,
        state: &SolverState,
        infer: &mut InferenceManager,
    ) -> bool {
        for &lit in state.assertions() {
            let (atom, expected) = Self::atom_and_polarity(terms, lit);

            if !Self::is_extf_predicate_atom(terms, atom) {
                continue;
            }
            if self.reduced_terms.contains(&atom) {
                continue;
            }

            let Some(actual) = Self::eval_extf_predicate(terms, state, atom) else {
                // CTN_LEN_INEQ_NSTRICT: for positive str.contains(x, needle)
                // where needle structurally contains x, infer that extra
                // components must be empty. len(needle) >= len(x) always holds,
                // so contains(x, needle) ⇒ x = needle ⇒ extra = "".
                // CVC5 reference: strings_entail.cpp:945 inferEqsFromContains
                if expected {
                    Self::infer_eqs_from_contains(terms, state, atom, lit, infer);
                    // CTN_LHS_EMPTYSTR: str.contains("", x) → x = "".
                    // The empty string only contains the empty string.
                    // CVC5 reference: core_solver.cpp checkCycles + strings_entail.cpp
                    Self::infer_contains_empty_haystack(terms, state, atom, lit, infer);
                }

                // Unsupported symbolic predicate reasoning must not produce SAT
                // in cases where the asserted polarity could hide unsat cores.
                if Self::unresolved_predicate_requires_unknown(terms, atom, expected) {
                    self.incomplete = true;
                }
                continue;
            };

            if actual != expected {
                // Explanation: the assertion itself + why each argument
                // resolved to its representative constant.
                let mut explanation = vec![lit];
                Self::add_arg_resolution_explanations(terms, state, atom, &mut explanation);
                if *DEBUG_STRING_CORE {
                    let atom_name = match terms.get(atom) {
                        TermData::App(sym, _) => sym.name(),
                        _ => "<non-app>",
                    };
                    let arg_debug = match terms.get(atom) {
                        TermData::App(_, args) if args.len() >= 2 => format!(
                            "args=({:?}, {:?}) data=({:?}, {:?}) direct=({:?}, {:?})",
                            args[0],
                            args[1],
                            terms.get(args[0]),
                            terms.get(args[1]),
                            Self::resolve_string_term(terms, state, args[0], 0),
                            Self::resolve_string_term(terms, state, args[1], 0)
                        ),
                        TermData::App(_, args) if args.len() == 1 => format!(
                            "arg={:?} direct={:?}",
                            args[0],
                            Self::resolve_string_term(terms, state, args[0], 0)
                        ),
                        _ => String::from("args=<n/a>"),
                    };
                    eprintln!(
                        "[STRING_CORE] check_extf_predicates conflict: lit={:?} atom={:?} ({}) expected={} actual={} {} expl_len={} expl={:?}",
                        lit,
                        atom,
                        atom_name,
                        expected,
                        actual,
                        arg_debug,
                        explanation.len(),
                        explanation
                    );
                    let expl_terms: Vec<String> = explanation
                        .iter()
                        .map(|l| format!("{:?} => {:?}", l, terms.get(l.term)))
                        .collect();
                    eprintln!(
                        "[STRING_CORE] check_extf_predicates conflict expl_terms={expl_terms:?}"
                    );
                }
                infer.add_conflict(InferenceKind::PredicateConflict, explanation);
                return true;
            }
        }

        infer.has_conflict()
    }

    /// Evaluate value-returning extf applications and check for EQC constant conflicts.
    ///
    /// For each EQC that has a known string constant, check if any member is a
    /// reducible function application (str.at, str.substr, str.replace) whose
    /// evaluated result differs from the EQC constant. This detects conflicts like:
    ///   str.at("hello", 0) = "e"  → evaluated "h" ≠ EQC constant "e" → conflict.
    ///
    /// Reference: CVC5 ExtfSolver::checkExtfReductions
    pub(super) fn check_extf_reductions(
        &mut self,
        terms: &TermStore,
        state: &SolverState,
        infer: &mut InferenceManager,
    ) -> bool {
        let reps = state.eqc_representatives();

        // Pass 1: For EQCs with a known constant, check that any reducible member
        // evaluates to the same constant (conflict detection).
        for &rep in &reps {
            let eqc = match state.get_eqc(&rep) {
                Some(eqc) => eqc,
                None => continue,
            };

            let eqc_const = match &eqc.constant {
                Some(c) => c.clone(),
                None => continue,
            };

            for &member in &eqc.members {
                if self.reduced_terms.contains(&member) {
                    // Soundness (#6715): Even for reduced terms, verify value
                    // consistency when the EQC has a constant. Structural
                    // decomposition lemmas constrain lengths/concatenation but
                    // do NOT propagate string content values through skolems.
                    if let Some(ref reduced) = Self::try_reduce_string_term(terms, state, member) {
                        if *reduced != eqc_const {
                            if *DEBUG_STRING_CORE {
                                eprintln!(
                                    "[STRING_CORE] check_extf_reductions conflict (reduced term): rep={:?} member={:?} data={:?} reduced={:?} eqc_const={:?}",
                                    rep, member, terms.get(member), reduced, eqc_const
                                );
                            }
                            let mut explanation = state.explain_or_all(member, rep);
                            if let Some(const_id) = state.find_constant_term_id_for_rep(terms, &rep)
                            {
                                explanation.extend(state.explain(const_id, rep));
                            }
                            Self::add_arg_resolution_explanations(
                                terms,
                                state,
                                member,
                                &mut explanation,
                            );
                            infer.add_conflict(InferenceKind::PredicateConflict, explanation);
                            return true;
                        }
                    }
                    continue;
                }
                if self.request_dynamic_extf_lemma(terms, member) {
                    continue;
                }
                let evaluated = Self::try_reduce_string_term(terms, state, member);
                if let Some(ref reduced) = evaluated {
                    if *reduced == eqc_const {
                        continue;
                    }
                    if *DEBUG_STRING_CORE {
                        eprintln!(
                            "[STRING_CORE] check_extf_reductions conflict: rep={:?} member={:?} data={:?} reduced={:?} eqc_const={:?}",
                            rep,
                            member,
                            terms.get(member),
                            reduced,
                            eqc_const
                        );
                    }
                    // Evaluated value differs from EQC constant → conflict.
                    // Explanation: why member is in this EQC + why the EQC
                    // has its constant + arg resolution for the reduction.
                    let mut explanation = state.explain_or_all(member, rep);
                    if let Some(const_id) = state.find_constant_term_id_for_rep(terms, &rep) {
                        explanation.extend(state.explain(const_id, rep));
                    }
                    Self::add_arg_resolution_explanations(terms, state, member, &mut explanation);
                    infer.add_conflict(InferenceKind::PredicateConflict, explanation);
                    return true;
                }

                if Self::is_reducible_string_app(terms, member)
                    && !self.reduced_terms.contains(&member)
                    && !self.request_dynamic_extf_lemma(terms, member)
                {
                    self.incomplete = true;
                }
            }
        }

        // Pass 2: For EQCs WITHOUT a constant, check if any reducible member
        // can be evaluated. If so, find the constant term for the reduced value
        // and assert an internal equality. This handles cases like
        // str.replace(y, y, "") reducing to "" before normal form computation.
        for &rep in &reps {
            let eqc = match state.get_eqc(&rep) {
                Some(eqc) => eqc,
                None => continue,
            };
            if eqc.constant.is_some() {
                continue; // Already handled in pass 1.
            }

            for &member in &eqc.members {
                if !Self::is_reducible_string_app(terms, member) {
                    continue;
                }
                // Skip terms that have DPLL-level reduction lemmas — their
                // semantics are captured by word equations + arithmetic.
                if self.reduced_terms.contains(&member) {
                    continue;
                }
                if self.request_dynamic_extf_lemma(terms, member) {
                    continue;
                }
                let Some(reduced) = Self::try_reduce_string_term(terms, state, member) else {
                    if !self.request_dynamic_extf_lemma(terms, member) {
                        self.incomplete = true;
                    }
                    continue;
                };
                // Find a registered constant term with this value.
                let const_term = Self::find_constant_term_for_value(terms, state, &reduced);
                if let Some(const_id) = const_term {
                    if state.find(member) != state.find(const_id) {
                        // Explanation: why each argument of member resolved
                        // to its current representative.
                        let mut explanation = Vec::new();
                        Self::add_arg_resolution_explanations(
                            terms,
                            state,
                            member,
                            &mut explanation,
                        );
                        // Ground extf evaluations (e.g., str.at("hello", 0) → "h")
                        // produce empty explanations because all arguments are
                        // constants that don't need EQC resolution. The
                        // merge_internal_equalities guard (#4057) skips merges
                        // with empty explanations. For ground evaluations, find
                        // an assertion that involves the extf's EQC as
                        // explanation — the assertion is the reason the extf
                        // term is relevant to the current SAT assignment.
                        if explanation.is_empty() {
                            let member_rep = state.find(member);
                            for &lit in state.assertions() {
                                let (atom, polarity) = Self::atom_and_polarity(terms, lit);
                                if !polarity {
                                    continue;
                                }
                                if let TermData::App(sym, args) = terms.get(atom) {
                                    if sym.name() == "=" && args.len() == 2 {
                                        let a_rep = state.find(args[0]);
                                        let b_rep = state.find(args[1]);
                                        if a_rep == member_rep || b_rep == member_rep {
                                            explanation.push(lit);
                                            break;
                                        }
                                    }
                                }
                            }
                        }
                        infer.add_internal_equality(
                            InferenceKind::Unify,
                            member,
                            const_id,
                            explanation,
                        );
                    }
                } else {
                    // Term reduces to a value but no matching constant exists
                    // in the state. Cannot merge; stay incomplete to avoid
                    // false SAT.
                    if !self.request_dynamic_extf_lemma(terms, member) {
                        self.incomplete = true;
                    }
                }
            }
        }

        if self.check_extf_string_equalities(terms, state, infer) {
            return true;
        }
        infer.has_conflict()
    }

    /// Simplify concat terms that reduce to a single non-empty child.
    ///
    /// After I_CYCLE and self-concat reasoning infer extras="", a concat like
    /// `str.++(x, y)` where `y=""` effectively equals `x`. This step infers
    /// that equality explicitly, breaking mutual NF dependency cycles (#3850).
    pub(super) fn simplify_singleton_concats(
        &self,
        terms: &TermStore,
        state: &SolverState,
        infer: &mut InferenceManager,
    ) -> bool {
        for rep in state.eqc_representatives() {
            let Some(eqc) = state.get_eqc(&rep) else {
                continue;
            };
            for &concat_term in &eqc.concat_terms {
                let Some(children) = state.get_concat_children(terms, concat_term) else {
                    continue;
                };

                let mut sole_child = None;
                let mut multi = false;
                for &child in children {
                    if !state.is_empty_string(terms, child) {
                        if sole_child.is_some() {
                            multi = true;
                            break;
                        }
                        sole_child = Some(child);
                    }
                }

                if multi {
                    continue;
                }

                let target = match sole_child {
                    Some(c) => c,
                    None => match state.empty_string_id() {
                        Some(eid) => eid,
                        None => continue,
                    },
                };

                if state.find(concat_term) != state.find(target) {
                    // Explain: concat_term = target because every sibling is
                    // empty. Collect explain(sibling, "") for each empty child.
                    let mut explanation = Vec::new();
                    if let Some(eid) = state.empty_string_id() {
                        for &child in children {
                            if Some(child) != sole_child {
                                explanation.extend(state.explain(child, eid));
                            }
                        }
                    }
                    if *DEBUG_STRING_CORE {
                        eprintln!(
                            "[STRING_CORE] simplify_singleton_concats: {:?} = {:?} (sole_child={:?}, explanation_len={})",
                            concat_term, target, sole_child, explanation.len()
                        );
                    }
                    infer.add_internal_equality(
                        InferenceKind::EndpointEq,
                        concat_term,
                        target,
                        explanation,
                    );
                }
            }
            if infer.has_conflict() {
                return true;
            }
        }
        infer.has_conflict()
    }

    /// Find a registered constant term with the given string value.
    ///
    /// Searches all EQCs for one whose constant matches `value`, then
    /// returns the actual constant TermId from that EQC.
    fn find_constant_term_for_value(
        terms: &TermStore,
        state: &SolverState,
        value: &str,
    ) -> Option<TermId> {
        // Fast path for empty string.
        if value.is_empty() {
            return state.empty_string_id();
        }
        // Slow path: scan EQCs for a matching constant.
        for rep in state.eqc_representatives() {
            if let Some(eqc) = state.get_eqc(&rep) {
                if eqc.constant.as_deref() == Some(value) {
                    return state.find_constant_term_id_for_rep(terms, &rep);
                }
            }
        }
        None
    }

    /// Evaluate asserted string equalities/disequalities involving extf apps.
    ///
    /// Unlike the EQC-constant scan above, this examines all asserted equality
    /// literals, including negated equalities where the extf app and constant are
    /// intentionally in different EQCs.
    fn check_extf_string_equalities(
        &mut self,
        terms: &TermStore,
        state: &SolverState,
        infer: &mut InferenceManager,
    ) -> bool {
        for &lit in state.assertions() {
            let (atom, equality_expected) = Self::atom_and_polarity(terms, lit);
            let TermData::App(eq_sym, eq_args) = terms.get(atom) else {
                continue;
            };
            if eq_sym.name() != "=" || eq_args.len() != 2 {
                continue;
            }

            let lhs = eq_args[0];
            let rhs = eq_args[1];
            if *terms.sort(lhs) != Sort::String || *terms.sort(rhs) != Sort::String {
                continue;
            }

            let lhs_extf = Self::is_reducible_string_app(terms, lhs);
            let rhs_extf = Self::is_reducible_string_app(terms, rhs);
            if !lhs_extf && !rhs_extf {
                continue;
            }
            if (lhs_extf && self.reduced_terms.contains(&lhs))
                || (rhs_extf && self.reduced_terms.contains(&rhs))
            {
                continue;
            }

            let lhs_value = Self::resolve_string_term(terms, state, lhs, 0);
            let rhs_value = Self::resolve_string_term(terms, state, rhs, 0);

            match (lhs_value.as_ref(), rhs_value.as_ref()) {
                (Some(lhs_eval), Some(rhs_eval)) => {
                    let actual = lhs_eval == rhs_eval;
                    if actual != equality_expected {
                        // The triggering assertion + argument resolution reasons.
                        let mut explanation = vec![lit];
                        // Explain why each extf argument resolves to its constant.
                        Self::add_arg_resolution_explanations(terms, state, lhs, &mut explanation);
                        Self::add_arg_resolution_explanations(terms, state, rhs, &mut explanation);
                        infer.add_conflict(InferenceKind::PredicateConflict, explanation);
                        return true;
                    }
                }
                _ => {
                    if !equality_expected
                        && ((lhs_extf && lhs_value.is_none()) || (rhs_extf && rhs_value.is_none()))
                    {
                        self.incomplete = true;
                    }
                }
            }
        }

        infer.has_conflict()
    }

    /// Evaluate integer-valued string functions and check for conflicts.
    ///
    /// For each asserted relation involving str.to_int, str.indexof, or
    /// str.to_code, evaluate if possible and compare against asserted
    /// integer values. Also detect impossible inequalities caused purely
    /// by function output ranges (e.g., str.to_int(x) < -2).
    pub(super) fn check_extf_int_reductions(
        &mut self,
        terms: &TermStore,
        state: &SolverState,
        infer: &mut InferenceManager,
    ) -> bool {
        for &lit in state.assertions() {
            let (atom, relation_expected) = Self::atom_and_polarity(terms, lit);
            let TermData::App(rel_sym, rel_args) = terms.get(atom) else {
                continue;
            };
            if rel_args.len() != 2 {
                continue;
            }

            match rel_sym.name() {
                "=" => {
                    // Try both orientations: f(x) = N and N = f(x).
                    for (func_side, const_side) in
                        [(rel_args[0], rel_args[1]), (rel_args[1], rel_args[0])]
                    {
                        if !Self::is_reducible_int_app(terms, func_side) {
                            continue;
                        }

                        let evaluated = Self::try_reduce_int_term(terms, state, func_side);
                        if let Some(ref reduced) = evaluated {
                            let rhs_value = Self::resolve_int_term(terms, state, const_side, 0);
                            if let Some(ref exp) = rhs_value {
                                let actual = reduced == exp;
                                if actual != relation_expected {
                                    if *DEBUG_STRING_CORE {
                                        // Show detailed resolution info to trace false conflicts.
                                        let func_args_info = if let TermData::App(sym, args) =
                                            terms.get(func_side)
                                        {
                                            let s_str = if !args.is_empty() {
                                                Self::resolve_string_term(terms, state, args[0], 0)
                                            } else {
                                                None
                                            };
                                            format!("{}(s={s_str:?},...)", sym.name())
                                        } else {
                                            "non-app".to_string()
                                        };
                                        let const_info = if let TermData::App(sym, _args) =
                                            terms.get(const_side)
                                        {
                                            let rep = state.find(const_side);
                                            format!("{}(rep={rep:?})", sym.name())
                                        } else {
                                            let crep = state.find(const_side);
                                            format!("const_rep={crep:?}")
                                        };
                                        eprintln!("[STRING_CORE] int_reduction conflict: func={func_args_info} reduced={reduced}, const={const_info} resolved={exp}, expected={relation_expected}, atom={atom:?}");
                                    }
                                    let mut explanation = vec![lit];
                                    Self::add_arg_resolution_explanations(
                                        terms,
                                        state,
                                        func_side,
                                        &mut explanation,
                                    );
                                    // Also explain the const_side's arg resolutions.
                                    // When const_side is str.len(x), resolve_int_term
                                    // resolves x via the string EQC.  If this resolution
                                    // path differs from the EQC constant path (line
                                    // 2900-2903), the explanation must include the string
                                    // EQC merge reasons for x in the const_side, not
                                    // just the func_side.
                                    Self::add_arg_resolution_explanations(
                                        terms,
                                        state,
                                        const_side,
                                        &mut explanation,
                                    );
                                    if *DEBUG_STRING_CORE {
                                        for elit in &explanation {
                                            let tdata = terms.get(elit.term);
                                            eprintln!(
                                                "[STRING_CORE]   expl lit: {:?} val={} term={:?}",
                                                elit.term, elit.value, tdata
                                            );
                                        }
                                    }
                                    infer.add_conflict(
                                        InferenceKind::PredicateConflict,
                                        explanation,
                                    );
                                    return true;
                                }
                            } else if !relation_expected {
                                // For negated equalities, unresolved RHS can hide a
                                // contradiction if it later resolves to the same value.
                                self.incomplete = true;
                            }
                        } else {
                            // Reducible int app exists but couldn't be reduced (argument
                            // not resolved).
                            if !relation_expected {
                                // Negated equalities always need incomplete: a negated
                                // equality like NOT(str.to_int(x) = 3) might hide a
                                // conflict if x later resolves to "3".
                                self.incomplete = true;
                            } else if Self::is_range_restricted_int_app(terms, func_side) {
                                // For positive equalities involving range-restricted
                                // functions (str.to_int, str.to_code, str.indexof),
                                // check if the asserted value is outside the valid
                                // range. If so, raise a conflict immediately.
                                // Otherwise, mark incomplete because the LIA solver
                                // treats these as uninterpreted and can't enforce the
                                // range constraint.
                                let rhs_value = Self::resolve_int_term(terms, state, const_side, 0);
                                if let Some(ref val) = rhs_value {
                                    if !Self::is_in_valid_range(terms, state, func_side, val) {
                                        let explanation = vec![lit];
                                        infer.add_conflict(
                                            InferenceKind::PredicateConflict,
                                            explanation,
                                        );
                                        return true;
                                    }
                                }
                                // Value is in valid range but can't verify — mark
                                // incomplete so we don't return false SAT.
                                self.incomplete = true;
                            }
                            // For positive equalities with non-range-restricted
                            // functions (none currently, but future-proofing), do NOT
                            // mark incomplete — the LIA solver handles consistency.
                        }
                    }
                }
                "<" | "<=" => {
                    // Try both orientations:
                    // - f(x) < N / f(x) <= N
                    // - N < f(x) / N <= f(x)  (normalized > / >=)
                    for (func_side, const_side, func_on_left) in [
                        (rel_args[0], rel_args[1], true),
                        (rel_args[1], rel_args[0], false),
                    ] {
                        if !Self::is_reducible_int_app(terms, func_side) {
                            continue;
                        }
                        let Some(relation) = Self::relation_for_int_app(
                            rel_sym.name(),
                            func_on_left,
                            relation_expected,
                        ) else {
                            continue;
                        };

                        let evaluated = Self::try_reduce_int_term(terms, state, func_side);
                        let Some(bound) = Self::resolve_int_term(terms, state, const_side, 0)
                        else {
                            continue;
                        };

                        if let Some(reduced) = evaluated {
                            if !Self::relation_holds(relation, &reduced, &bound) {
                                let mut explanation = vec![lit];
                                Self::add_arg_resolution_explanations(
                                    terms,
                                    state,
                                    func_side,
                                    &mut explanation,
                                );
                                infer.add_conflict(InferenceKind::PredicateConflict, explanation);
                                return true;
                            }
                        } else if Self::is_range_restricted_int_app(terms, func_side)
                            && !Self::range_has_witness_for_relation(
                                terms, state, func_side, relation, &bound,
                            )
                        {
                            let explanation = vec![lit];
                            infer.add_conflict(InferenceKind::PredicateConflict, explanation);
                            return true;
                        }
                    }
                }
                _ => {}
            }
        }
        infer.has_conflict()
    }
}
