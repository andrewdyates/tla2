// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Extended function pass: predicate evaluation and string equality checking.
//!
//! Evaluates extf predicates and checks string equalities/disequalities
//! using ground (EQC constant) resolution. Runs before normal-form
//! computation (effort 0).
//!
//! String reductions + helpers: see `extf_pass_reductions.rs`
//! Integer reductions: see `extf_pass_int.rs`

use super::*;

impl CoreSolver {
    /// Evaluate extf Boolean predicates with fully-resolved constant arguments.
    ///
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

    /// Evaluate asserted string equalities/disequalities involving extf apps.
    ///
    /// Unlike the EQC-constant scan above, this examines all asserted equality
    /// literals, including negated equalities where the extf app and constant are
    /// intentionally in different EQCs.
    pub(super) fn check_extf_string_equalities(
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
}
