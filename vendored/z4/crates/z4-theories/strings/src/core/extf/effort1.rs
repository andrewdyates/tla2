// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Extended function effort-1 evaluation: post-NF extf checking using
// normal-form-derived constant substitutions.
//
// Reference: `reference/cvc5/src/theory/strings/extf_solver.cpp`

use num_bigint::BigInt;
use z4_core::{Constant, Sort, TermData, TermId, TermStore, TheoryLit};

use crate::infer::{InferenceKind, InferenceManager};
use crate::state::SolverState;

use hashbrown::HashMap;

use super::super::{ContainsFact, CoreSolver, ExtfArgKey, ExtfSubstKey, DEBUG_STRING_CORE};

impl CoreSolver {
    /// Post-NF extf evaluation pass (CVC5 effort 1 style).
    ///
    /// This runs after normal forms are computed and checked. Terms that were
    /// unresolved during effort 0 can become evaluable once their EQC has a
    /// constant normal form, even if the EQC has no direct constant member.
    ///
    /// CVC5 reference: extf_solver.cpp `checkExtfEval` at effort 1.
    pub(in crate::core) fn check_extf_eval_effort1(
        &self,
        terms: &TermStore,
        state: &SolverState,
        infer: &mut InferenceManager,
    ) -> bool {
        // 1) Boolean extf atoms in assertions.
        let assertion_snapshot: Vec<_> = state.assertions().to_vec();
        for &lit in &assertion_snapshot {
            let (atom, expected) = Self::atom_and_polarity(terms, lit);
            if !Self::is_extf_predicate_atom(terms, atom) {
                continue;
            }
            if self.reduced_terms.contains(&atom) {
                continue;
            }
            let Some(actual) = self.eval_extf_predicate_effort1(terms, state, atom) else {
                continue;
            };
            if actual != expected {
                if *DEBUG_STRING_CORE {
                    let atom_name = match terms.get(atom) {
                        TermData::App(sym, _) => sym.name(),
                        _ => "<non-app>",
                    };
                    let arg_debug = match terms.get(atom) {
                        TermData::App(_, args) if args.len() >= 2 => format!(
                            "args=({:?}, {:?}) data=({:?}, {:?}) effort1=({:?}, {:?}) direct=({:?}, {:?})",
                            args[0],
                            args[1],
                            terms.get(args[0]),
                            terms.get(args[1]),
                            self.resolve_string_term_effort1(terms, state, args[0]),
                            self.resolve_string_term_effort1(terms, state, args[1]),
                            Self::resolve_string_term(terms, state, args[0], 0),
                            Self::resolve_string_term(terms, state, args[1], 0)
                        ),
                        TermData::App(_, args) if args.len() == 1 => format!(
                            "arg={:?} effort1={:?} direct={:?}",
                            args[0],
                            self.resolve_string_term_effort1(terms, state, args[0]),
                            Self::resolve_string_term(terms, state, args[0], 0)
                        ),
                        _ => String::from("args=<n/a>"),
                    };
                    eprintln!(
                        "[STRING_CORE] check_extf_eval_effort1 conflict: lit={lit:?} atom={atom:?} ({atom_name}) expected={expected} actual={actual} {arg_debug}"
                    );
                }
                let mut explanation = vec![lit];
                // Soundness (#4057): effort-1 evaluation may resolve args via
                // normal forms, not just direct EQC constants. Include NF deps.
                self.add_effort1_arg_resolution_explanations(terms, state, atom, &mut explanation);
                // Soundness guard (#6309): distinguish ground vs NF-derived
                // conflicts. Ground-only resolution produces trustworthy
                // conflicts; NF-derived resolution can produce spurious
                // conflicts from transient normal forms.
                let ground_also_conflicts = self
                    .eval_extf_predicate_ground(terms, state, atom)
                    .is_some_and(|v| v != expected);
                let kind = if ground_also_conflicts {
                    InferenceKind::PredicateConflict
                } else {
                    InferenceKind::PredicateConflictNfDerived
                };
                infer.add_conflict(kind, explanation);
                return true;
            }
        }

        // 2) String-valued extf apps in EQCs.
        let reps = state.eqc_representatives();
        for &rep in &reps {
            let Some(eqc) = state.get_eqc(&rep) else {
                continue;
            };
            let eqc_const = eqc.constant.as_deref();

            for &member in &eqc.members {
                if !Self::is_reducible_string_app(terms, member) {
                    continue;
                }
                if self.reduced_terms.contains(&member) {
                    // Soundness (#6715): For reduced terms with a known EQC
                    // constant, still verify value consistency via effort-1
                    // evaluation (same rationale as check_extf_reductions).
                    if let Some(c) = eqc_const {
                        if let Some(reduced) =
                            self.try_reduce_string_term_effort1(terms, state, member)
                        {
                            if reduced != *c {
                                if *DEBUG_STRING_CORE {
                                    eprintln!(
                                        "[STRING_CORE] check_extf_eval_effort1 conflict (reduced term): rep={:?} member={:?} data={:?} reduced={:?} eqc_const={:?}",
                                        rep, member, terms.get(member), reduced, c
                                    );
                                }
                                let mut explanation = state.explain_or_all(member, rep);
                                if let Some(const_id) =
                                    state.find_constant_term_id_for_rep(terms, &rep)
                                {
                                    explanation.extend(state.explain(const_id, rep));
                                }
                                self.add_effort1_arg_resolution_explanations(
                                    terms,
                                    state,
                                    member,
                                    &mut explanation,
                                );
                                infer.add_conflict(InferenceKind::PredicateConflict, explanation);
                                return true;
                            }
                        }
                    }
                    continue;
                }
                let Some(reduced) = self.try_reduce_string_term_effort1(terms, state, member)
                else {
                    continue;
                };

                if let Some(c) = eqc_const {
                    if reduced != *c {
                        if *DEBUG_STRING_CORE {
                            eprintln!(
                                "[STRING_CORE] check_extf_eval_effort1 value conflict: rep={:?} member={:?} data={:?} reduced={:?} eqc_const={:?}",
                                rep,
                                member,
                                terms.get(member),
                                reduced,
                                c
                            );
                        }
                        let mut explanation = state.explain_or_all(member, rep);
                        if let Some(const_id) = state.find_constant_term_id_for_rep(terms, &rep) {
                            explanation.extend(state.explain(const_id, rep));
                        }
                        // Soundness (#4057): effort-1 reduction may resolve args
                        // via normal forms. Include NF deps in explanation.
                        self.add_effort1_arg_resolution_explanations(
                            terms,
                            state,
                            member,
                            &mut explanation,
                        );
                        infer.add_conflict(InferenceKind::PredicateConflict, explanation);
                        return true;
                    }
                    continue;
                }

                // No direct EQC constant: propagate member = reduced-constant term
                // when that constant term already exists in the current state.
                if let Some(const_id) = Self::find_constant_term_for_value(terms, state, &reduced) {
                    if state.find(member) != state.find(const_id) {
                        let mut explanation = Vec::new();
                        self.add_effort1_arg_resolution_explanations(
                            terms,
                            state,
                            member,
                            &mut explanation,
                        );
                        infer.add_internal_equality(
                            InferenceKind::Unify,
                            member,
                            const_id,
                            explanation,
                        );
                    }
                }
            }
        }

        self.check_equal_after_substitution_effort1(terms, state, infer);
        if self.check_contains_transitivity_effort1(terms, state, infer) {
            return true;
        }
        self.check_extf_equality_rewrites_effort1(terms, state, infer);

        infer.has_conflict()
    }

    /// CVC5 `checkExtfInference` (part 1): infer equality between different
    /// extf terms that become equal after effort-1 substitution.
    pub(super) fn check_equal_after_substitution_effort1(
        &self,
        terms: &TermStore,
        state: &SolverState,
        infer: &mut InferenceManager,
    ) {
        let mut seen: HashMap<ExtfSubstKey, TermId> = HashMap::new();
        let reps = state.eqc_representatives();
        for &rep in &reps {
            let Some(eqc) = state.get_eqc(&rep) else {
                continue;
            };
            for &member in &eqc.members {
                let Some(key) = self.extf_subst_key_effort1(terms, state, member) else {
                    continue;
                };
                let Some(&other) = seen.get(&key) else {
                    seen.insert(key, member);
                    continue;
                };
                if state.find(member) == state.find(other) {
                    continue;
                }

                let mut explanation = Vec::new();
                Self::add_arg_resolution_explanations(terms, state, member, &mut explanation);
                Self::add_arg_resolution_explanations(terms, state, other, &mut explanation);
                infer.add_internal_equality(InferenceKind::Unify, member, other, explanation);
            }
        }
    }

    /// Build a substitution key for an extf app after effort-1 substitutions.
    pub(super) fn extf_subst_key_effort1(
        &self,
        terms: &TermStore,
        state: &SolverState,
        term: TermId,
    ) -> Option<ExtfSubstKey> {
        if !Self::is_reducible_string_app(terms, term) && !Self::is_reducible_int_app(terms, term) {
            return None;
        }
        let TermData::App(sym, args) = terms.get(term) else {
            return None;
        };

        let mut key_args = Vec::with_capacity(args.len());
        for &arg in args {
            let arg_key = if terms.sort(arg) == &Sort::String {
                if let Some(s) = self.resolve_string_term_effort1(terms, state, arg) {
                    ExtfArgKey::StrConst(s)
                } else {
                    ExtfArgKey::Rep(state.find(arg))
                }
            } else if terms.sort(arg) == &Sort::Int {
                if let Some(n) = self.resolve_int_term_effort1(terms, state, arg) {
                    ExtfArgKey::IntConst(n)
                } else {
                    ExtfArgKey::Rep(state.find(arg))
                }
            } else {
                ExtfArgKey::Rep(state.find(arg))
            };
            key_args.push(arg_key);
        }

        Some(ExtfSubstKey {
            symbol: sym.name().to_owned(),
            args: key_args,
        })
    }

    /// CVC5 `checkExtfInference` (part 2): detect contains-transitivity
    /// contradictions across asserted literals.
    ///
    /// Uses BFS over the positive `contains` graph to detect arbitrary-length
    /// chains.  For each negative `¬contains(h, n)`, check if `h` can reach
    /// `n` transitively through positive assertions; if so, emit a conflict
    /// with the full path explanation.
    ///
    /// CVC5 reference: `extf_solver.cpp:592-727`.
    pub(super) fn check_contains_transitivity_effort1(
        &self,
        terms: &TermStore,
        state: &SolverState,
        infer: &mut InferenceManager,
    ) -> bool {
        // Build directed graph: h_rep → [(n_rep, ContainsFact)]
        let mut graph: HashMap<TermId, Vec<(TermId, ContainsFact)>> = HashMap::new();
        let mut negative_facts: Vec<(TermId, TermId, ContainsFact)> = Vec::new();

        for &lit in state.assertions() {
            let (atom, expected) = Self::atom_and_polarity(terms, lit);
            let TermData::App(sym, args) = terms.get(atom) else {
                continue;
            };
            if sym.name() != "str.contains" || args.len() != 2 {
                continue;
            }

            let fact = ContainsFact {
                haystack: args[0],
                needle: args[1],
                lit,
            };
            let h_rep = state.find(fact.haystack);
            let n_rep = state.find(fact.needle);
            if expected {
                // Skip self-loops (contains(x,x) is trivially true).
                if h_rep != n_rep {
                    graph.entry(h_rep).or_default().push((n_rep, fact));
                }
            } else {
                negative_facts.push((h_rep, n_rep, fact));
            }
        }

        if graph.is_empty() || negative_facts.is_empty() {
            return false;
        }

        // For each negative fact, BFS to find a path in the positive graph.
        for (neg_h_rep, neg_n_rep, neg_fact) in &negative_facts {
            if neg_h_rep == neg_n_rep {
                // ¬contains(x,x) is immediately false; handled elsewhere.
                continue;
            }
            if let Some(path) = Self::bfs_contains_path(&graph, *neg_h_rep, *neg_n_rep) {
                let mut explanation = Vec::new();
                // Add all positive edge literals.
                for edge_fact in &path {
                    explanation.push(edge_fact.lit);
                }
                // Add the negative literal.
                explanation.push(neg_fact.lit);
                // Add EQC merge explanations for each edge connection.
                // First edge: neg_fact.haystack == path[0].haystack (same EQC).
                Self::append_rep_explanation_if_needed(
                    state,
                    neg_fact.haystack,
                    path[0].haystack,
                    &mut explanation,
                );
                // Chain edges: path[i].needle == path[i+1].haystack.
                for i in 0..path.len() - 1 {
                    Self::append_rep_explanation_if_needed(
                        state,
                        path[i].needle,
                        path[i + 1].haystack,
                        &mut explanation,
                    );
                }
                // Last edge: path[last].needle == neg_fact.needle (same EQC).
                Self::append_rep_explanation_if_needed(
                    state,
                    path[path.len() - 1].needle,
                    neg_fact.needle,
                    &mut explanation,
                );
                infer.add_conflict(InferenceKind::PredicateConflict, explanation);
                return true;
            }
        }

        false
    }

    /// BFS over the positive contains graph from `start` to `target`.
    /// Returns the path (sequence of `ContainsFact` edges) if reachable.
    pub(super) fn bfs_contains_path(
        graph: &HashMap<TermId, Vec<(TermId, ContainsFact)>>,
        start: TermId,
        target: TermId,
    ) -> Option<Vec<ContainsFact>> {
        use std::collections::{HashSet, VecDeque};

        // parent[node] = (predecessor_node, edge_fact)
        let mut parent: HashMap<TermId, (TermId, ContainsFact)> = HashMap::new();
        let mut visited: HashSet<TermId> = HashSet::new();
        let mut queue: VecDeque<TermId> = VecDeque::new();

        visited.insert(start);
        queue.push_back(start);

        while let Some(current) = queue.pop_front() {
            if let Some(neighbors) = graph.get(&current) {
                for &(next, ref fact) in neighbors {
                    if !visited.insert(next) {
                        continue;
                    }
                    parent.insert(next, (current, *fact));
                    if next == target {
                        // Reconstruct path.
                        let mut path = Vec::new();
                        let mut node = target;
                        while let Some(&(pred, ref edge)) = parent.get(&node) {
                            path.push(*edge);
                            node = pred;
                        }
                        path.reverse();
                        return Some(path);
                    }
                    queue.push_back(next);
                }
            }
        }
        None
    }

    pub(super) fn append_rep_explanation_if_needed(
        state: &SolverState,
        a: TermId,
        b: TermId,
        explanation: &mut Vec<TheoryLit>,
    ) {
        if a != b && state.find(a) == state.find(b) {
            explanation.extend(state.explain(a, b));
        }
    }

    /// CVC5 `checkExtfInference` (part 3): apply limited equality rewrites for
    /// non-predicate extf terms equal to constants.
    pub(super) fn check_extf_equality_rewrites_effort1(
        &self,
        terms: &TermStore,
        state: &SolverState,
        infer: &mut InferenceManager,
    ) {
        for &lit in state.assertions() {
            let (atom, expected) = Self::atom_and_polarity(terms, lit);
            if !expected {
                continue;
            }
            let TermData::App(sym, args) = terms.get(atom) else {
                continue;
            };
            if sym.name() != "=" || args.len() != 2 {
                continue;
            }

            if let Some((lhs, rhs, mut explanation)) =
                Self::rewrite_extf_equality_effort1(terms, state, args[0], args[1])
            {
                if state.find(lhs) != state.find(rhs) {
                    let mut full_expl = vec![lit];
                    full_expl.append(&mut explanation);
                    Self::add_arg_resolution_explanations(terms, state, args[0], &mut full_expl);
                    infer.add_internal_equality(InferenceKind::Unify, lhs, rhs, full_expl);
                }
            }
            if let Some((lhs, rhs, mut explanation)) =
                Self::rewrite_extf_equality_effort1(terms, state, args[1], args[0])
            {
                if state.find(lhs) != state.find(rhs) {
                    let mut full_expl = vec![lit];
                    full_expl.append(&mut explanation);
                    Self::add_arg_resolution_explanations(terms, state, args[1], &mut full_expl);
                    infer.add_internal_equality(InferenceKind::Unify, lhs, rhs, full_expl);
                }
            }
        }
    }

    /// Rewrite a limited subset of extf equalities `extf_term = const_term`
    /// to a simpler equality if the rewrite is semantics-preserving.
    pub(super) fn rewrite_extf_equality_effort1(
        terms: &TermStore,
        state: &SolverState,
        extf_term: TermId,
        const_term: TermId,
    ) -> Option<(TermId, TermId, Vec<TheoryLit>)> {
        if !matches!(terms.get(const_term), TermData::Const(Constant::String(_))) {
            return None;
        }

        let TermData::App(sym, args) = terms.get(extf_term) else {
            return None;
        };
        match sym.name() {
            // str.replace(s, s, u) == u.
            "str.replace" if args.len() == 3 => {
                if state.find(args[0]) != state.find(args[1]) {
                    return None;
                }
                let mut explanation = Vec::new();
                Self::append_rep_explanation_if_needed(state, args[0], args[1], &mut explanation);
                Some((args[2], const_term, explanation))
            }
            _ => None,
        }
    }

    /// Evaluate extf predicates using NF-derived substitutions.
    pub(super) fn eval_extf_predicate_effort1(
        &self,
        terms: &TermStore,
        state: &SolverState,
        atom: TermId,
    ) -> Option<bool> {
        let TermData::App(sym, args) = terms.get(atom) else {
            return None;
        };

        match sym.name() {
            "str.contains" if args.len() == 2 => {
                // Soundness guard (#4057): avoid NF-only contains evaluation.
                //
                // Effort-1 NF substitutions can transiently resolve both sides
                // of a branch-local contains atom to constants. For reduction
                // guards (especially inside replace ITE branches), using those
                // transient values for hard conflicts can over-prune the search.
                //
                // Keep contains evaluation here strictly ground via direct EQC
                // constants/functions. Non-ground cases remain deferred.
                let h = Self::resolve_string_term(terms, state, args[0], 0)?;
                let n = Self::resolve_string_term(terms, state, args[1], 0)?;
                Some(h.contains(n.as_str()))
            }
            "str.prefixof" if args.len() == 2 => {
                // Soundness guard (#6309): use ground-only resolution, matching
                // the str.contains guard (#4057). NF-derived constants can
                // produce transient mismatches that cause false-UNSAT.
                if state.find(args[0]) == state.find(args[1]) {
                    return Some(true);
                }
                let prefix = Self::resolve_string_term(terms, state, args[0], 0)?;
                let s = Self::resolve_string_term(terms, state, args[1], 0)?;
                Some(s.starts_with(prefix.as_str()))
            }
            "str.suffixof" if args.len() == 2 => {
                // Soundness guard (#6309): use ground-only resolution, matching
                // the str.contains guard (#4057).
                if state.find(args[0]) == state.find(args[1]) {
                    return Some(true);
                }
                let suffix = Self::resolve_string_term(terms, state, args[0], 0)?;
                let s = Self::resolve_string_term(terms, state, args[1], 0)?;
                Some(s.ends_with(suffix.as_str()))
            }
            "str.<=" if args.len() == 2 => {
                // Soundness guard (#6309): ground-only resolution.
                if state.find(args[0]) == state.find(args[1]) {
                    return Some(true);
                }
                let a = Self::resolve_string_term(terms, state, args[0], 0)?;
                let b = Self::resolve_string_term(terms, state, args[1], 0)?;
                Some(a <= b)
            }
            "str.<" if args.len() == 2 => {
                // Soundness guard (#6309): ground-only resolution.
                if state.find(args[0]) == state.find(args[1]) {
                    return Some(false);
                }
                let a = Self::resolve_string_term(terms, state, args[0], 0)?;
                let b = Self::resolve_string_term(terms, state, args[1], 0)?;
                Some(a < b)
            }
            "str.is_digit" if args.len() == 1 => {
                // Soundness guard (#6309): ground-only resolution.
                let s = Self::resolve_string_term(terms, state, args[0], 0)?;
                Some(s.len() == 1 && s.chars().next().is_some_and(|c| c.is_ascii_digit()))
            }
            _ => None,
        }
    }

    /// Evaluate extf predicates using ground-only (EQC constant) resolution.
    /// Returns None if the predicate cannot be evaluated from ground data alone.
    /// Used to distinguish ground vs NF-derived conflicts (#6309).
    pub(super) fn eval_extf_predicate_ground(
        &self,
        terms: &TermStore,
        state: &SolverState,
        atom: TermId,
    ) -> Option<bool> {
        let TermData::App(sym, args) = terms.get(atom) else {
            return None;
        };

        match sym.name() {
            "str.contains" if args.len() == 2 => {
                let h = Self::resolve_string_term(terms, state, args[0], 0)?;
                let n = Self::resolve_string_term(terms, state, args[1], 0)?;
                Some(h.contains(n.as_str()))
            }
            "str.prefixof" if args.len() == 2 => {
                if state.find(args[0]) == state.find(args[1]) {
                    return Some(true);
                }
                let prefix = Self::resolve_string_term(terms, state, args[0], 0)?;
                let s = Self::resolve_string_term(terms, state, args[1], 0)?;
                Some(s.starts_with(prefix.as_str()))
            }
            "str.suffixof" if args.len() == 2 => {
                if state.find(args[0]) == state.find(args[1]) {
                    return Some(true);
                }
                let suffix = Self::resolve_string_term(terms, state, args[0], 0)?;
                let s = Self::resolve_string_term(terms, state, args[1], 0)?;
                Some(s.ends_with(suffix.as_str()))
            }
            "str.<=" if args.len() == 2 => {
                if state.find(args[0]) == state.find(args[1]) {
                    return Some(true);
                }
                let a = Self::resolve_string_term(terms, state, args[0], 0)?;
                let b = Self::resolve_string_term(terms, state, args[1], 0)?;
                Some(a <= b)
            }
            "str.<" if args.len() == 2 => {
                if state.find(args[0]) == state.find(args[1]) {
                    return Some(false);
                }
                let a = Self::resolve_string_term(terms, state, args[0], 0)?;
                let b = Self::resolve_string_term(terms, state, args[1], 0)?;
                Some(a < b)
            }
            "str.is_digit" if args.len() == 1 => {
                let s = Self::resolve_string_term(terms, state, args[0], 0)?;
                Some(s.len() == 1 && s.chars().next().is_some_and(|c| c.is_ascii_digit()))
            }
            _ => None,
        }
    }

    /// Resolve a string term to a concrete value, allowing NF-derived constants.
    pub(super) fn resolve_string_term_effort1(
        &self,
        terms: &TermStore,
        state: &SolverState,
        t: TermId,
    ) -> Option<String> {
        if let Some(s) = Self::resolve_string_term(terms, state, t, 0) {
            return Some(s);
        }

        let rep = state.find(t);
        self.normal_forms
            .get(&rep)
            .and_then(|nf| self.nf_to_constant(terms, state, nf))
    }

    /// Resolve an integer term to a concrete value with NF-derived string args.
    pub(super) fn resolve_int_term_effort1(
        &self,
        terms: &TermStore,
        state: &SolverState,
        t: TermId,
    ) -> Option<BigInt> {
        if let Some(n) = Self::resolve_int_term(terms, state, t, 0) {
            return Some(n);
        }
        let TermData::App(sym, args) = terms.get(t) else {
            return None;
        };
        match sym.name() {
            "str.indexof" if args.len() == 3 => {
                let s = self.resolve_string_term_effort1(terms, state, args[0])?;
                let pat = self.resolve_string_term_effort1(terms, state, args[1])?;
                let start = self.resolve_int_term_effort1(terms, state, args[2])?;
                Self::eval_str_indexof(&s, &pat, &start)
            }
            "str.len" if args.len() == 1 => {
                let s = self.resolve_string_term_effort1(terms, state, args[0])?;
                Some(BigInt::from(s.chars().count()))
            }
            "str.to_int" | "str.to.int" if args.len() == 1 => {
                let s = self.resolve_string_term_effort1(terms, state, args[0])?;
                Some(Self::eval_str_to_int(&s))
            }
            "str.to_code" if args.len() == 1 => {
                let s = self.resolve_string_term_effort1(terms, state, args[0])?;
                Some(Self::eval_str_to_code(&s))
            }
            _ => None,
        }
    }

    /// Effort-1 reduction for string-valued extf applications.
    pub(super) fn try_reduce_string_term_effort1(
        &self,
        terms: &TermStore,
        state: &SolverState,
        t: TermId,
    ) -> Option<String> {
        let TermData::App(sym, args) = terms.get(t) else {
            return None;
        };
        match sym.name() {
            "str.at" if args.len() == 2 => {
                let s = self.resolve_string_term_effort1(terms, state, args[0])?;
                let i = self.resolve_int_term_effort1(terms, state, args[1])?;
                Self::eval_str_at(&s, &i)
            }
            "str.substr" if args.len() == 3 => {
                let s = self.resolve_string_term_effort1(terms, state, args[0])?;
                let i = self.resolve_int_term_effort1(terms, state, args[1])?;
                let j = self.resolve_int_term_effort1(terms, state, args[2])?;
                Self::eval_str_substr(&s, &i, &j)
            }
            "str.replace" if args.len() == 3 => {
                if state.find(args[0]) == state.find(args[1]) {
                    return self.resolve_string_term_effort1(terms, state, args[2]);
                }
                let s = self.resolve_string_term_effort1(terms, state, args[0])?;
                let t_str = self.resolve_string_term_effort1(terms, state, args[1])?;
                let u = self.resolve_string_term_effort1(terms, state, args[2])?;
                Some(Self::eval_str_replace(&s, &t_str, &u))
            }
            "str.from_int" | "int.to.str" if args.len() == 1 => {
                let n = self.resolve_int_term_effort1(terms, state, args[0])?;
                Some(Self::eval_str_from_int(&n))
            }
            "str.replace_all" if args.len() == 3 => {
                let s = self.resolve_string_term_effort1(terms, state, args[0])?;
                let t_str = self.resolve_string_term_effort1(terms, state, args[1])?;
                let u = self.resolve_string_term_effort1(terms, state, args[2])?;
                Some(Self::eval_str_replace_all(&s, &t_str, &u))
            }
            "str.replace_re" if args.len() == 3 => {
                let s = self.resolve_string_term_effort1(terms, state, args[0])?;
                let t = self.resolve_string_term_effort1(terms, state, args[2])?;
                Self::eval_str_replace_re(terms, &s, args[1], &t)
            }
            "str.replace_re_all" if args.len() == 3 => {
                let s = self.resolve_string_term_effort1(terms, state, args[0])?;
                let t = self.resolve_string_term_effort1(terms, state, args[2])?;
                Self::eval_str_replace_re_all(terms, &s, args[1], &t)
            }
            "str.from_code" if args.len() == 1 => {
                let n = self.resolve_int_term_effort1(terms, state, args[0])?;
                Some(Self::eval_str_from_code(&n))
            }
            "str.to_lower" if args.len() == 1 => {
                let s = self.resolve_string_term_effort1(terms, state, args[0])?;
                Some(crate::eval::eval_str_to_lower(&s))
            }
            "str.to_upper" if args.len() == 1 => {
                let s = self.resolve_string_term_effort1(terms, state, args[0])?;
                Some(crate::eval::eval_str_to_upper(&s))
            }
            _ => None,
        }
    }

    /// Try to reduce a string function application to a concrete value.
    ///
    /// Unlike `resolve_string_term`, this only evaluates function applications
    /// (str.at, str.substr, str.replace, str.from_int, str.to_lower,
    /// str.to_upper) — not EQC constants or syntactic constants.
    pub(super) fn try_reduce_string_term(terms: &TermStore, state: &SolverState, t: TermId) -> Option<String> {
        let TermData::App(sym, args) = terms.get(t) else {
            return None;
        };
        match sym.name() {
            "str.at" if args.len() == 2 => {
                let s = Self::resolve_string_term(terms, state, args[0], 0)?;
                let i = Self::resolve_int_term(terms, state, args[1], 0)?;
                Self::eval_str_at(&s, &i)
            }
            "str.substr" if args.len() == 3 => {
                let s = Self::resolve_string_term(terms, state, args[0], 0)?;
                let i = Self::resolve_int_term(terms, state, args[1], 0)?;
                let j = Self::resolve_int_term(terms, state, args[2], 0)?;
                Self::eval_str_substr(&s, &i, &j)
            }
            "str.replace" if args.len() == 3 => {
                // Identity reduction: str.replace(s, s, u) = u for all s.
                // When haystack and pattern are in the same EQC, the result
                // is always the replacement string regardless of s's value.
                if state.find(args[0]) == state.find(args[1]) {
                    return Self::resolve_string_term(terms, state, args[2], 0);
                }
                let s = Self::resolve_string_term(terms, state, args[0], 0)?;
                let t_str = Self::resolve_string_term(terms, state, args[1], 0)?;
                let u = Self::resolve_string_term(terms, state, args[2], 0)?;
                Some(Self::eval_str_replace(&s, &t_str, &u))
            }
            "str.from_int" | "int.to.str" if args.len() == 1 => {
                let n = Self::resolve_int_term(terms, state, args[0], 0)?;
                Some(Self::eval_str_from_int(&n))
            }
            "str.replace_all" if args.len() == 3 => {
                let s = Self::resolve_string_term(terms, state, args[0], 0)?;
                let t_str = Self::resolve_string_term(terms, state, args[1], 0)?;
                let u = Self::resolve_string_term(terms, state, args[2], 0)?;
                Some(Self::eval_str_replace_all(&s, &t_str, &u))
            }
            "str.replace_re" if args.len() == 3 => {
                let s = Self::resolve_string_term(terms, state, args[0], 0)?;
                let t = Self::resolve_string_term(terms, state, args[2], 0)?;
                Self::eval_str_replace_re(terms, &s, args[1], &t)
            }
            "str.replace_re_all" if args.len() == 3 => {
                let s = Self::resolve_string_term(terms, state, args[0], 0)?;
                let t = Self::resolve_string_term(terms, state, args[2], 0)?;
                Self::eval_str_replace_re_all(terms, &s, args[1], &t)
            }
            "str.from_code" if args.len() == 1 => {
                let n = Self::resolve_int_term(terms, state, args[0], 0)?;
                Some(Self::eval_str_from_code(&n))
            }
            "str.to_lower" if args.len() == 1 => {
                let s = Self::resolve_string_term(terms, state, args[0], 0)?;
                Some(crate::eval::eval_str_to_lower(&s))
            }
            "str.to_upper" if args.len() == 1 => {
                let s = Self::resolve_string_term(terms, state, args[0], 0)?;
                Some(crate::eval::eval_str_to_upper(&s))
            }
            _ => None,
        }
    }
}
