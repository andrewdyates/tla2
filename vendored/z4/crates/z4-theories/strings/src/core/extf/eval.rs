// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Extended function evaluation: predicate evaluation, string/integer term
// resolution, structural contains analysis, and pure SMT-LIB eval helpers.
//
// Reference: `reference/cvc5/src/theory/strings/core_solver.cpp`

use num_bigint::BigInt;
use z4_core::{Constant, TermData, TermId, TermStore, TheoryLit};

use crate::infer::{InferenceKind, InferenceManager};
use crate::regexp::{MatchResult, RegExpSolver};
use crate::state::SolverState;

use super::super::{CoreSolver, DEBUG_STRING_CORE};

impl CoreSolver {
    /// Evaluate `str.contains(haystack, needle)` with structural entailment.
    ///
    /// CVC5 reference: sequences_rewriter.cpp rewriteContains
    pub(super) fn eval_contains(
        terms: &TermStore,
        state: &SolverState,
        haystack: TermId,
        needle: TermId,
    ) -> Option<bool> {
        // Reflexive: x contains x.
        if state.find(haystack) == state.find(needle) {
            return Some(true);
        }
        // Everything contains "".
        if state.is_empty_string(terms, needle) {
            return Some(true);
        }
        // CTN_LHS_EMPTYSTR: str.contains("", x) ↔ x = "".
        if state.is_empty_string(terms, haystack) {
            if state.is_empty_string(terms, needle) {
                return Some(true);
            }
            if Self::has_positive_min_length(terms, state, needle) {
                return Some(false);
            }
            // Unknown whether needle is empty.
            return None;
        }
        // CTN_LEN_INEQ: needle strictly longer than haystack → false.
        if Self::needle_strictly_longer(terms, state, haystack, needle) {
            return Some(false);
        }
        // CTN_LEN_INEQ_NSTRICT: needle reduces to haystack after empty removal.
        if Self::needle_reduces_to_haystack(terms, state, haystack, needle) {
            return Some(true);
        }
        // Structural: constant needle found in a constant concat component.
        if let Some(needle_str) = Self::resolve_string_term(terms, state, needle, 0) {
            if Self::concat_contains_constant(terms, state, haystack, &needle_str) {
                return Some(true);
            }
            // CTN_COMPONENT: check haystack's EQC concat terms.
            //
            // When the haystack is a variable y with y = str.++(x, "world"),
            // the syntactic check above misses it because y itself is not
            // a concat. Check the EQC's concat terms directly.
            //
            // Safety: this only returns Some(true), never Some(false).
            // For positive contains assertions, this is sound because the
            // EQC concat equation provides a structural witness. For negative
            // assertions, the caller detects actual != expected as a conflict
            // with proper explanation.
            //
            // CVC5 reference: sequences_rewriter.cpp:2925 CTN_COMPONENT
            let haystack_rep = state.find(haystack);
            if let Some(eqc) = state.get_eqc(&haystack_rep) {
                if *DEBUG_STRING_CORE {
                    eprintln!(
                        "[STRING_CORE] CTN_COMPONENT: haystack={:?} rep={:?} needle=\"{}\" concat_terms={:?}",
                        haystack, haystack_rep, needle_str, eqc.concat_terms
                    );
                }
                for &ct in &eqc.concat_terms {
                    if Self::concat_contains_constant(terms, state, ct, &needle_str) {
                        if *DEBUG_STRING_CORE {
                            eprintln!(
                                "[STRING_CORE] CTN_COMPONENT: found needle in concat term {ct:?}"
                            );
                        }
                        return Some(true);
                    }
                }
            }
        }
        // Full resolution: both args resolve to constants.
        let h = Self::resolve_string_term(terms, state, haystack, 0)?;
        let n = Self::resolve_string_term(terms, state, needle, 0)?;
        Some(h.contains(n.as_str()))
    }

    /// Evaluate `str.prefixof(prefix, s)`.
    pub(super) fn eval_prefixof(
        terms: &TermStore,
        state: &SolverState,
        prefix: TermId,
        s: TermId,
    ) -> Option<bool> {
        if state.find(prefix) == state.find(s) {
            return Some(true);
        }
        if state.is_empty_string(terms, prefix) {
            return Some(true);
        }
        // EQC component check: if s's EQC has a concat starting
        // with a component in the same EQC as prefix, return true.
        let prefix_rep = state.find(prefix);
        let s_rep = state.find(s);
        if let Some(eqc) = state.get_eqc(&s_rep) {
            for &ct in &eqc.concat_terms {
                if let Some(children) = state.get_concat_children(terms, ct) {
                    for &child in children {
                        if state.is_empty_string(terms, child) {
                            continue;
                        }
                        if state.find(child) == prefix_rep {
                            return Some(true);
                        }
                        break;
                    }
                }
            }
        }
        let prefix_str = Self::resolve_string_term(terms, state, prefix, 0)?;
        let s_str = Self::resolve_string_term(terms, state, s, 0)?;
        Some(s_str.starts_with(prefix_str.as_str()))
    }

    /// Evaluate str.suffixof(suffix, s).
    pub(super) fn eval_suffixof(
        terms: &TermStore,
        state: &SolverState,
        suffix: TermId,
        s: TermId,
    ) -> Option<bool> {
        if state.find(suffix) == state.find(s) {
            return Some(true);
        }
        if state.is_empty_string(terms, suffix) {
            return Some(true);
        }
        // EQC component check: if s's EQC has a concat ending
        // with a component in the same EQC as suffix, return true.
        let suffix_rep = state.find(suffix);
        let s_rep = state.find(s);
        if let Some(eqc) = state.get_eqc(&s_rep) {
            for &ct in &eqc.concat_terms {
                if let Some(children) = state.get_concat_children(terms, ct) {
                    for &child in children.iter().rev() {
                        if state.is_empty_string(terms, child) {
                            continue;
                        }
                        if state.find(child) == suffix_rep {
                            return Some(true);
                        }
                        break;
                    }
                }
            }
        }
        let suffix_str = Self::resolve_string_term(terms, state, suffix, 0)?;
        let s_str = Self::resolve_string_term(terms, state, s, 0)?;
        Some(s_str.ends_with(suffix_str.as_str()))
    }

    /// Evaluate supported extf predicates if their arguments resolve to strings.
    ///
    /// Returns `None` when the predicate is unsupported or any argument cannot
    /// be resolved to a concrete constant.
    pub(super) fn eval_extf_predicate(terms: &TermStore, state: &SolverState, atom: TermId) -> Option<bool> {
        let TermData::App(sym, args) = terms.get(atom) else {
            return None;
        };

        match sym.name() {
            "str.contains" if args.len() == 2 => {
                Self::eval_contains(terms, state, args[0], args[1])
            }
            "str.prefixof" if args.len() == 2 => {
                Self::eval_prefixof(terms, state, args[0], args[1])
            }
            "str.suffixof" if args.len() == 2 => {
                Self::eval_suffixof(terms, state, args[0], args[1])
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
                // SMT-LIB: true iff s is a single character in '0'-'9'.
                Some(s.len() == 1 && s.chars().next().is_some_and(|c| c.is_ascii_digit()))
            }
            _ => None,
        }
    }

    /// Resolve a string term to a concrete string when possible.
    ///
    /// Resolution order:
    /// 1. EQC constant value
    /// 2. Syntactic string constant
    /// 3. Concat of recursively-resolved string terms
    /// 4. `str.at(s, i)` with resolved string and integer arguments
    /// 5. `str.substr(s, i, j)` with resolved arguments
    /// 6. `str.replace(s, t, u)` with resolved arguments
    pub(in crate::core) fn resolve_string_term(
        terms: &TermStore,
        state: &SolverState,
        t: TermId,
        depth: usize,
    ) -> Option<String> {
        if depth > Self::MAX_RESOLVE_DEPTH {
            return None;
        }

        let rep = state.find(t);
        if let Some(s) = state.get_eqc(&rep).and_then(|e| e.constant.as_deref()) {
            if *DEBUG_STRING_CORE && depth == 0 && !matches!(terms.get(t), TermData::Const(_)) {
                eprintln!(
                    "[STRING_CORE] resolve_string_term: {t:?} (rep={rep:?}) -> EQC constant {s:?}"
                );
            }
            return Some(s.to_owned());
        }

        match terms.get(t) {
            TermData::Const(Constant::String(s)) => Some(s.clone()),
            TermData::App(sym, args) => match sym.name() {
                "str.++" => {
                    let mut out = String::new();
                    for &arg in args {
                        out.push_str(&Self::resolve_string_term(terms, state, arg, depth + 1)?);
                    }
                    Some(out)
                }
                "str.at" if args.len() == 2 => {
                    let s = Self::resolve_string_term(terms, state, args[0], depth + 1)?;
                    let i = Self::resolve_int_term(terms, state, args[1], depth + 1)?;
                    Self::eval_str_at(&s, &i)
                }
                "str.substr" if args.len() == 3 => {
                    let s = Self::resolve_string_term(terms, state, args[0], depth + 1)?;
                    let i = Self::resolve_int_term(terms, state, args[1], depth + 1)?;
                    let j = Self::resolve_int_term(terms, state, args[2], depth + 1)?;
                    Self::eval_str_substr(&s, &i, &j)
                }
                "str.replace" if args.len() == 3 => {
                    // Identity reduction: str.replace(s, s, u) = u for all s.
                    if state.find(args[0]) == state.find(args[1]) {
                        return Self::resolve_string_term(terms, state, args[2], depth + 1);
                    }
                    let s = Self::resolve_string_term(terms, state, args[0], depth + 1)?;
                    let t_str = Self::resolve_string_term(terms, state, args[1], depth + 1)?;
                    let u = Self::resolve_string_term(terms, state, args[2], depth + 1)?;
                    Some(Self::eval_str_replace(&s, &t_str, &u))
                }
                "str.replace_all" if args.len() == 3 => {
                    let s = Self::resolve_string_term(terms, state, args[0], depth + 1)?;
                    let t_str = Self::resolve_string_term(terms, state, args[1], depth + 1)?;
                    let u = Self::resolve_string_term(terms, state, args[2], depth + 1)?;
                    Some(Self::eval_str_replace_all(&s, &t_str, &u))
                }
                "str.replace_re" if args.len() == 3 => {
                    let s = Self::resolve_string_term(terms, state, args[0], depth + 1)?;
                    let t = Self::resolve_string_term(terms, state, args[2], depth + 1)?;
                    Self::eval_str_replace_re(terms, &s, args[1], &t)
                }
                "str.replace_re_all" if args.len() == 3 => {
                    let s = Self::resolve_string_term(terms, state, args[0], depth + 1)?;
                    let t = Self::resolve_string_term(terms, state, args[2], depth + 1)?;
                    Self::eval_str_replace_re_all(terms, &s, args[1], &t)
                }
                "str.from_int" | "int.to.str" if args.len() == 1 => {
                    let n = Self::resolve_int_term(terms, state, args[0], depth + 1)?;
                    Some(Self::eval_str_from_int(&n))
                }
                "str.from_code" if args.len() == 1 => {
                    let n = Self::resolve_int_term(terms, state, args[0], depth + 1)?;
                    Some(Self::eval_str_from_code(&n))
                }
                "str.to_lower" if args.len() == 1 => {
                    let s = Self::resolve_string_term(terms, state, args[0], depth + 1)?;
                    Some(crate::eval::eval_str_to_lower(&s))
                }
                "str.to_upper" if args.len() == 1 => {
                    let s = Self::resolve_string_term(terms, state, args[0], depth + 1)?;
                    Some(crate::eval::eval_str_to_upper(&s))
                }
                _ => None,
            },
            _ => None,
        }
    }

    /// Check if a concat term structurally contains a constant substring.
    ///
    /// Walks the concat structure of `haystack` looking for any constant
    /// component (or adjacent constants) that contain `needle`. Returns true
    /// if the needle is found without requiring the full haystack to be ground.
    ///
    /// This enables `str.contains(str.++(x, "world"), "world")` to evaluate
    /// to true even when `x` is unresolved.
    pub(super) fn concat_contains_constant(
        terms: &TermStore,
        state: &SolverState,
        haystack: TermId,
        needle: &str,
    ) -> bool {
        if needle.is_empty() {
            return true;
        }
        // Collect the concat components (flattening nested concats).
        let mut components = Vec::new();
        Self::flatten_concat(terms, state, haystack, &mut components);

        // Check individual constant components.
        for comp in &components {
            if let Some(s) = Self::resolve_string_term(terms, state, *comp, 0) {
                if s.contains(needle) {
                    return true;
                }
            }
        }

        // Check adjacent constant pairs (needle may span two components).
        for window in components.windows(2) {
            if let (Some(a), Some(b)) = (
                Self::resolve_string_term(terms, state, window[0], 0),
                Self::resolve_string_term(terms, state, window[1], 0),
            ) {
                let combined = format!("{a}{b}");
                if combined.contains(needle) {
                    return true;
                }
            }
        }

        false
    }

    /// Flatten a concat term into its leaf components (syntactic only).
    ///
    /// Only walks the syntactic `str.++` structure of the term itself.
    /// Does NOT follow EQC representatives or members — doing so is unsound
    /// because EQC members may include Skolem decomposition terms that
    /// circularly assume the predicate being evaluated (e.g., the contains
    /// Skolem `x = str.++(sk, needle, sk2)` would always make
    /// `concat_contains_constant` return true, masking real contradictions
    /// like `x = "goodbye"` ∧ `str.contains(x, "hello")`).
    pub(super) fn flatten_concat(terms: &TermStore, _state: &SolverState, t: TermId, out: &mut Vec<TermId>) {
        if let TermData::App(sym, args) = terms.get(t) {
            if sym.name() == "str.++" {
                for &arg in args {
                    Self::flatten_concat(terms, _state, arg, out);
                }
                return;
            }
        }
        out.push(t);
    }

    /// Check whether the needle's minimum length strictly exceeds the
    /// haystack's maximum length, using structural analysis of concat
    /// components. Returns true when `str.contains(haystack, needle)` must
    /// be false due to length.
    ///
    /// Handles patterns like `str.contains(x, str.++(x, y))` when `y` is
    /// provably non-empty: the needle includes `x` plus extra, so its
    /// length exceeds `len(x)`.
    ///
    /// CVC5 reference: sequences_rewriter.cpp:2986 CTN_LEN_INEQ
    pub(super) fn needle_strictly_longer(
        terms: &TermStore,
        state: &SolverState,
        haystack: TermId,
        needle: TermId,
    ) -> bool {
        let mut components = Vec::new();
        Self::flatten_concat(terms, state, needle, &mut components);
        if components.len() < 2 {
            return false;
        }

        let haystack_rep = state.find(haystack);

        // Check if any component of the needle is in the same EQC as haystack.
        // If so, the remaining components represent "extra" length that must be
        // accounted for. If any remaining component has provably positive min
        // length, the needle is strictly longer.
        let mut found_haystack = false;
        let mut has_positive_extra = false;
        for &comp in &components {
            let comp_rep = state.find(comp);
            if comp_rep == haystack_rep && !found_haystack {
                found_haystack = true;
                continue;
            }
            // Check if this "extra" component has provably positive min length.
            if Self::has_positive_min_length(terms, state, comp) {
                has_positive_extra = true;
            }
        }

        found_haystack && has_positive_extra
    }

    /// Check whether the needle's concat components, after removing
    /// empty-EQC components, reduce to a single term in the same EQC as
    /// the haystack.
    ///
    /// For example: `str.contains(x, str.++(x, y))` with `y` in the
    /// empty-EQC → needle reduces to `x` → true (reflexive containment).
    pub(super) fn needle_reduces_to_haystack(
        terms: &TermStore,
        state: &SolverState,
        haystack: TermId,
        needle: TermId,
    ) -> bool {
        let mut components = Vec::new();
        Self::flatten_concat(terms, state, needle, &mut components);
        if components.len() < 2 {
            return false;
        }

        let haystack_rep = state.find(haystack);

        // Filter out empty-EQC components.
        let non_empty: Vec<_> = components
            .iter()
            .filter(|&&c| !state.is_empty_string(terms, c))
            .collect();

        // After removing empty components, the needle should reduce to
        // a single term in the same EQC as haystack.
        non_empty.len() == 1 && state.find(*non_empty[0]) == haystack_rep
    }

    /// Whether a string term has a provably positive minimum length.
    ///
    /// Returns true if the term is a known non-empty constant, or is in an
    /// EQC with a non-empty constant. Variables with unknown value return
    /// false (they might be "").
    pub(super) fn has_positive_min_length(terms: &TermStore, state: &SolverState, t: TermId) -> bool {
        // Check EQC constant.
        let rep = state.find(t);
        if let Some(info) = state.get_eqc(&rep) {
            if let Some(c) = info.constant.as_deref() {
                return !c.is_empty();
            }
        }
        // Check syntactic constant.
        if let TermData::Const(Constant::String(s)) = terms.get(t) {
            return !s.is_empty();
        }
        // Concat: all components must have positive min length for the whole
        // to have positive min length — but even one component with positive
        // min length suffices to contribute positive extra in the caller.
        // Here we just need any positive contribution.
        if let TermData::App(sym, args) = terms.get(t) {
            if sym.name() == "str.++" {
                return args
                    .iter()
                    .any(|&a| Self::has_positive_min_length(terms, state, a));
            }
        }
        false
    }

    /// For a positive `str.contains(haystack, needle)` where the needle is
    /// a concat that includes the haystack as a component, infer that all
    /// extra components must equal the empty string.
    ///
    /// `str.contains(x, str.++(x, y))` is true → `len(x) >= len(x) + len(y)`
    /// → `len(y) = 0` → `y = ""`. Emits `y = ""` as an internal equality.
    ///
    /// CVC5 reference: strings_entail.cpp:945 inferEqsFromContains
    pub(super) fn infer_eqs_from_contains(
        terms: &TermStore,
        state: &SolverState,
        atom: TermId,
        contains_lit: TheoryLit,
        infer: &mut InferenceManager,
    ) {
        let TermData::App(sym, args) = terms.get(atom) else {
            return;
        };
        if sym.name() != "str.contains" || args.len() != 2 {
            return;
        }
        let Some(empty_id) = state.empty_string_id() else {
            return;
        };

        let haystack = args[0];
        let needle = args[1];
        let haystack_rep = state.find(haystack);

        let mut components = Vec::new();
        Self::flatten_concat(terms, state, needle, &mut components);
        if components.len() < 2 {
            return;
        }

        // Check if any component is in the same EQC as haystack.
        let mut found_haystack = false;
        let mut haystack_comp = None;
        let mut extra = Vec::new();
        for &comp in &components {
            if state.find(comp) == haystack_rep && !found_haystack {
                found_haystack = true;
                haystack_comp = Some(comp);
            } else {
                extra.push(comp);
            }
        }

        if !found_haystack || extra.is_empty() {
            return;
        }

        // Explain: the contains assertion + why the component equals haystack.
        let mut explanation = vec![contains_lit];
        if let Some(hc) = haystack_comp {
            if hc != haystack {
                explanation.extend(state.explain(hc, haystack));
            }
        }
        for comp in extra {
            if !state.is_empty_string(terms, comp) {
                infer.add_internal_equality(
                    InferenceKind::EndpointEq,
                    comp,
                    empty_id,
                    explanation.clone(),
                );
            }
        }
    }

    /// CTN_LHS_EMPTYSTR: for positive str.contains("", x), infer x = "".
    ///
    /// The empty string only contains the empty string, so
    /// `str.contains("", x)` being true forces `x = ""`.
    /// CVC5 handles this in strings_entail.cpp and via reduction lemmas.
    pub(super) fn infer_contains_empty_haystack(
        terms: &TermStore,
        state: &SolverState,
        atom: TermId,
        contains_lit: TheoryLit,
        infer: &mut InferenceManager,
    ) {
        let TermData::App(sym, args) = terms.get(atom) else {
            return;
        };
        if sym.name() != "str.contains" || args.len() != 2 {
            return;
        }
        let Some(empty_id) = state.empty_string_id() else {
            return;
        };

        let haystack = args[0];
        let needle = args[1];

        // Only applies when haystack is known to be "".
        if !state.is_empty_string(terms, haystack) {
            return;
        }
        // If needle is already known empty, nothing to infer.
        if state.is_empty_string(terms, needle) {
            return;
        }

        // Explain: the contains assertion + why haystack is "".
        let mut explanation = vec![contains_lit];
        if haystack != empty_id && state.find(haystack) == state.find(empty_id) {
            explanation.extend(state.explain(haystack, empty_id));
        }
        infer.add_internal_equality(InferenceKind::EndpointEq, needle, empty_id, explanation);
    }

    /// Resolve an integer term to a concrete BigInt when possible.
    ///
    /// Resolution order:
    /// 1. Syntactic integer constant
    /// 2. `str.indexof(s, t, i)` with resolved arguments
    /// 3. `str.len(s)` with resolved string argument
    /// 4. `str.to_int(s)` with resolved string argument
    pub(in crate::core) fn resolve_int_term(
        terms: &TermStore,
        state: &SolverState,
        t: TermId,
        depth: usize,
    ) -> Option<BigInt> {
        if depth > Self::MAX_RESOLVE_DEPTH {
            return None;
        }

        let rep = state.find(t);
        // Check via EQC representative first, then direct term.
        if let TermData::Const(Constant::Int(n)) = terms.get(rep) {
            return Some(n.clone());
        }
        match terms.get(t) {
            TermData::Const(Constant::Int(n)) => Some(n.clone()),
            TermData::App(sym, args) => match sym.name() {
                "str.indexof" if args.len() == 3 => {
                    let s = Self::resolve_string_term(terms, state, args[0], depth + 1)?;
                    let pat = Self::resolve_string_term(terms, state, args[1], depth + 1)?;
                    let start = Self::resolve_int_term(terms, state, args[2], depth + 1)?;
                    Self::eval_str_indexof(&s, &pat, &start)
                }
                "str.len" if args.len() == 1 => {
                    let s = Self::resolve_string_term(terms, state, args[0], depth + 1)?;
                    Some(BigInt::from(s.chars().count()))
                }
                "str.to_int" | "str.to.int" if args.len() == 1 => {
                    let s = Self::resolve_string_term(terms, state, args[0], depth + 1)?;
                    Some(Self::eval_str_to_int(&s))
                }
                "str.to_code" if args.len() == 1 => {
                    let s = Self::resolve_string_term(terms, state, args[0], depth + 1)?;
                    Some(Self::eval_str_to_code(&s))
                }
                _ => None,
            },
            _ => None,
        }
    }

    // ── SMT-LIB string function evaluation ─────────────────────────────
    // Delegates to crate::eval for shared implementations (#5813).

    pub(super) fn eval_str_at(s: &str, i: &BigInt) -> Option<String> {
        crate::eval::eval_str_at(s, i)
    }

    pub(super) fn eval_str_substr(s: &str, i: &BigInt, n: &BigInt) -> Option<String> {
        crate::eval::eval_str_substr(s, i, n)
    }

    pub(super) fn eval_str_replace(s: &str, t: &str, u: &str) -> String {
        crate::eval::eval_str_replace(s, t, u)
    }

    pub(super) fn eval_str_indexof(s: &str, t: &str, start: &BigInt) -> Option<BigInt> {
        crate::eval::eval_str_indexof(s, t, start)
    }

    pub(super) fn eval_str_to_int(s: &str) -> BigInt {
        crate::eval::eval_str_to_int(s)
    }

    pub(super) fn eval_str_replace_all(s: &str, t: &str, u: &str) -> String {
        crate::eval::eval_str_replace_all(s, t, u)
    }

    /// Resolve a regex term to a literal string if it is `str.to_re("...")`.
    ///
    /// Returns `None` for non-literal regexes (union, star, etc.).
    /// Evaluate `str.replace_re(s, r, t)`: replace first regex match in s with t.
    ///
    /// SMT-LIB semantics: leftmost shortest match of r in s is replaced with t.
    /// If no match, returns s unchanged.
    pub(in crate::core) fn eval_str_replace_re(terms: &TermStore, s: &str, r: TermId, t: &str) -> Option<String> {
        match RegExpSolver::find_first_match(terms, s, r) {
            MatchResult::Found(start, end) => {
                let mut result = s[..start].to_string();
                result.push_str(t);
                result.push_str(&s[end..]);
                Some(result)
            }
            MatchResult::NoMatch => Some(s.to_string()),
            MatchResult::Incomplete => None,
        }
    }

    /// Evaluate `str.replace_re_all(s, r, t)`: replace all regex matches in s with t.
    ///
    /// SMT-LIB semantics: leftmost shortest non-overlapping matches.
    /// If regex matches empty string, each inter-character position gets one replacement.
    pub(in crate::core) fn eval_str_replace_re_all(terms: &TermStore, s: &str, r: TermId, t: &str) -> Option<String> {
        let mut result = String::new();
        let mut remaining = s;

        loop {
            if remaining.is_empty() {
                if RegExpSolver::evaluate(terms, "", r)? {
                    result.push_str(t);
                }
                break;
            }

            match RegExpSolver::find_first_match(terms, remaining, r) {
                MatchResult::Found(start, end) => {
                    result.push_str(&remaining[..start]);
                    result.push_str(t);
                    if start == end {
                        // Empty match: consume one character to avoid infinite loop.
                        if let Some(ch) = remaining[end..].chars().next() {
                            result.push(ch);
                            remaining = &remaining[end + ch.len_utf8()..];
                        } else {
                            break;
                        }
                    } else {
                        remaining = &remaining[end..];
                    }
                }
                MatchResult::NoMatch => {
                    result.push_str(remaining);
                    break;
                }
                MatchResult::Incomplete => return None,
            }
        }

        Some(result)
    }

    pub(super) fn eval_str_from_int(n: &BigInt) -> String {
        crate::eval::eval_str_from_int(n)
    }

    pub(super) fn eval_str_to_code(s: &str) -> BigInt {
        crate::eval::eval_str_to_code(s)
    }

    pub(super) fn eval_str_from_code(n: &BigInt) -> String {
        crate::eval::eval_str_from_code(n)
    }

}
