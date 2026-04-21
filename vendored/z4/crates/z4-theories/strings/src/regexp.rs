// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regex membership solver for ground `str.in_re` constraints.
//!
//! When both the string and regex resolve to concrete values, evaluates
//! membership by recursive descent over the regex structure. Non-ground
//! memberships are marked incomplete.
//!
//! The algorithm is equivalent to Brzozowski derivatives applied to concrete
//! strings, but avoids creating intermediate regex terms (TermStore is
//! immutable in the theory solver context).
//!
//! Reference: CVC5 `regexp_eval.cpp` and `regexp_operation.cpp` (BSD license).
//! Algorithm: Brzozowski, J.A. "Derivatives of Regular Expressions" (1964).

use z4_core::term::{Constant, TermData, TermId, TermStore};
use z4_core::{Symbol, TheoryLit};

use crate::infer::{InferenceKind, InferenceManager};
use crate::state::SolverState;

/// Result of searching for the first regex match in a string.
#[derive(Debug)]
pub(crate) enum MatchResult {
    /// Match found at byte range [start, end).
    Found(usize, usize),
    /// No match anywhere in the string.
    NoMatch,
    /// Regex contains unresolvable constructs.
    Incomplete,
}

/// Regex membership solver.
///
/// Evaluates `str.in_re(s, R)` assertions when both `s` and `R` are ground
/// (fully resolved to concrete values). Non-ground memberships are left
/// incomplete for the DPLL(T) loop to handle via splits.
pub(crate) struct RegExpSolver {
    /// Whether this check round found unresolvable regex memberships.
    incomplete: bool,
}

impl RegExpSolver {
    /// Create a new regex solver.
    pub(crate) fn new() -> Self {
        Self { incomplete: false }
    }

    /// Clear per-check state.
    pub(crate) fn clear(&mut self) {
        self.incomplete = false;
    }

    /// Whether the regex solver has unresolved memberships.
    pub(crate) fn is_incomplete(&self) -> bool {
        self.incomplete
    }

    /// Check all regex membership assertions.
    ///
    /// Scans assertions for `str.in_re(s, R)` atoms. For each:
    /// - If both `s` and `R` resolve to ground values, evaluates membership.
    /// - If the evaluation contradicts the asserted polarity, raises a conflict.
    /// - If either side is non-ground, marks incomplete.
    ///
    /// Returns true if a conflict was found.
    pub(crate) fn check(
        &mut self,
        terms: &TermStore,
        state: &SolverState,
        infer: &mut InferenceManager,
    ) -> bool {
        for &lit in state.assertions() {
            let (atom, polarity) = Self::atom_and_polarity(terms, lit);

            let TermData::App(sym, args) = terms.get(atom) else {
                continue;
            };

            if !matches!(sym.name(), "str.in_re" | "str.in.re") || args.len() != 2 {
                continue;
            }

            let string_term = args[0];
            let regex_term = args[1];

            // Try to resolve the string to a concrete value.
            let string_val = Self::resolve_string(terms, state, string_term);

            if let Some(ref s) = string_val {
                let result = Self::evaluate(terms, s, regex_term);
                match result {
                    Some(matches) => {
                        if matches != polarity {
                            // Evaluation contradicts asserted polarity.
                            // Explain: the membership literal + why string_term
                            // equals its constant representative.
                            let mut explanation = vec![lit];
                            if let Some(const_id) = state.find_constant_term_id(terms, string_term)
                            {
                                if const_id != string_term {
                                    explanation.extend(state.explain(string_term, const_id));
                                }
                            }
                            infer.add_conflict(InferenceKind::PredicateConflict, explanation);
                            return true;
                        }
                    }
                    None => {
                        // Could not evaluate (non-ground regex).
                        self.incomplete = true;
                    }
                }
            } else {
                // String not resolved.
                self.incomplete = true;
            }
        }

        infer.has_conflict()
    }

    /// Evaluate whether concrete string `s` matches regex term `r`.
    ///
    /// Returns `Some(true/false)` for ground regexes, `None` for non-ground.
    ///
    /// This is a recursive descent evaluator that works directly on the
    /// term representation without creating intermediate terms.
    pub(crate) fn evaluate(terms: &TermStore, s: &str, r: TermId) -> Option<bool> {
        let TermData::App(sym, args) = terms.get(r) else {
            return None;
        };

        match sym.name() {
            // re.none: empty language — nothing matches.
            "re.none" if args.is_empty() => Some(false),

            // re.all: universal language — everything matches.
            "re.all" if args.is_empty() => Some(true),

            // re.allchar: matches exactly one character.
            "re.allchar" if args.is_empty() => Some(s.chars().count() == 1),

            // re.range(lo, hi): matches a single character c with lo <= c <= hi.
            "re.range" if args.len() == 2 => {
                let lo = Self::resolve_string_const(terms, args[0])?;
                let hi = Self::resolve_string_const(terms, args[1])?;
                let lo_char = lo.chars().next()?;
                let hi_char = hi.chars().next()?;
                if s.chars().count() != 1 {
                    return Some(false);
                }
                let c = s.chars().next().unwrap();
                Some(lo_char <= c && c <= hi_char)
            }

            // str.to_re(t): matches exactly the string t.
            "str.to_re" | "str.to.re" if args.len() == 1 => {
                let t = Self::resolve_string_const(terms, args[0])?;
                Some(s == t)
            }

            // re.++(R1, R2, ...Rn): concatenation.
            // s matches iff s can be split into s1.s2...sn where si matches Ri.
            "re.++" if !args.is_empty() => {
                let children: Vec<_> = args.clone();
                Self::eval_concat(terms, s, &children, 0)
            }

            // re.union(R1, R2, ...): s matches iff s matches any Ri.
            "re.union" if !args.is_empty() => {
                for &child in args {
                    if Self::evaluate(terms, s, child)? {
                        return Some(true);
                    }
                }
                Some(false)
            }

            // re.inter(R1, R2, ...): s matches iff s matches all Ri.
            "re.inter" if !args.is_empty() => {
                for &child in args {
                    if !Self::evaluate(terms, s, child)? {
                        return Some(false);
                    }
                }
                Some(true)
            }

            // re.*(R): Kleene star. s matches iff s = "" or s can be split
            // into s1.s2...sn where each si is non-empty and matches R.
            "re.*" if args.len() == 1 => {
                if s.is_empty() {
                    return Some(true);
                }
                Self::eval_star(terms, s, args[0])
            }

            // re.+(R): one or more. s matches iff s is non-empty and can be
            // split into parts each matching R.
            "re.+" if args.len() == 1 => {
                if s.is_empty() {
                    return Self::delta(terms, args[0]);
                }
                Self::eval_star(terms, s, args[0])
            }

            // re.opt(R): zero or one. s matches iff s = "" or s matches R.
            "re.opt" if args.len() == 1 => {
                if s.is_empty() {
                    return Some(true);
                }
                Self::evaluate(terms, s, args[0])
            }

            // re.comp(R): complement. s matches iff s does NOT match R.
            "re.comp" if args.len() == 1 => Self::evaluate(terms, s, args[0]).map(|b| !b),

            // re.diff(R1, R2): difference. s matches iff s matches R1 and not R2.
            "re.diff" if args.len() == 2 => {
                let m1 = Self::evaluate(terms, s, args[0])?;
                if !m1 {
                    return Some(false);
                }
                let m2 = Self::evaluate(terms, s, args[1])?;
                Some(!m2)
            }

            // (_ re.loop n m) R: bounded repetition.
            // s matches iff s can be split into k pieces (n <= k <= m) each matching R.
            "re.loop" if args.len() == 1 => {
                let Symbol::Indexed(_, indices) = sym else {
                    return None;
                };
                if indices.len() != 2 {
                    return None;
                }
                let lo = indices[0] as usize;
                let hi = indices[1] as usize;
                if lo > hi {
                    return Some(false);
                }
                Self::eval_loop(terms, s, args[0], lo, hi)
            }

            _ => None,
        }
    }

    /// Evaluate concatenation: does `s` match `children[idx..]`?
    ///
    /// Tries all possible split points for the first child's match length.
    /// Uses backtracking to find a valid decomposition.
    fn eval_concat(terms: &TermStore, s: &str, children: &[TermId], idx: usize) -> Option<bool> {
        if idx >= children.len() {
            return Some(s.is_empty());
        }

        if idx == children.len() - 1 {
            // Last child must match the entire remaining string.
            return Self::evaluate(terms, s, children[idx]);
        }

        // Optimization: if current child is str.to_re(constant), only one
        // split point is valid (the constant must be a prefix).
        if let Some(prefix) = Self::fixed_string(terms, children[idx]) {
            if s.starts_with(prefix.as_str()) {
                return Self::eval_concat(terms, &s[prefix.len()..], children, idx + 1);
            } else {
                return Some(false);
            }
        }

        // General case: try all character-boundary split points.
        // Split at position i: s[..i] matches children[idx], s[i..] matches rest.
        let char_count = s.chars().count();
        for i in 0..=char_count {
            let byte_offset = s.char_indices().nth(i).map(|(b, _)| b).unwrap_or(s.len());
            let prefix = &s[..byte_offset];
            let suffix = &s[byte_offset..];

            if Self::evaluate(terms, prefix, children[idx])?
                && Self::eval_concat(terms, suffix, children, idx + 1)?
            {
                return Some(true);
            }
        }

        Some(false)
    }

    /// Evaluate Kleene star: does non-empty `s` match `R*`?
    ///
    /// Tries all non-empty prefixes of `s` that match `R`, then recursively
    /// checks the remainder against `R*`.
    fn eval_star(terms: &TermStore, s: &str, r: TermId) -> Option<bool> {
        if s.is_empty() {
            return Some(true);
        }

        // Optimization for str.to_re(constant) under star: the constant must
        // tile the string exactly.
        if let Some(pat) = Self::fixed_string(terms, r) {
            if pat.is_empty() {
                // (re.* (str.to_re "")) matches only "".
                return Some(s.is_empty());
            }
            // Check if s is a repetition of pat.
            let mut remaining = s;
            while !remaining.is_empty() {
                if remaining.starts_with(pat.as_str()) {
                    remaining = &remaining[pat.len()..];
                } else {
                    return Some(false);
                }
            }
            return Some(true);
        }

        // General case: try all non-empty prefix lengths.
        let char_count = s.chars().count();
        for len in 1..=char_count {
            let byte_offset = s.char_indices().nth(len).map(|(b, _)| b).unwrap_or(s.len());
            let prefix = &s[..byte_offset];
            let suffix = &s[byte_offset..];

            if Self::evaluate(terms, prefix, r)? && Self::eval_star(terms, suffix, r)? {
                return Some(true);
            }
        }

        Some(false)
    }

    /// Evaluate bounded repetition: does `s` match `R` repeated between `lo` and `hi` times?
    fn eval_loop(terms: &TermStore, s: &str, r: TermId, lo: usize, hi: usize) -> Option<bool> {
        if hi == 0 {
            return Some(s.is_empty());
        }
        if s.is_empty() {
            return Some(lo == 0);
        }
        let char_count = s.chars().count();
        for len in 1..=char_count {
            let byte_offset = s.char_indices().nth(len).map(|(b, _)| b).unwrap_or(s.len());
            let prefix = &s[..byte_offset];
            let suffix = &s[byte_offset..];

            if Self::evaluate(terms, prefix, r)? {
                let new_lo = lo.saturating_sub(1);
                if Self::eval_loop(terms, suffix, r, new_lo, hi - 1)? {
                    return Some(true);
                }
            }
        }
        Some(false)
    }

    /// Nullable check: does the regex accept the empty string?
    ///
    /// Returns `Some(true)` if nullable, `Some(false)` if not,
    /// `None` if unknown (non-ground regex).
    ///
    /// Reference: CVC5 `regexp_operation.cpp:124-264`.
    fn delta(terms: &TermStore, r: TermId) -> Option<bool> {
        let TermData::App(sym, args) = terms.get(r) else {
            return None;
        };

        match sym.name() {
            "re.none" if args.is_empty() => Some(false),
            "re.allchar" if args.is_empty() => Some(false),
            "re.all" if args.is_empty() => Some(true),
            "re.range" if args.len() == 2 => Some(false),

            "str.to_re" | "str.to.re" if args.len() == 1 => {
                let s = Self::resolve_string_const(terms, args[0])?;
                Some(s.is_empty())
            }

            "re.++" if !args.is_empty() => {
                for &child in args {
                    if !Self::delta(terms, child)? {
                        return Some(false);
                    }
                }
                Some(true)
            }

            "re.union" if !args.is_empty() => {
                for &child in args {
                    if Self::delta(terms, child)? {
                        return Some(true);
                    }
                }
                Some(false)
            }

            "re.inter" if !args.is_empty() => {
                for &child in args {
                    if !Self::delta(terms, child)? {
                        return Some(false);
                    }
                }
                Some(true)
            }

            "re.*" | "re.opt" if args.len() == 1 => Some(true),
            "re.+" if args.len() == 1 => Self::delta(terms, args[0]),
            "re.comp" if args.len() == 1 => Self::delta(terms, args[0]).map(|b| !b),

            "re.diff" if args.len() == 2 => {
                let d1 = Self::delta(terms, args[0])?;
                let d2 = Self::delta(terms, args[1])?;
                Some(d1 && !d2)
            }

            // (_ re.loop n m) R: nullable iff n == 0 or R is nullable.
            "re.loop" if args.len() == 1 => {
                let Symbol::Indexed(_, indices) = sym else {
                    return None;
                };
                if indices.len() != 2 {
                    return None;
                }
                if indices[0] == 0 {
                    Some(true)
                } else {
                    Self::delta(terms, args[0])
                }
            }

            _ => None,
        }
    }

    /// If `r` is `str.to_re(constant)`, return the constant string.
    fn fixed_string(terms: &TermStore, r: TermId) -> Option<String> {
        let TermData::App(sym, args) = terms.get(r) else {
            return None;
        };
        if !matches!(sym.name(), "str.to_re" | "str.to.re") || args.len() != 1 {
            return None;
        }
        Self::resolve_string_const(terms, args[0])
    }

    // ── String resolution helpers ──────────────────────────────────────

    /// Resolve a term to a concrete string constant via the term store.
    fn resolve_string_const(terms: &TermStore, t: TermId) -> Option<String> {
        match terms.get(t) {
            TermData::Const(Constant::String(s)) => Some(s.clone()),
            _ => None,
        }
    }

    /// Resolve a term to a concrete string using EQC representatives.
    fn resolve_string(terms: &TermStore, state: &SolverState, t: TermId) -> Option<String> {
        if let Some(s) = Self::resolve_string_const(terms, t) {
            return Some(s);
        }
        let rep = state.find(t);
        if rep != t {
            if let Some(s) = Self::resolve_string_const(terms, rep) {
                return Some(s);
            }
        }
        // Check EQC info for a constant value.
        state.get_eqc(&rep).and_then(|info| info.constant.clone())
    }

    /// Normalize a theory literal into `(atom, expected_truth_value)`.
    fn atom_and_polarity(terms: &TermStore, lit: TheoryLit) -> (TermId, bool) {
        let mut term = lit.term;
        let mut polarity = lit.value;
        while let TermData::Not(inner) = terms.get(term) {
            term = *inner;
            polarity = !polarity;
        }
        (term, polarity)
    }

    /// Find the first (leftmost shortest) match of regex `r` in string `s`.
    ///
    /// Tries every start position and returns the shortest match at the
    /// leftmost position. Returns `Incomplete` if the regex contains
    /// constructs that `evaluate()` cannot handle.
    pub(crate) fn find_first_match(terms: &TermStore, s: &str, r: TermId) -> MatchResult {
        let chars: Vec<char> = s.chars().collect();
        for start in 0..=chars.len() {
            let start_byte = chars[..start].iter().map(|c| c.len_utf8()).sum::<usize>();
            for end in start..=chars.len() {
                let end_byte = chars[..end].iter().map(|c| c.len_utf8()).sum::<usize>();
                let substr = &s[start_byte..end_byte];
                match Self::evaluate(terms, substr, r) {
                    Some(true) => return MatchResult::Found(start_byte, end_byte),
                    Some(false) => {}
                    None => return MatchResult::Incomplete,
                }
            }
        }
        MatchResult::NoMatch
    }
}

#[allow(clippy::panic)]
#[cfg(test)]
#[path = "regexp_tests.rs"]
mod tests;
