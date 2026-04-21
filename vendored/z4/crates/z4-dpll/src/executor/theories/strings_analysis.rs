// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! String formula analysis helpers: length bounds, alphabet collection,
//! candidate generation, and decomposition concat collection.
//!
//! Extracted from `strings.rs` for code health (#5970). These helpers
//! are shared by both `strings.rs` (QF_S) and `strings_lia.rs` (QF_SLIA).

use z4_core::term::{Constant, Symbol, TermData, TermId};
use z4_core::Sort;

use super::super::Executor;

/// Allow a small number of repeated string lemma requests before declaring stall.
///
/// A single immediate repeat can still make progress after SAT explores the
/// updated search space from prior splits. We only treat the loop as stalled
/// after multiple consecutive repeats of the exact same lemma.
pub(super) const MAX_CONSECUTIVE_DUPLICATE_LEMMAS: usize = 5;

/// Maximum upper bound for a pivot variable to be eligible for enumeration.
/// Variables with len > this are too expensive to enumerate character by character.
const MAX_PIVOT_BOUND: usize = 3;

/// Maximum number of candidate values to enumerate before falling back.
pub(super) const MAX_PIVOT_CANDIDATES: usize = 200;

/// Detected length bound for a string variable.
pub(super) struct LengthBound {
    /// The variable's TermId
    pub(super) var: TermId,
    pub(super) lower: usize,
    pub(super) upper: usize,
}

impl Executor {
    fn known_exact_string_length(
        &self,
        term: TermId,
        exact_var_lengths: &hashbrown::HashMap<TermId, usize>,
        visiting: &mut hashbrown::HashSet<TermId>,
    ) -> Option<usize> {
        if let Some(&len) = exact_var_lengths.get(&term) {
            return Some(len);
        }

        if !visiting.insert(term) {
            return None;
        }

        let result = match self.ctx.terms.get(term) {
            TermData::Const(Constant::String(s)) => Some(s.chars().count()),
            TermData::App(Symbol::Named(name), args) if name == "str.++" => {
                let mut total = 0usize;
                for &arg in args {
                    let len = self.known_exact_string_length(arg, exact_var_lengths, visiting)?;
                    total = total.checked_add(len)?;
                }
                Some(total)
            }
            _ => None,
        };

        visiting.remove(&term);
        result
    }

    /// Detect direct string equalities whose exact lengths already contradict.
    ///
    /// This catches formulas like `(= (str.++ x y) "abc")` together with
    /// exact length facts `len(x)=2` and `len(y)=2`, which are UNSAT even
    /// before the string normal-form solver starts splitting.
    pub(super) fn has_exact_string_length_contradiction(&self, assertions: &[TermId]) -> bool {
        let exact_var_lengths: hashbrown::HashMap<TermId, usize> = self
            .detect_bounded_string_vars_in(assertions)
            .into_iter()
            .filter(|bound| bound.lower == bound.upper)
            .map(|bound| (bound.var, bound.lower))
            .collect();

        assertions.iter().copied().any(|assertion| {
            let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(assertion) else {
                return false;
            };
            if name != "=" || args.len() != 2 {
                return false;
            }
            if *self.ctx.terms.sort(args[0]) != Sort::String
                || *self.ctx.terms.sort(args[1]) != Sort::String
            {
                return false;
            }

            let mut visiting = hashbrown::HashSet::new();
            match (
                self.known_exact_string_length(args[0], &exact_var_lengths, &mut visiting),
                self.known_exact_string_length(args[1], &exact_var_lengths, &mut visiting),
            ) {
                (Some(lhs), Some(rhs)) => lhs != rhs,
                _ => false,
            }
        })
    }

    /// Collect witness concat terms introduced by preregistered decomposition clauses.
    ///
    /// Contains/prefix/suffix preregistration emits implication clauses whose
    /// conclusions are equalities like `x = str.++(sk_pre, y, sk_post)`. These
    /// concat terms are branch-local witnesses, not user-level word equations,
    /// so normal-form checking must ignore them the same way it ignores extf
    /// reduction concats.
    pub(super) fn collect_decomposition_concat_terms(&self, assertions: &[TermId]) -> Vec<TermId> {
        use hashbrown::HashSet;

        let mut reduced = Vec::new();
        let mut seen_terms = HashSet::new();
        let mut visited = HashSet::new();
        let mut stack: Vec<TermId> = assertions.to_vec();

        while let Some(term) = stack.pop() {
            if !visited.insert(term) {
                continue;
            }
            match self.ctx.terms.get(term) {
                TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2 => {
                    for &side in args {
                        if matches!(self.ctx.terms.get(side), TermData::App(sym, _) if sym.name() == "str.++")
                            && seen_terms.insert(side)
                        {
                            reduced.push(side);
                        }
                    }
                    stack.extend(args.iter().copied());
                }
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, t, e) => {
                    stack.push(*c);
                    stack.push(*t);
                    stack.push(*e);
                }
                TermData::Let(bindings, body) => {
                    for (_, value) in bindings {
                        stack.push(*value);
                    }
                    stack.push(*body);
                }
                TermData::Const(_)
                | TermData::Var(_, _)
                | TermData::Forall(_, _, _)
                | TermData::Exists(_, _, _)
                | _ => {}
            }
        }

        reduced
    }

    /// Detect string variables with bounded lengths from assertion constraints.
    ///
    /// Looks for patterns like `(<= (* (str.len X) k) c)` and
    /// `(>= (* (str.len X) k) c)` in the assertion set and extracts
    /// integer bounds on variable lengths.
    pub(super) fn detect_bounded_string_vars(&self) -> Vec<LengthBound> {
        self.detect_bounded_string_vars_in(&self.ctx.assertions)
    }

    /// Detect string variables with bounded lengths from an explicit assertion set.
    pub(super) fn detect_bounded_string_vars_in(&self, assertions: &[TermId]) -> Vec<LengthBound> {
        use hashbrown::HashMap;
        // Map: variable TermId → (lower_bound, upper_bound)
        let mut bounds: HashMap<TermId, (Option<usize>, Option<usize>)> = HashMap::new();

        for &assertion in assertions {
            self.extract_length_bound_from_term(assertion, &mut bounds);
        }

        bounds
            .into_iter()
            .filter_map(|(var, (lo, hi))| {
                let lower = lo.unwrap_or(0);
                let upper = hi?;
                if upper <= MAX_PIVOT_BOUND {
                    debug_assert!(
                        lower <= upper,
                        "BUG: detect_bounded_string_vars: lower {lower} > upper {upper} for var {var:?}"
                    );
                    Some(LengthBound { var, lower, upper })
                } else {
                    None
                }
            })
            .collect()
    }

    /// Extract a length bound from a single assertion term.
    ///
    /// Recognizes patterns:
    /// - `(<= (* (str.len X) k) c)` → len(X) <= c/k
    /// - `(>= (* (str.len X) k) c)` → len(X) >= ceil(c/k)
    /// - `(<= (str.len X) c)` → len(X) <= c
    /// - `(>= (str.len X) c)` → len(X) >= c
    fn extract_length_bound_from_term(
        &self,
        term: TermId,
        bounds: &mut hashbrown::HashMap<TermId, (Option<usize>, Option<usize>)>,
    ) {
        let terms = &self.ctx.terms;
        match terms.get(term) {
            TermData::App(Symbol::Named(op), args) if args.len() == 2 => {
                let is_le = op == "<=";
                let is_ge = op == ">=";
                let is_eq = op == "=";
                if !is_le && !is_ge && !is_eq {
                    return;
                }
                // Try to extract (str.len var, coefficient, rhs_constant).
                // For equality, also check the reverse direction: (= 3 (str.len x)).
                let parsed = Self::parse_scaled_strlen(terms, args[0], args[1]).or_else(|| {
                    if is_eq {
                        Self::parse_scaled_strlen(terms, args[1], args[0])
                    } else {
                        None
                    }
                });
                if let Some((var, coeff, rhs)) = parsed {
                    if coeff == 0 {
                        return;
                    }
                    let entry = bounds.entry(var).or_insert((None, None));
                    if is_eq {
                        // len(var) = rhs/coeff — sets both bounds (#7460).
                        let bound = rhs / coeff;
                        entry.0 = Some(entry.0.map_or(bound, |prev: usize| prev.max(bound)));
                        entry.1 = Some(entry.1.map_or(bound, |prev: usize| prev.min(bound)));
                    } else if is_le {
                        // coeff * len(var) <= rhs → len(var) <= rhs / coeff
                        let bound = rhs / coeff;
                        entry.1 = Some(entry.1.map_or(bound, |prev: usize| prev.min(bound)));
                    } else {
                        // coeff * len(var) >= rhs → len(var) >= ceil(rhs / coeff)
                        let bound = rhs.div_ceil(coeff);
                        entry.0 = Some(entry.0.map_or(bound, |prev: usize| prev.max(bound)));
                    }
                }
            }
            _ => {}
        }
    }

    /// Parse a term that represents `k * str.len(var)` or just `str.len(var)`.
    /// Returns `(var, coefficient, rhs_constant)` if recognized.
    fn parse_scaled_strlen(
        terms: &z4_core::term::TermStore,
        lhs: TermId,
        rhs: TermId,
    ) -> Option<(TermId, usize, usize)> {
        // rhs must be an integer constant
        let rhs_val = match terms.get(rhs) {
            TermData::Const(Constant::Int(n)) => usize::try_from(n).ok()?,
            _ => return None,
        };
        // lhs is either str.len(var) or (* (str.len var) k) or (* k (str.len var))
        match terms.get(lhs) {
            TermData::App(Symbol::Named(name), args) if name == "str.len" && args.len() == 1 => {
                // Simple: str.len(var)
                let var = args[0];
                if matches!(terms.get(var), TermData::Var(..)) {
                    Some((var, 1, rhs_val))
                } else {
                    None
                }
            }
            TermData::App(Symbol::Named(name), args) if name == "*" && args.len() == 2 => {
                // Scaled: (* (str.len var) k) or (* k (str.len var))
                let (strlen_arg, coeff_arg) = if Self::is_strlen_of_var(terms, args[0]) {
                    (args[0], args[1])
                } else if Self::is_strlen_of_var(terms, args[1]) {
                    (args[1], args[0])
                } else {
                    return None;
                };
                let coeff = match terms.get(coeff_arg) {
                    TermData::Const(Constant::Int(n)) => usize::try_from(n).ok()?,
                    _ => return None,
                };
                // Extract var from str.len(var)
                match terms.get(strlen_arg) {
                    TermData::App(_, args) if !args.is_empty() => Some((args[0], coeff, rhs_val)),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// Check if a term is `str.len(var)` where var is a string variable.
    fn is_strlen_of_var(terms: &z4_core::term::TermStore, term: TermId) -> bool {
        matches!(terms.get(term),
            TermData::App(Symbol::Named(name), args)
                if name == "str.len" && args.len() == 1
                    && matches!(terms.get(args[0]), TermData::Var(..)))
    }

    /// Collect the alphabet (unique characters) from all string constants in the formula.
    pub(super) fn collect_alphabet(&self) -> Vec<char> {
        let mut chars = hashbrown::HashSet::new();
        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        let mut visited = hashbrown::HashSet::new();
        while let Some(tid) = stack.pop() {
            if !visited.insert(tid) {
                continue;
            }
            match self.ctx.terms.get(tid) {
                TermData::Const(Constant::String(s)) => {
                    chars.extend(s.chars());
                }
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, t, e) => {
                    stack.push(*c);
                    stack.push(*t);
                    stack.push(*e);
                }
                _ => {}
            }
        }
        let mut result: Vec<char> = chars.into_iter().collect();
        result.sort_unstable();
        result
    }

    /// Generate all candidate strings of a given length from an alphabet.
    pub(super) fn generate_candidates(
        alphabet: &[char],
        lower: usize,
        upper: usize,
    ) -> Vec<String> {
        let mut candidates = Vec::new();
        for len in lower..=upper {
            if len == 0 {
                candidates.push(String::new());
                continue;
            }
            // Generate all strings of exactly `len` characters from alphabet
            let mut indices = vec![0usize; len];
            loop {
                let s: String = indices.iter().map(|&i| alphabet[i]).collect();
                candidates.push(s);
                if candidates.len() >= MAX_PIVOT_CANDIDATES {
                    return candidates;
                }
                // Increment indices (odometer-style)
                let mut pos = len - 1;
                loop {
                    indices[pos] += 1;
                    if indices[pos] < alphabet.len() {
                        break;
                    }
                    indices[pos] = 0;
                    if pos == 0 {
                        // Done with this length
                        break;
                    }
                    pos -= 1;
                }
                if pos == 0 && indices[0] == 0 {
                    break; // All strings of this length generated
                }
            }
        }
        debug_assert!(
            candidates.iter().all(|s| {
                let len = s.chars().count();
                len >= lower && len <= upper
            }),
            "BUG: generate_candidates produced string with length outside [{lower}, {upper}]"
        );
        candidates
    }
}
