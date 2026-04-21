// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Ground string evaluation helpers.
//!
//! Syntactic ground evaluation of string-sorted and integer-sorted terms
//! using only term-store constants (no solver state needed).

use num_bigint::BigInt;
use z4_core::term::{Constant, Symbol, TermData};
use z4_core::{Sort, TermId};

use super::super::Executor;

impl Executor {
    /// Returns true if `term` is syntactically fixed to a concrete string.
    pub(super) fn term_has_ground_string_value(
        &self,
        ground_string_terms: &hashbrown::HashSet<TermId>,
        term: TermId,
    ) -> bool {
        matches!(
            self.ctx.terms.get(term),
            TermData::Const(Constant::String(_))
        ) || ground_string_terms.contains(&term)
    }

    /// Collect terms that are fixed to a single string constant by top-level
    /// conjunction equalities in `assertions`.
    pub(super) fn collect_top_level_ground_string_terms(
        &self,
        assertions: &[TermId],
    ) -> hashbrown::HashSet<TermId> {
        let mut eq_graph: hashbrown::HashMap<TermId, Vec<TermId>> = hashbrown::HashMap::new();
        let mut eq_nodes: hashbrown::HashSet<TermId> = hashbrown::HashSet::new();

        let mut stack: Vec<TermId> = assertions.to_vec();
        while let Some(term) = stack.pop() {
            match self.ctx.terms.get(term) {
                TermData::App(Symbol::Named(name), args) if name == "and" => {
                    let args_copy: Vec<TermId> = args.clone();
                    for arg in args_copy {
                        stack.push(arg);
                    }
                }
                TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2 => {
                    let lhs = args[0];
                    let rhs = args[1];
                    if *self.ctx.terms.sort(lhs) == Sort::String
                        && *self.ctx.terms.sort(rhs) == Sort::String
                    {
                        eq_graph.entry(lhs).or_default().push(rhs);
                        eq_graph.entry(rhs).or_default().push(lhs);
                        eq_nodes.insert(lhs);
                        eq_nodes.insert(rhs);
                    }
                }
                _ => {}
            }
        }

        let mut ground_terms = hashbrown::HashSet::new();
        let mut visited = hashbrown::HashSet::new();

        for &root in &eq_nodes {
            if !visited.insert(root) {
                continue;
            }

            let mut component = Vec::new();
            let mut component_stack = vec![root];
            let mut unique_constant: Option<TermId> = None;
            let mut has_conflicting_constants = false;

            while let Some(current) = component_stack.pop() {
                component.push(current);

                if let TermData::Const(Constant::String(_)) = self.ctx.terms.get(current) {
                    if let Some(existing) = unique_constant {
                        if existing != current {
                            has_conflicting_constants = true;
                        }
                    } else {
                        unique_constant = Some(current);
                    }
                }

                if let Some(neighbors) = eq_graph.get(&current) {
                    for &next in neighbors {
                        if visited.insert(next) {
                            component_stack.push(next);
                        }
                    }
                }
            }

            if unique_constant.is_some() && !has_conflicting_constants {
                ground_terms.extend(component);
            }
        }

        ground_terms
    }

    /// Build an index mapping each term to the set of concat leaf components
    /// it is syntactically equated to in the assertions.
    pub(super) fn build_concat_component_index(
        &self,
        assertions: &[TermId],
    ) -> hashbrown::HashMap<TermId, hashbrown::HashSet<TermId>> {
        let mut index: hashbrown::HashMap<TermId, hashbrown::HashSet<TermId>> =
            hashbrown::HashMap::new();
        for &a in assertions {
            let mut eq_stack = vec![a];
            while let Some(t) = eq_stack.pop() {
                match self.ctx.terms.get(t) {
                    TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2 => {
                        let lhs = args[0];
                        let rhs = args[1];
                        let mut lhs_leaves = Vec::new();
                        Self::collect_concat_leaves(&self.ctx.terms, lhs, &mut lhs_leaves);
                        if lhs_leaves.len() > 1 {
                            let set: hashbrown::HashSet<TermId> =
                                lhs_leaves.iter().copied().collect();
                            index.entry(rhs).or_default().extend(&set);
                            index.entry(lhs).or_default().extend(&set);
                        }
                        let mut rhs_leaves = Vec::new();
                        Self::collect_concat_leaves(&self.ctx.terms, rhs, &mut rhs_leaves);
                        if rhs_leaves.len() > 1 {
                            let set: hashbrown::HashSet<TermId> =
                                rhs_leaves.iter().copied().collect();
                            index.entry(lhs).or_default().extend(&set);
                            index.entry(rhs).or_default().extend(&set);
                        }
                    }
                    TermData::App(Symbol::Named(name), args) if name == "and" => {
                        for &arg in args.iter() {
                            eq_stack.push(arg);
                        }
                    }
                    _ => {}
                }
            }
        }
        index
    }

    /// Collect leaf components of a syntactic concat term.
    pub(super) fn collect_concat_leaves(
        terms: &z4_core::TermStore,
        t: TermId,
        out: &mut Vec<TermId>,
    ) {
        match terms.get(t) {
            TermData::App(sym, args) if sym.name() == "str.++" => {
                for &arg in args {
                    Self::collect_concat_leaves(terms, arg, out);
                }
            }
            _ => out.push(t),
        }
    }

    /// Check if `needle` appears as a syntactic component of `haystack`'s
    /// concat structure (using the pre-built component index).
    pub(super) fn needle_in_concat_components(
        concat_components: &hashbrown::HashMap<TermId, hashbrown::HashSet<TermId>>,
        terms: &z4_core::TermStore,
        haystack: TermId,
        needle: TermId,
    ) -> bool {
        let Some(components) = concat_components.get(&haystack) else {
            return false;
        };
        // Direct match: needle term is a component.
        if components.contains(&needle) {
            return true;
        }
        // Constant substring match: if needle is a string constant, check if
        // any constant component contains it.
        if let TermData::Const(Constant::String(needle_str)) = terms.get(needle) {
            for &comp in components {
                if let TermData::Const(Constant::String(comp_str)) = terms.get(comp) {
                    if comp_str.contains(needle_str.as_str()) {
                        return true;
                    }
                }
            }
        }
        false
    }

    /// Fold fully-ground string operations to constants pre-Tseitin.
    ///
    /// Walks each assertion's DAG bottom-up: when a string operation has all
    /// constant arguments, evaluate it and replace the term with the result.
    /// This eliminates ground computation from the SAT encoding.
    pub(super) fn fold_ground_string_ops(&mut self, assertions: &[TermId]) -> Vec<TermId> {
        let mut cache: hashbrown::HashMap<TermId, TermId> = hashbrown::HashMap::new();
        assertions
            .iter()
            .map(|&t| self.rewrite_ground_string_ops(t, &mut cache))
            .collect()
    }

    fn rewrite_ground_string_ops(
        &mut self,
        term: TermId,
        cache: &mut hashbrown::HashMap<TermId, TermId>,
    ) -> TermId {
        if let Some(&cached) = cache.get(&term) {
            return cached;
        }
        let result = match self.ctx.terms.get(term).clone() {
            TermData::App(ref sym, ref args) if !args.is_empty() => {
                let new_args: Vec<TermId> = args
                    .iter()
                    .map(|&a| self.rewrite_ground_string_ops(a, cache))
                    .collect();
                let changed = new_args.iter().zip(args.iter()).any(|(a, b)| a != b);
                let rebuilt = if changed {
                    // Use mk_eq for equality nodes so constant-folding fires
                    if sym.name() == "=" && new_args.len() == 2 {
                        self.ctx.terms.mk_eq(new_args[0], new_args[1])
                    } else {
                        self.ctx.terms.mk_app(
                            sym.clone(),
                            new_args,
                            self.ctx.terms.sort(term).clone(),
                        )
                    }
                } else {
                    term
                };
                // Try to evaluate the rebuilt term if it's now ground
                self.fold_ground_evaluated_term(rebuilt)
            }
            TermData::Not(inner) => {
                let new_inner = self.rewrite_ground_string_ops(inner, cache);
                if new_inner != inner {
                    self.ctx.terms.mk_not(new_inner)
                } else {
                    term
                }
            }
            TermData::Ite(c, t, e) => {
                let nc = self.rewrite_ground_string_ops(c, cache);
                let nt = self.rewrite_ground_string_ops(t, cache);
                let ne = self.rewrite_ground_string_ops(e, cache);
                if nc != c || nt != t || ne != e {
                    self.ctx.terms.mk_ite(nc, nt, ne)
                } else {
                    term
                }
            }
            _ => term,
        };
        cache.insert(term, result);
        result
    }

    fn fold_ground_evaluated_term(&mut self, term: TermId) -> TermId {
        // Try string evaluation
        if let Some(s) = ground_eval_string_term(&self.ctx.terms, term) {
            return self.ctx.terms.mk_string(s);
        }
        // Try int evaluation (str.len, str.indexof, etc.)
        if let Some(i) = ground_eval_int_term(&self.ctx.terms, term) {
            return self.ctx.terms.mk_int(i);
        }
        // Try bool evaluation (str.contains, str.prefixof, etc.)
        if let Some(b) = self.ground_eval_bool_term(term) {
            return self.ctx.terms.mk_bool(b);
        }
        term
    }

    fn ground_eval_bool_term(&self, term: TermId) -> Option<bool> {
        match self.ctx.terms.get(term) {
            TermData::App(Symbol::Named(name), args) => match name.as_str() {
                "str.contains" if args.len() == 2 => {
                    let s = ground_eval_string_term(&self.ctx.terms, args[0])?;
                    let t = ground_eval_string_term(&self.ctx.terms, args[1])?;
                    Some(s.contains(&*t))
                }
                "str.prefixof" if args.len() == 2 => {
                    let p = ground_eval_string_term(&self.ctx.terms, args[0])?;
                    let s = ground_eval_string_term(&self.ctx.terms, args[1])?;
                    Some(s.starts_with(&*p))
                }
                "str.suffixof" if args.len() == 2 => {
                    let suf = ground_eval_string_term(&self.ctx.terms, args[0])?;
                    let s = ground_eval_string_term(&self.ctx.terms, args[1])?;
                    Some(s.ends_with(&*suf))
                }
                "str.is_digit" if args.len() == 1 => {
                    let s = ground_eval_string_term(&self.ctx.terms, args[0])?;
                    Some(s.len() == 1 && s.chars().next().is_some_and(|c| c.is_ascii_digit()))
                }
                _ => None,
            },
            _ => None,
        }
    }
}

/// Syntactic ground evaluation of a string-sorted term.
///
/// Returns `Some(s)` if the term can be fully evaluated to a concrete string
/// using only syntactic constants in the term store (no EQC lookup, no solver
/// state). This handles the case where extended functions like `str.replace`
/// appear inside `str.len` with all-constant arguments.
///
/// CVC5 reference: `extf_solver.cpp:295-530` (partial evaluation pipeline).
pub(super) fn ground_eval_string_term(terms: &z4_core::TermStore, t: TermId) -> Option<String> {
    match terms.get(t) {
        TermData::Const(Constant::String(s)) => Some(s.clone()),
        TermData::App(Symbol::Named(name), args) => match name.as_str() {
            "str.++" => {
                let mut result = String::new();
                for &arg in args {
                    result.push_str(&ground_eval_string_term(terms, arg)?);
                }
                Some(result)
            }
            "str.replace" if args.len() == 3 => {
                let s = ground_eval_string_term(terms, args[0])?;
                let pattern = ground_eval_string_term(terms, args[1])?;
                let replacement = ground_eval_string_term(terms, args[2])?;
                if pattern.is_empty() {
                    let mut r = replacement;
                    r.push_str(&s);
                    Some(r)
                } else {
                    match s.find(&*pattern) {
                        Some(pos) => {
                            let mut r = s[..pos].to_string();
                            r.push_str(&replacement);
                            r.push_str(&s[pos + pattern.len()..]);
                            Some(r)
                        }
                        None => Some(s),
                    }
                }
            }
            "str.replace_all" if args.len() == 3 => {
                let s = ground_eval_string_term(terms, args[0])?;
                let pattern = ground_eval_string_term(terms, args[1])?;
                let replacement = ground_eval_string_term(terms, args[2])?;
                if pattern.is_empty() {
                    Some(s)
                } else {
                    Some(s.replace(&*pattern, &replacement))
                }
            }
            "str.substr" if args.len() == 3 => {
                let s = ground_eval_string_term(terms, args[0])?;
                let start = ground_eval_int_term(terms, args[1])?;
                let len = ground_eval_int_term(terms, args[2])?;
                eval_substr(&s, &start, &len)
            }
            "str.at" if args.len() == 2 => {
                let s = ground_eval_string_term(terms, args[0])?;
                let i = ground_eval_int_term(terms, args[1])?;
                eval_str_at(&s, &i)
            }
            "str.from_int" | "int.to.str" if args.len() == 1 => {
                let n = ground_eval_int_term(terms, args[0])?;
                if n < BigInt::from(0) {
                    Some(String::new())
                } else {
                    Some(n.to_string())
                }
            }
            "str.from_code" if args.len() == 1 => {
                let n = ground_eval_int_term(terms, args[0])?;
                let code: i64 = n.try_into().ok()?;
                if !(0..=196_607).contains(&code) {
                    Some(String::new())
                } else {
                    char::from_u32(code as u32)
                        .map(|c| c.to_string())
                        .or(Some(String::new()))
                }
            }
            "str.to_lower" if args.len() == 1 => {
                let s = ground_eval_string_term(terms, args[0])?;
                Some(s.to_lowercase())
            }
            "str.to_upper" if args.len() == 1 => {
                let s = ground_eval_string_term(terms, args[0])?;
                Some(s.to_uppercase())
            }
            "str.replace_re" if args.len() == 3 => {
                let s = ground_eval_string_term(terms, args[0])?;
                let t = ground_eval_string_term(terms, args[2])?;
                // args[1] is a RegLan term — evaluate structurally.
                z4_strings::ground_eval_replace_re(terms, &s, args[1], &t)
            }
            "str.replace_re_all" if args.len() == 3 => {
                let s = ground_eval_string_term(terms, args[0])?;
                let t = ground_eval_string_term(terms, args[2])?;
                z4_strings::ground_eval_replace_re_all(terms, &s, args[1], &t)
            }
            _ => None,
        },
        _ => None,
    }
}

/// Syntactic ground evaluation of an integer-sorted term.
///
/// Returns `Some(n)` if the term is a syntactic integer constant.
/// Does not handle arithmetic expressions — only literal constants.
pub(super) fn ground_eval_int_term(terms: &z4_core::TermStore, t: TermId) -> Option<BigInt> {
    match terms.get(t) {
        TermData::Const(Constant::Int(n)) => Some(n.clone()),
        // Handle negation: (- n) where n is a positive constant.
        TermData::App(Symbol::Named(name), args) if name == "-" && args.len() == 1 => {
            let inner = ground_eval_int_term(terms, args[0])?;
            Some(-inner)
        }
        _ => None,
    }
}

/// SMT-LIB `str.substr(s, start, len)` with ground arguments.
pub(super) fn eval_substr(s: &str, start: &BigInt, len: &BigInt) -> Option<String> {
    let zero = BigInt::from(0);
    if *start < zero || *len <= zero {
        return Some(String::new());
    }
    let start_usize: usize = start.try_into().ok()?;
    let len_usize: usize = len.try_into().ok()?;
    let chars: Vec<char> = s.chars().collect();
    if start_usize >= chars.len() {
        return Some(String::new());
    }
    debug_assert!(
        start_usize.checked_add(len_usize).is_some(),
        "BUG: eval_substr overflow: start {start_usize} + len {len_usize} overflows usize"
    );
    let end = std::cmp::min(start_usize + len_usize, chars.len());
    Some(chars[start_usize..end].iter().collect())
}

/// SMT-LIB `str.at(s, i)` with ground arguments.
pub(super) fn eval_str_at(s: &str, i: &BigInt) -> Option<String> {
    let zero = BigInt::from(0);
    if *i < zero {
        return Some(String::new());
    }
    let idx: usize = i.try_into().ok()?;
    let chars: Vec<char> = s.chars().collect();
    if idx >= chars.len() {
        Some(String::new())
    } else {
        Some(chars[idx].to_string())
    }
}

/// Compute the minimum length a string must have to contain both `s1` and `s2`.
///
/// The two patterns may overlap in x: a suffix of one can be a prefix of the
/// other, reducing the combined footprint. The minimum combined length is:
///   `len(s1) + len(s2) - max_suffix_prefix_overlap(s1, s2)`
///
/// where `max_suffix_prefix_overlap(a, b)` is `max(spo(a,b), spo(b,a))` and
/// `spo(a, b)` is the length of the longest suffix of `a` that is a prefix of `b`.
///
/// Example: "ab" and "cd" → overlap 0 → min len 4
/// Example: "ab" and "bc" → overlap 1 → min len 3
/// Example: "abc" and "abc" → overlap 3 → min len 3
pub(super) fn multi_contains_min_len(s1: &str, s2: &str) -> usize {
    let len1 = s1.chars().count();
    let len2 = s2.chars().count();
    let overlap = suffix_prefix_overlap(s1, s2).max(suffix_prefix_overlap(s2, s1));
    len1 + len2 - overlap
}

/// Length of the longest suffix of `a` that is a prefix of `b`.
pub(super) fn suffix_prefix_overlap(a: &str, b: &str) -> usize {
    let a_chars: Vec<char> = a.chars().collect();
    let b_chars: Vec<char> = b.chars().collect();
    let max_check = a_chars.len().min(b_chars.len());
    for overlap in (1..=max_check).rev() {
        if a_chars[a_chars.len() - overlap..] == b_chars[..overlap] {
            return overlap;
        }
    }
    0
}

#[cfg(test)]
mod tests;
