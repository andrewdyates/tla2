// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Ground sequence reconstruction and evaluation helpers.

use num_traits::ToPrimitive;

use z4_core::term::{Constant, Symbol, TermData, TermId};

use super::super::super::Executor;

impl Executor {
    /// Build a map from variables to ground sequence expressions from equality
    /// assertions. When we see `(= x EXPR)` or `(= EXPR x)` where `x` is a
    /// variable and `EXPR` is a ground sequence (composed of seq.unit/seq.++/
    /// seq.empty over constants), record the mapping.
    ///
    /// Also reconstructs ground sequences from nth constraints (#6028):
    /// when a variable `s` has `(= (seq.len s) n)` and all `n` elements
    /// defined via `(= (seq.nth s 0) c0) ... (= (seq.nth s (n-1)) c_{n-1})`,
    /// synthesizes `seq.++(seq.unit(c0), ...)` and adds it to the map.
    ///
    /// Used by `generate_seq_contains_axioms` to evaluate ground contains
    /// and fix false-SAT (#6024, #6028).
    pub(super) fn build_ground_seq_map(&mut self) -> hashbrown::HashMap<TermId, TermId> {
        let mut map = hashbrown::HashMap::new();

        // Pass 1: direct variable-to-ground-seq equalities
        for &assertion in &self.ctx.assertions {
            if let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(assertion) {
                if name == "=" && args.len() == 2 {
                    let (a, b) = (args[0], args[1]);
                    if matches!(self.ctx.terms.get(a), TermData::Var(..))
                        && self.try_extract_ground_seq(b).is_some()
                    {
                        map.insert(a, b);
                    } else if matches!(self.ctx.terms.get(b), TermData::Var(..))
                        && self.try_extract_ground_seq(a).is_some()
                    {
                        map.insert(b, a);
                    }
                }
            }
        }

        // Pass 2: reconstruct ground sequences from nth + len constraints (#6028).
        let mut len_map: hashbrown::HashMap<TermId, usize> = hashbrown::HashMap::new();
        let mut nth_map: hashbrown::HashMap<TermId, Vec<(usize, TermId)>> =
            hashbrown::HashMap::new();

        for &assertion in &self.ctx.assertions {
            if let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(assertion) {
                if name != "=" || args.len() != 2 {
                    continue;
                }
                let (a, b) = (args[0], args[1]);

                Self::try_extract_len_constraint(&self.ctx.terms, a, b, &mut len_map);
                Self::try_extract_len_constraint(&self.ctx.terms, b, a, &mut len_map);

                Self::try_extract_nth_constraint(&self.ctx.terms, a, b, &mut nth_map);
                Self::try_extract_nth_constraint(&self.ctx.terms, b, a, &mut nth_map);
            }
        }

        // For each variable with known length and all elements defined,
        // synthesize a ground sequence and add to the map.
        for (var, len) in &len_map {
            if map.contains_key(var) {
                continue;
            }
            // Cap at 64 elements to avoid blowup
            if *len > 64 {
                continue;
            }
            if let Some(elements) = nth_map.get(var) {
                let mut index_vals: Vec<Option<TermId>> = vec![None; *len];
                for &(idx, val) in elements {
                    if idx < *len {
                        index_vals[idx] = Some(val);
                    }
                }
                if index_vals.iter().all(Option::is_some) {
                    if let Some(ground_term) = self.synthesize_ground_seq(*var, &index_vals) {
                        map.insert(*var, ground_term);
                    }
                }
            }
        }

        map
    }

    /// Extract `(= (seq.len s) n)`: lhs is `seq.len(var)`, rhs is int constant.
    fn try_extract_len_constraint(
        terms: &z4_core::term::TermStore,
        lhs: TermId,
        rhs: TermId,
        len_map: &mut hashbrown::HashMap<TermId, usize>,
    ) {
        if let TermData::App(Symbol::Named(name), args) = terms.get(lhs) {
            if name == "seq.len" && args.len() == 1 {
                let seq_var = args[0];
                if matches!(terms.get(seq_var), TermData::Var(..)) {
                    if let TermData::Const(Constant::Int(n)) = terms.get(rhs) {
                        if let Some(len) = n.to_usize() {
                            len_map.insert(seq_var, len);
                        }
                    }
                }
            }
        }
    }

    /// Extract `(= (seq.nth s i) c)`: lhs is `seq.nth(var, int_const)`, rhs is constant.
    fn try_extract_nth_constraint(
        terms: &z4_core::term::TermStore,
        lhs: TermId,
        rhs: TermId,
        nth_map: &mut hashbrown::HashMap<TermId, Vec<(usize, TermId)>>,
    ) {
        if let TermData::App(Symbol::Named(name), args) = terms.get(lhs) {
            if name == "seq.nth" && args.len() == 2 {
                let seq_var = args[0];
                let idx_term = args[1];
                if matches!(terms.get(seq_var), TermData::Var(..)) {
                    if let TermData::Const(Constant::Int(idx_val)) = terms.get(idx_term) {
                        if let Some(idx) = idx_val.to_usize() {
                            if matches!(terms.get(rhs), TermData::Const(..)) {
                                nth_map.entry(seq_var).or_default().push((idx, rhs));
                            }
                        }
                    }
                }
            }
        }
    }

    /// Synthesize a ground sequence term from element constants.
    /// Returns `None` if the variable's sort is not `Seq(T)`.
    fn synthesize_ground_seq(
        &mut self,
        var: TermId,
        elements: &[Option<TermId>],
    ) -> Option<TermId> {
        let seq_sort = self.ctx.terms.sort(var).clone();
        let _elem_sort = seq_sort.seq_element()?;

        if elements.is_empty() {
            return Some(self.mk_seq_empty(&seq_sort));
        }

        // Build right-to-left: seq.++(seq.unit(c_last), seq.empty), then prepend each.
        let empty = self.mk_seq_empty(&seq_sort);

        let mut result = empty;
        for elem_const in elements.iter().rev() {
            let c = (*elem_const)?;
            let unit = self
                .ctx
                .terms
                .mk_app(Symbol::named("seq.unit"), vec![c], seq_sort.clone());
            result = self.ctx.terms.mk_app(
                Symbol::named("seq.++"),
                vec![unit, result],
                seq_sort.clone(),
            );
        }

        Some(result)
    }

    /// Generate equality axioms for nth-reconstructed ground sequences (#6036).
    ///
    /// For each variable `s` where `(= (seq.len s) n)` and all `n` elements
    /// are defined via `(= (seq.nth s i) ci)`, inject `(= s ground_seq)`.
    /// This makes ALL axiom generators (extract, prefixof, etc.) benefit from
    /// nth ground reconstruction, not just `contains` (#6028).
    pub(super) fn generate_nth_ground_equality_axioms(&mut self) -> Vec<TermId> {
        let mut axioms = Vec::new();
        let mut len_map: hashbrown::HashMap<TermId, usize> = hashbrown::HashMap::new();
        let mut nth_map: hashbrown::HashMap<TermId, Vec<(usize, TermId)>> =
            hashbrown::HashMap::new();

        // Check for variables already equated to ground seqs (skip those).
        let mut already_ground = hashbrown::HashSet::new();
        for &assertion in &self.ctx.assertions {
            if let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(assertion) {
                if name == "=" && args.len() == 2 {
                    let (a, b) = (args[0], args[1]);
                    if matches!(self.ctx.terms.get(a), TermData::Var(..))
                        && self.try_extract_ground_seq(b).is_some()
                    {
                        already_ground.insert(a);
                    } else if matches!(self.ctx.terms.get(b), TermData::Var(..))
                        && self.try_extract_ground_seq(a).is_some()
                    {
                        already_ground.insert(b);
                    }
                }
            }
        }

        for &assertion in &self.ctx.assertions {
            if let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(assertion) {
                if name != "=" || args.len() != 2 {
                    continue;
                }
                let (a, b) = (args[0], args[1]);
                Self::try_extract_len_constraint(&self.ctx.terms, a, b, &mut len_map);
                Self::try_extract_len_constraint(&self.ctx.terms, b, a, &mut len_map);
                Self::try_extract_nth_constraint(&self.ctx.terms, a, b, &mut nth_map);
                Self::try_extract_nth_constraint(&self.ctx.terms, b, a, &mut nth_map);
            }
        }

        for (var, len) in &len_map {
            if already_ground.contains(var) || *len > 64 {
                continue;
            }
            if let Some(elements) = nth_map.get(var) {
                let mut index_vals: Vec<Option<TermId>> = vec![None; *len];
                for &(idx, val) in elements {
                    if idx < *len {
                        index_vals[idx] = Some(val);
                    }
                }
                if index_vals.iter().all(Option::is_some) {
                    if let Some(ground_term) = self.synthesize_ground_seq(*var, &index_vals) {
                        axioms.push(self.ctx.terms.mk_eq(*var, ground_term));
                    }
                }
            }
        }

        axioms
    }

    /// Try to extract a ground (fully concrete) sequence as a list of element TermIds.
    ///
    /// Returns `Some(elements)` if the term is a ground sequence composed entirely
    /// of `seq.unit(constant)`, `seq.++`, and `seq.empty`. Each element in the
    /// returned Vec is a `seq.unit(constant)` TermId.
    ///
    /// Returns `None` if the term contains variables, uninterpreted functions,
    /// or other non-ground subterms.
    pub(super) fn try_extract_ground_seq(&self, term: TermId) -> Option<Vec<TermId>> {
        let mut elements = Vec::new();
        let mut stack = vec![term];

        while let Some(t) = stack.pop() {
            match self.ctx.terms.get(t) {
                TermData::App(Symbol::Named(name), args) => match name.as_str() {
                    "seq.unit" if args.len() == 1 => {
                        // Check that the argument is a constant
                        match self.ctx.terms.get(args[0]) {
                            TermData::Const(_) => elements.push(t),
                            _ => return None,
                        }
                    }
                    "seq.++" if args.len() >= 2 => {
                        // Push arguments in reverse order so they come out in order
                        for arg in args.iter().rev() {
                            stack.push(*arg);
                        }
                    }
                    "seq.empty" if args.is_empty() => {
                        // Empty sequence contributes no elements
                    }
                    _ => return None, // Non-ground
                },
                _ => return None, // Variable or non-App
            }
        }

        Some(elements)
    }

    /// Evaluate ground `seq.contains(s, t)` by checking if the element sequence
    /// of `t` appears as a contiguous subsequence of `s`.
    ///
    /// Both `s_elems` and `t_elems` are lists of `seq.unit(constant)` TermIds.
    /// Two elements match if their underlying constants are equal.
    pub(super) fn ground_seq_contains(&self, s_elems: &[TermId], t_elems: &[TermId]) -> bool {
        if t_elems.is_empty() {
            return true;
        }
        if t_elems.len() > s_elems.len() {
            return false;
        }
        // Sliding window search
        'outer: for i in 0..=(s_elems.len() - t_elems.len()) {
            for j in 0..t_elems.len() {
                if !self.ground_seq_elem_eq(s_elems[i + j], t_elems[j]) {
                    continue 'outer;
                }
            }
            return true;
        }
        false
    }

    /// Check if two `seq.unit(constant)` elements have equal underlying constants.
    pub(super) fn ground_seq_elem_eq(&self, a: TermId, b: TermId) -> bool {
        match (self.ctx.terms.get(a), self.ctx.terms.get(b)) {
            (
                TermData::App(Symbol::Named(na), args_a),
                TermData::App(Symbol::Named(nb), args_b),
            ) if na == "seq.unit" && nb == "seq.unit" && args_a.len() == 1 && args_b.len() == 1 => {
                match (self.ctx.terms.get(args_a[0]), self.ctx.terms.get(args_b[0])) {
                    (TermData::Const(ca), TermData::Const(cb)) => ca == cb,
                    _ => false,
                }
            }
            _ => false,
        }
    }

    /// Create the canonical empty sequence term for the given sequence sort.
    ///
    /// String axioms use `""` so they share a TermId with parsed string literals.
    /// Other sequence sorts have no string-literal encoding, so use `seq.empty`.
    pub(super) fn mk_seq_empty(&mut self, seq_sort: &z4_core::Sort) -> TermId {
        if *seq_sort == z4_core::Sort::String {
            self.ctx.terms.mk_string(String::new())
        } else {
            self.ctx
                .terms
                .mk_app(Symbol::named("seq.empty"), vec![], seq_sort.clone())
        }
    }

    /// Create a `seq.len(t)` term node.
    pub(super) fn mk_seq_len(&mut self, seq_term: TermId) -> TermId {
        self.ctx
            .terms
            .mk_app(Symbol::named("seq.len"), vec![seq_term], z4_core::Sort::Int)
    }
}
