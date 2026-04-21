// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! EUF solver query and utility methods.
//!
//! Term decoding, constant lookups, function application tracking,
//! and equality hashing. Extracted from `solver.rs` to keep each file
//! under 500 lines.

use super::solver::EufSolver;
#[cfg(not(kani))]
use hashbrown::HashMap;
#[cfg(kani)]
use z4_core::kani_compat::DetHashMap as HashMap;
use z4_core::term::{Constant, Symbol, TermData, TermId};
use z4_core::Sort;

impl EufSolver<'_> {
    pub(crate) fn is_builtin_symbol(sym: &Symbol) -> bool {
        matches!(sym.name(), "and" | "or" | "=" | "distinct")
    }

    pub(crate) fn decode_eq(&self, term: TermId) -> Option<(TermId, TermId)> {
        match self.terms.get(term) {
            TermData::App(sym, args) if sym.name() == "=" && args.len() == 2 => {
                Some((args[0], args[1]))
            }
            _ => z4_core::decode_bool_biconditional_eq(self.terms, term),
        }
    }

    pub(crate) fn decode_distinct(&self, term: TermId) -> Option<&[TermId]> {
        match self.terms.get(term) {
            TermData::App(sym, args) if sym.name() == "distinct" => Some(args),
            _ => None,
        }
    }

    /// Check if a term is a constant (Int, Real, BV literal)
    pub(crate) fn is_constant(&self, term: TermId) -> bool {
        matches!(self.terms.get(term), TermData::Const(_))
    }

    /// Find the integer constant value in the same equivalence class as `term`,
    /// if one exists. Used by the Nelson-Oppen interface bridge to evaluate UF
    /// terms like `Succ(x)` when EUF knows `Succ(x) = 1` via congruence. (#5081)
    ///
    /// Returns `(value, const_term_id)` so the caller can build explain reasons.
    pub fn find_int_const_in_class(&self, term: TermId) -> Option<(num_bigint::BigInt, TermId)> {
        // Use E-graph class iteration in incremental mode (O(class_size)),
        // fall back to linear scan over UF in legacy mode (O(|terms|)).
        if !self.enodes_init || (term.0 as usize) >= self.enodes.len() {
            return None;
        }
        let rep = self.enode_find_const(term.0);
        for member in self.enode_class_iter(rep) {
            let tid = TermId(member);
            if let TermData::Const(Constant::Int(n)) = self.terms.get(tid) {
                return Some((n.clone(), tid));
            }
        }
        None
    }

    /// Build a map from TermId → (integer_value, constant_term_id) for all terms
    /// in equivalence classes that contain an integer constant. Single-pass O(n)
    /// construction, used by the Nelson-Oppen bridge to evaluate UF subterms. (#5081)
    pub fn build_int_value_map(&self) -> HashMap<TermId, (num_bigint::BigInt, TermId)> {
        // Pass 1: find the integer constant for each representative (if any).
        let mut rep_to_const: HashMap<u32, (num_bigint::BigInt, TermId)> = HashMap::new();
        for tid in self.terms.term_ids() {
            if let TermData::Const(Constant::Int(val)) = self.terms.get(tid) {
                let rep = self.enode_find_const(tid.0);
                rep_to_const
                    .entry(rep)
                    .or_insert_with(|| (val.clone(), tid));
            }
        }
        if rep_to_const.is_empty() {
            return HashMap::new();
        }
        // Pass 2: for each non-constant term, check if its representative has a constant.
        let mut result = HashMap::new();
        for tid in self.terms.term_ids() {
            if matches!(self.terms.get(tid), TermData::Const(Constant::Int(_))) {
                continue; // Skip constants themselves
            }
            let rep = self.enode_find_const(tid.0);
            if let Some(entry) = rep_to_const.get(&rep) {
                result.insert(tid, entry.clone());
            }
        }
        result
    }

    /// Check if a term is a UF function application (not a builtin) returning a theory sort
    pub(crate) fn is_theory_func_app(&self, term: TermId) -> bool {
        match self.terms.get(term) {
            TermData::App(sym, args) if !Self::is_builtin_symbol(sym) && !args.is_empty() => {
                // Check return sort is a theory sort (Int, Real, BV)
                let sort = self.terms.sort(term);
                matches!(sort, Sort::Int | Sort::Real | Sort::BitVec(_))
            }
            _ => false,
        }
    }

    /// Track function application value when processing (= func_app constant)
    pub(crate) fn try_track_func_app_value(&mut self, eq_term: TermId) {
        if let Some((lhs, rhs)) = self.decode_eq(eq_term) {
            // Check both directions: (= func_app const) and (= const func_app)
            let (func_app, constant) = if self.is_theory_func_app(lhs) && self.is_constant(rhs) {
                (lhs, rhs)
            } else if self.is_theory_func_app(rhs) && self.is_constant(lhs) {
                (rhs, lhs)
            } else {
                return;
            };

            // Only record if we don't already have a value for this func_app
            if !self.func_app_values.contains_key(&func_app) {
                self.func_app_values.insert(func_app, constant);
            }
        }
    }

    /// Rebuild tracked UF application values from the currently asserted literals.
    /// Needed after incremental pop(), which clears derived state but does not
    /// force a full rebuild before callers may extract a model.
    pub(crate) fn resync_func_app_values_from_assigns(&mut self) {
        self.func_app_values.clear();
        let true_equalities: Vec<TermId> = self
            .assigns
            .iter()
            .filter_map(|(&term, &value)| value.then_some(term))
            .collect();
        for eq_term in true_equalities {
            self.try_track_func_app_value(eq_term);
        }
    }

    /// Helper to create a canonical edge key (smaller id first)
    pub(crate) fn edge_key(a: u32, b: u32) -> (u32, u32) {
        if a < b {
            (a, b)
        } else {
            (b, a)
        }
    }
}
