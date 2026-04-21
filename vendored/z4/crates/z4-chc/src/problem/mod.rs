// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! CHC problem definition

use crate::bv_util::bv_mask;
use crate::{
    ChcExpr, ChcOp, ChcResult, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause, Predicate,
    PredicateId,
};
use rustc_hash::{FxHashMap, FxHashSet};
use std::sync::Arc;

mod analysis;
mod api;
mod case_split;
mod preprocess;
mod scalarization;
#[cfg(test)]
mod tests;

/// A constant array index, either an integer or a bitvector.
///
/// Used during scalarization to represent the set of constant indices at which
/// arrays are accessed.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum ConstIndex {
    Int(i64),
    BitVec(u128, u32), // (value, width)
}

impl ConstIndex {
    /// Convert this index back to a ChcExpr literal.
    fn to_expr(&self) -> ChcExpr {
        match self {
            Self::Int(k) => ChcExpr::Int(*k),
            Self::BitVec(v, w) => ChcExpr::BitVec(*v, *w),
        }
    }

    /// Coerce this index to match the target key sort (#6084).
    ///
    /// When a `Select(Array(BitVec(N), _), Int(k))` is encountered during
    /// scalarization, the constant index is `Int(k)` but needs to become
    /// `BitVec(k, N)` so the generated scalar variable and equality have
    /// the correct sort.
    fn coerce_to_sort(self, key_sort: &ChcSort) -> Self {
        match (&self, key_sort) {
            (Self::Int(k), ChcSort::BitVec(w)) => Self::BitVec(*k as u128 & bv_mask(*w), *w),
            (Self::BitVec(v, _), ChcSort::Int) => Self::Int(*v as i64),
            _ => self,
        }
    }

    /// Suffix string for naming scalar variables, e.g. "0", "neg3", "bv5_32".
    fn suffix(&self) -> String {
        match self {
            Self::Int(k) => {
                if *k < 0 {
                    format!("neg{}", k.unsigned_abs())
                } else {
                    k.to_string()
                }
            }
            Self::BitVec(v, w) => format!("bv{v}_{w}"),
        }
    }
}

/// A Constrained Horn Clause problem
///
/// Contains:
/// - A set of predicate declarations (uninterpreted relations)
/// - A set of Horn clauses (rules)
/// - Query clauses (clauses with false head)
#[derive(Debug, Clone)]
pub struct ChcProblem {
    /// Predicate declarations
    predicates: Vec<Predicate>,
    /// Map from name to predicate ID
    predicate_names: FxHashMap<String, PredicateId>,
    /// All Horn clauses
    clauses: Vec<HornClause>,
    /// Whether the input used Z3 fixedpoint format (declare-rel/rule/query).
    /// In fixedpoint format, sat/unsat polarity is inverted relative to SMT-LIB HORN:
    /// - HORN: sat = satisfiable (safe), unsat = unsatisfiable (unsafe)
    /// - Fixedpoint: sat = query reachable (unsafe), unsat = query unreachable (safe)
    fixedpoint_format: bool,
    /// Datatype definitions from declare-datatype commands (#7016).
    /// Maps datatype name → Vec<(constructor_name, Vec<(selector_name, selector_sort)>)>.
    /// Preserves structural metadata that the function signature map discards.
    datatype_defs: FxHashMap<String, Vec<(String, Vec<(String, ChcSort)>)>>,
}

impl Default for ChcProblem {
    fn default() -> Self {
        Self::new()
    }
}
