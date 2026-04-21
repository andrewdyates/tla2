// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![forbid(unsafe_code)]

//! Z4 DT - Algebraic Datatypes theory solver
//!
//! Implements reasoning about algebraic datatypes (constructors, selectors, testers).
//!
//! ## Algorithm
//!
//! Based on Barrett, Shikanian, and Tinelli's 2007 algorithm:
//! - **Constructor clash**: C1(a) = C2(b) where C1 != C2 → CONFLICT
//! - **Injectivity**: C(a1, ..., an) = C(b1, ..., bn) → a1 = b1 AND ... AND an = bn
//!
//! ## References
//!
//! - Barrett et al. "An Abstract Decision Procedure for a Theory of Inductive Data Types" (2007)
//! - Z3: reference/z3/src/smt/theory_datatype.cpp (MIT)
//! - Design: designs/2026-01-31-mvp-datatype-theory.md

#![warn(missing_docs)]
#![warn(clippy::all)]

mod conflicts;
mod theory_impl;

#[cfg(not(kani))]
use hashbrown::{HashMap, HashSet};
#[cfg(kani)]
use z4_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use z4_core::term::{Symbol, TermData, TermId, TermStore};
use z4_core::{
    DiscoveredEquality, EqualityPropagationResult, TheoryLit, TheoryPropagation, TheoryResult,
    TheorySolver,
};

/// Information about a constructor application term.
#[derive(Debug, Clone)]
struct ConstructorInfo {
    /// Name of the datatype (e.g., "Option")
    dt_name: String,
    /// Name of the constructor (e.g., "Some", "None")
    ctor_name: String,
    /// Argument term IDs (parallel to constructor fields)
    args: Vec<TermId>,
}

/// An undo record for rolling back mutations on pop().
///
/// Scope state for push/pop support.
#[derive(Debug, Clone, Default)]
struct DtScope {
    /// Constructor registrations added in this scope
    registered_ctors: Vec<TermId>,
    /// Length of `asserted_eq_lits` before this scope (for rollback).
    asserted_eq_lits_len: usize,
    /// Length of `asserted_diseqs` before this scope was pushed.
    asserted_diseqs_len: usize,
    /// Tester result keys added in this scope (for undo on pop).
    tester_keys: Vec<TermId>,
    /// Snapshot of the union-find `parent` map at push time.
    /// Restored on pop to undo all union() and path compression changes (#3656).
    parent_snapshot: HashMap<TermId, TermId>,
}

/// Datatype theory solver
///
/// Tracks constructor applications and detects:
/// 1. **Constructor clash**: Two different constructors in the same equivalence class
/// 2. **Injectivity**: Same constructor applications should have equal fields
pub struct DtSolver<'a> {
    /// Reference to the term store for looking up term structure
    terms: &'a TermStore,
    /// Map from term IDs to their constructor info (if they are constructor applications)
    term_constructors: HashMap<TermId, ConstructorInfo>,
    /// Union-find for equivalence classes. Maps term -> representative.
    parent: HashMap<TermId, TermId>,
    /// Pending propagations (injectivity equalities)
    pending: Vec<TheoryPropagation>,
    /// Scope stack for push/pop
    scopes: Vec<DtScope>,
    /// Current scope
    current_scope: DtScope,
    /// Registered datatype definitions: dt_name -> list of constructor names
    datatype_defs: HashMap<String, Vec<String>>,
    /// Constructor name -> datatype name mapping
    ctor_to_dt: HashMap<String, String>,
    /// Registered tester predicates: is-CtorName -> (dt_name, ctor_name)
    tester_map: HashMap<String, (String, String)>,
    /// Asserted tester results: arg_term -> (ctor_name, value, tester_literal).
    /// The tester_literal is the original `is-C(arg)` term for conflict explanation.
    tester_results: HashMap<TermId, (String, bool, TermId)>,
    /// Equality literals asserted true (used for conflict explanation).
    asserted_eq_lits: Vec<TermId>,
    /// Pending injectivity equalities to propagate via Nelson-Oppen.
    /// These are discovered when same-constructor terms are in the same equivalence class.
    pending_injectivity_eqs: Vec<DiscoveredEquality>,
    /// Track which (lhs, rhs) pairs we've already propagated to avoid duplicates.
    propagated_eq_pairs: HashSet<(TermId, TermId)>,
    /// Asserted disequalities: (lhs, rhs, reason_lit). Used to detect injectivity conflicts.
    asserted_diseqs: Vec<(TermId, TermId, TermId)>,
    // Per-theory runtime statistics (#4706)
    check_count: u64,
    conflict_count: u64,
    propagation_count: u64,
    /// Cached `Z4_DEBUG_DT` / `Z4_DEBUG_THEORY` env-var flag (#4706).
    debug: bool,
}

impl<'a> DtSolver<'a> {
    /// Create a new DT solver with access to the term store
    #[must_use]
    pub fn new(terms: &'a TermStore) -> Self {
        DtSolver {
            terms,
            term_constructors: HashMap::new(),
            parent: HashMap::new(),
            pending: Vec::new(),
            scopes: Vec::new(),
            current_scope: DtScope::default(),
            datatype_defs: HashMap::new(),
            ctor_to_dt: HashMap::new(),
            tester_map: HashMap::new(),
            tester_results: HashMap::new(),
            asserted_eq_lits: Vec::new(),
            pending_injectivity_eqs: Vec::new(),
            propagated_eq_pairs: HashSet::new(),
            asserted_diseqs: Vec::new(),
            check_count: 0,
            conflict_count: 0,
            propagation_count: 0,
            debug: std::env::var("Z4_DEBUG_DT").is_ok() || std::env::var("Z4_DEBUG_THEORY").is_ok(),
        }
    }

    /// Register a datatype definition.
    ///
    /// This is called when `declare-datatype` is processed.
    pub fn register_datatype(&mut self, dt_name: &str, constructors: &[String]) {
        self.datatype_defs
            .insert(dt_name.to_string(), constructors.to_vec());
        for ctor in constructors {
            let tester_name = format!("is-{ctor}");
            self.tester_map
                .insert(tester_name, (dt_name.to_string(), ctor.clone()));
            // Track constructor -> datatype mapping
            self.ctor_to_dt.insert(ctor.clone(), dt_name.to_string());
        }
    }

    /// Get the datatype name for a constructor
    fn get_datatype_for_ctor(&self, name: &str) -> Option<&str> {
        self.ctor_to_dt.get(name).map(String::as_str)
    }

    /// Try to extract constructor info from a term
    fn try_extract_constructor(&self, term_id: TermId) -> Option<(String, String, Vec<TermId>)> {
        match self.terms.get(term_id) {
            TermData::App(Symbol::Named(name), args) => {
                if let Some(dt_name) = self.get_datatype_for_ctor(name) {
                    return Some((dt_name.to_string(), name.clone(), args.clone()));
                }
                None
            }
            TermData::Var(name, _) => {
                // Nullary constructors are stored as variables
                if let Some(dt_name) = self.get_datatype_for_ctor(name) {
                    return Some((dt_name.to_string(), name.clone(), vec![]));
                }
                None
            }
            _ => None,
        }
    }

    /// Process an equality, potentially involving constructor terms
    fn process_equality(&mut self, eq_term: TermId, lhs: TermId, rhs: TermId, positive: bool) {
        if !positive {
            // Track disequalities for injectivity-conflict checking.
            self.asserted_diseqs.push((lhs, rhs, eq_term));
            self.current_scope.asserted_diseqs_len = self
                .current_scope
                .asserted_diseqs_len
                .max(self.asserted_diseqs.len());
            return;
        }

        // Track the equality literal for conflict explanation
        self.asserted_eq_lits.push(eq_term);

        // Register any constructor applications
        for &side in &[lhs, rhs] {
            if let Some((dt_name, ctor_name, args)) = self.try_extract_constructor(side) {
                if !self.term_constructors.contains_key(&side) {
                    self.register_constructor(side, &dt_name, &ctor_name, &args);
                }
            }
        }

        // Union the terms
        self.union(lhs, rhs);
    }

    /// Decode a NOT wrapper: `(not inner)` → Some(inner)
    fn decode_not(&self, term: TermId) -> Option<TermId> {
        match self.terms.get(term) {
            TermData::Not(inner) => Some(*inner),
            _ => None,
        }
    }

    /// Decode an equality: `(= lhs rhs)` → Some((lhs, rhs))
    fn decode_eq(&self, term: TermId) -> Option<(TermId, TermId)> {
        match self.terms.get(term) {
            TermData::App(sym, args) if sym.name() == "=" && args.len() == 2 => {
                Some((args[0], args[1]))
            }
            _ => None,
        }
    }

    /// Register a constructor application for a term
    pub fn register_constructor(
        &mut self,
        term_id: TermId,
        _dt_name: &str,
        ctor_name: &str,
        args: &[TermId],
    ) {
        let dt_name = self
            .get_datatype_for_ctor(ctor_name)
            .unwrap_or(_dt_name)
            .to_string();
        self.term_constructors.insert(
            term_id,
            ConstructorInfo {
                dt_name,
                ctor_name: ctor_name.to_string(),
                args: args.to_vec(),
            },
        );
        self.current_scope.registered_ctors.push(term_id);
        // Ensure term is in union-find
        self.parent.entry(term_id).or_insert(term_id);
    }

    /// Assert an equality between two terms
    pub fn assert_equality(&mut self, a: TermId, b: TermId) {
        self.union(a, b);
    }

    /// Find the representative of a term in the union-find.
    ///
    /// No path compression: mutations must be undoable on pop().
    /// DT equivalence classes are small enough that O(depth) traversal is fine.
    fn find(&self, term: TermId) -> TermId {
        let mut curr = term;
        loop {
            let parent = *self.parent.get(&curr).unwrap_or(&curr);
            if parent == curr {
                return curr;
            }
            curr = parent;
        }
    }

    /// Union two terms in the union-find.
    ///
    /// Pop restores state via parent_snapshot (#3656).
    fn union(&mut self, a: TermId, b: TermId) {
        let ra = self.find(a);
        let rb = self.find(b);
        if ra != rb {
            self.parent.insert(ra, rb);
        }
    }
}

#[allow(clippy::panic)]
#[cfg(test)]
mod tests;

#[cfg(kani)]
mod verification;
