// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl ChcProblem {
    /// Create a new empty CHC problem
    pub fn new() -> Self {
        Self {
            predicates: Vec::new(),
            predicate_names: FxHashMap::default(),
            clauses: Vec::new(),
            fixedpoint_format: false,
            datatype_defs: FxHashMap::default(),
        }
    }

    /// Declare a new predicate
    pub fn declare_predicate(
        &mut self,
        name: impl Into<String>,
        arg_sorts: Vec<ChcSort>,
    ) -> PredicateId {
        let name = name.into();
        let id = PredicateId::new(self.predicates.len() as u32);
        let pred = Predicate::new(id, name.clone(), arg_sorts);
        self.predicates.push(pred);
        self.predicate_names.insert(name, id);
        id
    }

    /// Get a predicate by ID
    pub fn get_predicate(&self, id: PredicateId) -> Option<&Predicate> {
        self.predicates.get(id.index())
    }

    /// Get a predicate by name
    pub fn get_predicate_by_name(&self, name: &str) -> Option<&Predicate> {
        self.predicate_names
            .get(name)
            .and_then(|id| self.predicates.get(id.index()))
    }

    /// Look up predicate ID by name
    pub fn lookup_predicate(&self, name: &str) -> Option<PredicateId> {
        self.predicate_names.get(name).copied()
    }

    /// Add a Horn clause
    pub fn add_clause(&mut self, clause: HornClause) {
        self.clauses.push(clause);
    }

    /// Iteratively tear down owned clause expressions to avoid recursive Drop.
    pub(crate) fn iterative_drop(mut self) {
        for clause in self.clauses.drain(..) {
            clause.iterative_drop();
        }
    }

    /// Get all clauses
    pub fn clauses(&self) -> &[HornClause] {
        &self.clauses
    }

    /// Get mutable access to all clauses
    pub fn clauses_mut(&mut self) -> &mut [HornClause] {
        &mut self.clauses
    }

    /// Get all predicates
    pub fn predicates(&self) -> &[Predicate] {
        &self.predicates
    }

    /// Whether the input used Z3 fixedpoint format (declare-rel/rule/query).
    /// When true, the sat/unsat output polarity must be inverted:
    /// Safe => "unsat", Unsafe => "sat" (opposite of HORN convention).
    pub fn is_fixedpoint_format(&self) -> bool {
        self.fixedpoint_format
    }

    /// Mark this problem as using Z3 fixedpoint format.
    pub fn set_fixedpoint_format(&mut self) {
        self.fixedpoint_format = true;
    }

    /// Datatype definitions from declare-datatype commands (#7016).
    /// Maps datatype name → Vec<(constructor_name, Vec<(selector_name, selector_sort)>)>.
    pub fn datatype_defs(&self) -> &FxHashMap<String, Vec<(String, Vec<(String, ChcSort)>)>> {
        &self.datatype_defs
    }

    /// Register a datatype definition parsed from declare-datatype (#7016).
    pub fn add_datatype_def(
        &mut self,
        name: String,
        constructors: Vec<(String, Vec<(String, ChcSort)>)>,
    ) {
        self.datatype_defs.insert(name, constructors);
    }

    /// Create an SmtContext pre-configured with this problem's DT definitions (#7016).
    pub fn make_smt_context(&self) -> crate::smt::SmtContext {
        let mut smt = crate::smt::SmtContext::new();
        if !self.datatype_defs.is_empty() {
            smt.set_datatype_defs(self.datatype_defs.clone());
        }
        smt
    }

    /// Whether any predicate has a BitVec-sorted argument.
    /// Used to skip pure QF_LIA assumptions in model verification
    /// (BV constraints are expected to produce Unknown from the LIA solver).
    pub fn has_bv_sorts(&self) -> bool {
        self.predicates
            .iter()
            .any(|p| p.arg_sorts.iter().any(|s| matches!(s, ChcSort::BitVec(_))))
    }

    /// Maximum predicate arity if BvToBool bit-blasting were applied.
    /// Each `BitVec(w)` argument expands to `w` Bool arguments.
    /// Used to decide whether BvToBool arity explosion is too severe (#5877).
    pub fn max_bv_expanded_arity(&self) -> usize {
        self.predicates
            .iter()
            .map(|p| {
                p.arg_sorts
                    .iter()
                    .map(|s| match s {
                        ChcSort::BitVec(w) => *w as usize,
                        _ => 1,
                    })
                    .sum::<usize>()
            })
            .max()
            .unwrap_or(0)
    }

    /// Whether the problem contains BV operations that BvToInt cannot encode
    /// exactly (bitwise, shift, rotation, signed div/rem/mod).
    ///
    /// When false, BvToInt preserves full precision and BvToBool bit-blasting
    /// can be skipped to avoid predicate arity explosion. For example, a
    /// predicate with 10 BV32 arguments stays at arity 10 (as Int) instead of
    /// expanding to 320 Bool parameters (#5877).
    pub fn has_bv_bitwise_ops(&self) -> bool {
        self.clauses.iter().any(|clause| {
            // Check body constraint
            if let Some(c) = &clause.body.constraint {
                if c.contains_bv_bitwise_ops() {
                    return true;
                }
            }
            // Check body predicate arguments
            for (_, args) in &clause.body.predicates {
                for arg in args {
                    if arg.contains_bv_bitwise_ops() {
                        return true;
                    }
                }
            }
            // Check head predicate arguments
            if let ClauseHead::Predicate(_, args) = &clause.head {
                for arg in args {
                    if arg.contains_bv_bitwise_ops() {
                        return true;
                    }
                }
            }
            false
        })
    }

    /// Whether any predicate has an Array-sorted argument.
    /// Used to guard engines whose transition-system encodings only handle
    /// scalar predicate state.
    pub fn has_array_sorts(&self) -> bool {
        self.predicates
            .iter()
            .any(|p| p.arg_sorts.iter().any(Self::sort_contains_array))
    }

    fn sort_contains_array(sort: &ChcSort) -> bool {
        match sort {
            ChcSort::Array(_, _) => true,
            _ => false,
        }
    }

    /// Whether any predicate has a Real-sorted argument.
    /// Used to guard Kind deferred-safe and other paths that lack LRA model support.
    pub fn has_real_sorts(&self) -> bool {
        self.predicates
            .iter()
            .any(|p| p.arg_sorts.iter().any(Self::sort_contains_real))
    }

    fn sort_contains_real(sort: &ChcSort) -> bool {
        match sort {
            ChcSort::Real => true,
            ChcSort::Array(k, v) => Self::sort_contains_real(k) || Self::sort_contains_real(v),
            _ => false,
        }
    }

    /// Whether any predicate has a Datatype-sorted argument (#7930).
    /// Used to skip Kind engine and cap PDR escalation for DT+BV problems.
    pub fn has_datatype_sorts(&self) -> bool {
        self.predicates
            .iter()
            .any(|p| p.arg_sorts.iter().any(Self::sort_contains_datatype))
    }

    fn sort_contains_datatype(sort: &ChcSort) -> bool {
        match sort {
            ChcSort::Datatype { .. } => true,
            ChcSort::Array(k, v) => {
                Self::sort_contains_datatype(k) || Self::sort_contains_datatype(v)
            }
            _ => false,
        }
    }
}
